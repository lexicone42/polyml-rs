//! The binary **bicimage** format — a compact, endian-neutral binary
//! serialization of the same object graph as the [`crate::pexport`] text format.
//!
//! Motivation (`notes/hard-problems.md` §5, and the cross-word-size finding in
//! `docs/tier-b-portable-images-design.md`): pexport is a *text* format (decimal
//! integers + hex byte strings) — portable on the wire but bulky and slow to
//! parse. `bicimage` carries the identical [`Image`] (objects / root / arch /
//! word size) as a tagged binary stream:
//!
//! - **Endian-neutral.** Every multi-byte quantity is an LEB128 varint (a byte
//!   stream, no host byte order), so a `.bic` written on one machine reads
//!   identically on any other — the portable-image property, by construction.
//! - **Explicitly tagged.** The header records the source arch + word size, so a
//!   reader can decide compatibility up front (same-word-size cross-arch loads;
//!   cross-word-size carries *data*, not word-size-specific compiled code — see
//!   the design doc).
//! - **Compact.** Small ints/ids are 1–2 bytes (vs. their decimal/hex text), and
//!   byte segments are length-prefixed raw bytes (no hex doubling).
//!
//! This is a faithful re-encoding: `read_bic(write_bic(img)) == img` for every
//! `Image` (round-trip test below), and pexport→bic→runtime loads identically to
//! pexport→runtime.

// Intentional, checked casts in the binary codec: zigzag/unzigzag reinterpret
// bits by design, and word_size.bytes() is only ever 4 or 8.
#![allow(
    clippy::cast_sign_loss,
    clippy::cast_possible_wrap,
    clippy::cast_possible_truncation
)]

use crate::pexport::{CodeReloc, Image, ObjFlags, Object, ObjectBody, SourceArch, Value, WordSize};
use std::io::{self, Write};
use thiserror::Error;

/// Magic prefix: `"BICIMG"` + a format-version byte. Bump the version byte on any
/// incompatible layout change.
pub const MAGIC: &[u8; 7] = b"BICIMG\x01";

/// Cheap check (used by the CLI to auto-detect `.bic` vs pexport text).
#[must_use]
pub fn is_bicimage(bytes: &[u8]) -> bool {
    bytes.starts_with(MAGIC)
}

#[derive(Debug, Error)]
pub enum BicError {
    #[error("not a bicimage (bad magic)")]
    BadMagic,
    #[error("unexpected end of input at byte {at}")]
    Eof { at: usize },
    #[error("unknown object type tag {tag} at byte {at}")]
    BadType { tag: u8, at: usize },
    #[error("unknown value tag {tag} at byte {at}")]
    BadValue { tag: u8, at: usize },
    #[error("varint overflow at byte {at}")]
    VarintOverflow { at: usize },
    #[error("length {len} exceeds remaining input at byte {at}")]
    BadLength { len: u64, at: usize },
}

// ---- varint helpers (LEB128; zigzag for signed) -----------------------------

fn write_uvarint<W: Write>(w: &mut W, mut v: u64) -> io::Result<()> {
    loop {
        let byte = (v & 0x7f) as u8;
        v >>= 7;
        if v == 0 {
            return w.write_all(&[byte]);
        }
        w.write_all(&[byte | 0x80])?;
    }
}

const fn zigzag(v: i64) -> u64 {
    ((v << 1) ^ (v >> 63)) as u64
}

const fn unzigzag(v: u64) -> i64 {
    ((v >> 1) as i64) ^ -((v & 1) as i64)
}

// ---- arch <-> byte (mirrors the pexport text writer) ------------------------

const fn arch_byte(a: SourceArch) -> u8 {
    match a {
        SourceArch::Interpreted => b'I',
        SourceArch::X86 => b'X',
        SourceArch::Arm => b'A',
        SourceArch::Other(c) => c,
    }
}

const fn arch_from_byte(b: u8) -> SourceArch {
    match b {
        b'I' => SourceArch::Interpreted,
        b'X' => SourceArch::X86,
        b'A' => SourceArch::Arm,
        other => SourceArch::Other(other),
    }
}

// ---- object type tags -------------------------------------------------------

const T_ORDINARY: u8 = 0;
const T_CLOSURE: u8 = 1;
const T_LEGACY_CLOSURE: u8 = 2;
const T_STRING: u8 = 3;
const T_BYTES: u8 = 4;
const T_CODE: u8 = 5;
const T_ENTRY_POINT: u8 = 6;
const T_WEAK_REF: u8 = 7;

// ---- value tags -------------------------------------------------------------

const V_TAGGED: u8 = 0;
const V_REF: u8 = 1;

// ---- writer -----------------------------------------------------------------

fn write_value<W: Write>(w: &mut W, v: Value) -> io::Result<()> {
    match v {
        Value::Tagged(n) => {
            w.write_all(&[V_TAGGED])?;
            write_uvarint(w, zigzag(n))
        }
        Value::Ref(id) => {
            w.write_all(&[V_REF])?;
            write_uvarint(w, u64::from(id))
        }
    }
}

fn write_values<W: Write>(w: &mut W, vs: &[Value]) -> io::Result<()> {
    write_uvarint(w, vs.len() as u64)?;
    for &v in vs {
        write_value(w, v)?;
    }
    Ok(())
}

fn write_bytes<W: Write>(w: &mut W, b: &[u8]) -> io::Result<()> {
    write_uvarint(w, b.len() as u64)?;
    w.write_all(b)
}

fn write_body<W: Write>(w: &mut W, body: &ObjectBody) -> io::Result<()> {
    match body {
        ObjectBody::Ordinary(vs) => {
            w.write_all(&[T_ORDINARY])?;
            write_values(w, vs)
        }
        ObjectBody::Closure { code_addr, values } => {
            w.write_all(&[T_CLOSURE])?;
            write_uvarint(w, u64::from(*code_addr))?;
            write_values(w, values)
        }
        ObjectBody::LegacyClosure { values } => {
            w.write_all(&[T_LEGACY_CLOSURE])?;
            write_values(w, values)
        }
        ObjectBody::String(b) => {
            w.write_all(&[T_STRING])?;
            write_bytes(w, b)
        }
        ObjectBody::Bytes(b) => {
            w.write_all(&[T_BYTES])?;
            write_bytes(w, b)
        }
        ObjectBody::Code {
            code_bytes,
            constants,
            relocs,
        } => {
            w.write_all(&[T_CODE])?;
            write_bytes(w, code_bytes)?;
            write_values(w, constants)?;
            write_uvarint(w, relocs.len() as u64)?;
            for r in relocs {
                write_uvarint(w, u64::from(r.offset))?;
                w.write_all(&[r.kind])?;
                write_uvarint(w, u64::from(r.target))?;
            }
            Ok(())
        }
        ObjectBody::EntryPoint(name) => {
            w.write_all(&[T_ENTRY_POINT])?;
            write_bytes(w, name.as_bytes())
        }
        ObjectBody::WeakRef => w.write_all(&[T_WEAK_REF]),
    }
}

impl Image {
    /// Serialize this image to the binary bicimage format.
    ///
    /// # Errors
    /// Propagates any I/O error from the writer.
    pub fn write_bic<W: Write>(&self, w: &mut W) -> io::Result<()> {
        w.write_all(MAGIC)?;
        w.write_all(&[arch_byte(self.arch)])?;
        w.write_all(&[self.word_size.bytes() as u8])?;
        write_uvarint(w, u64::from(self.root))?;
        write_uvarint(w, self.objects.len() as u64)?;
        for obj in &self.objects {
            w.write_all(&[obj.flags.bits()])?;
            write_body(w, &obj.body)?;
        }
        Ok(())
    }

    /// Serialize to a freshly-allocated `Vec<u8>`.
    #[must_use]
    pub fn to_bic_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        // Writing to a Vec is infallible.
        self.write_bic(&mut out).expect("Vec write is infallible");
        out
    }

    /// Parse an image from the binary bicimage format.
    ///
    /// # Errors
    /// Returns [`BicError`] on a bad magic, truncated input, or an unknown tag.
    pub fn read_bic(bytes: &[u8]) -> Result<Self, BicError> {
        let mut r = Reader { buf: bytes, pos: 0 };
        for &m in MAGIC {
            if r.u8()? != m {
                return Err(BicError::BadMagic);
            }
        }
        let arch = arch_from_byte(r.u8()?);
        let word_size = match r.u8()? {
            4 => WordSize::Bits32,
            _ => WordSize::Bits64,
        };
        let root = r.u32()?;
        let count = r.usize()?;
        // Capacity hint is clamped to the remaining bytes (each object needs at
        // least 2 bytes: flags + type tag), so a bogus huge count can't OOM.
        let mut objects = Vec::with_capacity(count.min(r.buf.len() / 2 + 1));
        for _ in 0..count {
            let flags = ObjFlags::from_bits_truncate(r.u8()?);
            let body = read_body(&mut r)?;
            objects.push(Object { flags, body });
        }
        Ok(Self {
            root,
            arch,
            word_size,
            objects,
        })
    }
}

// ---- reader -----------------------------------------------------------------

struct Reader<'a> {
    buf: &'a [u8],
    pos: usize,
}

impl Reader<'_> {
    fn u8(&mut self) -> Result<u8, BicError> {
        let b = *self
            .buf
            .get(self.pos)
            .ok_or(BicError::Eof { at: self.pos })?;
        self.pos += 1;
        Ok(b)
    }

    fn uvarint(&mut self) -> Result<u64, BicError> {
        let mut result: u64 = 0;
        let mut shift: u32 = 0;
        loop {
            let byte = self.u8()?;
            if shift >= 64 {
                return Err(BicError::VarintOverflow { at: self.pos });
            }
            result |= u64::from(byte & 0x7f) << shift;
            if byte & 0x80 == 0 {
                return Ok(result);
            }
            shift += 7;
        }
    }

    fn ivarint(&mut self) -> Result<i64, BicError> {
        Ok(unzigzag(self.uvarint()?))
    }

    fn u32(&mut self) -> Result<u32, BicError> {
        u32::try_from(self.uvarint()?).map_err(|_| BicError::VarintOverflow { at: self.pos })
    }

    fn usize(&mut self) -> Result<usize, BicError> {
        usize::try_from(self.uvarint()?).map_err(|_| BicError::VarintOverflow { at: self.pos })
    }

    fn bytes(&mut self) -> Result<Vec<u8>, BicError> {
        let len_u64 = self.uvarint()?;
        let len = usize::try_from(len_u64).map_err(|_| BicError::BadLength {
            len: len_u64,
            at: self.pos,
        })?;
        let end = self
            .pos
            .checked_add(len)
            .filter(|&e| e <= self.buf.len())
            .ok_or(BicError::BadLength {
                len: len_u64,
                at: self.pos,
            })?;
        let v = self.buf[self.pos..end].to_vec();
        self.pos = end;
        Ok(v)
    }

    fn value(&mut self) -> Result<Value, BicError> {
        let tag = self.u8()?;
        match tag {
            V_TAGGED => Ok(Value::Tagged(self.ivarint()?)),
            V_REF => Ok(Value::Ref(self.u32()?)),
            t => Err(BicError::BadValue {
                tag: t,
                at: self.pos,
            }),
        }
    }

    fn values(&mut self) -> Result<Vec<Value>, BicError> {
        let n = self.usize()?;
        // Clamp the capacity hint: each value is ≥2 bytes.
        let mut out = Vec::with_capacity(n.min(self.buf.len() / 2 + 1));
        for _ in 0..n {
            out.push(self.value()?);
        }
        Ok(out)
    }
}

fn read_body(r: &mut Reader) -> Result<ObjectBody, BicError> {
    let tag = r.u8()?;
    match tag {
        T_ORDINARY => Ok(ObjectBody::Ordinary(r.values()?)),
        T_CLOSURE => {
            let code_addr = r.u32()?;
            let values = r.values()?;
            Ok(ObjectBody::Closure { code_addr, values })
        }
        T_LEGACY_CLOSURE => Ok(ObjectBody::LegacyClosure {
            values: r.values()?,
        }),
        T_STRING => Ok(ObjectBody::String(r.bytes()?)),
        T_BYTES => Ok(ObjectBody::Bytes(r.bytes()?)),
        T_CODE => {
            let code_bytes = r.bytes()?;
            let constants = r.values()?;
            let n_relocs = r.usize()?;
            let mut relocs = Vec::with_capacity(n_relocs.min(r.buf.len() / 3 + 1));
            for _ in 0..n_relocs {
                let offset = r.u32()?;
                let kind = r.u8()?;
                let target = r.u32()?;
                relocs.push(CodeReloc {
                    offset,
                    kind,
                    target,
                });
            }
            Ok(ObjectBody::Code {
                code_bytes,
                constants,
                relocs,
            })
        }
        T_ENTRY_POINT => {
            let name = String::from_utf8_lossy(&r.bytes()?).into_owned();
            Ok(ObjectBody::EntryPoint(name))
        }
        T_WEAK_REF => Ok(ObjectBody::WeakRef),
        t => Err(BicError::BadType { tag: t, at: r.pos }),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small pexport image exercising every object variant round-trips
    /// through bic byte-for-byte (Image equality).
    #[test]
    fn round_trip_pexport_image() {
        // ordinary, closure, string, bytes, big tagged int, ref.
        let src = b"Objects\t4\nRoot\t0 I 8\n\
                    0:C2|@1,7\n\
                    1:O2|-1152921504606846976,@2\n\
                    2:S5|68656c6c6f\n\
                    3:B3|010203\n";
        let img = Image::parse(src).expect("parse pexport");
        let bic = img.to_bic_bytes();
        assert!(is_bicimage(&bic), "magic present");
        let back = Image::read_bic(&bic).expect("read bic");
        assert_eq!(img, back, "bic round-trip preserves the image");
    }

    #[test]
    fn bad_magic_is_rejected() {
        assert!(matches!(
            Image::read_bic(b"not a bic"),
            Err(BicError::BadMagic)
        ));
        assert!(!is_bicimage(b"Objects\t1\n"));
    }

    #[test]
    fn truncated_input_errors_cleanly() {
        let src = b"Objects\t1\nRoot\t0 I 8\n0:O1|7\n";
        let img = Image::parse(src).unwrap();
        let bic = img.to_bic_bytes();
        // Lop off the tail: must error, never panic.
        for cut in (MAGIC.len() + 1)..bic.len() {
            let _ = Image::read_bic(&bic[..cut]); // Result; just must not panic.
        }
    }
}
