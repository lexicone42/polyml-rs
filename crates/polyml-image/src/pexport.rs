//! Reader (and eventually writer) for PolyML's portable export text format.
//!
//! The format is defined by `vendor/polyml/libpolyml/pexport.cpp`.
//!
//! A file looks like:
//!
//! ```text
//! Objects<TAB><count>
//! Root<TAB><id> <arch> <word_size>
//! <id>:[MNVW]<type><payload>
//! <id>:[MNVW]<type><payload>
//! ...
//! ```
//!
//! Where `<type>` is one of `O C L S B F E K` and the payload format
//! depends on the type. See `ObjectBody` and the per-type parse routines.
//!
//! The file is parsed in two passes: first we walk every object line to
//! learn its size and allocate a slot, then we re-walk filling in
//! contents (so that forward `@<id>` references resolve cleanly).

use bitflags::bitflags;
use thiserror::Error;

/// An index into [`Image::objects`]. Stored as `u32` to keep [`Value`]
/// small; PolyML images in practice have well under 4 G objects.
pub type ObjectId = u32;

/// Source architecture of the image, as recorded in the `Root` line.
/// See `pexport.cpp:305-315` (writer) and `pexport.cpp:544-549` (reader).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SourceArch {
    /// `'I'` — bytecode interpreter. The interesting case for portability:
    /// images written under `MA_Interpreted` are loadable on any 64-bit
    /// (or 32-bit) target by falling back to the interpreter.
    Interpreted,
    /// `'X'` — i386 / x86_64 / x86_64_32.
    X86,
    /// `'A'` — arm64 / arm64_32.
    Arm,
    /// Some other architecture marker we don't recognise. Keep as raw
    /// char so we can round-trip without losing information.
    Other(u8),
}

/// Native word size as recorded in the image header (4 or 8 bytes).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WordSize {
    Bits32,
    Bits64,
}

impl WordSize {
    #[must_use]
    pub const fn bytes(self) -> usize {
        match self {
            Self::Bits32 => 4,
            Self::Bits64 => 8,
        }
    }
}

bitflags! {
    /// Per-object modifiers, encoded as letters preceding the type char
    /// (in any order). See `pexport.cpp:119-126` (writer) and
    /// `pexport.cpp:568-576` (reader).
    ///
    /// Values match `F_*_BIT` constants in
    /// `vendor/polyml/libpolyml/globals.h:237-249` so they can be OR'd
    /// into a length-word top byte at runtime-conversion time.
    #[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
    pub struct ObjFlags: u8 {
        const MUTABLE      = 0x40;  // M
        const NEGATIVE     = 0x10;  // N — sign bit for arbitrary precision
        const NO_OVERWRITE = 0x08;  // V
        const WEAK         = 0x20;  // W
    }
}

/// A PolyWord value as it appears in a pexport file: either an
/// already-untagged integer or a reference to another object.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Value {
    /// `<digits>` or `-<digits>`. Already untagged — caller is
    /// responsible for re-tagging when converting to runtime form.
    Tagged(i64),
    /// `@<id>` — reference to another object in the image.
    Ref(ObjectId),
}

/// A single relocation within a code object's instruction bytes. See
/// `pexport.cpp:256-267` (writer): `<offset>,<kind>,@<target> `
/// (space-separated within the relocations section).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct CodeReloc {
    /// Byte offset from the start of the code object.
    pub offset: u32,
    /// `ScanRelocationKind` from `vendor/polyml/libpolyml/scanaddrs.h`
    /// — architecture-specific (e.g. x86 RIP-relative vs. arm64 ADRP).
    /// Kept opaque at this layer; the runtime decodes it.
    pub kind: u8,
    pub target: ObjectId,
}

/// Body of an object — the variant differs by type letter in the file.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ObjectBody {
    /// `O<nWords>|<v0>,<v1>,...` — ordinary word object (tuple, record).
    Ordinary(Vec<Value>),
    /// `C<nItems>|@<code>,<v0>,...` — closure (32-in-64 form).
    /// The first item is always a code pointer; the rest are captured
    /// values.
    Closure {
        code_addr: ObjectId,
        values: Vec<Value>,
    },
    /// `L<nWords>|...` — legacy closure (older images). Same shape as
    /// `Closure` for our purposes; we normalise on parse.
    LegacyClosure { values: Vec<Value> },
    /// `S<nBytes>|<hex>` — string (counted bytes, not NUL-terminated in
    /// memory).
    String(Vec<u8>),
    /// `B<nBytes>|<hex>` — byte segment (arbitrary precision int, real,
    /// or other unstructured bytes).
    Bytes(Vec<u8>),
    /// `F<nWords>,<nBytes>|<code_hex>|<c0>,<c1>,...|<reloc> <reloc>...`
    /// — code object. `code_bytes` is the machine code; `constants` are
    /// word-sized PolyWord values appearing in the constants segment;
    /// `relocs` patch addresses *within* the machine code.
    Code {
        code_bytes: Vec<u8>,
        constants: Vec<Value>,
        relocs: Vec<CodeReloc>,
    },
    /// `E<nBytes>|<name>` — entry point. A `uintptr_t` placeholder
    /// followed by a NUL-terminated C string giving the symbol name.
    EntryPoint(String),
    /// `K` — single weak reference (FFI). No payload in the file.
    WeakRef,
}

/// A whole parsed pexport image.
///
/// Conversion to runtime heap layout (mmap, real PolyWord values with
/// bottom-bit tagging) is a separate step in `polyml-runtime`; this
/// type is intended for inspection and for the loader pipeline.
#[derive(Debug, Clone)]
pub struct Image {
    pub root: ObjectId,
    pub arch: SourceArch,
    pub word_size: WordSize,
    pub objects: Vec<Object>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Object {
    pub flags: ObjFlags,
    pub body: ObjectBody,
}

/// Errors returned from [`Image::parse`].
#[derive(Debug, Error)]
pub enum ParseError {
    #[error("unexpected end of input at byte {at}")]
    Eof { at: usize },
    #[error("expected {what} at byte {at}, got {got:?}")]
    Expected {
        what: &'static str,
        at: usize,
        got: u8,
    },
    #[error("malformed header: {0}")]
    BadHeader(&'static str),
    #[error("unknown object type {got:?} at byte {at}")]
    UnknownType { at: usize, got: u8 },
    #[error("object index {id} out of range (count={count})")]
    BadIndex { id: u64, count: u32 },
    #[error("invalid number at byte {at}: {reason}")]
    BadNumber { reason: &'static str, at: usize },
    #[error("invalid hex byte at byte {at}")]
    BadHex { at: usize },
    #[error("declared and observed counts disagree: declared {declared}, observed {observed}")]
    CountMismatch { declared: u32, observed: u32 },
}

// ----- Writer -----------------------------------------------------------

fn write_object<W: std::io::Write>(
    w: &mut W,
    id: u32,
    obj: &Object,
) -> std::io::Result<()> {
    write!(w, "{id}:")?;
    // Modifier letters in the order MNVW (matches upstream).
    if obj.flags.contains(ObjFlags::MUTABLE) {
        w.write_all(b"M")?;
    }
    if obj.flags.contains(ObjFlags::NEGATIVE) {
        w.write_all(b"N")?;
    }
    if obj.flags.contains(ObjFlags::NO_OVERWRITE) {
        w.write_all(b"V")?;
    }
    if obj.flags.contains(ObjFlags::WEAK) {
        w.write_all(b"W")?;
    }
    match &obj.body {
        ObjectBody::Ordinary(values) => {
            write!(w, "O{}|", values.len())?;
            write_value_list(w, values)?;
        }
        ObjectBody::Closure { code_addr, values } => {
            // n_items = 1 code-addr "word" + values
            let n_items = 1 + values.len();
            write!(w, "C{n_items}|")?;
            write_value(w, &Value::Ref(*code_addr))?;
            for v in values {
                w.write_all(b",")?;
                write_value(w, v)?;
            }
        }
        ObjectBody::LegacyClosure { values } => {
            write!(w, "L{}|", values.len())?;
            write_value_list(w, values)?;
        }
        ObjectBody::String(bytes) => {
            write!(w, "S{}|", bytes.len())?;
            write_hex(w, bytes)?;
        }
        ObjectBody::Bytes(bytes) => {
            write!(w, "B{}|", bytes.len())?;
            write_hex(w, bytes)?;
        }
        ObjectBody::Code {
            code_bytes,
            constants,
            relocs,
        } => {
            write!(
                w,
                "F{},{}|",
                constants.len(),
                code_bytes.len(),
            )?;
            write_hex(w, code_bytes)?;
            w.write_all(b"|")?;
            write_value_list(w, constants)?;
            w.write_all(b"|")?;
            for r in relocs {
                write!(w, "{},{},", r.offset, r.kind)?;
                write_value(w, &Value::Ref(r.target))?;
                w.write_all(b" ")?;
            }
        }
        ObjectBody::EntryPoint(name) => {
            write!(w, "E{}|{}", name.len(), name)?;
        }
        ObjectBody::WeakRef => {
            w.write_all(b"K")?;
        }
    }
    w.write_all(b"\n")?;
    Ok(())
}

fn write_value_list<W: std::io::Write>(
    w: &mut W,
    values: &[Value],
) -> std::io::Result<()> {
    for (i, v) in values.iter().enumerate() {
        if i > 0 {
            w.write_all(b",")?;
        }
        write_value(w, v)?;
    }
    Ok(())
}

fn write_value<W: std::io::Write>(w: &mut W, v: &Value) -> std::io::Result<()> {
    match v {
        Value::Tagged(n) => write!(w, "{n}"),
        Value::Ref(id) => write!(w, "@{id}"),
    }
}

fn write_hex<W: std::io::Write>(w: &mut W, bytes: &[u8]) -> std::io::Result<()> {
    for b in bytes {
        write!(w, "{:02x}", b)?;
    }
    Ok(())
}

// ----- Parser -----------------------------------------------------------

struct Cursor<'a> {
    bytes: &'a [u8],
    pos: usize,
}

impl<'a> Cursor<'a> {
    const fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, pos: 0 }
    }

    fn peek(&self) -> Result<u8, ParseError> {
        self.bytes
            .get(self.pos)
            .copied()
            .ok_or(ParseError::Eof { at: self.pos })
    }

    fn bump(&mut self) -> Result<u8, ParseError> {
        let b = self.peek()?;
        self.pos += 1;
        Ok(b)
    }

    fn expect(&mut self, byte: u8, what: &'static str) -> Result<(), ParseError> {
        let got = self.bump()?;
        if got == byte {
            Ok(())
        } else {
            Err(ParseError::Expected {
                what,
                at: self.pos - 1,
                got,
            })
        }
    }

    fn skip_while(&mut self, pred: impl Fn(u8) -> bool) {
        while let Some(&b) = self.bytes.get(self.pos) {
            if pred(b) {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    const fn at_eof(&self) -> bool {
        self.pos >= self.bytes.len()
    }

    /// Read an unsigned decimal integer.
    fn read_u64(&mut self) -> Result<u64, ParseError> {
        let start = self.pos;
        self.skip_while(|b| b.is_ascii_digit());
        if self.pos == start {
            return Err(ParseError::BadNumber { reason: "expected digit", at: start });
        }
        // SAFETY: digits are ASCII.
        let s = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        s.parse::<u64>()
            .map_err(|_| ParseError::BadNumber { reason: "overflow", at: start })
    }

    /// Read an unsigned decimal integer that fits in `usize`. On 64-bit
    /// hosts this is the same as `read_u64`; on 32-bit hosts a count
    /// exceeding `u32::MAX` would be rejected as a parse error rather
    /// than silently truncated.
    fn read_usize(&mut self) -> Result<usize, ParseError> {
        let at = self.pos;
        let v = self.read_u64()?;
        usize::try_from(v).map_err(|_| ParseError::BadNumber {
            reason: "count exceeds usize",
            at,
        })
    }

    /// Read a signed decimal integer (`-?<digits>`).
    fn read_i64(&mut self) -> Result<i64, ParseError> {
        let start = self.pos;
        if self.peek()? == b'-' {
            self.pos += 1;
        }
        self.skip_while(|b| b.is_ascii_digit());
        if self.pos == start || (self.pos == start + 1 && self.bytes[start] == b'-') {
            return Err(ParseError::BadNumber { reason: "expected digit", at: start });
        }
        let s = std::str::from_utf8(&self.bytes[start..self.pos]).unwrap();
        s.parse::<i64>()
            .map_err(|_| ParseError::BadNumber { reason: "overflow", at: start })
    }

    /// Read `n` hex characters into a `Vec<u8>` (2 chars per byte).
    fn read_hex_bytes(&mut self, n: usize) -> Result<Vec<u8>, ParseError> {
        let mut out = Vec::with_capacity(n);
        for _ in 0..n {
            let h = self.bump()?;
            let l = self.bump()?;
            let v = (hex_digit(h, self.pos - 2)? << 4) | hex_digit(l, self.pos - 1)?;
            out.push(v);
        }
        Ok(out)
    }
}

const fn hex_digit(b: u8, at: usize) -> Result<u8, ParseError> {
    match b {
        b'0'..=b'9' => Ok(b - b'0'),
        b'a'..=b'f' => Ok(10 + b - b'a'),
        b'A'..=b'F' => Ok(10 + b - b'A'),
        _ => Err(ParseError::BadHex { at }),
    }
}

impl Image {
    /// Write this image out in the pexport text format. Round-trips
    /// with [`parse`](Self::parse).
    ///
    /// Mirrors `vendor/polyml/libpolyml/pexport.cpp:114-250`.
    pub fn write<W: std::io::Write>(&self, w: &mut W) -> std::io::Result<()> {
        let n = self.objects.len();
        let word_size_n: u8 = match self.word_size {
            WordSize::Bits32 => 4,
            WordSize::Bits64 => 8,
        };
        let arch_char: u8 = match self.arch {
            SourceArch::Interpreted => b'I',
            SourceArch::X86 => b'X',
            SourceArch::Arm => b'A',
            SourceArch::Other(c) => c,
        };
        writeln!(w, "Objects\t{n}")?;
        writeln!(
            w,
            "Root\t{} {} {}",
            self.root,
            arch_char as char,
            word_size_n,
        )?;
        for (id, obj) in self.objects.iter().enumerate() {
            write_object(w, id as u32, obj)?;
        }
        Ok(())
    }

    /// Parse a pexport file from raw bytes. The file is expected to be
    /// ASCII-clean (newlines, decimal digits, hex digits, the type
    /// letters, and the punctuation `: , | @ <space> <tab>`).
    pub fn parse(bytes: &[u8]) -> Result<Self, ParseError> {
        let mut c = Cursor::new(bytes);
        let (n_objects, root, arch, word_size) = parse_header(&mut c)?;

        // ---- Pass 1: scan object lines to discover sizes (declared by
        // the type-specific count fields). We don't actually need the
        // contents on pass 1; just the count check. The two-pass shape
        // exists in the C++ reader because it allocates real memory in
        // pass 1; we instead use a Vec of `Option<Object>` and fill in
        // a single forward pass below, since `Value::Ref` doesn't
        // require the target object to exist yet — it's just an index.
        //
        // We keep the C++'s pass-1 shape conceptually (validate object
        // header order, count match) but skip the re-scan.
        let pass2_start = c.pos;

        let mut objects: Vec<Option<Object>> = vec![None; n_objects as usize];
        let mut observed: u32 = 0;

        loop {
            // Skip blank lines / trailing newlines.
            c.skip_while(|b| matches!(b, b'\r' | b'\n'));
            if c.at_eof() {
                break;
            }
            let (id, obj) = parse_object_line(&mut c, n_objects)?;
            if (id as usize) >= objects.len() {
                return Err(ParseError::BadIndex {
                    id: u64::from(id),
                    count: n_objects,
                });
            }
            objects[id as usize] = Some(obj);
            observed = observed.saturating_add(1);
        }

        if observed != n_objects {
            return Err(ParseError::CountMismatch {
                declared: n_objects,
                observed,
            });
        }

        // Suppress unused-warning while we keep `pass2_start` for the
        // future two-pass reader (if we ever want true random access).
        let _ = pass2_start;

        let objects: Vec<Object> = objects
            .into_iter()
            .enumerate()
            .map(|(i, o)| {
                o.ok_or(ParseError::BadIndex {
                    id: i as u64,
                    count: n_objects,
                })
            })
            .collect::<Result<_, _>>()?;

        Ok(Self {
            root,
            arch,
            word_size,
            objects,
        })
    }
}

fn parse_header(
    c: &mut Cursor<'_>,
) -> Result<(u32, ObjectId, SourceArch, WordSize), ParseError> {
    // "Objects\t<count>\n"
    for &expected in b"Objects" {
        c.expect(expected, "header magic 'Objects'")?;
    }
    c.skip_while(|b| b == b'\t' || b == b' ');
    let count = c.read_u64()?;
    let count: u32 = u32::try_from(count)
        .map_err(|_| ParseError::BadHeader("object count exceeds u32"))?;
    c.skip_while(|b| matches!(b, b'\r' | b'\n'));

    // "Root\t<id> <arch> <word_size>\n"
    for &expected in b"Root" {
        c.expect(expected, "header keyword 'Root'")?;
    }
    c.skip_while(|b| b == b'\t' || b == b' ');
    let root_u = c.read_u64()?;
    let root: ObjectId = u32::try_from(root_u)
        .map_err(|_| ParseError::BadHeader("root index exceeds u32"))?;

    // Older versions omit arch+word_size. Be lenient.
    c.skip_while(|b| b == b' ' || b == b'\t');
    let arch;
    let word_size;
    match c.peek()? {
        b'\r' | b'\n' => {
            // Legacy image, no arch/word_size — assume the safest defaults:
            // interpreted (so it doesn't claim native code) and 64-bit
            // (matches what every modern build uses). The runtime is
            // ultimately responsible for figuring it out.
            arch = SourceArch::Interpreted;
            word_size = WordSize::Bits64;
        }
        a => {
            arch = match a {
                b'I' => SourceArch::Interpreted,
                b'X' => SourceArch::X86,
                b'A' => SourceArch::Arm,
                other => SourceArch::Other(other),
            };
            c.pos += 1;
            c.skip_while(|b| b == b' ' || b == b'\t');
            let w = c.read_u64()?;
            word_size = match w {
                4 => WordSize::Bits32,
                8 => WordSize::Bits64,
                _ => return Err(ParseError::BadHeader("word size must be 4 or 8")),
            };
        }
    }

    c.skip_while(|b| matches!(b, b'\r' | b'\n'));
    Ok((count, root, arch, word_size))
}

fn parse_object_line(c: &mut Cursor<'_>, n_objects: u32) -> Result<(ObjectId, Object), ParseError> {
    // <id>:
    let id_u = c.read_u64()?;
    let id = u32::try_from(id_u).map_err(|_| ParseError::BadIndex {
        id: id_u,
        count: n_objects,
    })?;
    if id >= n_objects {
        return Err(ParseError::BadIndex {
            id: id_u,
            count: n_objects,
        });
    }
    c.expect(b':', "':' after object id")?;

    // Optional modifier letters (M, N, V, W) in any order.
    let mut flags = ObjFlags::empty();
    loop {
        match c.peek()? {
            b'M' => {
                flags |= ObjFlags::MUTABLE;
                c.pos += 1;
            }
            b'N' => {
                flags |= ObjFlags::NEGATIVE;
                c.pos += 1;
            }
            b'V' => {
                flags |= ObjFlags::NO_OVERWRITE;
                c.pos += 1;
            }
            b'W' => {
                flags |= ObjFlags::WEAK;
                c.pos += 1;
            }
            _ => break,
        }
    }

    // Type letter and payload.
    let ty = c.bump()?;
    let body = match ty {
        b'O' => parse_ordinary(c, n_objects)?,
        b'C' => parse_closure(c, n_objects)?,
        b'L' => parse_legacy_closure(c, n_objects)?,
        b'S' => parse_string(c)?,
        b'B' => parse_bytes(c)?,
        b'F' => parse_code(c, n_objects)?,
        b'E' => parse_entry_point(c)?,
        b'K' => ObjectBody::WeakRef,
        other => {
            return Err(ParseError::UnknownType {
                at: c.pos - 1,
                got: other,
            });
        }
    };

    // Skip to end of line (the writer always ends with '\n').
    c.skip_while(|b| !matches!(b, b'\n' | b'\r'));
    Ok((id, Object { flags, body }))
}

fn parse_value(c: &mut Cursor<'_>, n_objects: u32) -> Result<Value, ParseError> {
    match c.peek()? {
        b'@' => {
            c.pos += 1;
            let id_u = c.read_u64()?;
            let id = u32::try_from(id_u).map_err(|_| ParseError::BadIndex {
                id: id_u,
                count: n_objects,
            })?;
            if id >= n_objects {
                return Err(ParseError::BadIndex {
                    id: id_u,
                    count: n_objects,
                });
            }
            Ok(Value::Ref(id))
        }
        b'-' | b'0'..=b'9' => Ok(Value::Tagged(c.read_i64()?)),
        got => Err(ParseError::Expected {
            what: "'@' or digit (Value)",
            at: c.pos,
            got,
        }),
    }
}

fn parse_value_list(
    c: &mut Cursor<'_>,
    n: usize,
    n_objects: u32,
) -> Result<Vec<Value>, ParseError> {
    let mut out = Vec::with_capacity(n);
    for i in 0..n {
        out.push(parse_value(c, n_objects)?);
        if i + 1 < n {
            c.expect(b',', "',' between values")?;
        }
    }
    Ok(out)
}

fn parse_ordinary(c: &mut Cursor<'_>, n_objects: u32) -> Result<ObjectBody, ParseError> {
    let n = c.read_usize()?;
    c.expect(b'|', "'|' after O<count>")?;
    Ok(ObjectBody::Ordinary(parse_value_list(c, n, n_objects)?))
}

fn parse_closure(c: &mut Cursor<'_>, n_objects: u32) -> Result<ObjectBody, ParseError> {
    let n_items = c.read_usize()?;
    c.expect(b'|', "'|' after C<count>")?;
    // First item is always an @-address (the code pointer).
    c.expect(b'@', "'@' for closure code address")?;
    let id_u = c.read_u64()?;
    let code_addr = u32::try_from(id_u).map_err(|_| ParseError::BadIndex {
        id: id_u,
        count: n_objects,
    })?;
    if code_addr >= n_objects {
        return Err(ParseError::BadIndex {
            id: id_u,
            count: n_objects,
        });
    }
    let rest = n_items.saturating_sub(1);
    if rest > 0 {
        c.expect(b',', "',' after closure code address")?;
    }
    let values = parse_value_list(c, rest, n_objects)?;
    Ok(ObjectBody::Closure { code_addr, values })
}

fn parse_legacy_closure(c: &mut Cursor<'_>, n_objects: u32) -> Result<ObjectBody, ParseError> {
    let n = c.read_usize()?;
    c.expect(b'|', "'|' after L<count>")?;
    Ok(ObjectBody::LegacyClosure {
        values: parse_value_list(c, n, n_objects)?,
    })
}

fn parse_string(c: &mut Cursor<'_>) -> Result<ObjectBody, ParseError> {
    let n = c.read_usize()?;
    c.expect(b'|', "'|' after S<count>")?;
    Ok(ObjectBody::String(c.read_hex_bytes(n)?))
}

fn parse_bytes(c: &mut Cursor<'_>) -> Result<ObjectBody, ParseError> {
    let n = c.read_usize()?;
    c.expect(b'|', "'|' after B<count>")?;
    Ok(ObjectBody::Bytes(c.read_hex_bytes(n)?))
}

fn parse_code(c: &mut Cursor<'_>, n_objects: u32) -> Result<ObjectBody, ParseError> {
    // F<constCount>,<byteCount>|<code_hex>|<const0>,<const1>,...|<relocs>
    let n_consts = c.read_usize()?;
    c.expect(b',', "',' after F<constCount>")?;
    let n_bytes = c.read_usize()?;
    c.expect(b'|', "'|' after F header")?;
    let code_bytes = c.read_hex_bytes(n_bytes)?;
    c.expect(b'|', "'|' after F code bytes")?;
    let constants = parse_value_list(c, n_consts, n_objects)?;
    c.expect(b'|', "'|' after F constants")?;
    // Relocations: zero or more "<offset>,<kind>,@<id> " entries
    // (space-separated, possibly zero of them). The writer trails a
    // space after each, but be defensive about EOL.
    let mut relocs = Vec::new();
    loop {
        match c.peek()? {
            b'\n' | b'\r' => break,
            b' ' => {
                c.pos += 1;
            }
            _ => {
                let offset_u = c.read_u64()?;
                c.expect(b',', "',' after reloc offset")?;
                let kind_u = c.read_u64()?;
                c.expect(b',', "',' after reloc kind")?;
                c.expect(b'@', "'@' for reloc target")?;
                let id_u = c.read_u64()?;
                let target = u32::try_from(id_u).map_err(|_| ParseError::BadIndex {
                    id: id_u,
                    count: n_objects,
                })?;
                if target >= n_objects {
                    return Err(ParseError::BadIndex {
                        id: id_u,
                        count: n_objects,
                    });
                }
                relocs.push(CodeReloc {
                    offset: u32::try_from(offset_u).map_err(|_| ParseError::BadHeader(
                        "reloc offset exceeds u32",
                    ))?,
                    kind: u8::try_from(kind_u)
                        .map_err(|_| ParseError::BadHeader("reloc kind exceeds u8"))?,
                    target,
                });
            }
        }
    }
    Ok(ObjectBody::Code {
        code_bytes,
        constants,
        relocs,
    })
}

fn parse_entry_point(c: &mut Cursor<'_>) -> Result<ObjectBody, ParseError> {
    let n = c.read_usize()?;
    c.expect(b'|', "'|' after E<count>")?;
    let start = c.pos;
    // The name is plain ASCII up to end of line. The writer writes
    // exactly `n` bytes (the strlen) before the newline.
    let end = start + n;
    if end > c.bytes.len() {
        return Err(ParseError::Eof { at: end });
    }
    let name = std::str::from_utf8(&c.bytes[start..end])
        .map_err(|_| ParseError::BadHeader("entry point name not UTF-8"))?
        .to_owned();
    c.pos = end;
    Ok(ObjectBody::EntryPoint(name))
}

// ----- Tests ------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    /// Round-trip the header line only.
    #[test]
    fn parse_minimal_header() {
        let src = b"Objects\t0\nRoot\t0 I 8\n";
        let img = Image::parse(src).unwrap();
        assert_eq!(img.root, 0);
        assert_eq!(img.arch, SourceArch::Interpreted);
        assert_eq!(img.word_size, WordSize::Bits64);
        assert_eq!(img.objects.len(), 0);
    }

    #[test]
    fn parse_one_ordinary() {
        // Two objects: O1 ref to next, O1 with tagged 0
        let src = b"Objects\t2\nRoot\t0 I 8\n\
                    0:O1|@1\n\
                    1:O1|0\n";
        let img = Image::parse(src).unwrap();
        assert_eq!(img.objects.len(), 2);
        match &img.objects[0].body {
            ObjectBody::Ordinary(vs) => assert_eq!(vs, &[Value::Ref(1)]),
            other => panic!("expected Ordinary, got {other:?}"),
        }
        match &img.objects[1].body {
            ObjectBody::Ordinary(vs) => assert_eq!(vs, &[Value::Tagged(0)]),
            other => panic!("expected Ordinary, got {other:?}"),
        }
    }

    #[test]
    fn parse_modifiers_in_any_order() {
        // MV is mutable + no-overwrite
        let src = b"Objects\t1\nRoot\t0 X 8\n0:MVO1|42\n";
        let img = Image::parse(src).unwrap();
        let f = img.objects[0].flags;
        assert!(f.contains(ObjFlags::MUTABLE));
        assert!(f.contains(ObjFlags::NO_OVERWRITE));
        assert!(!f.contains(ObjFlags::WEAK));
    }

    #[test]
    fn parse_string() {
        // "AB" -> 4142 in hex
        let src = b"Objects\t1\nRoot\t0 I 8\n0:S2|4142\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::String(s) => assert_eq!(s, b"AB"),
            other => panic!("expected String, got {other:?}"),
        }
    }

    #[test]
    fn parse_bytes_with_modifier() {
        // 8 zero bytes — looks like the first B record in bootstrap64.txt
        let src = b"Objects\t1\nRoot\t0 I 8\n0:B8|0000000000000000\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::Bytes(b) => assert_eq!(b, &[0u8; 8]),
            other => panic!("expected Bytes, got {other:?}"),
        }
    }

    #[test]
    fn parse_closure() {
        // Closure with 2 items: code ptr + one captured value
        let src = b"Objects\t2\nRoot\t0 I 8\n\
                    0:C2|@1,42\n\
                    1:O1|0\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::Closure { code_addr, values } => {
                assert_eq!(*code_addr, 1);
                assert_eq!(values, &[Value::Tagged(42)]);
            }
            other => panic!("expected Closure, got {other:?}"),
        }
    }

    #[test]
    fn parse_closure_no_captures() {
        // C1 = just a code address, no captures
        let src = b"Objects\t2\nRoot\t0 I 8\n\
                    0:C1|@1\n\
                    1:O1|0\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::Closure { code_addr, values } => {
                assert_eq!(*code_addr, 1);
                assert_eq!(values, &[]);
            }
            other => panic!("expected Closure, got {other:?}"),
        }
    }

    #[test]
    fn parse_legacy_header_no_arch() {
        // Pre-arch-aware images omit arch and word_size.
        let src = b"Objects\t0\nRoot\t0\n";
        let img = Image::parse(src).unwrap();
        assert_eq!(img.arch, SourceArch::Interpreted);
        assert_eq!(img.word_size, WordSize::Bits64);
    }

    #[test]
    fn parse_negative_tagged_int() {
        let src = b"Objects\t1\nRoot\t0 I 8\n0:O1|-7\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::Ordinary(vs) => assert_eq!(vs, &[Value::Tagged(-7)]),
            other => panic!("expected Ordinary, got {other:?}"),
        }
    }

    #[test]
    fn parse_code_no_relocs() {
        // F1,4 = 1 constant, 4 bytes of code
        // Code "deadbeef" -> [0xde, 0xad, 0xbe, 0xef]
        // 1 constant: tagged 0
        // No relocations.
        let src = b"Objects\t1\nRoot\t0 X 8\n0:F1,4|deadbeef|0|\n";
        let img = Image::parse(src).unwrap();
        match &img.objects[0].body {
            ObjectBody::Code {
                code_bytes,
                constants,
                relocs,
            } => {
                assert_eq!(code_bytes, &[0xde, 0xad, 0xbe, 0xef]);
                assert_eq!(constants, &[Value::Tagged(0)]);
                assert!(relocs.is_empty());
            }
            other => panic!("expected Code, got {other:?}"),
        }
    }

    #[test]
    fn rejects_bad_index() {
        // 2 objects but a Value::Ref(99)
        let src = b"Objects\t2\nRoot\t0 I 8\n0:O1|@99\n1:O1|0\n";
        let err = Image::parse(src).unwrap_err();
        assert!(matches!(err, ParseError::BadIndex { id: 99, count: 2 }));
    }

    #[test]
    fn rejects_missing_objects() {
        // Declares 2 but provides 1.
        let src = b"Objects\t2\nRoot\t0 I 8\n0:O1|0\n";
        let err = Image::parse(src).unwrap_err();
        assert!(matches!(
            err,
            ParseError::BadIndex { .. } | ParseError::CountMismatch { .. }
        ));
    }

    fn roundtrip(src: &[u8]) {
        let img = Image::parse(src).unwrap();
        let mut buf = Vec::new();
        img.write(&mut buf).unwrap();
        let img2 = Image::parse(&buf).unwrap_or_else(|e| {
            panic!(
                "re-parse failed: {e:?}\n--- emitted ---\n{}",
                String::from_utf8_lossy(&buf),
            )
        });
        assert_eq!(img.root, img2.root);
        assert_eq!(img.arch, img2.arch);
        assert_eq!(img.word_size, img2.word_size);
        assert_eq!(img.objects.len(), img2.objects.len());
        for (a, b) in img.objects.iter().zip(img2.objects.iter()) {
            assert_eq!(a, b);
        }
    }

    #[test]
    fn roundtrip_ordinary_and_ref() {
        roundtrip(b"Objects\t2\nRoot\t0 I 8\n0:MO2|@1,42\n1:O1|7\n");
    }

    #[test]
    fn roundtrip_string_and_bytes() {
        roundtrip(b"Objects\t2\nRoot\t0 I 8\n0:S5|68656c6c6f\n1:NB3|010203\n");
    }

    #[test]
    fn roundtrip_closure() {
        roundtrip(b"Objects\t2\nRoot\t0 I 8\n0:F0,4|deadbeef||\n1:C2|@0,9\n");
    }

    #[test]
    fn roundtrip_entry_and_weak() {
        roundtrip(b"Objects\t2\nRoot\t0 I 8\n0:VWE10|PolyFinish\n1:WK\n");
    }

    #[test]
    fn roundtrip_code_with_reloc() {
        // 1 const, 4 code bytes, 1 reloc at offset 0, kind 1, target @0
        roundtrip(b"Objects\t1\nRoot\t0 I 8\n0:F1,4|deadbeef|@0|0,1,@0 \n");
    }
}
