//! Boolean environment-variable parsing.
//!
//! Historically every boolean env gate in the tree was PRESENCE-only
//! (`env::var(name).is_ok()`), so `POLY_REAL_THREADS=0` silently
//! ENABLED real threads — contradicting every doc that says `=1`.
//! Boolean gates now go through [`env_flag`]: unset, empty, `0`,
//! `false`, and `off` (ASCII case-insensitive, whitespace-trimmed)
//! mean OFF; any other set value means ON — so the documented `=1`
//! idiom works, and `=0` really disables.

/// Read the boolean environment variable `name`.
///
/// See the module docs for the accepted spellings. This does a fresh
/// environ read per call — callers on hot paths must memoize the result
/// (see `interpreter::real_threads_enabled` for the cache discipline).
#[must_use]
pub fn env_flag(name: &str) -> bool {
    std::env::var_os(name).is_some_and(|v| env_flag_value(&v.to_string_lossy()))
}

/// The pure value-parsing core of [`env_flag`]: does this *set* value
/// mean ON?
#[must_use]
pub fn env_flag_value(value: &str) -> bool {
    let v = value.trim();
    !(v.is_empty() || v == "0" || v.eq_ignore_ascii_case("false") || v.eq_ignore_ascii_case("off"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn off_spellings() {
        for v in [
            "", "0", "false", "FALSE", "False", "off", "OFF", " 0 ", "  ",
        ] {
            assert!(!env_flag_value(v), "{v:?} should be OFF");
        }
    }

    #[test]
    fn on_spellings() {
        for v in ["1", "true", "on", "yes", "2", " 1", "enabled"] {
            assert!(env_flag_value(v), "{v:?} should be ON");
        }
    }

    #[test]
    fn env_flag_reads_process_env() {
        // SAFETY: test-unique names; nothing else in the process reads
        // or writes them, and env_flag only reads.
        unsafe {
            std::env::set_var("POLYML_RS_ENV_FLAG_TEST_ON", "1");
            std::env::set_var("POLYML_RS_ENV_FLAG_TEST_OFF", "0");
        }
        assert!(env_flag("POLYML_RS_ENV_FLAG_TEST_ON"));
        // `=0` must mean OFF (the POLY_REAL_THREADS=0 reviewer finding).
        assert!(!env_flag("POLYML_RS_ENV_FLAG_TEST_OFF"));
        assert!(!env_flag("POLYML_RS_ENV_FLAG_TEST_UNSET"));
    }
}
