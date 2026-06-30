# Malicious-image corpus (task #96 — untrusted safe mode)

Each `.txt` here is a deliberately-malicious pexport image that drives a
dangerous pointer-follow in the interpreter (type-confusion / wild ptr /
OOB field / non-closure call). Run each through the SAFE MODE:

```
poly run --untrusted <image>.txt
```

Under `--untrusted` every one of these is SAFE: it halts cleanly with a
`bad untrusted image` error (exit 4) or a controlled stop, NEVER a SEGV /
OOB / abort / hang. Without `--untrusted` (the trusted default) a
malicious image may cause UB — that is the documented caveat the safe
mode closes.

These are regenerated + replayed by
`cargo test -p polyml-bin --test untrusted_corpus`.

## Images

- `lf_ref_52_type_confused_call.txt` — tuple/closure field re-pointed at a code object, then mis-followed as a closure (CALL → wild jump)
- `noncode_call_target.txt` — closure capture is an ordinary tuple; bytecode CALLs it → do_call follows word0 as a code addr
- `call_wrongtype_closure_header.txt` — CALL on an ordinary-tuple 'closure' whose word0 resolves to a real code object
- `call_resolves_to_noncode_object.txt` — CALL whose word0 is an in-space, aligned pointer to a NON-code tuple → require_code must fire
- `oob_field_index.txt` — INDIRECT at a field index (250) far past a 1-word object → OOB read
- `wild_pointer_from_bytes.txt` — read a forged 8-byte word from a Bytes object, then follow it as a pointer → wild deref
- `code_object_as_ref_cell.txt` — a code object reached via a closure capture and dereferenced as a ref cell
- `real_neg_wild_operand.txt` — a forged wild pointer used as the operand of REAL_NEG -> read_real OOB deref
- `fastcall_wild_stub.txt` — a forged wild pointer used as the STUB of CALL_FAST_R_TO_R -> dispatch_typed_fast_call token OOB read
