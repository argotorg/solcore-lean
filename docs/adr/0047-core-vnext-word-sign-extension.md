# ADR-0047: Add internal word sign extension

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-ninth internal Semantic Core vNext slice
- Implementation: In progress

## Context

Core has two's-complement comparison and arithmetic right shift, but it cannot
yet extend a signed value held in a selected low-order byte width to the full
256-bit word. This operation is useful as an internal semantic primitive and
does not require a source spelling or a public wire tag.

## Decision

Add `BinaryOp.wordSignExtend : word × word → word` and total
`Word.signExtend(index, value)`. The left operand is the byte index and the
right operand is the value. Core evaluates the index first and the value
second, each exactly once, and retains the value evaluation's final store.

Indices at least 32 leave the value unchanged. For an index below 32, define:

```text
width = 8 * (index + 1)
low   = value mod 2^width
sign  = 2^(width - 1)
```

If `low < sign`, the selected sign bit is clear and the result is `low`. If
`sign ≤ low`, the bit is set and the result is:

```text
2^256 - 2^width + low
```

Results are represented through `Word.ofNatModulo`. At index 31 the selected
width is the whole 256-bit word, so every input is unchanged. Oversized indices
also use strict identity rather than truncating the index or returning zero.

## Required proof interface

Publish exactly ten focused theorems. Five Word laws are:

- `Word.signExtend_clear` for an index below 32 with a clear selected sign bit;
- `Word.signExtend_set` for an index below 32 with a set selected sign bit;
- `Word.signExtend_ge_32` for oversized-index identity;
- `Word.signExtend_zero`; and
- `Word.signExtend_index31` for full-width identity.

The remaining five are:

- `BinaryOp.apply_wordSignExtend`;
- general store-threaded `Evaluates.wordSignExtend`; and
- `Evaluates.wordSignExtend_clear`, `wordSignExtend_set`, and
  `wordSignExtend_ge_32`.

The general evaluation theorem exposes the intermediate store after the index
and the final store after the value. Do not duplicate generic typing,
inference, renaming, correspondence, machine, or Safety theorems.

## Required tests

Focused regressions cover:

- compile-time use of all ten theorem names;
- zero and maximum values;
- index 0 boundaries `0x7f`, `0x80`, and `0xff`;
- index 1 boundaries `0x7fff` and `0x8000`;
- index 31 identity for values below and above the sign bit;
- index 32 and maximum-index strict identity;
- word result typing, a wrong declared result type, and wrong index/value types;
- unchecked operands exposing the exact invalid left or right payload;
- an index fault that skips the value and a value fault that observes completed
  index effects;
- two allocating and writing operands evaluated index then value exactly once,
  retaining their final store;
- exact literal 4/5 and effectful 28/29 CEK fuel boundaries; and
- rejection by frozen Wire v1/v2 expression projection and by the Wire v2
  `BinaryOp` conversion itself.

These cases distinguish sign extension from masking, zero extension, and the
bounded shift operations. In particular, index 0 with `0x80` must fill all
upper bits, while index 32 must return its input exactly.

## Publication and exclusions

`wordSignExtend` is internal-only. Do not add it to frozen Wire v1 or v2, their
JSON enums, any public Oracle, schema, profile, version, or golden byte stream.
This slice adds no source syntax, standard-library API, ABI rule, opcode
lowering, or gas rule.

## Consequences

Internal Core gains a total, fixed-width sign-extension operation with explicit
operand order and reusable boundary laws. Public behavior and bytes remain
unchanged.
