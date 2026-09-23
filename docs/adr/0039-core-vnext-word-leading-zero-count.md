# ADR-0039: Add an internal word leading-zero count

- Status: Accepted
- Decision date: 2026-08-27
- Scope: twenty-first internal Semantic Core vNext slice
- Implementation: Complete

## Context

Core has fixed-width 256-bit words but no operation for counting their leading
zero bits. This internal operation supports later normalization and bit
algorithms without requiring source syntax or publication through frozen Wire.

## Decision

Add the internal unary operation `wordClz : word -> word`. For a Word `value`:

```text
wordClz(0) = 256
wordClz(value) = 255 - Nat.log2(value.val), when value != 0
```

The natural count is embedded with `Word.ofNatModulo`; every result is between
zero and 256, so it does not wrap. Zero maps to 256, one to 255, `2^255` to
zero, and the maximum Word to zero.

Add one `UnaryOp.wordClz` tag to internal Core syntax and extend existing
typing, inference, renaming, weakening, evaluator, machine, Safety, and proof
cases consistently. The operand evaluates exactly once, and its final store is
the operation's final store.

This tag is not published. Frozen Wire v1 and Wire v2 must both reject it. No
public wire tag, schema, version, or encoding changes.

## Required proof interface

Publish exactly eleven focused theorems:

- `Word.clz_zero`, `Word.clz_nonzero`, `Word.clz_one`,
  `Word.clz_highBit`, and `Word.clz_maximum`;
- `UnaryOp.apply_wordClz`; and
- store-threaded `Evaluates.wordClz`, `Evaluates.wordClz_zero`,
  `Evaluates.wordClz_one`, `Evaluates.wordClz_highBit`, and
  `Evaluates.wordClz_maximum`.

`Word.clz_nonzero` states the general `255 - Nat.log2 value.val` equation under
a nonzero premise. Do not duplicate generic typing, inference, renaming,
weakening, Safety, totality, or machine-correspondence theorem surfaces beyond
the cases required for the new tag.

## Required tests

Focused regressions cover:

- inputs zero, one, two, `2^255`, and maximum, yielding 256, 255, 254, zero,
  and zero;
- Word operand/result typing, wrong operand type, and wrong declared result;
- the raw invalid-unary-operand fault;
- an allocating and writing operand evaluated exactly once with its final
  store retained;
- exact literal 2/3 and effectful 14/15 fuel boundaries; and
- rejection by both frozen Wire v1 and Wire v2 encoders.

Compile-time examples exercise all eleven names. Tests also confirm that no
Core or JSON round trip exists for the unpublished operation.

## Boundaries

This decision adds no `Expr` alias, source or standard-library API, ABI rule,
opcode lowering, or gas rule. It does not define leading-zero count for
unbounded integers or widths other than 256. Existing operation values, types,
faults, effects, fuel, and Wire meaning remain unchanged.

## Consequences

Internal Core gains one precise, total bit-analysis primitive while its public
formats remain frozen. Further primitives require separate ADRs.

## Implementation result

Internal Core now has `UnaryOp.wordClz` and the total `Word.clz` operation with
the specified zero and nonzero definitions. All eleven focused theorems are
implemented: five Word laws, one exact application equation, and five
store-threaded general/boundary evaluations.

Compile-time and runtime tests cover 0, 1, 2, `2^255`, and maximum; Word result
typing and wrong result/operand types; the raw invalid-unary-operand fault; and
an allocating, writing operand evaluated exactly once with its final store.
Literal evaluation has the exact 2/3 fuel boundary and effectful evaluation the
exact 14/15 boundary. Frozen Wire v1 and v2 both reject `wordClz`, so no Core or
JSON projection is introduced.

The implementation, focused semantic/Wire validation, and independent audit
are complete. The audit found no P0-P3 issue, no source trust escape hatch, and
only the repository-approved Lean foundational dependencies. Published Wire
metadata, schemas, versions, and encodings remain unchanged.
