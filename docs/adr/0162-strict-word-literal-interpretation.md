# ADR-0162: Numeric spelling and strict Word literal interpretation

- Status: Accepted
- Decision date: 2026-09-08
- Scope: standalone mathematical literal interpretation for the frontend

## Decision

Provide an independent natural-number meaning for canonical numeric literal
payloads, and a separate explicit projection to Semantic Core Word. This unit
does not integrate literals into the local-expression resolver or checker;
their current unsupported-literal boundary remains unchanged. It supplies a
proof-connected semantic building block without deciding general source
literal types, `fromInteger` conversion, or class/overload resolution.

Decimal spelling is one or more ASCII digits `0` through `9`. Hexadecimal
spelling is the exact lowercase prefix `0x` followed by one or more ASCII
digits `0` through `9`, `a` through `f`, or `A` through `F`. Both permit leading
zeroes without a length limit. Character case changes a hexadecimal digit's
spelling, not its value. These are the existing canonical lexer's token
spellings, not the more permissive conventions of a host numeric parser.

Define digit and digit-sequence meaning independently of the executable
decoder, using positional accumulation `next = base * accumulator + digit`.
Literal meaning requires a nonempty digit sequence and the appropriate whole
spelling/prefix. No suffix, whitespace, sign, separator, non-ASCII digit, or
fractional component is ignored. String payloads have no numeric meaning.

The explicit Word interpretation succeeds exactly when that natural value is
less than `2^256`, reusing `Core.Word.ofNat?`. Out-of-range values are rejected,
not reduced modulo the Word modulus. This is a chosen strict Word projection,
not a consequence of syntax or a universal source literal conversion policy.
Arbitrarily many leading zeroes must not cause a representable value to fail.

## Raw AST and parser boundaries

Canonical literal payloads retain raw strings; neither their type nor source
span validity proves numeric spelling validity. The interpreter therefore
validates even manually constructed AST payloads. Located interpretation ignores
only the source range, never characters in the payload. Do not use a host
`toNat?` without the exact ASCII grammar: the pinned Lean runtime accepts
underscores that the canonical lexer does not accept inside a numeric token.

Source-text tests require an entire diagnostic-free literal expression parse
before interpretation. Inputs such as `0x`, `0Xff`, `1_000`, `123abc`, or
`0x1g` must not succeed by interpreting only their first valid token.

## Guarantees and validation

Prove executable digit/sequence/literal soundness and completeness against the
independent mathematical relations, value uniqueness, and exact failure
characterization. Connect the strict Word result to the natural value and
range bound, with exact payload/span preservation. The interpreter is total
and does not change stores, tables, or source ASTs.

Tests cover decimal/hex agreement, both hex letter cases, leading zeroes,
zero/one/maximum and the first out-of-range value, malformed payloads, Unicode
digits, separators/signs/whitespace, string rejection, and full parsed-source
consumption. Public proofs use only standard kernel axioms. Run focused and
aggregate builds, complete tests, kernel checks, and metadata checks.

This adds no local-expression typing/evaluation constructor, general source
type policy, parser change, external endpoint, Core machine rule, Wire format,
or capability change.
