# ADR-0051: Canonical runtime scalar observations

- Status: Accepted
- Decision date: 2026-08-27
- Scope: first internal contract-runtime observation foundation slice
- Implementation: Complete

## Context

The internal Core now covers the planned pure word operations, but contract
execution will also need byte strings, addresses, returndata, logs, storage
keys, and other externally observed values. ADR-0008 already requires words,
addresses, and byte strings to have canonical lowercase hexadecimal
representations. That requirement needs an executable, proved foundation
before contract state or ABI rules can use it.

The frozen Core Wire v1 and v2 codecs each contain a private Word-only
hexadecimal implementation. Surface hexadecimal literals are not suitable for
runtime observations: they permit uppercase spelling, omit the `0x` prefix,
and do not preserve a fixed runtime width. A new syntax-independent kernel is
therefore required.

## Decision

Add an internal canonical runtime scalar layer with these values:

- `Bytes`, represented by `ByteArray` and interpreted as an ordered sequence
  of octets;
- `Address`, represented as an unsigned 160-bit value; and
- the existing `Core.Word`, retained as the only unsigned 256-bit word type.

Their canonical text representations are:

```text
Bytes:   0x followed by exactly two lowercase hex digits per byte
Address: 0x followed by exactly 40 lowercase hex digits
Word:    0x followed by exactly 64 lowercase hex digits
```

Digits are most-significant first. Empty bytes encode as `0x`. Leading and
trailing zero bytes are retained. Address and Word encoders left-pad with zero
digits to their exact widths.

Decoding is strict and canonical-only. It rejects a missing or altered prefix,
uppercase letters, non-hex characters, odd byte-string digit counts, and
incorrect Address or Word widths. It never truncates, sign-extends, or reduces
an out-of-range input modulo the target width.

The runtime layer also provides a 32-byte big-endian representation of every
Word and its strict inverse. Byte index zero is the most-significant byte and
must agree with the existing Core `Word.byteAt` convention. This is a scalar
representation rule, not an ABI padding or conversion rule.

## Required proof interface

Publish exactly sixteen focused scalar theorems. For each of `Bytes`,
`Address`, and `Word`, publish:

- the exact canonical text length;
- decoder-after-encoder round trip;
- encoder-after-successful-decoder canonicality; and
- encoder injectivity.

For the Word big-endian byte representation, additionally publish:

- exact 32-byte length;
- bytes-decoder after Word-encoder round trip;
- Word-encoder after successful bytes-decoder canonicality; and
- indexed-byte agreement with `Word.byteAt`.

Generic fixed-radix and hexadecimal helper lemmas are implementation
infrastructure and do not count toward the sixteen focused scalar theorems.

## Required tests

Focused regressions cover:

- empty bytes, one-byte `00` and `ff`, multi-byte values, and retained leading
  and trailing zero bytes;
- Address zero, one, and maximum with exact 40-digit payloads;
- Word zero, one, and maximum with exact 64-digit payloads;
- 32-byte Word big-endian order and byte-index agreement at indices 0, 30,
  and 31;
- rejection of missing prefixes, uppercase digits, invalid characters, odd
  byte-string widths, and incorrect Address and Word widths;
- encode/decode round trips and accepted-input canonicalization; and
- equality of the new Word text with frozen Core Wire v1 and v2 output for
  representative values, while metadata and golden bytes remain unchanged.

## Staged implementation plan

Keep every commit at roughly 300 changed lines or fewer and leave the tree
green:

1. add a proof-oriented fixed-radix byte kernel and include Foundation in the
   semantic-kernel policy scan;
2. add canonical lowercase hexadecimal encoding and strict decoding;
3. add `Bytes`, `Address`, and existing-Word runtime scalar APIs;
4. add the exact sixteen focused scalar theorems;
5. add boundary, rejection, big-endian, and frozen-Wire compatibility tests;
6. independently audit the slice and update completion documentation.

The frozen Wire implementations may later delegate to the shared foundation,
but such refactoring is not required for this slice and must preserve their
error ordering, JSON bytes, schemas, profiles, and golden data exactly.

## Completion evidence

The completed internal layer includes a reusable fixed-radix kernel, strict
canonical hexadecimal codecs, and the `Bytes`, `Address`, and existing-Word
APIs exposed through `Solcore.Semantics`. Exactly sixteen focused theorems prove
text lengths, decoder-after-encoder round trips, successful-decoder
canonicality, text injectivity, exact 32-byte Word width, and agreement with
`Word.byteAt`.

Executable regressions cover the required boundaries and rejection cases, a
complete 32-byte big-endian fixture, accepted-input canonicalization, and Word
text compatibility with frozen Core Wire v1 and v2. The frozen Wire codecs were
not refactored; the tests compare their existing output with the new internal
encoder. Focused and full builds and tests, trust-zero checking, the semantic
kernel and metadata checks, and the axiom audit pass. The independent audit
found no P0-P3 issue.

## Publication and exclusions

This layer is internal and does not add a Core type, value, expression,
machine transition, source form, Wire tag, JSON schema, Oracle capability, or
published observation profile. It adds no hashing, selector, ABI padding,
storage layout, address-to-word conversion, address truncation, contract
state, call, rollback, EVM revision, gas, or map-order rule.

Publication of runtime observations remains a separate versioned decision.
Keccak and selectors require a later resource and trust-boundary decision;
contract execution requires separate state and outcome decisions.

## Consequences

Later runtime features can share one canonical byte and scalar vocabulary
without depending on concrete source syntax or compiler artifacts. Leading
zeros, byte order, and strict textual acceptance become proved semantic facts
rather than conventions repeated in serializers. Frozen public behavior stays
unchanged while compatibility with its existing Word spelling remains
executable evidence.
