# ADR-0054: Strict address byte representation

- Status: Accepted
- Decision date: 2026-08-27
- Scope: fourth internal contract-runtime foundation slice
- Implementation: Complete

## Context

[ADR-0051](0051-canonical-runtime-scalars.md) fixes `Address` as an unsigned
160-bit value and gives it canonical fixed-width text, but deliberately leaves
an address byte representation undecided. It already fixes Core words as 32
most-significant-byte-first octets.

[ADR-0053](0053-strict-address-word-bridge.md) now provides a lossless numeric
embedding from Address into Core Word. The remaining byte boundary can therefore
be fixed and checked against that established Word view without choosing source
casts, ABI padding, contract state, or an EVM operation.

## Decision

Add two internal, syntax-independent conversions:

```text
encodeAddressBytesBE  : Address → ByteArray
decodeAddressBytesBE? : ByteArray → Option Address
```

Encoding always produces exactly 20 octets in most-significant-byte-first
order. Leading zero octets are retained. Decoding succeeds only for exactly 20
octets and preserves every octet, including leading and trailing zeros.

The decoder rejects every shorter or longer input. It never pads, truncates,
reduces modulo `2^160`, accepts an ABI-sized 32-byte value, or interprets an
integer with another byte order.

The byte order agrees with the completed Word representation. After losslessly
widening an address, address byte index 0 is Word byte index 12 and address byte
index 19 is Word byte index 31. Thus all 20 address octets are exactly the low
20-byte suffix of the widened Word's 32-byte big-endian view.

## Required proof interface

Publish exactly six focused laws:

1. `encodeAddressBytesBE_size` proves every encoding has size 20.
2. `decodeAddressBytesBE?_encodeAddressBytesBE` proves decoder-after-encoder
   round trips.
3. `encodeAddressBytesBE_of_decodeAddressBytesBE?_eq_some` proves that encoding
   any successfully decoded address recovers the exact input bytes.
4. `decodeAddressBytesBE?_success_iff` proves that some address is returned
   exactly when the input size is 20.
5. `encodeAddressBytesBE_injective` proves that encoding is injective.
6. `encodeAddressBytesBE_getElem_byteAt` proves, for every `index : Fin 20`,
   that encoded address byte `index` equals `Core.Word.byteAt` index
   `index + 12` of `addressToWord address`.

The successful-decoder theorem preserves exact bytes, while the success-domain
theorem fixes strict width independently of any particular payload. Private
fixed-radix, vector, and index-arithmetic helpers do not add to the exact six
public laws. The implementation uses no custom axioms or unchecked
declarations; standard Lean axiom dependencies are audited and recorded.

## Required tests

Provide exactly ten executable runtime assertions:

1. address zero encodes as 20 zero octets;
2. address one encodes with 19 leading zeros and a final one;
3. the maximum address encodes as 20 `0xff` octets;
4. the zero fixture decodes to address zero;
5. the one fixture decodes to address one;
6. the maximum fixture decodes to the maximum address;
7. a 19-byte input is rejected;
8. a 21-byte input is rejected;
9. a representative nontrivial address round trips; and
10. all 20 encoded octets agree with byte indices 12 through 31 of the widened
    Word.

The assertions execute the two conversions directly. The short and long
fixtures demonstrate exact-width rejection rather than relying on proof
elaboration as runtime coverage.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the internal slice active in documentation;
2. add the two conversions and expose them through the semantics umbrella;
3. add the exact six focused laws;
4. add the exact ten executable runtime assertions; and
5. independently audit the slice and update completion documentation.

## Completion evidence

The completed internal layer contains exactly two executable definitions for
20-byte big-endian encoding and strict-width decoding. Exactly six focused laws
prove size, both round-trip directions, the exact decoder success domain,
injectivity, and agreement with widened Word byte indices 12 through 31.

Exactly ten runtime assertions cover independent zero, one, and maximum
fixtures in both directions; rejection of 19- and 21-byte inputs; a round-trip
table containing zero, one, a nontrivial middle value, and the maximum address;
and all 20 suffix indices for each of those four representative values. The one
fixture explicitly retains all 19 leading zero octets.

The axiom audit reports `propext` and `Quot.sound` for laws one through five;
the byte-index agreement law additionally reports `Classical.choice`. There
are no custom axioms, `sorryAx`, or unchecked declarations. Focused and full
builds and tests, trust-zero, semantic-kernel, metadata, document-link, and diff
checks pass. The independent audit found no P0-P3 issue.

## Publication and exclusions

This slice adds no variable-width address bytes, alternate byte order, padding,
truncation, modulo conversion, address derivation, hexadecimal change, source
cast, source type rule, elaboration rule, ABI encoding or decoding, selector,
or hashing algorithm. It does not change ADR-0051 codecs or ADR-0053 numeric
conversion.

It adds no Core type, expression, primitive, evaluator step, contract entry,
frame adapter, trap taxonomy, world state, account, storage, balance, log, call,
creation, checkpoint, rollback, state delta, EVM revision, gas schedule, host
behavior, or resource-limit meaning.

It adds no Wire tag, JSON schema, profile, or published observation. Frozen
public formats and metadata remain unchanged.

## Consequences

Later internal runtime semantics can use one strict address-byte vocabulary
whose width, round trips, injectivity, and big-endian agreement are proved.
Future ABI or source conversion rules must define their own padding and
admissibility behavior rather than silently changing this exact representation.
