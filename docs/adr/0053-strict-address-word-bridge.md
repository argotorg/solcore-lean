# ADR-0053: Strict address and word bridge

- Status: Accepted
- Decision date: 2026-08-27
- Scope: third internal contract-runtime foundation slice
- Implementation: Complete

## Context

[ADR-0051](0051-canonical-runtime-scalars.md) defines `Address` as an unsigned
160-bit value and retains `Core.Word` as the unsigned 256-bit word type. It
deliberately leaves conversion between them undecided. The completed frame
outcome carrier in [ADR-0052](0052-contract-frame-outcomes.md) likewise leaves
address conversion separate from state and execution.

Contract state will eventually use addresses alongside words, but no state
carrier is ready yet. A lossless bridge between the two existing scalar types
can be fixed now without choosing accounts, storage, rollback, source casts,
or ABI layout. The important boundary is narrowing: silently discarding the
upper 96 bits would hide information and would prematurely choose a language
or ABI conversion rule.

## Decision

Add two internal, syntax-independent conversions:

```text
addressToWord  : Address → Core.Word
wordToAddress? : Core.Word → Option Address
```

`addressToWord` preserves the address's natural-number value. Equivalently,
it zero-extends the 160-bit address into a 256-bit word, so the upper 96 bits
are zero.

`wordToAddress? word` succeeds exactly when
`word.val < addressModulus`, where `addressModulus = 2^160`. On success it
returns the address with the same natural-number value. At `2^160` and above
it returns `none`.

The narrowing conversion never truncates the upper bits and never reduces a
word modulo `2^160`. In particular, the word `2^160` is rejected rather than
becoming address zero, and the maximum 256-bit word is rejected rather than
becoming the maximum address.

This bridge is an internal lossless embedding and strict partial inverse. It
does not decide how a future source-language cast or ABI decoder behaves.

## Required proof interface

Publish exactly six focused laws:

1. `wordToAddress?_eq_some_iff` proves
   `wordToAddress? word = some address` exactly when
   `word.val = address.val`.
2. `wordToAddress?_success_iff` proves
   `(∃ address : Address, wordToAddress? word = some address)` exactly when
   `word.val < addressModulus`.
3. `wordToAddress?_failure_iff` proves
   `wordToAddress? word = none` exactly when
   `addressModulus ≤ word.val`.
4. `wordToAddress?_addressToWord` proves that narrowing a widened address
   returns that address.
5. `addressToWord_of_wordToAddress?_eq_some` proves that widening any
   successfully narrowed address recovers the original word.
6. `addressToWord_injective` proves that widening is injective.

Definitional reduction equations and private range helpers do not add to the
six-law public interface. The proofs must work for the existing `Address` and
`Core.Word` types without adding assumptions or axioms.

## Required tests

Provide exactly ten executable runtime assertions:

1. address zero widens to word zero;
2. address one widens to word one;
3. the maximum address widens with value `2^160 - 1`;
4. word zero narrows to address zero;
5. word one narrows to address one;
6. the word with value `2^160 - 1` narrows to the maximum address;
7. the first overflowing word, with value `2^160`, is rejected;
8. the maximum 256-bit word is rejected;
9. representative addresses pass narrowing after widening; and
10. representative successful narrowings recover their original words after
    widening.

The representative checks include zero, one, a nontrivial middle value, and
the maximum address. The assertions exercise the executable conversions
directly rather than replaying the proof theorems. The two rejection cases
also demonstrate that narrowing is not low-160-bit truncation.

## Staged implementation plan

Keep every commit below 300 changed lines and leave the tree green:

1. accept this ADR and mark the internal slice active in documentation;
2. add the two conversions and expose them through the semantics umbrella;
3. add the exact six focused laws;
4. add the exact ten executable runtime assertions; and
5. independently audit the slice and update completion documentation.

## Completion evidence

The completed internal bridge contains exactly two executable definitions:
lossless address widening and strict, partial word narrowing. Exactly six
focused, axiom-free laws characterize successful results, the accepted and
rejected ranges, both partial-inverse directions, and injectivity.

Exactly ten runtime assertions cover zero, one, a nontrivial middle value, and
the maximum address. They also reject the first overflowing word, `2^160`, and
the maximum 256-bit word, demonstrating that narrowing never truncates or
reduces modulo the address width.

Focused and full builds and tests, trust-zero checking, semantic-kernel and
metadata checks, the axiom audit, document-link validation, and diff checking
pass. The independent audit found no P0-P3 issue.

## Publication and exclusions

This slice adds no truncating or modulo address conversion, address byte
representation, hexadecimal rule, source cast, source type rule, elaboration
rule, ABI padding or admissibility rule, selector, or address-derivation rule.
It does not change the canonical scalar codecs from ADR-0051.

It adds no Core type, expression, primitive, evaluator step, contract entry or
`main` result rule, frame-result adapter, trap taxonomy, world state, account,
storage, balance, log, call, creation, checkpoint, rollback, or state delta.
It chooses no hashing algorithm, EVM revision, gas schedule, host behavior, or
resource-limit meaning.

It adds no Wire tag, JSON schema, profile, or published observation. Frozen
public formats and metadata remain unchanged.

## Consequences

Later internal semantics can move an address into a word without losing its
numeric identity and can reject an out-of-range word before treating it as an
address. Any future semantics that intentionally truncates, decodes ABI
padding, or defines a source cast will need its own named operation and
decision rather than changing this strict bridge.
