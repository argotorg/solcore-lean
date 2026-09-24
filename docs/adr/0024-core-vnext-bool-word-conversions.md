# ADR-0024: Semantic Core vNext boolean and word conversions

- Status: Accepted
- Decision date: 2026-08-27
- Scope: sixth internal Semantic Core vNext vertical slice
- Implementation: Complete

## Context

The Core already has boolean and 256-bit word values, conditionals, word
equality, and boolean negation. It can therefore express the two basic
conversions between these types without adding another primitive operation or
changing the expression algebra.

Fixing these conversions now gives later resolved and source layers an
unambiguous semantic target. It does not choose source cast syntax, and it must
not accidentally settle the stricter rules needed by a future ABI decoder.

## Decision

The internal Core library provides two derived expression builders:

```text
boolToWord(value) =
  if value then word(1) else word(0)

wordToBool(value) =
  boolNot(wordEq(value, word(0)))
```

They have the following meaning:

| Conversion | Input | Result |
| --- | --- | --- |
| `boolToWord` | `false` | word zero |
| `boolToWord` | `true` | word one |
| `wordToBool` | word zero | `false` |
| `wordToBool` | any nonzero word | `true` |

The typing rules are:

```text
Gamma |- value : bool
------------------------
Gamma |- boolToWord(value) : word

Gamma |- value : word
------------------------
Gamma |- wordToBool(value) : bool
```

These are derived forms, not new Core tags. Their Lean definitions construct
ordinary existing expressions. Consequently, executable inference, detailed
checking, big-step evaluation, CEK execution, correspondence, safety, and fuel
behavior remain those of the expanded expressions.

## Evaluation order and effects

The operand appears exactly once in each expansion.

- `boolToWord` evaluates its operand once as the conditional's condition, then
  evaluates only the selected constant branch.
- `wordToBool` evaluates its operand once as the left operand of word equality;
  the right operand is the constant zero. Boolean negation then consumes the
  equality result without re-evaluating the original operand.

Both conversions pass through the store produced by their operand. They create
no cell, perform no write, and add no effect of their own. This exactly-once rule
applies equally when the operand contains bindings, function calls, matching,
or local-cell effects.

## Separation from ABI boolean decoding

`wordToBool` is a total truthiness conversion. In particular, word two and every
other nonzero word convert to `true`.

A future ABI boolean decoder has a different responsibility. Its admissible
input is expected to be canonical zero or one, and it must reject other encoded
words if that strict rule is accepted. This ADR neither defines nor proves that
admissibility rule. `wordToBool` must not be used as an ABI decoder or as
evidence that an encoded boolean is canonical.

Likewise, `boolToWord` fixes only the semantic word value zero or one. It does
not define byte width, padding, byte order, calldata layout, storage layout, or
any other encoding rule.

## Core and publication boundary

This slice adds no type, value, expression, frame, transition, machine fault,
or diagnostic tag. In particular:

- the CEK machine receives no new frame or transition;
- big-step evaluation receives no new rule;
- no public source spelling or cast operation is introduced.

A Wire projection sees only the expanded ordinary expression. This is not a
new Wire feature.

## Required implementation and proof

- define both expression constructors solely by the expansions in this ADR;
- prove their declarative typing rules and executable inference results;
- prove the two boolean cases for `boolToWord`;
- prove zero and arbitrary nonzero cases for `wordToBool`;
- prove that evaluation threads the operand's resulting store unchanged through
  the conversion itself;
- prove or reuse an explicit exactly-once expansion fact, with no duplicated
  operand subtree;
- show that existing big-step/CEK correspondence, progress, preservation,
  typed-result, totality, sufficient-fuel, and fault-exclusion results apply
  without a new semantic case;
- test type-correct and type-incorrect operands;
- test false, true, zero, one, and representative nonzero word boundaries,
  including the maximum word;
- test an effectful operand to detect duplicate or skipped evaluation.

The completed implementation provides dedicated typing, inference, evaluation,
zero/nonzero, store-threading, and weakening theorems. Focused tests cover
effects, exact fuel, type errors, word boundaries, and canonical expansions;
the full test, warning, kernel-trust, axiom, and whitespace audits pass.

## Deferred

This ADR does not add:

- source cast syntax, implicit coercions, or overload resolution;
- ABI admissibility, encoding, decoding, or dispatch;
- conversion failure or a checked/canonical word-to-boolean decoder;
- signed words, integer-width changes, truncation, or extension;
- conversions involving products, sums, named data, cells, functions, bytes,
  addresses, or contract values;
- optimizer rules that replace the expansions with backend instructions; or
- a new public Core version.

## Consequences

The two conversions have stable semantics while remaining ordinary Core
programs. The implementation can add focused theorems and convenient builders
without extending every syntax-indexed proof or serialization layer. Future
source elaboration may target these builders, while future ABI work must retain
its separate strict validation boundary.
