# ADR-0346: Primitive builtin Int resolution profile

## Status

Implemented as the evidence-resolution layer for target-compatible literals.

## Context

ADR-0344 introduced the staged `integer` type and modulo-Word projection.
ADR-0345 separated builtin identities from source declaration identities.  A
literal conversion plan still needs canonical evidence that Word and integer
have primitive `Int` implementations, without inventing source declarations or
polluting source catalog counts.

## Decision

Publish `ProgramSignatures.builtinIntPredicate`, the exact unary builtin `Int`
goal constructor.  Its subject is the selected type and its argument list is
always empty.

Install two premise-free rules in stable order:

1. builtin `Int<Word>` with implementation identity `intWord`;
2. builtin `Int<integer>` with implementation identity `intInteger`.

`ProgramSignatures.resolutionRules` prepends those rules to the source-only
`implRules` list.  The `traits`, `implementations`, and `implRules` fields remain
unchanged source catalogs; builtins have no fabricated declaration, method, or
source body.

General evidence consumers use the combined view: source inference, primary
and method evidence validation in the source-method executor, resolved static
method assumptions in the direct linker, and the corresponding canonical
evidence regressions.  Coercion-edge enumeration deliberately stays on
source-only `implRules`; the new primitive rules are `Int` evidence, not
executable `Coerce` edges.

## Consequences

Closed builtin `Int<Word>` and `Int<integer>` goals now select tagged primitive
evidence.  `Int<Bool>` and goals with extra arguments have no primitive
solution.  A source trait also spelled `Int` remains a distinct declaration
identity and its source implementation remains independently resolvable.

This slice does not attach an `Int.fromInteger` plan to typed literal nodes and
does not add builtin method execution or change Core lowering.  The staged
`integer` type must still be eliminated by a later specialization step before
runtime Core.

## Verification

Focused tests fix the exact builtin-first combined rule order, both primitive
evidence trees, unary arity rejection, builtin/source name disjointness, source
`Int` resolution, and unchanged source trait/implementation/rule counts.  The
full source inference, executable-method, direct-linking, kernel, metadata, and
format checks remain part of repository validation.
