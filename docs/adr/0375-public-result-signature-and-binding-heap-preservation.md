# ADR-0375: Public result signatures and binding-heap preservation

## Status

Accepted for the next whole-program preservation tranche.

## Context

ADR-0374 proved backend-native successful-result typing. Its Core and graph
conclusions referred to linker/runtime result types, while the public compiler
exposes a source `CompiledEntry.resultType`. The source-typed conclusion already
used that public type. Separately, the shallow heap invariant covered primitive
allocation and writes but not the argument-binding operation used by calls and
pattern matching.

## Decision

- The direct-Core linker checks that its elaborated return type is the Core
  lowering of the selected specialization's inferred source result type. A
  single-seed successful-link theorem records the type and key agreement.
- Each finite-graph linked entry carries its selected source body type and
  checked projection to `resultType`. It also certifies that the checked
  runtime table's entry signature has exactly that result type. An inconsistent
  linked table is rejected before execution.
- Compilation validates the selected backend's result against the canonical
  public root and proves `CompiledEntry.HasPublicResultProjection` for every
  successful `compileChecked` or raw `compile`. Direct-Core successful results
  now have deep result/final-store typing at the public result projection;
  finite-graph successful results have the public result projection's shallow
  runtime tag. The source-typed public result theorem remains in force.
- In the source-typed runtime, successful `bindValues` preserves
  `RuntimeState.HasShallowTypes`, extending the heap proof from primitive
  allocation to the binding path used for function arguments and match binders.

## Proof boundary

The three backend results now agree with the compiler's public result
signature, but only direct Core has deep value and final-store preservation.
The graph theorem still uses a shallow tag; it does not validate closure
bodies, captures, or the final graph store. The source-typed binding theorem
does not yet cover complete expression/statement execution, recursive heap
validity, or all control-flow outcomes. Whole-language deep subject reduction
therefore remains open.

## Verification target

The focused modules, full build and tests, metadata and kernel-policy checks,
and whitespace check must pass. No omitted proof, new axiom, unsafe definition,
or native decision shortcut is permitted.
