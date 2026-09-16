# ADR-0342: Executable whole-program static-semantics spine

## Status

Implemented for the initial executable checking profile.  Explicit public
interfaces, type/trait/value imports and re-exports, rank-1 inference, bounded
trait evidence, overload selection, one-step expected-type coercion and numeric
defaulting are connected end to end.  Multi-step coercion/ranking and
specialization to Semantic Core remain staged extensions.

## Context

The canonical syntax retains declarations, imports, generic parameters,
predicates, traits and impls, while the active frontend still consumes
caller-supplied monomorphic name tables.  Extending local expression adapters
does not establish a source-program type system.

The next milestone prioritizes one executable path across the whole static
semantics over theorem density.  Parser diagnostics and exhaustive edge-case
proofs remain useful, but they must not block an initial working checker.

## Decision

Add an independent source type-system layer instead of extending `Core.Ty`.
The layer provides:

1. deterministic whole-program declaration identities and environments;
2. source type-name resolution, including generic-parameter shadowing;
3. rigid type parameters, flexible inference variables, substitutions,
   schemes and instantiation;
4. occurs-checking first-order unification;
5. resolved trait predicates, impl rules, evidence and bounded tabled search;
6. overload selection, explicit coercion search and literal defaulting; and
7. an executable parser-to-program-checker entry point.

The implementation order is:

```text
program environment
  -> type-name resolution
  -> source types and schemes
  -> unification and impl-head matching
  -> trait evidence and tabled resolution
  -> overload/coercion/literal inference
  -> whole-program checking
```

`Core.Ty` remains the closed monomorphic runtime language.  A later
specialization boundary projects fully solved source types and expressions to
Core.  This prevents source polymorphism from invalidating the existing Core
metatheory.

## Initial executable profile

The first profile is deliberately small but end to end:

- canonical parsed files and stable top-level declaration IDs;
- builtin and user-defined type constructors;
- rank-1 explicit polymorphism and ordinary let generalization where safe;
- functions, calls, lambdas, tuples, conditionals and the canonical operators;
- numeric literal constraints with a deterministic default;
- trait and impl predicates with finite evidence-producing search; and
- enough statement checking to validate ordinary function bodies.

Success, rejection and inconclusive search are distinct results.  No failed
selected overload or impl silently falls back after committing to an ambiguous
candidate.

## Deferred boundaries

The first profile may reject rather than guess for:

- cyclic aliases and polymorphic recursion;
- higher-rank or higher-kinded polymorphism;
- overlapping/default impl policy beyond explicit ambiguity;
- recursive trait cycles that need coinductive reasoning;
- multi-step or user-defined coercion cycles;
- constructor/operator export selectors and the remaining module-reference
  edge cases;
- nested contract namespaces and every member-overload rule; and
- proof-level completeness for diagnostics and all negative edge cases.

These are explicit extensions of the executable profile, not permission to
return an unsound successful result.

## Verification policy

Every stage must compile and have executable positive and negative tests.
Small correspondence lemmas are added where they stabilize an API, but broad
soundness/completeness theorem families are postponed until the vertical path
is usable.  `sorry`, `admit`, authored axioms, `unsafe` and `native_decide`
remain forbidden.

ADR-0340's standalone generic grouped-conditional work remains compatible but
is not a prerequisite for this milestone.  Further grouped-depth frontend
expansion is paused while this whole-program path is built.

## Implemented boundary

The executable path now validates and parses every workspace module, assigns
stable declaration identities, constructs whole-program namespaces, resolves
source types and signatures, checks implementation heads and `where`
predicates, and infers the supported function-body fragment.  Successful
checking retains substitutions, normalized predicates and concrete trait
evidence.  Failed and depth/cycle/ambiguity-inconclusive trait searches remain
distinct results.

This delivery intentionally has a lower proof density than the preceding
parser and local-semantics slices.  Executable positive and negative tests fix
the vertical behavior; broad soundness/completeness theorem families and rare
negative cases are deferred.  Imports consume explicit fixed-point public
interfaces in the type, trait and value namespaces; overload sets, aliases,
hiding, local and remote re-exports, positive cycles, and public module-binding
traversal are executable.  The initial profile still retains its no-import and
explicit canonical-path compatibility fallbacks.  Constructor/operator export
selectors, advanced expressions/statements, multi-step and per-argument product
coercion, literal-default-aware overload ranking, and source specialization or
lowering to `Core.Ty` are outside the completed profile.
