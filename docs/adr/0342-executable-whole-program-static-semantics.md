# ADR-0342: Executable whole-program static-semantics spine

## Status

Implemented for the initial executable checking profile.  Explicit public
interfaces, type/trait/value imports and re-exports, rank-1 inference, bounded
trait evidence, minimum-cost overload selection after candidate-local literal
defaulting, source-arity-preserving per-argument coercion and bounded multi-step
shortest-path coercion are connected end to end.  Executable conversion-term
insertion and specialization to Semantic Core remain staged extensions.

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
- trait and impl predicates with finite evidence-producing search;
- direct-first, bounded shortest-path coercion over concrete intermediate
  types; and
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
- generic or symbolic intermediate coercion paths and coercion cycles that need
  coinductive reasoning;
- insertion of executable conversion terms;
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
explicit canonical-path compatibility fallbacks.  Source arity controls
per-argument fitting without flattening a tuple-valued argument.  Candidate-
local numeric defaulting and coercion counts select only minimum-cost overloads.
Expected-type mismatches prefer a direct coercion, then breadth-first search
ground intermediate types to the configured bound; a unique shortest path
retains ordered predicates and evidence, while equal shortest paths and depth
exhaustion are explicit errors.  Proxy values resolve their source type, and
mapping read indexes unify a key/value pair while checking the key through the
same expected-type/coercion boundary.  They remain type-checking-only forms.
Constructor/operator export selectors, the remaining advanced expressions and
statements, generic/symbolic coercion intermediates, executable conversion
terms, and source specialization or lowering to `Core.Ty` are outside the
completed profile.

The next internal boundary is an occurrence-addressed typed/resolved source IR.
As its first carrier step, every inferred trait or coercion obligation now gets
a function-local `RequirementId`.  Unsolved requirements retain that identity,
and finalization produces one ordered `SolvedRequirement` containing the same
identity, its normalized predicate and its matching evidence.  Speculative
overload candidates fork the immutable input state and only the selected state
is committed, so rejected candidates cannot consume IDs or leave gaps.  Small
preservation lemmas fix canonical allocation and ID-order preservation across
solving, while executable tests cover coercion paths, candidate rollback,
numeric finalization and repeated equal predicates.

The checker still does not attach those IDs to exact syntax occurrences.
The additive carrier for doing so is now present: declaration-owned occurrence
IDs distinguish expressions and statements; typed nodes retain binders,
selected declaration instantiations, requirement IDs and ordered coercion
steps; and a final substitution closes every embedded type, scheme and
predicate without changing identities.  Generic declaration instantiation now
also retains the exact rigid-parameter substitution instead of only its applied
body and predicates.  This carrier is public and independently tested, but the
inference traversal has not yet populated it.

The inference state now owns the declaration, stable input and nested local
binders, monotone binder/occurrence allocators and the typed-node table.  Scope
exit restores only lexical visibility, never allocation or accumulated
semantic facts.  The remaining connection is for expression, statement and
candidate-resolution paths to emit and annotate the prepared nodes.

Executable conversion and specialization additionally need stable expression
and local binder identities, chosen declarations and instantiations, and the
ordered coercion requirements at each occurrence.  Selection-bearing
constructor/member/match/assignment work follows that carrier rather than
extending an information-losing result shape.  Whole-program consumers identify
an obligation by its owning declaration together with its function-local ID.
