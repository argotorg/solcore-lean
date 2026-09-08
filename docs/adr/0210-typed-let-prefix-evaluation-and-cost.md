# ADR-0210: Evaluation and cost of typed let prefixes

- Status: Accepted
- Decision date: 2026-09-09
- Scope: Independent raw/cost semantics and exact checked Core correspondence

## Decision

Complement ADR-0209 with independent evaluation and cost judgments for its
original annotated, initialized let-prefix shape. A terminal tree reuses the
existing tree judgment. A binding evaluates its actual initializer once in the
old name table and environment, then evaluates the original remaining statements
with the new name, fresh ID and actual resulting value prepended. Retain initial,
intermediate and final stores explicitly. The wrapper adds the two existing Core
let transitions, so its cost is initializer cost plus tail cost plus two.
Unused initializers still require evaluation and contribute their full cost.

Raw rules carry no annotation meaning, unused-name, whole-checking, runtime-type
or store-validity premise. The annotation and initializer must both be present
in the original syntax, but rejected annotations or repeated spellings may have
raw paths. This permissive operational relation is not a source-language
shadowing or acceptance policy. Whole checking still follows ADR-0209 and checks
every initializer and terminal branch, including unselected source.

Choose the raw binder ID with `freshLocalId owner (table.map Prod.snd)`. Freshness
is relative to this name table, not to an arbitrary inconsistent environment.
Add the missing type-only name/ID projection law, so actual static input names
choose precisely the same ID as `LocalTypeInputs.bindFresh`. Accepted checking
and aligned environment IDs suffice for exact Core evaluation correspondence;
no runtime inhabitants or typing are inferred from ID alignment alone.

Prove raw determinism and unchanged stores, cost erasure/existence, positive and
unique costs. Independent source typing with an actual aligned, typed environment
separately gives evaluation existence and result typing. Initializer result
typing justifies the extended tail environment; never fabricate a value for an
arbitrary static type. Existing cell references and captured closures may be
returned unchanged, without allocation or invocation.

Prove evaluation iff for the actual accepted Core, and exact cost paths under
any original continuation, with an empty-continuation specialization. Reuse
`CostStepComposition.letE`: the initializer runs with the original environment
and a pending let frame, the tail runs with the obtained value prepended and the
original continuation. No weakening, second reversal or new Core primitive is
needed. Reaching a retained continuation is not executing it: an incompatible
frame may fault at zero remaining fuel, so arbitrary-continuation endpoint
paths do not imply unconditional fuel exhaustion.

## Boundaries and validation

No parser, Core, Resolved, Wire or existing checker/entry policy changes. Do not
add a new body runner, source fuel bound, resumption API or function-entry
integration in this unit. Old raw tree paths and costs embed without acceptance
or typing assumptions. Omitted initializers, inference, arm-local let prefixes,
mutation, calls and general early return remain outside the new profile.

Use independent arbitrary-length source paths and actual parsed typed arguments,
exact old-scope references and noncommutative arithmetic, unused initializer
costs, asymmetric terminal choices and distinct stores. Include raw success with
whole rejection, missing-initializer-value failure, aligned but untyped Core
correspondence and misaligned-ID contrasts. Check actual exact Core paths with
empty, safe pending and incompatible continuations. Audit public contracts and
consumers, standard axioms, registration/dependency direction, focused/aggregate
builds, actual parsed execution, full tests and policy checks. Keep files below
300 lines, commits small, diagnostics paused and scratch inside the repository.
