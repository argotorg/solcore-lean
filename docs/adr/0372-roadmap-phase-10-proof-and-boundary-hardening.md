# ADR-0372: Roadmap phase 10 proof and boundary hardening

## Status

Accepted for roadmap phase 10.  This phase strengthens the executable frontend
delivered by phases 1–9 with checked laws and adversarial boundary regressions.
It does not claim a complete metatheory for the whole source language.

## Context

The staging, specialization, runtime-call-graph, typed-source runtime,
module/type-resolution, and restricted compiler slices are executable.  Their
end-to-end tests are intentionally much denser than their general theorems.
The phase-9 compiler properties in particular previously fixed only convenience
wrapper equations and one-shot reuse.

The roadmap's final hardening phase names preservation, ownership, soundness,
resource bounds, and negative proofs.  Treating those words as a claim about
every deferred language feature would be false: the current compiler has an
explicit restricted profile, `compileChecked` accepts a caller-supplied checked
carrier, and several public fuels bound recursion depth rather than aggregate
work.  Phase 10 therefore hardens the implemented profile and records the
remaining proof boundaries precisely.

## Decision

### Prove the specialization budget and root identity boundaries

Every successful worklist run now exposes its accumulated plan through one
outcome projection.  General theorems show that:

- the plan retains exactly the eagerly canonicalized seed-key list, including
  its order and duplicates;
- `runAux` can add at most one specialization per remaining budget unit; and
- every complete or exhausted public outcome contains no more distinct admitted
  specializations than its supplied budget.

The compiler separately proves that exact-root recovery cannot change the sole
canonical seed identity.  Consequently a successful `compileChecked`, and the
raw `compile` path after successful checking, exposes the same specialization
key produced by exact seed resolution.  Backend fallback is not permitted to
swap the public root.

`specializationBudget` is therefore a proved aggregate bound on admitted
specializations.  No analogous aggregate-work claim is made for checking,
staging, input validation, or execution fuel.

### Make compiler phase and runtime-domain separation explicit

The public compiler now has laws fixing all of the following:

- checking failures cannot reach seed resolution;
- seed failures cannot reach specialization;
- a zero specialization budget reports the first canonical root and a
  one-element pending frontier, independently of staging fuel;
- one-shot compilation errors cannot be relabeled as execution errors;
- Core/call-graph artifacts reject typed invocations, and typed artifacts reject
  Core invocations, before a runtime starts;
- a matching call-graph or typed invocation always returns its native exact
  result carrier, so runtime faults and exhaustion are not facade failures; and
- the direct backend's only facade-level matched-domain rejection is its exact
  Core input-type mismatch.

The artifact constructor and executable payload remain private.  These laws
eliminate the sealed representation through its generated recursor without
exposing either constructor in the public API.

### Prove the staged carrier instead of relying on examples

The closed staged-value carrier now has general round-trip and reflection laws.
Embedding followed by projection is the identity; every successful projection
identifies the complete original Core value; projection is unique and preserves
the exact Core type; and embedding is injective.  Thus Unit, Bool, Word, and
binary products cannot be silently identified or retyped at the staging/Core
boundary.

The stage join also has algebraic laws for the empty and singleton cases,
runtime domination, all-comptime collections, the deferred case, and append
composition.  These laws fix the intended three-way dependence lattice used by
tuple, binary, and conditional analysis.

### Preserve state at the bounded typed-input gate

A typed-runtime law states that zero recursive validation depth on an exact root
with at least one expected input and at least one supplied argument rejects the
first expected argument before allocating a parameter cell or entering
evaluation.  The returned state is definitionally the supplied state.
Regression tests exercise this with a nonempty heap, not only the empty default.

The public negative matrix additionally fixes both directions of all three
backend/domain mismatches, malformed-source checking precedence, direct Core
type rejection, typed structural validation exhaustion, and execution
exhaustion after parameter allocation.

### Add a small type-system law layer

The first type-system property module covers only laws supported directly by
the present ordered, first-match substitutions and bounded first-order
unifier.  It proves lookup, erasure and quantified exclusion, general ordered
composition, scheme protection, and sound success for reflexive and one
variable-to-constructor constraint.  It does not silently assume duplicate-free
substitution domains or idempotent arbitrary substitutions.  General
multi-constraint unification soundness and completeness remain separate work.

## Resource and trust boundaries

`specializationBudget` counts aggregate admitted keys.  Staging and execution
fuel bound dynamic descent.  Typed input validation decrements across recursive
value depth, while sibling list entries reuse the same depth allowance.
Checking contains similarly structural bounds.  Phase 10 deliberately does not
rename these depth policies as total-work bounds.

`compile` starts from raw text and performs checking itself.  `compileChecked`
is the reuse boundary for a `CheckedProgram`; its public carrier can be built by
Lean clients, so theorems about arbitrary forged values need an explicit
validity premise.  The common canonical-plan validator and backend preflights
remain defensive executable checks, not a proof that every public wrapper
constructor is intrinsically trustworthy.

Direct Core successful-result safety also requires the existing Core context,
value, and store typing premises.  Equality of the shallow `Core.Value.type`
tags alone is not promoted to a never-fault theorem.

## Phase boundary

Roadmap phase 10 includes:

- canonical seed preservation and specialization-count resource laws;
- successful compiler-root identity preservation;
- staged-value round-trip, reflection, type-preservation, uniqueness, and
  injectivity laws;
- algebraic laws for three-way stage joins;
- exact compiler failure-phase and runtime-domain separation laws;
- zero-depth typed-input state preservation for nonempty expected and supplied
  argument lists;
- a focused initial type-system property layer; and
- expanded public compiler negative regressions and full trust audits.

Still deferred are:

- complete worklist graph closure and canonical-validator completeness proofs;
- general source-to-runtime type preservation for graph and typed heaps;
- full ownership/completeness theorems for every stage-analysis sidecar entry;
- fixed-point interface algebra and exhaustive module-resolution soundness;
- general multi-constraint unification soundness/completeness and
  trait-evidence soundness;
- aggregate-work budgets for staging, validation, and runtime evaluation; and
- correctness for language features outside the published restricted profile.

## Verification target

All new laws are kernel-checked without an axiom, unsafe definition, native
decision procedure, or omitted proof.  Focused builds cover the worklist,
staged carrier, stage algebra, typed validation, type-system, compiler, and
compiler regression modules.  The aggregate build, test suite, kernel audit,
metadata audit, forbidden-word scan, and whitespace check remain the release
boundary.
