# ADR-0373: Canonical-plan generation and validation certificates

## Status

Accepted for the first proof tranche after roadmap phase 10.

## Context

ADR-0372 proved the aggregate specialization-count bound and preservation of
the eagerly canonicalized seed list.  It deliberately left graph closure and
canonical-validator completeness for later work.  The executable compiler
already validates every complete specialization plan before backend selection,
but the useful facts established by that validation were not available as Lean
theorems.

This tranche separates two questions:

1. what every successful worklist generation guarantees; and
2. what can be extracted from a successful defensive `validatePlan` replay.

Keeping those directions separate avoids treating validator soundness as the
still-unproved converse theorem that every complete worklist result validates.

## Decision

### Expose canonical plan keys

`Plan.specializationKeys` is the ordered projection of canonical keys from the
admitted specialization carriers.  Successful `run` outcomes now have a
general proof that this list contains no duplicate keys, for both complete and
budget-exhausted results.

For a complete result, every key retained in `seedKeys` occurs in
`specializationKeys`.  Seed order and duplicates remain intentionally visible
in `seedKeys`, while admission into `specializations` remains unique.

### Extract an exact validator replay

Successful `SourceCoreDirectLinking.validatePlan` now yields an existential
bounded worklist replay.  The reconstructed run:

- uses a budget equal to the plan's admitted specialization count;
- completes rather than exhausting;
- preserves the plan's seed-key list, including duplicate roots;
- has the same specialization-key order; and
- has propositionally equal call-edge and reference-edge ledgers.

The executable validator is unchanged.  Its existing Boolean equality checks
are connected to propositional equality by private kernel-checked lemmas; no
new trusted equality or public certificate constructor is introduced.

### Extract accepted-plan endpoint closure

Every call or first-class-reference edge in an accepted plan has both its
caller and callee key in that plan's `specializationKeys`.  This is the closure
property consumed by the current compiler boundary: backend selection only
sees plans after `validatePlan` succeeds.

Positive regressions now exercise replay validation for an ordinary complete
plan and for a plan whose seed list contains a duplicate root while its admitted
specializations remain unique.

## Proof boundary

This tranche proves generation-side key uniqueness and seed closure, plus
validator-side replay and edge-endpoint soundness.  It does not yet prove:

- `run ... = .ok (.complete plan) → validatePlan program plan = .ok ()`;
- direct edge-endpoint closure for every raw complete worklist result before
  validator acceptance;
- equality of the complete specialized-function carriers in the extracted
  replay rather than their canonical key order;
- graph-runtime value/store type preservation; or
- source/runtime correspondence for linked execution.

The next canonical-plan proof step is the private `collectReferences`
request/edge correspondence, followed by worklist replay idempotence.  Together
with the uniqueness and seed-closure laws proved here, those results can support
the full validator-completeness direction without weakening the executable
checks.

## Verification target

The worklist properties, direct linker, specialization regressions, full build,
test suite, semantic-kernel audit, metadata audit, forbidden-proof scan, and
whitespace check must pass.  No omitted proof, new axiom, unsafe definition, or
native decision shortcut is permitted.
