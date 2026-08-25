# ADR-0004: Canonical Tabled Class Resolution

- Status: Accepted
- Decision date: 2026-07-23
- Scope: static semantics

## Reader summary / Current implementation

- **Decision:** Normative class resolution uses tabled search and returns sound,
  coherent evidence; reaching an explicit search limit is inconclusive.
- **Current implementation:** The feature is recorded as direction-accepted but
  planned. No source resolver or tabled class-resolution executor is present.
- **Boundary:** The completed M1 Core checker has no classes, and compiler legacy
  search behavior remains comparison evidence only.
- **Suggested reading:** Read “Decision” for solver semantics and
  “Conformance Requirements” for the future proof obligations.

## Context

The Haskell compiler's default legacy resolver produces different fixture
results from the Haskell tabled mode and the Rust resolver for recursive
superclasses, table reuse, and mutual chains. If failures from the legacy mode
were fixed as language rejections, the solver's search strategy would
accidentally define the type system.

Class resolution is not merely a Boolean decision. It must also guarantee the
soundness and coherence of the evidence used by elaboration.

## Decision

Normative class resolution in Lean uses tabled resolution.

- Goals and answers are tabled, permitting reuse of an identical subgoal.
- A successful result returns evidence that satisfies declarative entailment.
- Evidence for the same normative program must be observationally coherent.
- Explicit limits may be imposed on the solver's table count, answer count,
  and step count.
- Reaching a limit is `inconclusive`, not a type error.

Legacy resolution is represented only as an `ImplementationBaseline` in the
compatibility harness and is not included in a normative `SpecProfile`.

## Consequences

- A recursive or reuse fixture that fails only in legacy Haskell is not counted
  as a language difference.
- A historical verdict that did not record the solver mode cannot be used as
  normative evidence.
- Accidental success or failure caused by resolver search order is excluded
  from the specification.
- A different sound algorithm may conform in the future if it satisfies the
  same entailment and coherence requirements.

## Conformance Requirements

- A proof of declarative entailment must be constructible from each successful
  solver result.
- Positive tests must cover recursive superclasses, answer reuse, and mutual
  chains.
- A negative test must cover a finite goal that cannot be solved.
- Inconclusive tests must cover the table, answer, and step limits separately.
- Tests must verify that changing goal and instance enumeration order does not
  change the normative verdict.
- Compatibility runs must record the Haskell and Rust solver modes in their
  results.
