# ADR-0142: Branch-complete selected Word-code classification

- Status: Accepted
- Decision date: 2026-08-30
- Scope: classify address-selected checked code without conflating non-Word code with absence
- Implementation: Planned

## Context

ADR-0141 gives a checked Word-result program a canonical successful return
frame. That bridge begins with a `CheckedHostCoreWordProgram`, while Account
code is intentionally stored and selected as the more general
`CheckedHostCoreProgram`.

The existing `WorldState.code?` is the canonical address-selected code lookup.
Its `none` means that no checked code is available at the Address, whether the
Account itself is absent or the present Account has no code. A second optional
Word refinement applied directly to this lookup would also return `none` for a
present checked program whose declared result is not Word. That would conflate
two observably different cases needed by later selected execution.

This distinction can be fixed before defining another execution carrier,
parent continuation, or unsupported-result policy.

## Decision

Add one pure branch-complete classifier:

```lean
inductive CheckedHostCoreWordCodeSelection where
  | absent
  | nonWord
      (code : CheckedHostCoreProgram)
      (resultType_ne_word : code.program.resultType ≠ .word)
  | word (code : CheckedHostCoreWordProgram)
```

`absent` has exactly the meaning of the existing `WorldState.code? = none`.
It deliberately continues to combine an absent Account with a present Account
that has no code. This ADR separates only the new distinction introduced by
Word refinement.

`nonWord` retains the exact selected checked code and proof that its declared
result is not Word. `word` retains the existing ADR-0141 refinement, including
the exact selected checked code and its Word-result proof.

## Generic classification and erasure

Define a total classifier over the existing optional checked-code observation:

```lean
def CheckedHostCoreWordCodeSelection.classify
    (selected : Option CheckedHostCoreProgram) :
    CheckedHostCoreWordCodeSelection
```

It maps `none` to `absent`. For `some code`, it decides only
`code.program.resultType = .word`, producing `word` or `nonWord` with the
corresponding proof. It does not rerun either Core checker.

Provide two projections:

```lean
def toCheckedCode? :
  CheckedHostCoreWordCodeSelection → Option CheckedHostCoreProgram

def toWordCode? :
  CheckedHostCoreWordCodeSelection → Option CheckedHostCoreWordProgram
```

The checked-code erasure returns `none` only for `absent`, and returns the exact
selected checked code from both present branches. The Word projection succeeds
only for `word`.

Prove for every optional selected code:

```text
(classify selected).toCheckedCode? = selected
(classify selected).toWordCode? =
  selected.bind CheckedHostCoreWordProgram.ofChecked?
```

These equations make the new classifier a proof-refined, information-
preserving view of existing selection, not a second code store or lookup.

## WorldState selection boundary

Add exactly one WorldState adapter:

```lean
def WorldState.selectWordCode
    (state : WorldState)
    (codeAddress : Address) :
    CheckedHostCoreWordCodeSelection :=
  CheckedHostCoreWordCodeSelection.classify
    (state.code? codeAddress)
```

This adapter belongs next to `WorldState.code?`. It must not be placed in
`Account`: Account cannot observe Account absence. It must not be placed in the
storage-host Context: classification depends only on the selected working
WorldState and code Address and should not acquire an unrelated storage-
presence precondition.

The exact checked-code erasure from `selectWordCode` must equal
`state.code? codeAddress`.

## Exact proof interface

Expose laws for:

- all three generic classifier constructor equations;
- both projections on all three constructors;
- checked-code erasure and ADR-0141 optional-refinement coherence;
- `classify selected = absent` iff `selected = none`;
- exact `nonWord` classification iff the selected value is the retained code,
  given its non-Word proof;
- exact `word` classification iff the selected value is the wrapped checked
  code;
- pairwise branch disjointness and branch exhaustiveness;
- WorldState checked-code erasure;
- WorldState `absent`, `nonWord`, and `word` exact branch laws;
- Account-absent and present-Account-without-code specialization to the same
  `absent` code-selection branch; and
- exact present checked non-Word and Word specialization through existing
  `WorldState.code?` laws.

Proofs must use the existing checked Word refinement and WorldState code lookup.
They must not inspect or replay Core execution.

## Required regressions

Compile-time consumers must apply every public classifier, projection,
erasure, exact-branch, disjointness, exhaustiveness, and WorldState coherence
law from an external namespace.

Executable regressions must cover:

- `WorldState.empty` at an arbitrary Address as `absent`;
- a present `Account.empty` at that Address as the same `absent` code branch;
- a present checked Bool-result program as `nonWord`, retaining the exact code;
- a present checked Word-result program as `word`, retaining the exact
  ADR-0141 wrapper;
- checked-code erasure agreeing with `WorldState.code?` in all three branches;
- Word projection succeeding only in the Word branch; and
- an Account storage write preserving the selected branch and exact code.

The tests should reuse existing WorldState code fixtures where practical and
must not add a public encoding.

## Dependency and publication boundary

The generic carrier depends only on `CheckedHostCoreWordProgram`. The
WorldState adapter depends on existing WorldState code selection. Neither Core
nor Account storage representation gains a dependency on frame semantics.

This ADR adds no Wire tag, Oracle command, schema, profile, metadata capability,
Surface form, grammar, parser rule, or source elaboration. The parser proof
program remains paused. The root README does not change.

Acceptance requires focused and full builds, the executable suite, trust-zero
and warning-as-error checks for every changed Lean root, metadata and semantic
kernel checks, diff hygiene, axiom reports, and an independent contract audit.

## Non-goals

This ADR does not define or prove:

- selected code execution, fuel resumption, or a new execution result;
- successful Word completion, return bytes, or frame construction beyond
  reusing the ADR-0141 refinement;
- a parent-indexed result, parent continuation, child-result delivery, call
  kind, call stack, scheduling, recursion, or reentrancy;
- an outcome for executing checked non-Word code;
- a distinction between absent Account and present Account without code;
- Account mutation, balance transfer, gas charging, transaction commit,
  rollback application, or persistence;
- Solidity ABI encoding, arbitrary Core-value serialization, a public byte
  contract, external compatibility promise, or concrete syntax.

## Planned sequence

1. record and activate this internal selected-code classification contract;
2. implement the generic three-way classifier and exact projections;
3. implement the WorldState adapter and exact coherence laws;
4. add compile-time consumers and executable three-branch regressions; and
5. run full validation, independent audit, and completion-doc synchronization.

## Consequences

Later selected Word execution can distinguish unavailable code from available
but unsupported result type before any fuel is spent. It can route only the
`word` branch into ADR-0141 while retaining the exact generic checked code in
the `nonWord` branch.

The next integration slice may add a specialized selected-execution carrier.
If it does, it should store this classification and reuse `HostDriverResult`,
`WordReturnedFrameCompletion`, and existing parent continuation types rather
than duplicating their branch structure.
