# ADR-0143: Proof-refined selected checked Word execution

- Status: Complete
- Decision date: 2026-08-30
- Scope: connect branch-complete selected Word code to checked storage execution
- Implementation: Complete

## Context

ADR-0142 classifies address-selected checked code as `codeAbsent`, `nonWord`,
or `word` without losing the original checked program. ADR-0141 runs a known
`CheckedHostCoreWordProgram` and projects an exact successful Word completion
with canonical 32-byte return data.

The two boundaries are deliberately separate. A caller that starts from a
WorldState still has to retain the selected branch, run only the Word branch,
and distinguish an unavailable or unsupported program from a Word execution
that has merely exhausted its current fuel.

This integration must not introduce another enumeration of raw execution
outcomes. `HostDriverResult` already owns completion, exhaustion, fault, and
unsupported policy;
`WordReturnedFrameCompletion` already owns the successful Word projection.

## Decision

Add a proof-refined execution value indexed by the immutable initial storage
context and execution inputs:

```lean
structure SelectedCheckedWordExecution
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs) where
  providedFuel : Nat
  selection : CheckedHostCoreWordCodeSelection
  selection_eq :
    selection =
      initialContext.context.values.working.1.selectWordCode
        inputs.codeAddress
  execution? :
    Option
      (CheckedHostCoreWordProgram ×
        HostDriverResult
          (HostStorageDriver.Context RollbackState TraceState))
  execution_eq_run :
    execution? =
      selection.toWordCode?.map fun code =>
        (code, code.runWithStorage initialContext inputs providedFuel)
```

The initial context and all run-fixed inputs are type indices. They cannot be
replaced during resumption. Fuel is retained as a field so that summed-budget,
zero, and addition laws are ordinary equalities rather than cast-heavy
heterogeneous statements.

`selection` is the single branch authority. `execution?` is derived exactly
from that selection and is present only for `word`. Keeping both in the same
certified value preserves the difference between `codeAbsent` and `nonWord`
even though neither has a raw execution.

## Canonical start

Define:

```lean
def SelectedCheckedWordExecution.start
    (initialContext : HostStorageDriver.Context RollbackState TraceState)
    (inputs : HostStorageDriver.ExecutionInputs)
    (fuel : Nat) :
    SelectedCheckedWordExecution initialContext inputs
```

`start` performs the ADR-0142 selection against the working WorldState at
`inputs.codeAddress`. It executes exactly the selected Word program with the
given context, inputs, and fuel. The absent and non-Word branches perform no
Core execution and retain no invented outcome.

The structure's equality proof is the authoritative relation between the
stored optional execution and the canonical run. Later proofs and consumers
must not need to unfold the implementation of `start`.

## Completion projection

Define one derived projection:

```lean
def SelectedCheckedWordExecution.completion? ... :
    Option (WordReturnedFrameCompletion RollbackState TraceState)
```

It binds `execution?` and applies the existing
`HostDriverResult.toWordReturnedFrameCompletion?` to the retained raw result.
It does not copy the context, Word, Store, byte encoder, or frame adapter.

For the whole selected execution, `completion? = none` has three distinct
causes:

1. `execution? = none`, meaning `codeAbsent` or `nonWord`; or
2. a Word execution exists and its checked raw result is exactly exhausted; or
3. a Word execution exists and stops at an unsupported-policy suspension.

No global theorem may state that missing completion means only exhaustion.
Under an explicit `word code` selection, the existing ADR-0141 theorem does
give the exact exhaustion-or-unsupported equivalence.

## Fixed-input resumption

Define:

```lean
def SelectedCheckedWordExecution.resumeWithFuel
    (execution : SelectedCheckedWordExecution initialContext inputs)
    (additional : Nat) :
    SelectedCheckedWordExecution initialContext inputs
```

The selection remains unchanged. An absent or non-Word execution remains
absent. A retained Word raw result resumes through the existing storage handler
indexed by the same `inputs`; total provided fuel becomes
`execution.providedFuel + additional`.

The canonical-run proof is discharged with ADR-0141's exact split-fuel law.
Resumption must use the retained raw result, not silently execute an unrelated
program or accept replacement inputs.

Prove these session-level laws:

```text
resumeWithFuel execution additional =
  start initialContext inputs (execution.providedFuel + additional)

resumeWithFuel execution 0 = execution

resumeWithFuel (resumeWithFuel execution first) second =
  resumeWithFuel execution (first + second)
```

The one-shot equality also canonicalizes any proof fields carried by a value
constructed outside `start`.

## Exact proof interface

Expose laws for:

- every `start` field and its exact optional execution;
- extensional equality from `providedFuel`, `selection`, and `execution?`;
- selected checked-code erasure agreeing with the initial working
  `WorldState.code?` at `inputs.codeAddress`;
- selected Word projection agreeing with optional ADR-0141 refinement;
- `execution? = none` iff the selection has no Word projection;
- exact absence of execution for `codeAbsent` and `nonWord`;
- exact `(code, raw result)` execution for `word code`;
- an exact `execution? = some (code, result)` iff relating the selected Word
  branch to its canonical raw run;
- checked Word typing, raw-fault impossibility, and completed Word shape for
  every retained execution;
- exact successful completion/reconstruction through
  `WordReturnedFrameCompletion.toHostDriverResult`;
- the global missing-completion disjunction;
- the Word-branch missing-completion/exhaustion-or-unsupported equivalence;
- all resumption field projections, summed-run equality, zero identity,
  addition, and terminal-completion stability.

The public interface should let downstream proofs consume the contract without
unfolding `start`, `resumeWithFuel`, or `completion?`.

## Required regressions

Compile-time consumers must apply every public theorem from a namespace outside
the implementation namespace.

Executable regressions must use contexts whose storage Account is present and
cover:

- `codeAbsent` with small and large fuel, retaining no execution;
- a checked non-Word program with small and large fuel, retaining the exact
  `nonWord` branch and no execution;
- a checked Word program at the established exhaustion and completion fuel
  boundaries;
- exact split execution across the established boundary, including zero and
  addition laws;
- terminal completion stability after further fuel;
- completed Word, Store, final context, canonical 32-byte return data, and
  returned-frame projection through the existing ADR-0141 carrier; and
- unchanged selection and immutable inputs across every resume operation.

Fixtures should reuse ADR-0141 and ADR-0142 programs and contexts rather than
introducing another execution model.

## Dependency and publication boundary

The new carrier depends on ADR-0142 selection, ADR-0141 checked Word execution,
and existing storage-driver resumption. It embeds the existing raw result and
successful completion types; it does not add a competing frame or result
carrier.

This ADR adds no Wire tag, Oracle command, schema, profile, metadata capability,
Surface form, grammar, parser rule, or source elaboration. Parser work remains
paused. The root README does not change.

Acceptance requires focused and full builds, the executable suite, trust-zero
and warning-as-error checks for every changed Lean root, metadata and semantic
kernel checks, diff hygiene, axiom reports, and an independent contract audit.

## Non-goals

This ADR does not define or prove:

- storage-Account absence or parent-indexed initialization;
- changes to `runCodeWithStorage?`, `ParentIndexedSelectedExecutionResult`, or
  `ParentIndexedSelectedExecutionSession`;
- a new raw completion, exhaustion, fault, unsupported, frame, or resolution
  branch;
- execution, rejection, or trapping policy for selected non-Word code;
- replacement context or execution inputs during resumption;
- parent continuation, child-result delivery, call kind, scheduling,
  recursion, reentrancy, or a call stack;
- gas prices, consumed-gas reporting, refunds, balance transfer, transaction
  commit, rollback application, or persistence;
- Solidity ABI encoding, arbitrary Core-value serialization, a public byte
  contract, external compatibility promise, or concrete syntax.

## Completed implementation

The completed slice includes the proof-refined carrier, canonical start,
completion view, exact selection and execution laws, safety and projection
proofs, fixed-input resumption algebra, compile-time consumers, executable
branch and fuel regressions, full validation, independent audits, and
documentation synchronization.

The implementation exposes 32 public theorems with 32 external compile-time
consumers. Runtime regressions cover absent and non-Word selections at fuel 0
and 64, zero resumption, Word exhaustion at 9, 10, and 15, completion at 16,
exact 9+7, 10+6, and 15+1 splits, associative `(9+3)+4 = 9+(3+4) = 16`
resumption, and terminal stability. Successful tests retain the exact Store and
host context and verify canonical 32-byte data, decoding, and frame projection.

The full 709-job build, 1,306-job test-executable build, and test suite pass.
All 10 changed Lean roots pass trust-zero and warning-as-error checks; metadata,
semantic-kernel, and diff checks pass. Public theorem axiom reports are exactly
`[propext, Quot.sound]`. Independent coverage and contract audits found no
P0-P3 issue.

## Consequences

Address-selected checked code now has a direct path to canonical Word return
bytes without losing why execution did not start. Downstream parent integration
can embed this certified value and reuse its exact raw or completion view.

The next integration slice may add the missing storage-presence and
parent-indexed boundary. It should consume this carrier rather than repeat
selection or Word execution, and must still defer true nested-call policy until
child-result delivery and scheduling are specified.
