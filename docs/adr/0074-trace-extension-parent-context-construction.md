# ADR-0074: Trace-extension construction of parent-indexed frame contexts

- Status: Accepted
- Decision date: 2026-08-28
- Scope: construct one parent-indexed context from an indexed trace extension
- Implementation: Complete

## Context

ADR-0072 safely extends one fixed earlier trace event by event. ADR-0073 ties a
completed continuation context to one exact parent working pair, but leaves its
generated constructor as the only construction path. A caller must currently
assemble three nested carriers and supply both proof fields by hand.

ADR-0073 intentionally excluded a smart constructor from its own carrier
slice. This later decision narrowly overrides that exclusion in a downstream
module. The carrier and its existing resolver and laws remain unchanged.

## Decision

Add exactly one executable construction operation:

```lean
universe u v w

def ParentIndexedFrameContinuationContext.fromTraceExtension
    {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
    (parentWorking :
      WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
    (workingRollback : RollbackState)
    (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
    (result : FrameRunResult TrapReason) :
    ParentIndexedFrameContinuationContext
      RollbackState Event TrapReason parentWorking :=
  {
    stateCheckpoint := parentWorking.1
    effectCheckpoint := parentWorking.2
    effectWorking := ⟨workingRollback, extension.toTrace⟩
    result := result
    tracePrefix := extension.earlier_isPrefixOf_toTrace
    checkpoint_eq_parentWorking := rfl
  }
```

The operation accepts value arguments, not proof arguments. Its result still
stores the ADR-0071 prefix proof and ADR-0073 checkpoint-equality proof in
`Prop`; they are derived from the indexed extension and the chosen fields.

Do not accept a raw `FrameTrace`, full working journal, prefix proof, or
checkpoint-equality proof. Do not add a carrier, resolver, alias, coercion,
instance, default, second constructor operation, or branch-specific operation.
The generated definitional equation is an intentional reduction artifact.

## Required proof interface

Publish exactly four simp observation laws. For the same arguments as the
operation, their conclusions are:

```lean
namespace Solcore.Semantics.ParentIndexedFrameContinuationContext

universe u v w

variable {RollbackState : Type u} {Event : Type v} {TrapReason : Type w}
variable (parentWorking :
  WorldState × FrameEffectJournal RollbackState (FrameTrace Event))
variable (workingRollback : RollbackState)
variable (extension : FrameTrace.ExtensionFrom parentWorking.2.trace)
variable (result : FrameRunResult TrapReason)

@[simp] theorem
    stateCheckpoint_fromTraceExtension :
    (fromTraceExtension
      parentWorking workingRollback extension result).stateCheckpoint =
      parentWorking.1 := by
  rfl

@[simp] theorem
    effectCheckpoint_fromTraceExtension :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectCheckpoint =
      parentWorking.2 := by
  rfl

@[simp] theorem
    effectWorking_fromTraceExtension :
    (fromTraceExtension
      parentWorking workingRollback extension result).effectWorking =
      ⟨workingRollback, extension.toTrace⟩ := by
  rfl

@[simp] theorem
    result_fromTraceExtension :
    (fromTraceExtension
      parentWorking workingRollback extension result).result =
      result := by
  rfl

end Solcore.Semantics.ParentIndexedFrameContinuationContext
```

All four proofs are `rfl`. The operation and laws must report exactly
`[propext]` and no additional axioms. Add no prefix or resolution theorem:
ADR-0073's existing `parentWorking_tracePrefix`, `resolve_returned`, and
`resolve_reverted` laws apply directly to the constructed value.

## Required tests

Add exactly three runtime assertions importing definition modules only. Begin
with a nonempty parent trace and use ADR-0072 to record one nested event. Use
distinct parent and result WorldState storage values, parent and working
rollback values, and a nonempty result payload.

The first assertion identifies the parent state through a public storage
observation and checks the effect checkpoint's rollback and trace. The second
checks that the working journal combines the supplied rollback with the exact
parent-then-nested trace without duplicating the prefix. The third checks that
the supplied working WorldState and outcome payload are preserved in `result`.
ADR-0073 already tests return, revert, and trap resolution, so do not repeat
those branches here or import the four proof laws.

## Dependency boundary

The definition module imports only ADR-0072's trace-extension definition and
ADR-0073's carrier definition. The properties module imports only the new
definition module. Construction does not import ADR-0073's properties;
consumers may import both properties modules when they need observation and
resolution laws together.

## What this operation does not prove

The extension may be empty or contain multiple events. `workingRollback` and
`result` remain arbitrary inputs. The operation does not prove that the
extension and result came from the same execution, that an invocation occurred,
or that a runtime parent/child relationship exists.

It also does not establish checkpoint creation time, ownership or lifetime,
the relationship between parent and working rollback values, validity of
WorldState changes, event authenticity, stack or depth, scheduling,
reentrancy, argument/result delivery, trap disposition, trace survival after a
trap, transaction rollback, or atomicity.

## Staged implementation plan

Keep each of five commits below 300 changed lines: this decision and internal
roadmap update; the exact one operation and umbrella import; the exact four simp
laws and umbrella import; the exact three definition-only assertions and runner
wiring; independent audit and completion evidence.

## Publication and exclusions

This construction helper is internal. It adds no event taxonomy, balance,
code, call data, transferred value, host call/create behavior, ABI, EVM
revision, opcode, gas schedule, parser or source form, Core expression, Wire
field or tag, Profile, Oracle behavior, serialization, canonical delta, or
frozen artifact.

## Consequences

A caller can construct the exact ADR-0073 carrier from the restricted ADR-0072
extension path without supplying relationship proofs or an ambiguous complete
trace. Runtime provenance, invocation, scheduling, trap disposition, and
transaction policy remain separate decisions.

## Implementation record

The completed slice adds exactly one public `fromTraceExtension` operation in a
31-line definition module plus one umbrella import. It accepts no raw trace,
full working journal, or proof argument, and adds no carrier, resolver,
coercion, instance, alias, or second constructor operation.

A 58-line properties module plus one umbrella import publishes exactly four
simp `rfl` projection laws. The operation and all four laws report exactly
`[propext]`. An 87-line definition-only test module plus two runner lines
contains exactly three runtime assertions covering checkpoint observations,
working rollback with the exact nonduplicated trace extension, and preservation
of the supplied frame result.

The implementation commits are `d2e1959` (217 changed lines), `ef17abe` (32),
`d2b9e30` (59), and `fc3956b` (89), all below 300 changed lines; this completion
update is the fifth staged commit. Focused and full builds, tests, trust-zero,
axiom, semantic-kernel, metadata, diff, and independent P0-P3 audits pass.
