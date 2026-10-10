import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSelectedCallCodebookReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaCalls

/-! The original accepted second gate exposes the actual application child.
Pure variable and projection reads normalize its environment without changing
the child's grade, store, closure body or captured values. The same literal
application can be inserted back into the original suffix. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
open Core Frontend SourceInference CoreProof
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)

/-- Only the pure caller prefix is changed; the body is the supplied original
native child and keeps exactly the same grade and reached store. -/
theorem application_to_payload {size : Nat} {carrier packed value : Value}
    {actual : Environment} {before after : Store}
    (completed : EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after) :
    EvaluationSize size [carrier, packed] before CallableIndexedLambdaCalls.applyPayload value after := by
  cases completed with
  | apply selected argument body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases argument with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

/-- The physical prefix can be restored around the same application child. -/
theorem application_from_payload {size : Nat} {carrier packed value : Value}
    {actual : Environment} {before after : Store}
    (completed : EvaluationSize size [carrier, packed] before
      CallableIndexedLambdaCalls.applyPayload value after) :
    EvaluationSize size (.unit :: packed :: .unit :: carrier :: actual) before
      (.apply (.second (.first (.var 3))) (.var 1)) value after := by
  cases completed with
  | apply selected argument body =>
      cases selected with
      | second tagged =>
          cases tagged with
          | first lookup =>
              cases lookup with
              | var found =>
                  simp only [List.getElem?_cons_zero] at found
                  cases Option.some.inj found
                  cases argument with
                  | var read =>
                      simp only [List.getElem?_cons_succ, List.getElem?_cons_zero] at read
                      cases Option.some.inj read
                      exact .apply (.second (.first (.var rfl))) (.var rfl) body

section Gate
variable {sidecar : SourceCoreStageContracts.Sidecar} {site : SourceCoreCallableContracts.Callsite}
  {callee : ExpressionId} {ids : List ExpressionId} {metadata : SourceInference.IndirectCallResolution}
  {node : SourceInference.ExpressionNode} {row : SourceCoreStageCodebook.Decision}
  {raw carrier packed : Value} {tag unknown : Word} {actual : Environment} {store : Store}
  (shape : carrier = .pair raw (.word tag))
  (selected : Selected sidecar site callee ids metadata node row)
  (found : site.rowAt? tag = some row)
  (count : row.entry.parameterCount = ids.length)

include shape selected found count in
/-- The selected physical count determines the original second decision. -/
theorem accepted_gate :
    Evaluates (packed :: .unit :: carrier :: actual) store
      (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
      (.inRight .word .unit) store := by
  have read : Evaluates (packed :: .unit :: carrier :: actual) store
      (.second (.var 2)) (.word tag) store := by
    rw [shape]
    exact .second (.var rfl)
  have gate := site.dispatch_known .beforeApplication unknown tag row found read
  rw [SourceCoreCallableContracts.reason_accepted row site.reasonAt .beforeApplication
    (row.afterArguments_ok (count.trans selected.argument_count.symm))] at gate
  simpa only [CallableContract.resultValue] using gate

include shape selected found count in
/-- A genuine suffix completion has a strictly smaller payload application.
The accepted guard runs at the actual argument store and changes no state. -/
theorem reflects_suffix {budget size : Nat} {result : Ty} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size (packed :: .unit :: carrier :: actual) store
      (LanguageResult.bind result
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : size ≤ budget) :
    ∃ applicationSize, applicationSize < budget ∧
      EvaluationSize applicationSize [carrier, packed] store
        CallableIndexedLambdaCalls.applyPayload value finalStore := by
  have gate := accepted_gate (packed := packed) (actual := actual) (store := store)
    (unknown := unknown) shape selected found count
  cases CallableIndirectCallBounds.bind_completed completed within with
  | failed failed strict =>
      have same := (evaluation_deterministic failed.sound gate).1
      cases same
  | continued guard application guardStrict applicationStrict =>
      obtain ⟨same, sameStore⟩ := evaluation_deterministic guard.sound gate
      cases same
      cases sameStore
      exact ⟨_, applicationStrict, application_to_payload application⟩

include shape selected found count in
/-- The concrete payload application plugs into the original accepted suffix
once, at the unchanged argument store. No body law is a static premise. -/
theorem preserves_suffix {result : Ty} {value : Value} {finalStore : Store}
    (application : Evaluates [carrier, packed] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) :
    Evaluates (packed :: .unit :: carrier :: actual) store
      (LanguageResult.bind result
        (CallableContract.dispatch site.gates .beforeApplication unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size application
  exact LanguageResult.bind_success result
    (accepted_gate (packed := packed) (actual := actual) (store := store)
      (unknown := unknown) shape selected found count)
    (application_from_payload (actual := actual) sized).sound

end Gate
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix
