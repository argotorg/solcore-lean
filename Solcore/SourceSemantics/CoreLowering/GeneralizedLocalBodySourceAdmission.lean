import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryBodyMeaning
import Solcore.SourceSemantics.Staging.SelectedProgramPreservation
import Solcore.SourceSemantics.Staging.RecursiveBodyErasure

/-! Independent body execution supplies successful Source admission at the
actual reached heap. The stored compiler's raw return type is retained. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly

variable {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
  {context staticFinal finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
  {before after : Dynamic.Heap} {statements : List StatementId} {type : TypeSystem.Ty} {facts : BodyFacts}
  {size : Nat} {bodyOutcome : Staging.Recursive.BodyOutcome} {outcome : Staging.Recursive.Outcome}

/-- The genuine Source return rule and selected-registry preservation authenticate
values and deep heap typing. Semantic and staged failures assert no success. -/
theorem successful
    (selectedBodies : Staging.Recursive.SelectedPreservation.SelectedBodies program registry)
    (runtime : Dynamic.SourceRuntimeValid program context invocation.source)
    (covers : invocation.evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context before)
    (typed : StatementsHaveType invocation.source {returnType := type} context statements staticFinal facts)
    (completes : BodyCompletes type facts)
    (trace : Staging.Recursive.Size.Statements program registry size invocation context environment before
      statements finalContext bodyOutcome after)
    (matched : Staging.Recursive.BodyResult type bodyOutcome outcome) :
    ∀ value, outcome = .value value →
      Dynamic.ValueHasType context after value type ∧ Dynamic.HeapWellTyped context after := by
  intro value same
  subst outcome
  have preserved := Staging.Recursive.SelectedPreservation.statements selectedBodies
    runtime covers locals heapTyped typed trace
  cases matched with
  | returned => exact ⟨preserved.returned (fun _ => completes) value rfl, preserved.heap_typed⟩
  | unit => exact ⟨.unit, preserved.heap_typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
