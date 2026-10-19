import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalTerminalBodyMeaning
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
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

/-- The genuine Source return rule and whole-language preservation authenticate
values and deep heap typing. Semantic and staged failures assert no success. -/
theorem successful
    (wellFormed : ProgramWellFormed program)
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
  cases matched with
  | returned =>
    have preserved := Dynamic.FunctionStatementsExecute.preserved wellFormed
      runtime covers locals heapTyped typed completes (Staging.Recursive.Statements.returned_plain trace.sound)
    cases preserved.outcome_typed with
    | returned related => exact ⟨related, preserved.heap_typed⟩
  | unit =>
    have preserved := Dynamic.FunctionStatementsExecute.preserved wellFormed
      runtime covers locals heapTyped typed completes (Staging.Recursive.Statements.fallthrough_plain trace.sound)
    exact ⟨.unit, preserved.heap_typed⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodySourceAdmission
