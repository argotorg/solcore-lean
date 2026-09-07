import Solcore.Syntax.Parser.ExpressionAtomRecoveryTraceProperties
import Solcore.Syntax.Parser.CoreExpressionAtomBoundaryOutcomeSoundnessProperties

/-! Public atom guards and frames over the actual supplied core. Source/end-byte
frames deliberately allow changed token carriers and end indices. Full-window
context and ordinary execution are separate, explicit conditional contracts. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeclarativeGrammar ExpressionAtomInternals

variable {nested : Parser Expr} {block : Parser Block}

theorem isAtomBoundary_true_iff (input : State) :
    isAtomBoundary input = true ↔ ExpressionAtomBoundaryStops input.declarativeRemainder := by
  constructor
  · exact expressionAtomBoundaryStops_of_isAtomBoundary input
  · intro stops
    cases guard : isAtomBoundary input with
    | true => rfl
    | false => exact False.elim (no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false input guard stops)

theorem isAtomBoundary_false_iff (input : State) :
    isAtomBoundary input = false ↔ ¬ ExpressionAtomBoundaryStops input.declarativeRemainder := by
  constructor
  · exact no_expressionAtomBoundaryStops_of_isAtomBoundary_eq_false input
  · intro continues
    cases guard : isAtomBoundary input with
    | false => rfl
    | true => exact False.elim (continues ((isAtomBoundary_true_iff input).mp guard))

theorem expressionAtom_preservesFile
    (coreFile : Parser.PreservesFile (expressionAtomCore nested block)) :
    Parser.PreservesFile (expressionAtom nested block) := by
  intro input
  cases coreResult : expressionAtomCore nested block input with
  | ok value next =>
      simp only [expressionAtom, coreResult]
      exact coreFile.file_eq_of_ok coreResult
  | reject failure failed =>
      have frame := coreFile.file_eq_of_reject coreResult
      simp only [expressionAtom, coreResult]
      split
      · exact frame
      · exact (recoverAtom_preservesFile _).trans frame
  | invariant error => simp only [expressionAtom, coreResult]; trivial

theorem expressionAtom_success_source_end
    (coreSuccessFrame : ∀ {input output value}, expressionAtomCore nested block input = .ok value output →
      output.file = input.file ∧ output.window.endByte = input.window.endByte)
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input output : State} {value : Expr}
    (result : expressionAtom nested block input = .ok value output) :
    output.file = input.file ∧ output.window.endByte = input.window.endByte := by
  cases coreResult : expressionAtomCore nested block input with
  | ok actual next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      exact coreSuccessFrame coreResult
  | reject failure failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · contradiction
      · have recovery := recoverAtom_success_context result
        exact ⟨recovery.1.trans frame.1, (congrArg TokenWindow.endByte recovery.2).trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_source_end
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window.endByte = input.window.endByte := by
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact frame
      · have recovery := recoverAtom_reject_context result
        exact ⟨recovery.1.trans frame.1, (congrArg TokenWindow.endByte recovery.2).trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_success_context
    (coreSuccessFrame : ParserSuccessContext (expressionAtomCore nested block))
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window) :
    ParserSuccessContext (expressionAtom nested block) := by
  intro input output value result
  cases coreResult : expressionAtomCore nested block input with
  | ok actual next =>
      simp only [expressionAtom, coreResult] at result
      cases result
      exact coreSuccessFrame coreResult
  | reject failure failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · contradiction
      · have recovery := recoverAtom_success_context result
        exact ⟨recovery.1.trans frame.1, recovery.2.trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_reject_context
    (coreRejectFrame : ∀ {input rejected failure}, expressionAtomCore nested block input = .reject failure rejected →
      rejected.file = input.file ∧ rejected.window = input.window)
    {input rejected : State} {failure : Failure}
    (result : expressionAtom nested block input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  cases coreResult : expressionAtomCore nested block input with
  | ok value next => simp only [expressionAtom, coreResult] at result; contradiction
  | reject original failed =>
      have frame := coreRejectFrame coreResult
      simp only [expressionAtom, coreResult] at result
      split at result
      · rcases Reply.reject.inj result with ⟨rfl, stateEq⟩
        rw [← stateEq]
        exact frame
      · have recovery := recoverAtom_reject_context result
        exact ⟨recovery.1.trans frame.1, recovery.2.trans frame.2⟩
  | invariant error => simp only [expressionAtom, coreResult] at result; contradiction

theorem expressionAtom_ordinary_of_core
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block)) :
    Parser.Ordinary (expressionAtom nested block) := by
  intro input
  rcases coreOrdinary input with ⟨value, next, parsed⟩ | ⟨failure, failed, rejected⟩
  · exact .inl ⟨value, next, by simp only [expressionAtom, parsed]⟩
  · simp only [expressionAtom, rejected]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_core
    (coreOrdinary : Parser.Ordinary (expressionAtomCore nested block))
    (input : State) (error : ParserInvariantError) : expressionAtom nested block input ≠ .invariant error :=
  (expressionAtom_ordinary_of_core coreOrdinary).ne_invariant input error

end Solcore.Syntax.Parser
