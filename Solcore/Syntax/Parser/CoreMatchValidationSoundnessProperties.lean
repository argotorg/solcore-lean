import Solcore.Syntax.DeclarativeCoreMatchStatementGrammar
import Solcore.Syntax.Parser.DiagnosticReflectionProperties
import Solcore.Syntax.Parser.Statement.Match

/-! Diagnostic reflection and clean soundness of Core-match arity validation. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

private theorem bindOkComponents {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (result : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

@[simp] theorem patternArity_eq_declarative (scrutineeCount : Nat)
    (pattern : Pattern) :
    patternArity scrutineeCount pattern =
      DeclarativeGrammar.matchPatternArity scrutineeCount pattern := by
  unfold patternArity DeclarativeGrammar.matchPatternArity
  rfl

/-- One arity check never removes diagnostics. -/
theorem validateMatchCaseArity_reflectsDiagnosticFreeOnSuccess
    (scrutineeCount : Nat) (arm : MatchCase) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (validateMatchCaseArity scrutineeCount arm) := by
  intro input checked next result diagnosticFree
  unfold validateMatchCaseArity at result
  split at result
  · cases result
    exact diagnosticFree
  · exact emitDiagnostic_reflectsDiagnosticFreeOnSuccess _ input checked
      next result diagnosticFree

/-- The full arity pass reflects through every case. -/
theorem validateMatchArities_reflectsDiagnosticFreeOnSuccess
    (scrutineeCount : Nat) : ∀ cases,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (validateMatchArities scrutineeCount cases)
  | [] => Parser.pure_reflectsDiagnosticFreeOnSuccess ()
  | arm :: rest => by
      unfold validateMatchArities
      apply Parser.bind_reflectsDiagnosticFreeOnSuccess
        (validateMatchCaseArity_reflectsDiagnosticFreeOnSuccess
          scrutineeCount arm)
      intro checked
      exact validateMatchArities_reflectsDiagnosticFreeOnSuccess
        scrutineeCount rest

/-- A diagnostic-free single check proves exact arity equality. -/
theorem validateMatchCaseArity_success_sound
    (scrutineeCount : Nat) (arm : MatchCase) {input next : State}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : validateMatchCaseArity scrutineeCount arm input = .ok () next) :
    DeclarativeGrammar.matchPatternArity scrutineeCount arm.value.pattern =
        scrutineeCount ∧
      input.diagnosticsRev = [] ∧ next = input := by
  unfold validateMatchCaseArity at result
  split at result
  · cases result
    refine ⟨?_, diagnosticFree, rfl⟩
    rw [← patternArity_eq_declarative]
    exact beq_iff_eq.mp (by assumption)
  · unfold emitDiagnostic modifyState at result
    cases result
    simp [State.emit] at diagnosticFree

/-- Diagnostic-free validation proves every case has the scrutinee arity. -/
theorem validateMatchArities_success_sound (scrutineeCount : Nat) :
    ∀ cases input next,
      next.diagnosticsRev = [] →
      validateMatchArities scrutineeCount cases input = .ok () next →
      DeclarativeGrammar.MatchCaseAritiesValid scrutineeCount cases ∧
        input.diagnosticsRev = [] ∧ next = input := by
  intro cases
  induction cases with
  | nil =>
      intro input next diagnosticFree result
      simp only [validateMatchArities, pure] at result
      cases result
      exact ⟨by simp [DeclarativeGrammar.MatchCaseAritiesValid],
        diagnosticFree, rfl⟩
  | cons arm rest inductionHypothesis =>
      intro input next diagnosticFree result
      unfold validateMatchArities at result
      rcases bindOkComponents result with
        ⟨checked, afterCheck, checkResult, restResult⟩
      rcases inductionHypothesis afterCheck next diagnosticFree restResult with
        ⟨restValid, afterCheckFree, nextEq⟩
      rcases validateMatchCaseArity_success_sound scrutineeCount arm
          afterCheckFree checkResult with
        ⟨armValid, inputFree, afterCheckEq⟩
      refine ⟨?_, inputFree, nextEq.trans afterCheckEq⟩
      intro retained member
      rcases List.mem_cons.mp member with rfl | member
      · exact armValid
      · exact restValid retained member

end Solcore.Syntax.Parser.MatchInternals
