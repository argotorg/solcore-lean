import Solcore.Syntax.Parser.CoreExpressionAtomRecoveryOrdinarySoundnessProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! Complete ordinary outcome for the standalone Core atom recovery parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem expressionAtomRecoveryRejects_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.ExpressionAtomRecoveryRejects
      input.declarativeRemainder input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.ExpressionAtomRecoveryRejects.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

/-- Every complete executable recovery rejection is its unavailable first
token, with no cursor movement. -/
theorem recoverAtom_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverAtom input = .reject failure rejected) :
    DeclarativeGrammar.ExpressionAtomRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverAtom at result
  cases advanced : input.advance? with
  | none =>
      simp only [advanced] at result
      unfold rejectAt at result
      cases result
      exact expressionAtomRecoveryRejects_of_advance?_eq_none input advanced
  | some pair =>
      rcases pair with ⟨token, next⟩
      simp only [advanced] at result
      rcases recoverAtomAux_production_exists_ok token.span token.span next with
        ⟨expression, output, success⟩
      rw [success] at result
      contradiction

/-- Package exact ordinary success and rejection of standalone recovery. -/
theorem recoverAtom_ordinaryOutcome_sound :
    (∀ {input output : State} {expression : Expr},
      recoverAtom input = .ok expression output →
        DeclarativeGrammar.ExpressionAtomRecoveryParses
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverAtom input = .reject failure rejected →
        DeclarativeGrammar.ExpressionAtomRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverAtom_success_ordinary_sound, recoverAtom_reject_ordinary_sound⟩

/-- Re-export deterministic standalone recovery outcomes. -/
theorem recoverAtom_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ExpressionAtomRecoveryParses
      DeclarativeGrammar.ExpressionAtomRecoveryRejects :=
  DeclarativeGrammar.expressionAtomRecoveryDeterministicOutcomeSpec

end Solcore.Syntax.Parser.ExpressionAtomInternals
