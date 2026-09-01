import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Name

/-! Exact ordinary-rejection reflection for Core-type qualified names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A rejected dotted-name tail records the first missing component and every
preceding exact dot and identifier. -/
theorem qualifiedNameTail_reject_type_sound
    (context : ParseContext) (phase : ParserPhase)
    (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      QualifiedNameInternals.qualifiedNameTail context phase first fuel last
          tailRev input = .reject failure rejected →
        DeclarativeGrammar.TypeQualifiedNameTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [QualifiedNameInternals.qualifiedNameTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold QualifiedNameInternals.qualifiedNameTail at result
      split at result
      next dotPresent =>
        cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject dotFailure dotRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .dot context dotPresent with
              ⟨dot, parsed⟩
            rw [parsed] at dotResult
            contradiction
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject componentFailure componentRejected =>
                simp only [componentResult] at result
                cases result
                exact .componentRejected dot.span
                  (symbol_success_exactTokenParses .dot context dotResult)
                  (identifier_reject_sound context componentResult)
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact .laterRejected dot.span
                  (symbol_success_exactTokenParses .dot context dotResult)
                  (identifier_success_sound context componentResult)
                  (inductionHypothesis component (component :: tailRev)
                    afterComponent failure rejected result)
      next dotAbsent =>
        unfold QualifiedNameInternals.finishQualifiedName at result
        contradiction

/-- A rejected qualified name either lacks its first identifier or rejects at
the exact missing dotted component. -/
theorem qualifiedName_reject_type_sound
    (context : ParseContext) (phase : ParserPhase)
    {input rejected : State} {failure : Failure}
    (result : qualifiedName context phase input = .reject failure rejected) :
    DeclarativeGrammar.TypeQualifiedNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure firstRejected =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected (identifier_reject_sound context firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (identifier_success_sound context firstResult)
        (qualifiedNameTail_reject_type_sound context phase first
          (afterFirst.remainingCount + 1) first [] afterFirst failure rejected
          result)

end Solcore.Syntax.Parser
