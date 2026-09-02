import Solcore.Syntax.DeclarativePredicateExactnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeNamedRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.PredicateSoundnessProperties

/-! Exact executable ordinary-rejection reflection for one trait predicate. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable predicate rejection records its exact first rejected
stage after all successful prefixes. -/
theorem predicate_reject_sound {input rejected : State} {failure : Failure}
    (result : predicate input = .reject failure rejected) :
    DeclarativeGrammar.PredicateRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold predicate at result
  cases subjectResult : typeExpr input with
  | invariant error => simp [bind, subjectResult] at result
  | reject subjectFailure subjectRejected =>
      simp only [bind, subjectResult] at result
      cases result
      exact .subjectRejected (typeExpr_reject_sound subjectResult)
  | ok subject afterSubject =>
      simp only [bind, subjectResult] at result
      have subjectParsed := typeExpr_success_sound subjectResult
      cases colonResult : symbol .colon .typeExpr afterSubject with
      | invariant error => simp [colonResult] at result
      | reject colonFailure colonRejected =>
          have rejectedEq := symbol_reject_state_eq .colon .typeExpr
            colonResult
          subst colonRejected
          simp only [colonResult] at result
          cases result
          exact .colonMissing subjectParsed
            (symbol_reject_tokenKindAbsentAt .colon .typeExpr colonResult)
      | ok colon afterColon =>
          simp only [colonResult] at result
          have colonParsed := symbol_success_exactTokenParses .colon .typeExpr
            colonResult
          cases nameResult : identifier .typeExpr afterColon with
          | invariant error => simp [nameResult] at result
          | reject nameFailure nameRejected =>
              simp only [nameResult] at result
              cases result
              exact .nameRejected colon.span subjectParsed colonParsed
                (identifier_reject_sound .typeExpr nameResult)
          | ok traitName afterName =>
              simp only [nameResult] at result
              have nameParsed := identifier_success_sound .typeExpr nameResult
              cases argumentsResult : parseNamedTypeArguments typeExpr
                  afterName with
              | invariant error => simp [argumentsResult] at result
              | reject argumentsFailure argumentsRejected =>
                  simp only [argumentsResult] at result
                  cases result
                  exact .argumentsRejected colon.span subjectParsed
                    colonParsed nameParsed
                    (parseNamedTypeArguments_reject_type_sound typeExpr
                      DeclarativeGrammar.TypeExprRejects typeExpr_success_sound
                        typeExpr_reject_sound argumentsResult)
              | ok arguments afterArguments =>
                  simp [argumentsResult, pure] at result

/-- Package executable predicate success and exact ordinary rejection. -/
theorem predicate_ordinaryOutcome_sound :
    (∀ {input next : State} {value : Predicate},
      predicate input = .ok value next →
        DeclarativeGrammar.PredicateParses input.declarativeRemainder value
          next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      predicate input = .reject failure rejected →
        DeclarativeGrammar.PredicateRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨predicate_success_sound, predicate_reject_sound⟩

/-- Re-export exact single-predicate outcomes. -/
theorem predicate_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.PredicateParses DeclarativeGrammar.PredicateRejects :=
  DeclarativeGrammar.predicateExactOutcomeSpec

/-- Two successful predicates have the same AST and declarative remainder. -/
theorem predicate_success_result_unique
    {input leftOutput rightOutput : State} {left right : Predicate}
    (leftResult : predicate input = .ok left leftOutput)
    (rightResult : predicate input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateParses.result_unique
    (predicate_success_sound leftResult) (predicate_success_sound rightResult)

/-- Two predicate rejections have the same declarative endpoint. -/
theorem predicate_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : predicate input = .reject leftFailure leftOutput)
    (rightResult : predicate input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.PredicateRejects.output_unique
    (predicate_reject_sound leftResult) (predicate_reject_sound rightResult)

end Solcore.Syntax.Parser
