import Solcore.Syntax.DeclarativeReturnClauseExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.ReturnClauseSoundnessProperties

/-! Exact executable rejection reflection for optional canonical `returns`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable optional-`returns` rejection is the committed return-type
list rejection after its positively guarded marker. -/
theorem returnClause_reject_sound
    {input rejected : State} {failure : Failure}
    (result : returnClause input = .reject failure rejected) :
    DeclarativeGrammar.OptionalReturnClauseRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold returnClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .returns
  · rcases contextual_eq_ok_of_isContextual_eq_true .returns .typeExpr
        present with ⟨marker, markerResult⟩
    simp only [present, if_true, markerResult] at result
    cases typesResult : delimited .leftParen .rightParen true typeExpr
        .typeExpr .typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typesResult] at result
    | ok types afterTypes => simp [typesResult, pure] at result
    | reject typesFailure typesRejected =>
        simp only [typesResult] at result
        cases result
        exact .typesRejected marker.span
          (contextual_success_exactTokenParses .returns .typeExpr markerResult)
          (delimited_reject_sound .leftParen .rightParen true typeExpr
            DeclarativeGrammar.TypeExprOrdinaryParses
            DeclarativeGrammar.TypeExprRejects .typeExpr .typeExpr
            typeExpr_success_sound typeExpr_reject_sound typesResult)
  · have absent : isContextual input .returns = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package executable optional-`returns` success and exact rejection. -/
theorem returnClause_ordinaryOutcome_sound :
    (∀ {input next : State} {clause : Option ReturnClause},
      returnClause input = .ok clause next →
        DeclarativeGrammar.OptionalReturnClauseParses
          input.declarativeRemainder clause next.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      returnClause input = .reject failure rejected →
        DeclarativeGrammar.OptionalReturnClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨returnClause_success_sound, returnClause_reject_sound⟩

/-- Re-export exact optional return-clause outcomes. -/
theorem returnClause_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalReturnClauseParses
      DeclarativeGrammar.OptionalReturnClauseRejects :=
  DeclarativeGrammar.optionalReturnClauseExactOutcomeSpec

/-- Two successful optional return clauses have the same AST and remainder. -/
theorem returnClause_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option ReturnClause}
    (leftResult : returnClause input = .ok left leftOutput)
    (rightResult : returnClause input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalReturnClauseParses.result_unique
    (returnClause_success_sound leftResult)
    (returnClause_success_sound rightResult)

/-- Two return-clause rejections have the same declarative endpoint. -/
theorem returnClause_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : returnClause input = .reject leftFailure leftOutput)
    (rightResult : returnClause input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalReturnClauseRejects.output_unique
    (returnClause_reject_sound leftResult)
    (returnClause_reject_sound rightResult)

end Solcore.Syntax.Parser
