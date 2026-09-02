import Solcore.Syntax.DeclarativeReturnClauseOutcomeProperties
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

end Solcore.Syntax.Parser
