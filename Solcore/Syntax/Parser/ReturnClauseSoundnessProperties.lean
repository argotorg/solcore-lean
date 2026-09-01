import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.Signature
import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! Success soundness for optional function return clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional return clauses preserve marker priority, delimiters, and types. -/
theorem returnClause_success_sound {input next : State}
    {clause : Option ReturnClause}
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.OptionalReturnClauseParses input.declarativeRemainder
      clause next.declarativeRemainder := by
  unfold returnClause getState at result
  simp only [bind] at result
  by_cases present : isContextual input .returns
  · simp only [present, if_true] at result
    cases markerResult : contextual .returns .typeExpr input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases typesResult : delimited .leftParen .rightParen true typeExpr
            .typeExpr .typeExpr afterMarker with
        | invariant error => simp [typesResult] at result
        | reject failure rejected => simp [typesResult] at result
        | ok types afterTypes =>
            have typesGrammar := delimited_allowEmpty_trailing_success_sound
              .leftParen .rightParen typeExpr
              DeclarativeGrammar.TypeExprParses .typeExpr .typeExpr
              typeExpr_success_sound typeExpr_preservesTokenWindow typesResult
            simp only [typesResult, pure] at result
            cases result
            exact .present marker.span
              (contextual_success_exactTokenParses .returns .typeExpr
                markerResult) typesGrammar
  · have absent : isContextual input .returns = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (contextualAbsentAt_of_isContextual_eq_false .returns absent)

/-- Return-clause grammar soundness composes with source validity. -/
theorem returnClause_success_sound_and_validFor {input next : State}
    {clause : Option ReturnClause} (inputValid : input.ValidFor)
    (result : returnClause input = .ok clause next) :
    DeclarativeGrammar.OptionalReturnClauseParses input.declarativeRemainder
        clause next.declarativeRemainder ∧
      Option.ValidFor ReturnClause.ValidFor input.file clause := by
  refine ⟨returnClause_success_sound result, ?_⟩
  have valid := returnClause_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
