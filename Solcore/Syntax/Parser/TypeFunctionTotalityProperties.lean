import Solcore.Syntax.Parser.TypeNamedTotalityProperties
import Solcore.Syntax.Parser.TypeSimpleTotalityProperties

/-! Valid-input totality for function-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

/-- Optional function returns add no invariant beyond the nested type parser. -/
theorem parseFunctionReturns_invariantFreeOnValid
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionReturns nested) := by
  intro input inputValid
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerValid := contextual_validFor .returns .typeExpr input inputValid
      rw [markerResult] at markerValid
      rcases delimited_ordinary .leftParen .rightParen true nested
          .typeExpr .typeExpr contract afterMarker markerValid.2.1 with
        ⟨values, final, valuesResult⟩ |
        ⟨failure, rejected, valuesResult⟩
      · exact Or.inl ⟨some values, final, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionReturns, getState, bind, present,
          ↓reduceIte, markerResult]⟩
  · have absent : isContextual input .returns = false := by
      cases found : isContextual input .returns with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseFunctionReturns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseFunctionReturns_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
    (∃ failure next,
      parseFunctionReturns nested input = .reject failure next) :=
  parseFunctionReturns_invariantFreeOnValid nested contract input inputValid

theorem parseFunctionReturns_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionReturns nested input ≠ .invariant error :=
  (parseFunctionReturns_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

end TypeFunctionInternals

open TypeFunctionInternals

/-- Function types add no invariant beyond their nested type parser. -/
theorem parseFunctionType_invariantFreeOnValid
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested) :
    Parser.InvariantFreeOnValid (parseFunctionType nested) := by
  intro input inputValid
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · have keywordValid := keyword_validFor .functionKw .typeExpr input inputValid
    rw [keywordResult] at keywordValid
    rcases delimited_ordinary .leftParen .rightParen true nested
        .typeExpr .typeExpr contract afterKeyword keywordValid.2.1 with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersValid := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.validFor
        contract.preservesTokenWindow.preservesTokensOnSuccess
        afterKeyword keywordValid.2.1
      rw [parametersResult] at parametersValid
      rcases parseFunctionReturns_ordinary nested contract afterParameters
          parametersValid.2.1 with
        ⟨returns, final, returnsResult⟩ |
        ⟨failure, rejected, returnsResult⟩
      · let endSpan := match returns with
          | some values => values.span
          | none => parameters.span
        exact Or.inl ⟨{
            span := SourceSpan.cover functionKeyword.span endSpan
            value := .function functionKeyword.span parameters returns
          }, final, by
            simp only [parseFunctionType, bind, keywordResult,
              parametersResult, returnsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionType, bind, keywordResult,
            parametersResult, returnsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionType, bind, keywordResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseFunctionType, bind, keywordResult]⟩

theorem parseFunctionType_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
    (∃ failure next, parseFunctionType nested input = .reject failure next) :=
  parseFunctionType_invariantFreeOnValid nested contract input inputValid

theorem parseFunctionType_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error :=
  (parseFunctionType_invariantFreeOnValid nested contract).ne_invariant
    input inputValid error

end Solcore.Syntax.Parser
