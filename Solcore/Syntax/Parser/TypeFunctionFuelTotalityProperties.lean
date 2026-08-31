import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeFunctionTotalityProperties

/-! Fuel-aware totality for recursive function-type parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

/--
Optional function returns are ordinary when their input has one unit more than
the nested element-fuel bound. A present `returns` consumes that extra unit
before entering its delimited result list.
-/
theorem parseFunctionReturns_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
      (∃ failure next,
        parseFunctionReturns nested input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ |
      ⟨failure, rejected, markerResult⟩
    · have markerValid := contextual_validFor .returns .typeExpr
        input inputValid
      rw [markerResult] at markerValid
      have markerWindow := contextual_preservesTokenWindow .returns .typeExpr
        input
      rw [markerResult] at markerWindow
      have markerProgress : input.cursor < afterMarker.cursor :=
        acceptToken_cursor_lt_onSuccess (.contextual .returns) .typeExpr
          (·.isContextual .returns) markerResult
      have afterMarkerAdequate :
          afterMarker.remainingCount < elementFuel :=
        remainingCount_lt_after_strict_progress markerValid.2.1
          markerWindow.2 markerProgress adequate
      rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
          nested .typeExpr .typeExpr elementFuel contract afterMarker
          markerValid.2.1 (by omega) with
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

theorem parseFunctionReturns_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseFunctionReturns nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionReturns_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨returns, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end TypeFunctionInternals

/--
A function type is ordinary with one unit more than its nested element fuel.
The keyword pays that unit; parameter and return-list successes preserve the
strict remaining-count bound passed to later stages.
-/
theorem parseFunctionType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
      (∃ failure next,
        parseFunctionType nested input = .reject failure next) := by
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ |
    ⟨failure, rejected, keywordResult⟩
  · have keywordValid := keyword_validFor .functionKw .typeExpr
      input inputValid
    rw [keywordResult] at keywordValid
    have keywordWindow := keyword_preservesTokenWindow .functionKw .typeExpr
      input
    rw [keywordResult] at keywordWindow
    have keywordProgress : input.cursor < afterKeyword.cursor :=
      acceptToken_cursor_lt_onSuccess (.keyword .functionKw) .typeExpr
        (· == .keyword .functionKw) keywordResult
    have afterKeywordAdequate :
        afterKeyword.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress keywordValid.2.1
        keywordWindow.2 keywordProgress adequate
    rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
        nested .typeExpr .typeExpr elementFuel contract afterKeyword
        keywordValid.2.1 (by omega) with
      ⟨parameters, afterParameters, parametersResult⟩ |
      ⟨failure, rejected, parametersResult⟩
    · have parametersValid := delimited_validFor (fun _ _ => True)
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.validFor
        contract.preservesTokenWindow.preservesTokensOnSuccess
        afterKeyword keywordValid.2.1
      rw [parametersResult] at parametersValid
      have parametersWindow := delimited_preservesTokenWindow
        .leftParen .rightParen true nested .typeExpr .typeExpr
        contract.preservesTokenWindow afterKeyword
      rw [parametersResult] at parametersWindow
      have parametersMonotone := delimited_cursorMonotoneOnSuccess
        .leftParen .rightParen true nested .typeExpr .typeExpr
        afterKeyword parameters afterParameters parametersResult
      have afterParametersAdequate :
          afterParameters.remainingCount < elementFuel :=
        remainingCount_lt_of_cursor_le parametersWindow.2
          parametersMonotone afterKeywordAdequate
      rcases TypeFunctionInternals.parseFunctionReturns_ordinary_of_elementFuel
          nested elementFuel
          contract afterParameters parametersValid.2.1 (by omega) with
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

theorem parseFunctionType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseFunctionType nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionType_ordinary_of_elementFuel nested elementFuel
      contract input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
