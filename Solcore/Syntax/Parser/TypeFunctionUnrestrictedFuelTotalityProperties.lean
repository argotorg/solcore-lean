import Solcore.Syntax.Parser.DelimitedUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.TypeFunctionTotalityProperties

/-! Function, optional-return, and tuple parsing have ordinary outcomes on
arbitrary states under the recursive element bound. Successful child end-index
preservation suffices; no token carrier, source, or rejected-state frame is
required, and no global state-validity hypothesis is used. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeFunctionInternals

theorem parseFunctionReturns_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ returns next, parseFunctionReturns nested input = .ok returns next) ∨
      (∃ failure next, parseFunctionReturns nested input = .reject failure next) := by
  by_cases present : isContextual input .returns
  · rcases (contextual_ordinary .returns .typeExpr) input with
      ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
    · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
        contextual_remainingCount_lt_of_success .returns .typeExpr markerResult adequate
      rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true
          nested .typeExpr .typeExpr elementFuel contract afterMarker (by omega) with
        ⟨values, final, valuesResult⟩ | ⟨failure, rejected, valuesResult⟩
      · exact Or.inl ⟨some values, final, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult, pure]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionReturns, getState, bind, present,
            ↓reduceIte, markerResult, valuesResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionReturns, getState, bind, present, ↓reduceIte, markerResult]⟩
  · have absent : isContextual input .returns = false := Bool.eq_false_iff.mpr present
    exact Or.inl ⟨none, input, by
      simp only [parseFunctionReturns, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseFunctionReturns_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseFunctionReturns nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionReturns_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨returns, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end TypeFunctionInternals

theorem parseFunctionType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseFunctionType nested input = .ok value next) ∨
      (∃ failure next, parseFunctionType nested input = .reject failure next) := by
  rcases (keyword_ordinary .functionKw .typeExpr) input with
    ⟨functionKeyword, afterKeyword, keywordResult⟩ | ⟨failure, rejected, keywordResult⟩
  · have afterKeywordAdequate : afterKeyword.remainingCount < elementFuel :=
      keyword_remainingCount_lt_of_success .functionKw .typeExpr keywordResult adequate
    rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true nested
        .typeExpr .typeExpr elementFuel contract afterKeyword (by omega) with
      ⟨parameters, afterParameters, parametersResult⟩ | ⟨failure, rejected, parametersResult⟩
    · have parametersEndIndex := delimited_endIndex_onSuccess contract.endIndexOnSuccess
        .leftParen .rightParen true .typeExpr .typeExpr parametersResult
      have parametersMonotone := delimited_cursorMonotoneOnSuccess
        .leftParen .rightParen true nested .typeExpr .typeExpr
        afterKeyword parameters afterParameters parametersResult
      have afterParametersAdequate : afterParameters.remainingCount < elementFuel :=
        remainingCount_lt_of_endIndex_eq parametersEndIndex parametersMonotone afterKeywordAdequate
      rcases TypeFunctionInternals.parseFunctionReturns_ordinary_of_unrestrictedElementFuel
          nested elementFuel contract afterParameters (by omega) with
        ⟨returns, final, returnsResult⟩ | ⟨failure, rejected, returnsResult⟩
      · let endSpan := match returns with
          | some values => values.span
          | none => parameters.span
        exact Or.inl ⟨{
            span := SourceSpan.cover functionKeyword.span endSpan
            value := .function functionKeyword.span parameters returns
          }, final, by
            simp only [parseFunctionType, bind, keywordResult, parametersResult, returnsResult, pure]
            rfl⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseFunctionType, bind, keywordResult, parametersResult, returnsResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseFunctionType, bind, keywordResult, parametersResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseFunctionType, bind, keywordResult]⟩

theorem parseFunctionType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseFunctionType nested input ≠ .invariant error := by
  intro failed
  rcases parseFunctionType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseTupleType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseTupleType nested input = .ok value next) ∨
      (∃ failure next, parseTupleType nested input = .reject failure next) := by
  rcases delimited_ordinary_of_unrestrictedElementFuel .leftParen .rightParen true nested
      .typeExpr .typeExpr elementFuel contract input adequate with
    ⟨tuple, next, tupleResult⟩ | ⟨failure, rejected, tupleResult⟩
  · exact Or.inl ⟨{ span := tuple.span, value := .tuple tuple.elements }, next, by
      simp only [parseTupleType, tupleResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseTupleType, tupleResult, bind]⟩

theorem parseTupleType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) : parseTupleType nested input ≠ .invariant error := by
  intro failed
  rcases parseTupleType_ordinary_of_unrestrictedElementFuel nested elementFuel contract input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
