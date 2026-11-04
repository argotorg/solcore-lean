import Solcore.Syntax.Parser.Internal.DelimitedTotality
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.TypeFormTotality

/-!
Totality of the parsers of recursive type expressions at fuel: on valid input they make
progress and end in an ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TypeSimpleFuelTotalityProperties
/-! Fuel-aware totality for non-named, non-function recursive type forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Mapping types are ordinary when their nested type fuel covers the input. -/
theorem parseMappingType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseMappingType nested input = .ok value next) ∨
    (∃ failure next, parseMappingType nested input = .reject failure next) := by
  rcases (contextual_ordinary .mapping .typeExpr) input with
    ⟨mapping, afterMapping, mappingResult⟩ |
    ⟨failure, rejected, mappingResult⟩
  · have mappingValid := contextual_validFor .mapping .typeExpr input inputValid
    rw [mappingResult] at mappingValid
    have mappingWindow := contextual_preservesTokenWindow .mapping .typeExpr input
    rw [mappingResult] at mappingWindow
    have afterMappingAdequate : afterMapping.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress mappingValid.2.1
        mappingWindow.2
        (acceptToken_cursor_lt_onSuccess (.contextual .mapping) .typeExpr
          (·.isContextual .mapping) mappingResult) adequate
    rcases (symbol_ordinary .leftParen .typeExpr) afterMapping with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingValid := symbol_validFor .leftParen .typeExpr afterMapping
        mappingValid.2.1
      rw [openingResult] at openingValid
      have openingWindow :=
        symbol_preservesTokenWindow .leftParen .typeExpr afterMapping
      rw [openingResult] at openingWindow
      have afterOpeningAdequate :
          afterOpening.remainingCount < elementFuel :=
        remainingCount_lt_of_cursor_le openingWindow.2
          (symbol_cursorMonotoneOnSuccess .leftParen .typeExpr
            afterMapping opening afterOpening openingResult)
          afterMappingAdequate
      rcases contract.ordinary afterOpening openingValid.2.1
          afterOpeningAdequate with
        ⟨key, afterKey, keyResult⟩ | ⟨failure, rejected, keyResult⟩
      · have keyValid := contract.validFor afterOpening openingValid.2.1
        rw [keyResult] at keyValid
        have keyWindow := contract.preservesTokenWindow afterOpening
        rw [keyResult] at keyWindow
        have afterKeyAdequate : afterKey.remainingCount < elementFuel :=
          remainingCount_lt_of_cursor_le keyWindow.2
            (Nat.le_of_lt (contract.cursorLtOnSuccess keyResult))
            afterOpeningAdequate
        rcases (symbol_ordinary .fatArrow .typeExpr) afterKey with
          ⟨arrow, afterArrow, arrowResult⟩ |
          ⟨failure, rejected, arrowResult⟩
        · have arrowValid := symbol_validFor .fatArrow .typeExpr afterKey
            keyValid.2.1
          rw [arrowResult] at arrowValid
          have arrowWindow :=
            symbol_preservesTokenWindow .fatArrow .typeExpr afterKey
          rw [arrowResult] at arrowWindow
          have afterArrowAdequate :
              afterArrow.remainingCount < elementFuel :=
            remainingCount_lt_of_cursor_le arrowWindow.2
              (symbol_cursorMonotoneOnSuccess .fatArrow .typeExpr
                afterKey arrow afterArrow arrowResult) afterKeyAdequate
          rcases contract.ordinary afterArrow arrowValid.2.1
              afterArrowAdequate with
            ⟨mapped, afterValue, valueResult⟩ |
            ⟨failure, rejected, valueResult⟩
          · rcases (symbol_ordinary .rightParen .typeExpr) afterValue with
              ⟨closing, final, closingResult⟩ |
              ⟨failure, rejected, closingResult⟩
            · exact Or.inl ⟨{
                  span := SourceSpan.cover mapping.span closing.span
                  value := .mapping mapping.span
                    (SourceSpan.cover opening.span closing.span) key mapped
                }, final, by
                simp only [parseMappingType, bind, mappingResult,
                  openingResult, keyResult, arrowResult, valueResult,
                  closingResult, pure]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [parseMappingType, bind, mappingResult,
                  openingResult, keyResult, arrowResult, valueResult,
                  closingResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [parseMappingType, bind, mappingResult, openingResult,
                keyResult, arrowResult, valueResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [parseMappingType, bind, mappingResult, openingResult,
              keyResult, arrowResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseMappingType, bind, mappingResult, openingResult,
            keyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseMappingType, bind, mappingResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseMappingType, bind, mappingResult]⟩

theorem parseMappingType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseMappingType nested input ≠ .invariant error := by
  intro failed
  rcases parseMappingType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Comptime types are ordinary when their nested type fuel covers the input. -/
theorem parseComptimeType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseComptimeType nested input = .ok value next) ∨
    (∃ failure next, parseComptimeType nested input = .reject failure next) := by
  rcases (contextual_ordinary .comptime .typeExpr) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := contextual_validFor .comptime .typeExpr input inputValid
    rw [markerResult] at markerValid
    have markerWindow := contextual_preservesTokenWindow .comptime .typeExpr input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress markerValid.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.contextual .comptime) .typeExpr
          (·.isContextual .comptime) markerResult) adequate
    rcases (symbol_ordinary .less .typeExpr) afterMarker with
      ⟨opening, afterOpening, openingResult⟩ |
      ⟨failure, rejected, openingResult⟩
    · have openingValid := symbol_validFor .less .typeExpr afterMarker
        markerValid.2.1
      rw [openingResult] at openingValid
      have openingWindow := symbol_preservesTokenWindow .less .typeExpr afterMarker
      rw [openingResult] at openingWindow
      have afterOpeningAdequate :
          afterOpening.remainingCount < elementFuel :=
        remainingCount_lt_of_cursor_le openingWindow.2
          (symbol_cursorMonotoneOnSuccess .less .typeExpr afterMarker opening
            afterOpening openingResult) afterMarkerAdequate
      rcases contract.ordinary afterOpening openingValid.2.1
          afterOpeningAdequate with
        ⟨inner, afterInner, innerResult⟩ | ⟨failure, rejected, innerResult⟩
      · rcases (symbol_ordinary .greater .typeExpr) afterInner with
          ⟨closing, final, closingResult⟩ |
          ⟨failure, rejected, closingResult⟩
        · exact Or.inl ⟨{
              span := SourceSpan.cover marker.span closing.span
              value := .comptime marker.span
                (SourceSpan.cover opening.span closing.span) inner
            }, final, by
            simp only [parseComptimeType, bind, markerResult, openingResult,
              innerResult, closingResult, pure]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [parseComptimeType, bind, markerResult, openingResult,
              innerResult, closingResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseComptimeType, bind, markerResult, openingResult,
            innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseComptimeType, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseComptimeType, bind, markerResult]⟩

theorem parseComptimeType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseComptimeType nested input ≠ .invariant error := by
  intro failed
  rcases parseComptimeType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Proxy types are ordinary when their nested type fuel covers the input. -/
theorem parseProxyType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseProxyType nested input = .ok value next) ∨
    (∃ failure next, parseProxyType nested input = .reject failure next) := by
  rcases (symbol_ordinary .at .typeExpr) input with
    ⟨marker, afterMarker, markerResult⟩ |
    ⟨failure, rejected, markerResult⟩
  · have markerValid := symbol_validFor .at .typeExpr input inputValid
    rw [markerResult] at markerValid
    have markerWindow := symbol_preservesTokenWindow .at .typeExpr input
    rw [markerResult] at markerWindow
    have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      remainingCount_lt_after_strict_progress markerValid.2.1 markerWindow.2
        (acceptToken_cursor_lt_onSuccess (.symbol .at) .typeExpr
          (· == .symbol .at) markerResult) adequate
    rcases contract.ordinary afterMarker markerValid.2.1
        afterMarkerAdequate with
      ⟨inner, final, innerResult⟩ | ⟨failure, rejected, innerResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span inner.span
          value := .proxy marker.span inner
        }, final, by
        unfold parseProxyType
        simp only [markerResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        unfold parseProxyType
        simp only [markerResult, innerResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold parseProxyType
      simp only [markerResult]⟩

theorem parseProxyType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseProxyType nested input ≠ .invariant error := by
  intro failed
  rcases parseProxyType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Tuple types inherit the fuel-aware totality of generic delimiters. -/
theorem parseTupleType_ordinary_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseTupleType nested input = .ok value next) ∨
    (∃ failure next, parseTupleType nested input = .reject failure next) := by
  rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true nested
      .typeExpr .typeExpr elementFuel contract input inputValid adequate with
    ⟨tuple, next, tupleResult⟩ | ⟨failure, rejected, tupleResult⟩
  · exact Or.inl ⟨{
        span := tuple.span
        value := .tuple tuple.elements
      }, next, by
      unfold parseTupleType
      simp only [tupleResult, bind, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      unfold parseTupleType
      simp only [tupleResult, bind]⟩

theorem parseTupleType_ne_invariant_of_elementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : FuelElementTotalityContract nested elementFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseTupleType nested input ≠ .invariant error := by
  intro failed
  rcases parseTupleType_ordinary_of_elementFuel nested elementFuel contract
      input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.TypeFuelTotalityProperties
/-! Adequate-fuel and public totality for the recursive type parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- More fuel than remaining tokens rules out recursive type fuel exhaustion. -/
theorem typeExprWithFuel_ordinary_of_remainingCount_lt :
    ∀ fuel input, input.ValidFor → input.remainingCount < fuel →
      (∃ value next, typeExprWithFuel fuel input = .ok value next) ∨
      (∃ failure next,
        typeExprWithFuel fuel input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro input inputValid adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input inputValid adequate
      let nestedContract :
          FuelElementTotalityContract (typeExprWithFuel fuel) fuel := {
        validFor := (typeExprWithFuel_validFor fuel).mono
          (fun _file _value _valueValid => trivial)
        preservesTokenWindow := typeExprWithFuel_preservesTokenWindow fuel
        cursorLtOnSuccess := typeExprWithFuel_cursor_lt_onSuccess fuel
        ordinary := inductionHypothesis
      }
      simp only [typeExprWithFuel]
      split
      · exact parseFunctionType_ordinary_of_elementFuel
          (typeExprWithFuel fuel) fuel nestedContract input inputValid
          (by simpa [Nat.succ_eq_add_one] using adequate)
      · split
        · exact parseComptimeType_ordinary_of_elementFuel
            (typeExprWithFuel fuel) fuel nestedContract input inputValid
            (by simpa [Nat.succ_eq_add_one] using adequate)
        · split
          · exact parseMappingType_ordinary_of_elementFuel
              (typeExprWithFuel fuel) fuel nestedContract input inputValid
              (by simpa [Nat.succ_eq_add_one] using adequate)
          · split
            · exact parseProxyType_ordinary_of_elementFuel
                (typeExprWithFuel fuel) fuel nestedContract input inputValid
                (by simpa [Nat.succ_eq_add_one] using adequate)
            · split
              · exact parseTupleType_ordinary_of_elementFuel
                  (typeExprWithFuel fuel) fuel nestedContract input inputValid
                  (by simpa [Nat.succ_eq_add_one] using adequate)
              · split
                · exact parseNamedType_ordinary_of_elementFuel
                    (typeExprWithFuel fuel) fuel nestedContract input inputValid
                    (by simpa [Nat.succ_eq_add_one] using adequate)
                · exact Or.inr ⟨_, input, rfl⟩

theorem typeExprWithFuel_ne_invariant_of_remainingCount_lt
    (fuel : Nat) (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    typeExprWithFuel fuel input ≠ .invariant error := by
  intro failed
  rcases typeExprWithFuel_ordinary_of_remainingCount_lt fuel input inputValid
      adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- The production fuel choice makes public type parsing invariant-free. -/
theorem typeExpr_invariantFreeOnValid :
    Parser.InvariantFreeOnValid typeExpr := by
  intro input inputValid
  unfold typeExpr
  exact typeExprWithFuel_ordinary_of_remainingCount_lt
    (input.remainingCount + 1) input inputValid (by omega)

theorem typeExpr_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeExpr input ≠ .invariant error :=
  typeExpr_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public type parsing satisfies the complete recursive element contract. -/
theorem typeExpr_elementTotalityContract :
    ElementTotalityContract typeExpr := {
  validFor := typeExpr_validFor.mono
    (fun _file _value _valueValid => trivial)
  preservesTokenWindow := typeExpr_preservesTokenWindow
  cursorLtOnSuccess := typeExpr_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    typeExpr_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
end
