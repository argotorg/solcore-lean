import Solcore.Syntax.Parser.UnrestrictedFuelElementContract
import Solcore.Syntax.Parser.Type

/-! Raw proxy, comptime, and mapping types have ordinary outcomes on arbitrary
states when a real prefix token pays for the nested fuel. No source, token,
diagnostic, or validity invariant is needed. Successful child end-index and
cursor laws only propagate the bound between mapping's two nested calls. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

theorem parseProxyType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseProxyType nested input = .ok value next) ∨
    (∃ failure next, parseProxyType nested input = .reject failure next) := by
  rcases symbol_ordinary .at .typeExpr input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      symbol_remainingCount_lt_of_success .at .typeExpr markerResult adequate
    rcases contract.ordinary afterMarker afterMarkerAdequate with
      ⟨inner, final, innerResult⟩ | ⟨failure, rejected, innerResult⟩
    · exact Or.inl ⟨{
          span := SourceSpan.cover marker.span inner.span
          value := .proxy marker.span inner
        }, final, by simp only [parseProxyType, markerResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseProxyType, markerResult, innerResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseProxyType, markerResult]⟩

theorem parseProxyType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseProxyType nested input ≠ .invariant error := by
  intro failed
  rcases parseProxyType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseComptimeType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseComptimeType nested input = .ok value next) ∨
    (∃ failure next, parseComptimeType nested input = .reject failure next) := by
  rcases contextual_ordinary .comptime .typeExpr input with
    ⟨marker, afterMarker, markerResult⟩ | ⟨failure, rejected, markerResult⟩
  · have afterMarkerAdequate : afterMarker.remainingCount < elementFuel :=
      contextual_remainingCount_lt_of_success .comptime .typeExpr markerResult adequate
    rcases symbol_ordinary .less .typeExpr afterMarker with
      ⟨opening, afterOpening, openingResult⟩ | ⟨failure, rejected, openingResult⟩
    · have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success .less .typeExpr openingResult
          (Nat.lt_succ_of_lt afterMarkerAdequate)
      rcases contract.ordinary afterOpening afterOpeningAdequate with
        ⟨inner, afterInner, innerResult⟩ | ⟨failure, rejected, innerResult⟩
      · rcases symbol_ordinary .greater .typeExpr afterInner with
          ⟨closing, final, closingResult⟩ | ⟨failure, rejected, closingResult⟩
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
          simp only [parseComptimeType, bind, markerResult, openingResult, innerResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseComptimeType, bind, markerResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseComptimeType, bind, markerResult]⟩

theorem parseComptimeType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseComptimeType nested input ≠ .invariant error := by
  intro failed
  rcases parseComptimeType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

theorem parseMappingType_ordinary_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1) :
    (∃ value next, parseMappingType nested input = .ok value next) ∨
    (∃ failure next, parseMappingType nested input = .reject failure next) := by
  rcases contextual_ordinary .mapping .typeExpr input with
    ⟨mapping, afterMapping, mappingResult⟩ | ⟨failure, rejected, mappingResult⟩
  · have afterMappingAdequate : afterMapping.remainingCount < elementFuel :=
      contextual_remainingCount_lt_of_success .mapping .typeExpr mappingResult adequate
    rcases symbol_ordinary .leftParen .typeExpr afterMapping with
      ⟨opening, afterOpening, openingResult⟩ | ⟨failure, rejected, openingResult⟩
    · have afterOpeningAdequate : afterOpening.remainingCount < elementFuel :=
        symbol_remainingCount_lt_of_success .leftParen .typeExpr openingResult
          (Nat.lt_succ_of_lt afterMappingAdequate)
      rcases contract.ordinary afterOpening afterOpeningAdequate with
        ⟨key, afterKey, keyResult⟩ | ⟨failure, rejected, keyResult⟩
      · have afterKeyAdequate : afterKey.remainingCount < elementFuel :=
          contract.remainingCount_lt_of_success keyResult afterOpeningAdequate
        rcases symbol_ordinary .fatArrow .typeExpr afterKey with
          ⟨arrow, afterArrow, arrowResult⟩ | ⟨failure, rejected, arrowResult⟩
        · have afterArrowAdequate : afterArrow.remainingCount < elementFuel :=
            symbol_remainingCount_lt_of_success .fatArrow .typeExpr arrowResult
              (Nat.lt_succ_of_lt afterKeyAdequate)
          rcases contract.ordinary afterArrow afterArrowAdequate with
            ⟨mapped, afterValue, valueResult⟩ | ⟨failure, rejected, valueResult⟩
          · rcases symbol_ordinary .rightParen .typeExpr afterValue with
              ⟨closing, final, closingResult⟩ | ⟨failure, rejected, closingResult⟩
            · exact Or.inl ⟨{
                  span := SourceSpan.cover mapping.span closing.span
                  value := .mapping mapping.span
                    (SourceSpan.cover opening.span closing.span) key mapped
                }, final, by
                simp only [parseMappingType, bind, mappingResult, openingResult,
                  keyResult, arrowResult, valueResult, closingResult, pure]⟩
            · exact Or.inr ⟨failure, rejected, by
                simp only [parseMappingType, bind, mappingResult, openingResult,
                  keyResult, arrowResult, valueResult, closingResult]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [parseMappingType, bind, mappingResult, openingResult,
                keyResult, arrowResult, valueResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [parseMappingType, bind, mappingResult, openingResult, keyResult, arrowResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseMappingType, bind, mappingResult, openingResult, keyResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseMappingType, bind, mappingResult, openingResult]⟩
  · exact Or.inr ⟨failure, rejected, by simp only [parseMappingType, bind, mappingResult]⟩

theorem parseMappingType_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser TypeExpr) (elementFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested elementFuel)
    (input : State) (adequate : input.remainingCount < elementFuel + 1)
    (error : ParserInvariantError) :
    parseMappingType nested input ≠ .invariant error := by
  intro failed
  rcases parseMappingType_ordinary_of_unrestrictedElementFuel nested elementFuel contract
      input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
