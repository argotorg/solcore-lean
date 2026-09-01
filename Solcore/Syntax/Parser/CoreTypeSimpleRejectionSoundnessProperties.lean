import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.Type

/-! Exact ordinary-rejection reflection for simple recursive Core-type forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A selected `comptime<...>` branch rejects at its nested type or missing
closing angle token. -/
theorem parseComptimeType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .comptime = true)
    (followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol .less)) = true)
    (result : parseComptimeType nested input = .reject failure rejected) :
    DeclarativeGrammar.ComptimeTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_isContextual_eq_true .comptime .typeExpr
      markerPresent with ⟨marker, markerResult⟩
  have openingPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .less followingPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true .less .typeExpr openingPresent with
    ⟨opening, openingResult⟩
  unfold parseComptimeType at result
  simp only [bind, markerResult, openingResult] at result
  cases innerResult : nested
      { input with cursor := input.cursor + 1 + 1 } with
  | invariant error => simp [innerResult] at result
  | reject innerFailure innerRejected =>
      simp only [innerResult] at result
      cases result
      exact .innerRejected marker.span opening.span
        (contextual_success_exactTokenParses .comptime .typeExpr markerResult)
        (symbol_success_exactTokenParses .less .typeExpr openingResult)
        (nestedRejectSound innerResult)
  | ok inner afterInner =>
      simp only [innerResult] at result
      cases closingResult : symbol .greater .typeExpr afterInner with
      | invariant error => simp [closingResult] at result
      | ok closing afterClosing => simp [closingResult, pure] at result
      | reject closingFailure closingRejected =>
          have rejectedEq := symbol_reject_state_eq .greater .typeExpr
            closingResult
          subst rejectedEq
          simp only [closingResult] at result
          cases result
          exact .closingMissing marker.span opening.span
            (contextual_success_exactTokenParses .comptime .typeExpr
              markerResult)
            (symbol_success_exactTokenParses .less .typeExpr openingResult)
            (nestedSuccessSound innerResult)
            (symbol_reject_tokenKindAbsentAt .greater .typeExpr closingResult)

/-- A selected canonical mapping branch rejects at its key, arrow, value, or
closing parenthesis, in that exact order. -/
theorem parseMappingType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .mapping = true)
    (followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol .leftParen)) = true)
    (result : parseMappingType nested input = .reject failure rejected) :
    DeclarativeGrammar.MappingTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_isContextual_eq_true .mapping .typeExpr
      markerPresent with ⟨marker, markerResult⟩
  have openingPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .leftParen
      followingPresent
  rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr openingPresent
      with ⟨opening, openingResult⟩
  unfold parseMappingType at result
  simp only [bind, markerResult, openingResult] at result
  cases keyResult : nested { input with cursor := input.cursor + 1 + 1 } with
  | invariant error => simp [keyResult] at result
  | reject keyFailure keyRejected =>
      simp only [keyResult] at result
      cases result
      exact .keyRejected marker.span opening.span
        (contextual_success_exactTokenParses .mapping .typeExpr markerResult)
        (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
        (nestedRejectSound keyResult)
  | ok key afterKey =>
      simp only [keyResult] at result
      cases arrowResult : symbol .fatArrow .typeExpr afterKey with
      | invariant error => simp [arrowResult] at result
      | reject arrowFailure arrowRejected =>
          have rejectedEq := symbol_reject_state_eq .fatArrow .typeExpr
            arrowResult
          subst rejectedEq
          simp only [arrowResult] at result
          cases result
          exact .arrowMissing marker.span opening.span
            (contextual_success_exactTokenParses .mapping .typeExpr
              markerResult)
            (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
            (nestedSuccessSound keyResult)
            (symbol_reject_tokenKindAbsentAt .fatArrow .typeExpr arrowResult)
      | ok arrow afterArrow =>
          simp only [arrowResult] at result
          cases valueResult : nested afterArrow with
          | invariant error => simp [valueResult] at result
          | reject valueFailure valueRejected =>
              simp only [valueResult] at result
              cases result
              exact .valueRejected marker.span opening.span arrow.span
                (contextual_success_exactTokenParses .mapping .typeExpr
                  markerResult)
                (symbol_success_exactTokenParses .leftParen .typeExpr
                  openingResult)
                (nestedSuccessSound keyResult)
                (symbol_success_exactTokenParses .fatArrow .typeExpr
                  arrowResult)
                (nestedRejectSound valueResult)
          | ok value afterValue =>
              simp only [valueResult] at result
              cases closingResult : symbol .rightParen .typeExpr afterValue with
              | invariant error => simp [closingResult] at result
              | ok closing afterClosing => simp [closingResult, pure] at result
              | reject closingFailure closingRejected =>
                  have rejectedEq := symbol_reject_state_eq .rightParen
                    .typeExpr closingResult
                  subst rejectedEq
                  simp only [closingResult] at result
                  cases result
                  exact .closingMissing marker.span opening.span arrow.span
                    (contextual_success_exactTokenParses .mapping .typeExpr
                      markerResult)
                    (symbol_success_exactTokenParses .leftParen .typeExpr
                      openingResult)
                    (nestedSuccessSound keyResult)
                    (symbol_success_exactTokenParses .fatArrow .typeExpr
                      arrowResult)
                    (nestedSuccessSound valueResult)
                    (symbol_reject_tokenKindAbsentAt .rightParen .typeExpr
                      closingResult)

/-- A selected proxy type propagates exactly its nested rejection. -/
theorem parseProxyType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isSymbol input .at = true)
    (result : parseProxyType nested input = .reject failure rejected) :
    DeclarativeGrammar.ProxyTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .at .typeExpr markerPresent with
    ⟨marker, markerResult⟩
  unfold parseProxyType at result
  simp only [markerResult] at result
  cases innerResult : nested { input with cursor := input.cursor + 1 } with
  | invariant error => simp [innerResult] at result
  | ok inner afterInner => simp [innerResult] at result
  | reject innerFailure innerRejected =>
      simp only [innerResult] at result
      cases result
      exact .innerRejected marker.span
        (symbol_success_exactTokenParses .at .typeExpr markerResult)
        (nestedRejectSound innerResult)

/-- Tuple rejection is exactly generic allow-empty trailing-list rejection. -/
theorem parseTupleType_reject_type_sound
    (nested : Parser TypeExpr)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input next : State} {value : TypeExpr},
      nested input = .ok value next →
        DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
          next.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected →
        nestedRejects input.declarativeRemainder
          rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (openingPresent : isSymbol input .leftParen = true)
    (result : parseTupleType nested input = .reject failure rejected) :
    DeclarativeGrammar.TupleTypeRejects nestedRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseTupleType at result
  cases valuesResult : delimited .leftParen .rightParen true nested
      .typeExpr .typeExpr input with
  | invariant error => simp [bind, valuesResult] at result
  | ok values afterValues => simp [bind, valuesResult, pure] at result
  | reject valuesFailure valuesRejected =>
      simp only [bind, valuesResult] at result
      cases result
      rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeExpr
          openingPresent with ⟨opening, openingResult⟩
      exact .selected opening.span
        (symbol_success_exactTokenParses .leftParen .typeExpr openingResult)
        (delimited_reject_sound .leftParen .rightParen true nested
          DeclarativeGrammar.TypeExprParses nestedRejects .typeExpr .typeExpr
          nestedSuccessSound nestedRejectSound valuesResult)

end Solcore.Syntax.Parser
