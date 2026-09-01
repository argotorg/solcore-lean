import Solcore.Syntax.Parser.DelimitedNoTrailingAllowEmptySoundnessProperties
import Solcore.Syntax.Parser.DeriveRecoveryDiagnosticProperties
import Solcore.Syntax.Parser.DeriveTargetSoundnessProperties
import Solcore.Syntax.Parser.DeriveValidityProperties

/-! Success soundness of normal and public derive-attribute parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem deriveBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every success of the normal derive path follows its exact token grammar. -/
theorem deriveAttributeValid_success_sound {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold DeriveAttributeInternals.valid at result
  rcases deriveBind_success_components result with
    ⟨hash, afterHash, hashResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨deriveMarker, afterDerive, deriveResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨targets, afterTargets, targetsResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  have finalShape :
      next.declarativeRemainder = afterClosing.declarativeRemainder ∧
        value = {
          span := SourceSpan.cover hash.span closing.span
          value := { targets }
        } := by
    by_cases empty : targets.elements.isEmpty
    · simp only [empty, if_true, emitDiagnostic, modifyState, bind, pure] at rest
      cases rest
      exact ⟨rfl, rfl⟩
    · simp only [empty, pure] at rest
      cases rest
      exact ⟨rfl, rfl⟩
  have hashSound := symbol_ok_tokenAt .hash .topItem hashResult
  have openingSound := symbol_ok_tokenAt .leftBracket .topItem openingResult
  have deriveSound := contextual_ok_tokenAt .derive .topItem deriveResult
  have targetsSound := delimitedNoTrailing_allowEmpty_success_sound
    .leftParen .rightParen deriveTarget
    DeclarativeGrammar.DeriveTargetParses .topItem .topLevel
    deriveTarget_success_sound deriveTarget_preservesTokenWindow targetsResult
  have closingSound := symbol_ok_tokenAt .rightBracket .topItem closingResult
  have openingToken :
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        (input.cursor + 1) {
          span := opening.span
          value := .symbol .leftBracket
        } := by
    simpa only [hashSound.2, State.tokens, State.window, State.cursor] using
      openingSound.1
  have deriveToken :
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        (input.cursor + 2) {
          span := deriveMarker.span
          value := .identifier ContextualKeyword.derive.spelling
        } := by
    simpa only [openingSound.2, hashSound.2, State.tokens, State.window,
      State.cursor, Nat.add_assoc] using deriveSound.1
  have targetsGrammar :
      DeclarativeGrammar.NoTrailingDelimitedListParses .leftParen .rightParen
        DeclarativeGrammar.DeriveTargetParses {
          input.declarativeRemainder with cursor := input.cursor + 3
        } targets afterTargets.declarativeRemainder := by
    simpa only [deriveSound.2, openingSound.2, hashSound.2,
      State.declarativeRemainder, State.tokens, State.window, State.cursor,
      Nat.add_assoc] using targetsSound
  have outputEq : next.declarativeRemainder = {
      afterTargets.declarativeRemainder with
        cursor := afterTargets.cursor + 1
    } := by
    rw [finalShape.1, closingSound.2]
    rfl
  unfold DeclarativeGrammar.DeriveAttributeParses
  exact ⟨hash.span, opening.span, deriveMarker.span, targets,
    afterTargets.declarativeRemainder, closing.span, hashSound.1, openingToken,
    deriveToken, targetsGrammar, closingSound.1, outputEq, finalShape.2⟩

/-- Diagnostic-free public derive success cannot come from recovery. -/
theorem deriveAttribute_success_sound {input next : State}
    {value : DeriveAttribute} (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | ok parsed afterValid =>
      simp only [validResult] at result
      cases result
      exact deriveAttributeValid_success_sound validResult
  | reject failure rejected =>
      simp only [validResult] at result
      exact False.elim
        ((deriveRecovered_success_hasDiagnostic result) diagnosticFree)
  | invariant error => simp [validResult] at result

/-- Public derive grammar soundness composes with source validity. -/
theorem deriveAttribute_success_sound_and_validFor {input next : State}
    {value : DeriveAttribute} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file := by
  refine ⟨deriveAttribute_success_sound diagnosticFree result, ?_⟩
  have valid := deriveAttribute_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
