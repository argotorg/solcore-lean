import Solcore.Syntax.DeclarativeConstructorSelectionOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.ExportConstructorTotalityProperties

/-! Exact executable rejection reflection for constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem markerPresentAt_one_of_guard_eq_true {input : State}
    (present :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      (input.cursor + 1) { span, value := .symbol .star } := by
  have advancedPresent :=
    isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true .star present
  rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl
      advancedPresent with ⟨marker, markerResult⟩
  have parsed := symbol_success_exactTokenParses .star .exportDecl markerResult
  exact ⟨marker.span, by
    simpa only [State.declarativeRemainder, State.tokens, State.window,
      State.cursor] using parsed.1⟩

private theorem markerAbsentAt_one_of_guard_eq_false {input : State}
    (absent :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      (input.cursor + 1) (.symbol .star) := by
  rintro ⟨span, tokenAt⟩
  have found : input.peekOffsetKind? 1 = some (.symbol .star) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [tokenAt.1, ↓reduceIte, tokenAt.2, Option.map_some]
  have present :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true := by
    rw [found]
    rfl
  rw [present] at absent
  contradiction

/-- Every executable constructor-selection rejection records the exact first
failed all-selection token or named-list stage selected by offset lookahead. -/
theorem constructorSelection_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : ExportInternals.constructorSelection input =
      .reject failure rejected) :
    DeclarativeGrammar.ConstructorSelectionRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ExportInternals.constructorSelection getState at result
  simp only [bind] at result
  by_cases allPresent :
      (input.peekOffsetKind? 1 == some (.symbol .star)) = true
  · simp only [allPresent, if_true] at result
    rcases markerPresentAt_one_of_guard_eq_true allPresent with
      ⟨guardMarkerSpan, guardMarkerToken⟩
    cases openingResult : symbol .leftParen .exportDecl input with
    | invariant error => simp [openingResult] at result
    | reject openingFailure openingRejected =>
        have rejectedEq := symbol_reject_state_eq .leftParen .exportDecl
          openingResult
        simp only [openingResult] at result
        cases result
        rw [rejectedEq]
        exact .openingMissing guardMarkerSpan guardMarkerToken
          (symbol_reject_tokenKindAbsentAt .leftParen .exportDecl
            openingResult)
    | ok opening afterOpening =>
        have openingSound := symbol_ok_tokenAt .leftParen .exportDecl
          openingResult
        have openingParsed := symbol_success_exactTokenParses
          .leftParen .exportDecl openingResult
        have markerPresent : isSymbol afterOpening .star = true := by
          rw [openingSound.2]
          exact isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true
            .star allPresent
        rcases symbol_eq_ok_of_isSymbol_eq_true .star .exportDecl
            markerPresent with ⟨marker, markerResult⟩
        have markerParsed := symbol_success_exactTokenParses
          .star .exportDecl markerResult
        simp only [openingResult, markerResult] at result
        cases closingResult : symbol .rightParen .exportDecl
            { afterOpening with cursor := afterOpening.cursor + 1 } with
        | invariant error => simp [closingResult] at result
        | ok closing afterClosing =>
            simp [closingResult, pure] at result
        | reject closingFailure closingRejected =>
            have rejectedEq := symbol_reject_state_eq .rightParen .exportDecl
              closingResult
            simp only [closingResult] at result
            cases result
            rw [rejectedEq]
            exact .closingMissing opening.span marker.span openingParsed
              markerParsed
              (symbol_reject_tokenKindAbsentAt .rightParen .exportDecl
                closingResult)
  · have namedGuard :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false :=
      Bool.eq_false_iff.mpr allPresent
    simp only [namedGuard, Bool.false_eq_true, if_false] at result
    cases namesResult : delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel input with
    | invariant error => simp [namesResult] at result
    | reject namesFailure namesRejected =>
        simp only [namesResult] at result
        cases result
        exact .namedRejected
          (markerAbsentAt_one_of_guard_eq_false namedGuard)
          (delimitedNoTrailing_reject_sound .leftParen .rightParen false
            (identifier .exportDecl) DeclarativeGrammar.IdentifierParses
            DeclarativeGrammar.IdentifierRejects .exportDecl .topLevel
            (identifier_success_sound .exportDecl)
            (identifier_reject_sound .exportDecl) namesResult)
    | ok names afterNames =>
        simp only [namesResult] at result
        rcases
            ExportInternals.requireConstructorNames_ok_of_delimitedNoTrailing_false_ok
              namesResult with
          ⟨constructors, constructorsResult⟩
        simp [constructorsResult, pure] at result

end Solcore.Syntax.Parser
