import Solcore.Syntax.Parser.HidingClauseSoundnessProperties
import Solcore.Syntax.Parser.SelectedImportsSoundnessProperties

/-! Success soundness of selected imports with optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Diagnostic-free selected-import helper success follows the complete grammar. -/
theorem selectiveImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    DeclarativeGrammar.SelectiveImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.selectiveImport at result
  rcases importBind_success_components result with
    ⟨selection, afterSelection, selectionResult, rest⟩
  rcases importBind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases importBind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, hiddenResult, finishResult⟩
  have selectionSound := selectedImports_success_sound selectionResult
  have fromSound := contextual_ok_tokenAt .from .importDecl fromResult
  have pathSound := modulePath_success_sound .importDecl pathResult
  have hiddenSound := optionalHiding_success_sound hiddenResult
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.selected selection path none) afterHidden =
            .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedNone
      rcases importBind_success_components finishedNone with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree path.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.SelectiveImportTailParses
      refine ⟨selection, afterSelection.declarativeRemainder,
        fromToken.span, path, afterPath.declarativeRemainder, none,
        afterHidden.declarativeRemainder, semicolon.span, selectionSound,
        fromSound.1, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [fromSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.selected selection path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedSome
      rcases importBind_success_components finishedSome with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree clause.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.SelectiveImportTailParses
      refine ⟨selection, afterSelection.declarativeRemainder,
        fromToken.span, path, afterPath.declarativeRemainder, some clause,
        afterHidden.declarativeRemainder, semicolon.span, selectionSound,
        fromSound.1, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [fromSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]

/-- A selected-shaped import result follows the complete selected grammar. -/
theorem importDecl_selected_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (selectedShape : ∃ selection path hidden,
      declaration.value = .selected selection path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.SelectiveImportDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  unfold importDecl at result
  rcases importBind_success_components result with
    ⟨importKeyword, afterKeyword, keywordResult, rest⟩
  have keywordSound := keyword_ok_tokenAt .importKw .importDecl keywordResult
  rcases importBind_success_components rest with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · split at branchResult
    · rcases namespaceImport_success_value importKeyword.span branchResult with
        ⟨path, alias, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, hidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction
    · rcases wildcardImport_success_value importKeyword.span branchResult with
        ⟨path, hidden, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, selectedHidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction
  · split at branchResult
    · have tailGrammar := selectiveImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.SelectiveImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar
    · rcases plainImport_success_value importKeyword.span branchResult with
        ⟨path, valueEq⟩
      rcases selectedShape with
        ⟨selection, selectedPath, hidden, selectedEq⟩
      rw [valueEq] at selectedEq
      contradiction

/-- Selected-import grammar soundness composes with source provenance. -/
theorem importDecl_selected_success_sound_and_validFor
    {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (selectedShape : ∃ selection path hidden,
      declaration.value = .selected selection path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.SelectiveImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_selected_success_sound diagnosticFree selectedShape
    result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
