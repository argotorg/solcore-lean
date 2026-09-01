import Solcore.Syntax.Parser.HidingClauseSoundnessProperties

/-! Success soundness of wildcard imports with optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Diagnostic-free wildcard-helper success follows the complete grammar. -/
theorem wildcardImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    DeclarativeGrammar.WildcardImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  rcases importBind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  rcases importBind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases importBind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, hiddenResult, finishResult⟩
  have starSound := symbol_ok_tokenAt .star .importDecl starResult
  have fromSound := contextual_ok_tokenAt .from .importDecl fromResult
  have pathSound := modulePath_success_sound .importDecl pathResult
  have hiddenSound := optionalHiding_success_sound hiddenResult
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.wildcard path none) afterHidden = .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedNone
      rcases importBind_success_components finishedNone with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree path.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.WildcardImportTailParses
      refine ⟨star.span, fromToken.span, path,
        afterPath.declarativeRemainder, none,
        afterHidden.declarativeRemainder, semicolon.span, starSound.1,
        ?_, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [starSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using fromSound.1
      · simpa only [fromSound.2, starSound.2,
          State.declarativeRemainder, State.tokens, State.window,
          State.cursor, Nat.add_assoc] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.wildcard path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finishResult
      unfold ImportInternals.finish at finishedSome
      rcases importBind_success_components finishedSome with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree clause.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.WildcardImportTailParses
      refine ⟨star.span, fromToken.span, path,
        afterPath.declarativeRemainder, some clause,
        afterHidden.declarativeRemainder, semicolon.span, starSound.1,
        ?_, ?_, hiddenSound, semicolonToken, ?_, ?_⟩
      · simpa only [starSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using fromSound.1
      · simpa only [fromSound.2, starSound.2,
          State.declarativeRemainder, State.tokens, State.window,
          State.cursor, Nat.add_assoc] using pathSound
      · rw [afterEndEq]
        rfl
      · rw [endSpanEq]

/-- A wildcard-shaped import result follows the complete wildcard grammar. -/
theorem importDecl_wildcard_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (wildcardShape : ∃ path hidden,
      declaration.value = .wildcard path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportDeclParses input.declarativeRemainder
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
      rcases wildcardShape with ⟨wildcardPath, hidden, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction
    · have tailGrammar := wildcardImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.WildcardImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar
  · split at branchResult
    · rcases selectiveImport_success_value importKeyword.span branchResult with
        ⟨selection, path, hidden, valueEq⟩
      rcases wildcardShape with ⟨wildcardPath, wildcardHidden, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction
    · rcases plainImport_success_value importKeyword.span branchResult with
        ⟨path, valueEq⟩
      rcases wildcardShape with ⟨wildcardPath, hidden, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction

/-- A wildcard import with a present hiding clause uses the general grammar. -/
theorem importDecl_wildcardWithHiding_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (withHidingShape : ∃ path clause,
      declaration.value = .wildcard path (some clause))
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  apply importDecl_wildcard_success_sound diagnosticFree _ result
  rcases withHidingShape with ⟨path, clause, shape⟩
  exact ⟨path, some clause, shape⟩

/-- Wildcard grammar soundness composes with source-provenance validity. -/
theorem importDecl_wildcard_success_sound_and_validFor
    {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (wildcardShape : ∃ path hidden,
      declaration.value = .wildcard path hidden)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_wildcard_success_sound diagnosticFree wildcardShape
    result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

/-- Present-hiding wildcard soundness also retains source provenance. -/
theorem importDecl_wildcardWithHiding_success_sound_and_validFor
    {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (withHidingShape : ∃ path clause,
      declaration.value = .wildcard path (some clause))
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  apply importDecl_wildcard_success_sound_and_validFor inputValid
    diagnosticFree _ result
  rcases withHidingShape with ⟨path, clause, shape⟩
  exact ⟨path, some clause, shape⟩

end Solcore.Syntax.Parser
