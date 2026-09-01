import Solcore.Syntax.Parser.NamespaceImportSoundnessProperties

/-! Success soundness of diagnostic-free wildcard imports without hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful absence of a hiding clause leaves the parser state unchanged. -/
theorem optionalHiding_none_success_state {input next : State}
    (result : ImportInternals.optionalHiding input = .ok none next) :
    next = input := by
  unfold ImportInternals.optionalHiding at result
  simp only [getState, bind] at result
  split at result
  · cases hiddenResult : ImportInternals.hidingClause input <;>
      simp [hiddenResult, pure] at result
  · simp only [pure] at result
    cases result
    rfl

/--
Diagnostic-free wildcard-helper success with a no-hiding AST follows the exact
`* from ModulePath ;` grammar.  The AST guard excludes a parsed hiding clause;
the diagnostic premise excludes missing-semicolon recovery.
-/
theorem wildcardImport_noHiding_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    DeclarativeGrammar.WildcardImportNoHidingTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  rcases importBind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  have starSound := symbol_ok_tokenAt .star .importDecl starResult
  rcases importBind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  have fromSound := contextual_ok_tokenAt .from .importDecl fromResult
  rcases importBind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  have pathSound := modulePath_success_sound .importDecl pathResult
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, hiddenResult, finishResult⟩
  cases hidden with
  | none =>
      have afterHiddenEq := optionalHiding_none_success_state hiddenResult
      have finishedNone : ImportInternals.finish start path.span
          (.wildcard path none) afterHidden = .ok declaration next := by
        simpa using finishResult
      rw [afterHiddenEq] at finishedNone
      unfold ImportInternals.finish at finishedNone
      rcases importBind_success_components finishedNone with
        ⟨endSpan, afterEnd, endResult, finished⟩
      cases finished
      rcases importTerminator_success_sound_of_diagnosticFree path.span
          diagnosticFree endResult with
        ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
      unfold DeclarativeGrammar.WildcardImportNoHidingTailParses
      refine ⟨star.span, fromToken.span, path,
        afterPath.declarativeRemainder, semicolon.span, starSound.1,
        ?_, ?_, semicolonToken, ?_, ?_⟩
      · simpa [State.declarativeRemainder, starSound.2]
          using fromSound.1
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
      have valueEq := finishImport_success_value start clause.span
        (.wildcard path (some clause)) finishedSome
      rcases noHidingShape with ⟨expectedPath, expectedEq⟩
      rw [valueEq] at expectedEq
      cases expectedEq

/--
An AST-wildcard import without hiding and without diagnostics follows the
complete exact grammar, independently of dispatcher lookahead details.
-/
theorem importDecl_wildcardNoHiding_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportNoHidingDeclParses
      input.declarativeRemainder declaration next.declarativeRemainder := by
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
      rcases noHidingShape with ⟨wildcardPath, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction
    · have tailGrammar :=
        wildcardImport_noHiding_success_sound_of_diagnosticFree
          importKeyword.span diagnosticFree noHidingShape branchResult
      unfold DeclarativeGrammar.WildcardImportNoHidingDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar
  · split at branchResult
    · rcases selectiveImport_success_value importKeyword.span branchResult with
        ⟨selection, path, hidden, valueEq⟩
      rcases noHidingShape with ⟨wildcardPath, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction
    · rcases plainImport_success_value importKeyword.span branchResult with
        ⟨path, valueEq⟩
      rcases noHidingShape with ⟨wildcardPath, wildcardEq⟩
      rw [valueEq] at wildcardEq
      contradiction

/-- Wildcard no-hiding grammar soundness composes with provenance validity. -/
theorem importDecl_wildcardNoHiding_success_sound_and_validFor
    {input next : State} {declaration : ImportDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (noHidingShape :
      ∃ path, declaration.value = .wildcard path none)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.WildcardImportNoHidingDeclParses
        input.declarativeRemainder declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_wildcardNoHiding_success_sound diagnosticFree
    noHidingShape result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
