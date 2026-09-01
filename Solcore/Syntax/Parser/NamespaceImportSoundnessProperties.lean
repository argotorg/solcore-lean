import Solcore.Syntax.Parser.PlainImportSoundnessProperties

/-! Success soundness of diagnostic-free canonical namespace imports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/--
Diagnostic-free namespace-helper success follows the exact token grammar.
The premise excludes both a recovered missing semicolon and any diagnostic
emitted while checking the namespace alias or module-path identifiers.
-/
theorem namespaceImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    DeclarativeGrammar.NamespaceImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.namespaceImport at result
  rcases importBind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  have starSound := symbol_ok_tokenAt .star .importDecl starResult
  rcases importBind_success_components rest with
    ⟨asToken, afterAs, asResult, rest⟩
  have asSound := keyword_ok_tokenAt .asKw .importDecl asResult
  rcases importBind_success_components rest with
    ⟨alias, afterAlias, aliasResult, rest⟩
  have aliasSound := identifier_ok_tokenAt .importDecl aliasResult
  rcases importBind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  have fromSound := contextual_ok_tokenAt .from .importDecl fromResult
  rcases importBind_success_components rest with
    ⟨path, afterPath, pathResult, finishResult⟩
  have pathSound := modulePath_success_sound .importDecl pathResult
  unfold ImportInternals.finish at finishResult
  rcases importBind_success_components finishResult with
    ⟨endSpan, afterEnd, endResult, finished⟩
  cases finished
  rcases importTerminator_success_sound_of_diagnosticFree path.span
      diagnosticFree endResult with
    ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
  unfold DeclarativeGrammar.NamespaceImportTailParses
  refine ⟨star.span, asToken.span, alias, fromToken.span, path,
    afterPath.declarativeRemainder, semicolon.span, starSound.1,
    ?_, ?_, ?_, ?_, semicolonToken, ?_, ?_⟩
  · simpa [State.declarativeRemainder, starSound.2]
      using asSound.1
  · simpa [State.declarativeRemainder, asSound.2, starSound.2,
      Nat.add_assoc] using aliasSound.1
  · simpa [State.declarativeRemainder, aliasSound.2.1, aliasSound.2.2.1,
      aliasSound.2.2.2, asSound.2, starSound.2, State.tokens,
      State.window, State.cursor, Nat.add_assoc] using fromSound.1
  · simpa only [fromSound.2, aliasSound.2.1, aliasSound.2.2.1,
      aliasSound.2.2.2, asSound.2, starSound.2,
      State.declarativeRemainder, State.tokens, State.window, State.cursor,
      Nat.add_assoc] using pathSound
  · rw [afterEndEq]
    rfl
  · rw [endSpanEq]

/--
An AST-namespace import with no accumulated parse diagnostics follows the
complete namespace-import grammar.  Constructor guards, rather than dispatcher
lookahead facts, keep this API stable as import dispatch evolves.
-/
theorem importDecl_namespace_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.NamespaceImportDeclParses input.declarativeRemainder
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
    · have tailGrammar := namespaceImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.NamespaceImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar
    · rcases wildcardImport_success_value importKeyword.span branchResult with
        ⟨path, hidden, valueEq⟩
      rcases namespaceShape with ⟨namespacePath, alias, namespaceEq⟩
      rw [valueEq] at namespaceEq
      contradiction
  · split at branchResult
    · rcases selectiveImport_success_value importKeyword.span branchResult with
        ⟨selection, path, hidden, valueEq⟩
      rcases namespaceShape with ⟨namespacePath, alias, namespaceEq⟩
      rw [valueEq] at namespaceEq
      contradiction
    · rcases plainImport_success_value importKeyword.span branchResult with
        ⟨path, valueEq⟩
      rcases namespaceShape with ⟨namespacePath, alias, namespaceEq⟩
      rw [valueEq] at namespaceEq
      contradiction

/-- Namespace grammar soundness composes with source-provenance validity. -/
theorem importDecl_namespace_success_sound_and_validFor {input next : State}
    {declaration : ImportDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (namespaceShape :
      ∃ path alias, declaration.value = .namespace path alias)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.NamespaceImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_namespace_success_sound diagnosticFree namespaceShape
    result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
