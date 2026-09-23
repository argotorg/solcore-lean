import Solcore.Syntax.Parser.Import
import Solcore.Syntax.Parser.ImportProperties
import Solcore.Syntax.Parser.ModulePath

/-! Success soundness of diagnostic-free canonical plain imports. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful monadic import stage exposes both successful component replies. -/
theorem importBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
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

/--
A successful import terminator with no accumulated parse diagnostics consumed
an exact semicolon.  This common boundary excludes the missing-semicolon
recovery, because that branch always prepends `trailingSemicolonRequired` to
the output diagnostic accumulator.
-/
theorem importTerminator_success_sound_of_diagnosticFree
    (lastSpan : SourceSpan) {input next : State} {endSpan : SourceSpan}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.terminator lastSpan input = .ok endSpan next) :
    ∃ semicolon : Token,
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        input.cursor {
          span := semicolon.span
          value := .symbol .semicolon
        } ∧
      next = { input with cursor := input.cursor + 1 } ∧
      endSpan = semicolon.span := by
  unfold ImportInternals.terminator at result
  split at result
  · cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok semicolon afterSemicolon =>
        have sound := symbol_ok_tokenAt .semicolon .importDecl semicolonResult
        simp only [semicolonResult] at result
        cases result
        exact ⟨semicolon, sound.1, sound.2, rfl⟩
  · split at result
    · cases result
      simp [State.emit] at diagnosticFree
    · unfold rejectAt at result
      contradiction

/--
Diagnostic-free helper success consumes a module path and an exact semicolon.
The premise excludes the missing-semicolon recovery accepted by `plainImport`.
-/
theorem plainImport_success_sound_of_diagnosticFree
    (start : SourceSpan) {input next : State} {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    DeclarativeGrammar.PlainImportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ImportInternals.plainImport at result
  rcases importBind_success_components result with
    ⟨path, afterPath, pathResult, finishResult⟩
  have pathSound := modulePath_success_sound .importDecl pathResult
  unfold ImportInternals.finish at finishResult
  rcases importBind_success_components finishResult with
    ⟨endSpan, afterEnd, endResult, finished⟩
  cases finished
  rcases importTerminator_success_sound_of_diagnosticFree path.span
      diagnosticFree endResult with
    ⟨semicolon, semicolonToken, afterEndEq, endSpanEq⟩
  unfold DeclarativeGrammar.PlainImportTailParses
  refine ⟨path, afterPath.declarativeRemainder, semicolon.span, pathSound,
    semicolonToken, ?_, ?_⟩
  · rw [afterEndEq]
    rfl
  · rw [endSpanEq]

/-- Successful import finishing retains its supplied payload constructor. -/
theorem finishImport_success_value (start last : SourceSpan)
    (value : ImportDeclValue) {input next : State}
    {declaration : ImportDecl}
    (result : ImportInternals.finish start last value input =
      .ok declaration next) :
    declaration.value = value := by
  unfold ImportInternals.finish at result
  rcases importBind_success_components result with
    ⟨endSpan, afterEnd, _endResult, finished⟩
  cases finished
  rfl

/-- Plain-helper success produces exactly the plain payload constructor. -/
theorem plainImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.plainImport start input =
      .ok declaration next) :
    ∃ path, declaration.value = .plain path := by
  unfold ImportInternals.plainImport at result
  rcases importBind_success_components result with
    ⟨path, afterPath, _pathResult, finished⟩
  exact ⟨path,
    finishImport_success_value start path.span (.plain path) finished⟩

/-- Namespace-helper success produces exactly the namespace payload constructor. -/
theorem namespaceImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.namespaceImport start input =
      .ok declaration next) :
    ∃ path alias, declaration.value = .namespace path alias := by
  unfold ImportInternals.namespaceImport at result
  rcases importBind_success_components result with
    ⟨_star, afterStar, _, rest⟩
  rcases importBind_success_components rest with ⟨_as, afterAs, _, rest⟩
  rcases importBind_success_components rest with
    ⟨alias, afterAlias, _, rest⟩
  rcases importBind_success_components rest with
    ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with
    ⟨path, afterPath, _, finished⟩
  exact ⟨path, alias,
    finishImport_success_value start path.span (.namespace path alias) finished⟩

/-- Wildcard-helper success produces exactly the wildcard payload constructor. -/
theorem wildcardImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration next) :
    ∃ path hidden, declaration.value = .wildcard path hidden := by
  unfold ImportInternals.wildcardImport at result
  rcases importBind_success_components result with
    ⟨_star, afterStar, _, rest⟩
  rcases importBind_success_components rest with ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with ⟨path, afterPath, _, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, _, finished⟩
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.wildcard path none) afterHidden = .ok declaration next := by
        simpa using finished
      exact ⟨path, none,
        finishImport_success_value start path.span (.wildcard path none)
          finishedNone⟩
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.wildcard path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨path, some clause,
        finishImport_success_value start clause.span
          (.wildcard path (some clause)) finishedSome⟩

/-- Selective-helper success produces exactly the selected payload constructor. -/
theorem selectiveImport_success_value (start : SourceSpan)
    {input next : State} {declaration : ImportDecl}
    (result : ImportInternals.selectiveImport start input =
      .ok declaration next) :
    ∃ selection path hidden,
      declaration.value = .selected selection path hidden := by
  unfold ImportInternals.selectiveImport at result
  rcases importBind_success_components result with
    ⟨selection, afterSelection, _, rest⟩
  rcases importBind_success_components rest with ⟨_from, afterFrom, _, rest⟩
  rcases importBind_success_components rest with ⟨path, afterPath, _, rest⟩
  rcases importBind_success_components rest with
    ⟨hidden, afterHidden, _, finished⟩
  cases hidden with
  | none =>
      have finishedNone : ImportInternals.finish start path.span
          (.selected selection path none) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨selection, path, none,
        finishImport_success_value start path.span
          (.selected selection path none) finishedNone⟩
  | some clause =>
      have finishedSome : ImportInternals.finish start clause.span
          (.selected selection path (some clause)) afterHidden =
            .ok declaration next := by
        simpa using finished
      exact ⟨selection, path, some clause,
        finishImport_success_value start clause.span
          (.selected selection path (some clause)) finishedSome⟩

/--
An AST-plain import success with no accumulated parse diagnostics follows the
exact plain-import grammar.  Requiring an empty output diagnostic accumulator
rules out the parser's accepted missing-semicolon recovery, which always emits
`trailingSemicolonRequired`; the AST-shape premise makes this theorem stable
under changes to the dispatcher's token lookahead implementation.
-/
theorem importDecl_plain_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.PlainImportDeclParses input.declarativeRemainder
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
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
    · rcases wildcardImport_success_value importKeyword.span branchResult with
        ⟨path, hidden, valueEq⟩
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
  · split at branchResult
    · rcases selectiveImport_success_value importKeyword.span branchResult with
        ⟨selection, path, hidden, valueEq⟩
      rcases plainShape with ⟨plainPath, plainEq⟩
      rw [valueEq] at plainEq
      contradiction
    · have tailGrammar := plainImport_success_sound_of_diagnosticFree
        importKeyword.span diagnosticFree branchResult
      unfold DeclarativeGrammar.PlainImportDeclParses
      refine ⟨importKeyword.span, keywordSound.1, ?_⟩
      simpa only [keywordSound.2, State.declarativeRemainder,
        State.tokens, State.window, State.cursor] using tailGrammar

/-- Plain grammar soundness composes with source-provenance validity. -/
theorem importDecl_plain_success_sound_and_validFor {input next : State}
    {declaration : ImportDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (plainShape : ∃ path, declaration.value = .plain path)
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.PlainImportDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_plain_success_sound diagnosticFree plainShape result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
