import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.ImportProofs
import Solcore.Syntax.Parser.Internal.ExportProofs
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.State

/-!
Soundness of the parsers of import declarations: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.SelectiveImportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for selective-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · rcases contextual_eq_ok_of_isContextual_eq_true value context present
      with ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

private theorem finish_reject_ordinaryOutcome_sound
    (start last : SourceSpan) (value : ImportDeclValue)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.finish start last value input =
      .reject failure rejected) :
    DeclarativeGrammar.ImportTerminatorRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.finish at result
  cases terminatorResult : ImportInternals.terminator last input with
  | invariant error => simp [bind, terminatorResult] at result
  | ok endSpan output => simp [bind, terminatorResult, pure] at result
  | reject terminatorFailure terminatorRejected =>
      simp only [bind, terminatorResult] at result
      cases result
      exact importTerminator_reject_ordinaryOutcome_sound last
        terminatorResult

/-- Every executable selective-import rejection records its exact first
rejecting stage among selection, `from`, path, optional hiding, and
terminator. -/
theorem selectiveImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.selectiveImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.SelectiveImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.selectiveImport at result
  cases selectionResult : ImportInternals.selectedImports input with
  | invariant error => simp [bind, selectionResult] at result
  | reject selectionFailure selectionRejected =>
      simp only [bind, selectionResult] at result
      cases result
      exact .selectionRejected
        (selectedImports_reject_ordinaryOutcome_sound selectionResult)
  | ok selection afterSelection =>
      simp only [bind, selectionResult] at result
      have selectionParsed :=
        selectedImports_success_ordinaryOutcome_sound selectionResult
      cases fromResult : contextual .from .importDecl afterSelection with
      | invariant error => simp [fromResult] at result
      | reject fromFailure fromRejected =>
          have fromRejectedEq := contextual_reject_state_eq .from .importDecl
            fromResult
          subst fromRejected
          simp only [fromResult] at result
          cases result
          exact .fromMissing selectionParsed
            (contextual_reject_tokenKindAbsentAt .from .importDecl fromResult)
      | ok fromToken afterFrom =>
          simp only [fromResult] at result
          have fromParsed := contextual_success_exactTokenParses .from
            .importDecl fromResult
          cases pathResult : modulePath .importDecl afterFrom with
          | invariant error => simp [pathResult] at result
          | reject pathFailure pathRejected =>
              simp only [pathResult] at result
              cases result
              exact .pathRejected fromToken.span selectionParsed fromParsed
                (modulePath_reject_ordinaryOutcome_sound .importDecl
                  pathResult)
          | ok path afterPath =>
              simp only [pathResult] at result
              have pathParsed := modulePath_success_ordinaryOutcome_sound
                .importDecl pathResult
              cases hidingResult : ImportInternals.optionalHiding afterPath with
              | invariant error => simp [hidingResult] at result
              | reject hidingFailure hidingRejected =>
                  simp only [hidingResult] at result
                  cases result
                  exact .hidingRejected fromToken.span selectionParsed
                    fromParsed pathParsed
                    (optionalHiding_reject_ordinaryOutcome_sound hidingResult)
              | ok hidden afterHiding =>
                  simp only [hidingResult] at result
                  have hidingParsed :=
                    optionalHiding_success_ordinaryOutcome_sound hidingResult
                  cases hidden with
                  | none =>
                      exact .terminatorRejected fromToken.span selectionParsed
                        fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start path.span
                          (.selected selection path none) result)
                  | some clause =>
                      exact .terminatorRejected fromToken.span selectionParsed
                        fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start clause.span
                          (.selected selection path (some clause)) result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectiveImportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for selective import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selective-import success and exact stagewise rejection. -/
theorem selectiveImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.selectiveImport start input = .ok declaration output →
        DeclarativeGrammar.SelectiveImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.selectiveImport start input = .reject failure rejected →
        DeclarativeGrammar.SelectiveImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectiveImport_success_ordinaryOutcome_sound start,
    selectiveImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive selective-import outcomes. -/
theorem selectiveImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.SelectiveImportOrdinaryParses start)
      DeclarativeGrammar.SelectiveImportRejects :=
  DeclarativeGrammar.selectiveImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WildcardImportOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for wildcard import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_success_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable wildcard-import success preserves its fixed prefix,
module path, optional hiding, explicit-or-recovered terminator, AST, span, and
final remainder. -/
theorem wildcardImport_success_ordinaryOutcome_sound (start : SourceSpan)
    {input output : State} {declaration : ImportDecl}
    (result : ImportInternals.wildcardImport start input =
      .ok declaration output) :
    DeclarativeGrammar.WildcardImportOrdinaryParses start
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  rcases bind_success_components result with
    ⟨star, afterStar, starResult, rest⟩
  rcases bind_success_components rest with
    ⟨fromToken, afterFrom, fromResult, rest⟩
  rcases bind_success_components rest with
    ⟨path, afterPath, pathResult, rest⟩
  rcases bind_success_components rest with
    ⟨hidden, afterHiding, hidingResult, finishResult⟩
  cases hidden with
  | none =>
      have normalized : ImportInternals.finish start path.span
          (.wildcard path none) afterHiding = .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed star.span fromToken.span
        (symbol_success_exactTokenParses .star .importDecl starResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound path.span
          terminatorResult)
  | some clause =>
      have normalized : ImportInternals.finish start clause.span
          (.wildcard path (some clause)) afterHiding =
            .ok declaration output := by
        simpa using finishResult
      unfold ImportInternals.finish at normalized
      rcases bind_success_components normalized with
        ⟨endSpan, afterTerminator, terminatorResult, finished⟩
      cases finished
      exact .parsed star.span fromToken.span
        (symbol_success_exactTokenParses .star .importDecl starResult)
        (contextual_success_exactTokenParses .from .importDecl fromResult)
        (modulePath_success_ordinaryOutcome_sound .importDecl pathResult)
        (optionalHiding_success_ordinaryOutcome_sound hidingResult)
        (importTerminator_success_ordinaryOutcome_sound clause.span
          terminatorResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportDeclarationOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success reflection for complete import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem importDispatchSymbolPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.ImportDispatchTokenPresentAt
      input.declarativeRemainder 0 (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .importDecl present with
    ⟨token, result⟩
  have parsed := symbol_success_exactTokenParses value .importDecl result
  exact ⟨token.span, by simpa using parsed.1⟩

private theorem importDispatchAsPresentAt_of_peekOffsetKind_eq_true
    {input : State}
    (present :
      (input.peekOffsetKind? 1 == some (.keyword .asKw)) = true) :
    DeclarativeGrammar.ImportDispatchTokenPresentAt
      input.declarativeRemainder 1 (.keyword .asKw) := by
  unfold State.peekOffsetKind? at present
  cases found : input.peekOffset? 1 with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, actual⟩
      simp only [found, Option.map_some] at present
      have actualEq : actual = .keyword .asKw := by
        change instBEqTokenKind.beq actual (.keyword .asKw) = true at present
        cases actual <;> simp only [instBEqTokenKind.beq] at present
        all_goals try contradiction
        case keyword actual =>
          change instBEqHardKeyword.beq actual .asKw = true at present
          unfold instBEqHardKeyword.beq at present
          cases actual <;> first | rfl | cases present
      subst actual
      exact ⟨span,
        State.cursor_add_lt_endIndex_of_peekOffset?_eq_some found,
        State.getElem?_eq_some_of_peekOffset?_eq_some found⟩

private theorem asAbsentAt_of_peekOffsetKind_eq_false {input : State}
    (absent :
      (input.peekOffsetKind? 1 == some (.keyword .asKw)) = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      (input.cursor + 1) (.keyword .asKw) := by
  rintro ⟨span, tokenAt⟩
  have found : input.peekOffsetKind? 1 = some (.keyword .asKw) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [tokenAt.1, ↓reduceIte, tokenAt.2, Option.map_some]
  have present :
      (input.peekOffsetKind? 1 == some (.keyword .asKw)) = true := by
    rw [found]
    rfl
  rw [present] at absent
  contradiction

/-- Every executable complete import success follows the exact keyword and
prioritized namespace, wildcard, selective, or plain payload branch. -/
theorem importDecl_success_ordinaryOutcome_sound
    {input output : State} {declaration : ImportDecl}
    (result : importDecl input = .ok declaration output) :
    DeclarativeGrammar.ImportDeclOrdinaryParses input.declarativeRemainder
      declaration output.declarativeRemainder := by
  unfold importDecl at result
  rcases bind_success_components result with
    ⟨keywordToken, afterKeyword, keywordResult, rest⟩
  rcases bind_success_components rest with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  have keywordParsed :=
    keyword_success_exactTokenParses .importKw .importDecl keywordResult
  by_cases starPresent : isSymbol afterKeyword .star = true
  · simp only [starPresent, if_true] at branchResult
    have starParsed :=
      importDispatchSymbolPresentAt_of_isSymbol_eq_true .star starPresent
    by_cases asPresent :
        (afterKeyword.peekOffsetKind? 1 == some (.keyword .asKw)) = true
    · simp only [asPresent, if_true] at branchResult
      exact .namespaceImport keywordToken.span keywordParsed starParsed
        (importDispatchAsPresentAt_of_peekOffsetKind_eq_true asPresent)
        (namespaceImport_success_ordinaryOutcome_sound keywordToken.span
          branchResult)
    · have asAbsent :
          (afterKeyword.peekOffsetKind? 1 == some (.keyword .asKw)) = false :=
        Bool.eq_false_iff.mpr asPresent
      simp only [asAbsent, Bool.false_eq_true, if_false] at branchResult
      exact .wildcardImport keywordToken.span keywordParsed starParsed
        (asAbsentAt_of_peekOffsetKind_eq_false asAbsent)
        (wildcardImport_success_ordinaryOutcome_sound keywordToken.span
          branchResult)
  · have starAbsent : isSymbol afterKeyword .star = false :=
      Bool.eq_false_iff.mpr starPresent
    simp only [starAbsent, Bool.false_eq_true, if_false] at branchResult
    have starMissing : DeclarativeGrammar.TokenKindAbsentAt
        afterKeyword.tokens afterKeyword.window.endIndex
          (afterKeyword.cursor + 0) (.symbol .star) := by
      simpa using symbolAbsentAt_of_isSymbol_eq_false .star starAbsent
    by_cases leftBracePresent : isSymbol afterKeyword .leftBrace = true
    · simp only [leftBracePresent, if_true] at branchResult
      exact .selectiveImport keywordToken.span keywordParsed starMissing
        (importDispatchSymbolPresentAt_of_isSymbol_eq_true .leftBrace
          leftBracePresent)
        (selectiveImport_success_ordinaryOutcome_sound keywordToken.span
          branchResult)
    · have leftBraceAbsent : isSymbol afterKeyword .leftBrace = false :=
        Bool.eq_false_iff.mpr leftBracePresent
      simp only [leftBraceAbsent, Bool.false_eq_true, if_false]
        at branchResult
      have leftBraceMissing : DeclarativeGrammar.TokenKindAbsentAt
          afterKeyword.tokens afterKeyword.window.endIndex
            (afterKeyword.cursor + 0) (.symbol .leftBrace) := by
        simpa using
          (symbolAbsentAt_of_isSymbol_eq_false .leftBrace leftBraceAbsent)
      exact .plainImport keywordToken.span keywordParsed starMissing
        leftBraceMissing
        (plainImport_success_ordinaryOutcome_sound keywordToken.span
          branchResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WildcardImportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for wildcard-import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable wildcard-import rejection records its exact first
rejecting stage among `*`, `from`, path, optional hiding, and terminator. -/
theorem wildcardImport_reject_ordinaryOutcome_sound (start : SourceSpan)
    {input rejected : State} {failure : Failure}
    (result : ImportInternals.wildcardImport start input =
      .reject failure rejected) :
    DeclarativeGrammar.WildcardImportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ImportInternals.wildcardImport at result
  cases starResult : symbol .star .importDecl input with
  | invariant error => simp [bind, starResult] at result
  | reject starFailure starRejected =>
      have starRejectedEq := symbol_reject_state_eq .star .importDecl
        starResult
      subst starRejected
      simp only [bind, starResult] at result
      cases result
      exact .starMissing
        (symbol_reject_tokenKindAbsentAt .star .importDecl starResult)
  | ok star afterStar =>
      simp only [bind, starResult] at result
      have starParsed := symbol_success_exactTokenParses .star .importDecl
        starResult
      cases fromResult : contextual .from .importDecl afterStar with
      | invariant error => simp [fromResult] at result
      | reject fromFailure fromRejected =>
          have fromRejectedEq := contextual_reject_state_eq .from .importDecl
            fromResult
          subst fromRejected
          simp only [fromResult] at result
          cases result
          exact .fromMissing star.span starParsed
            (contextual_reject_tokenKindAbsentAt .from .importDecl fromResult)
      | ok fromToken afterFrom =>
          simp only [fromResult] at result
          have fromParsed := contextual_success_exactTokenParses .from
            .importDecl fromResult
          cases pathResult : modulePath .importDecl afterFrom with
          | invariant error => simp [pathResult] at result
          | reject pathFailure pathRejected =>
              simp only [pathResult] at result
              cases result
              exact .pathRejected star.span fromToken.span starParsed
                fromParsed
                (modulePath_reject_ordinaryOutcome_sound .importDecl
                  pathResult)
          | ok path afterPath =>
              simp only [pathResult] at result
              have pathParsed := modulePath_success_ordinaryOutcome_sound
                .importDecl pathResult
              cases hidingResult : ImportInternals.optionalHiding afterPath with
              | invariant error => simp [hidingResult] at result
              | reject hidingFailure hidingRejected =>
                  simp only [hidingResult] at result
                  cases result
                  exact .hidingRejected star.span fromToken.span starParsed
                    fromParsed pathParsed
                    (optionalHiding_reject_ordinaryOutcome_sound hidingResult)
              | ok hidden afterHiding =>
                  simp only [hidingResult] at result
                  have hidingParsed :=
                    optionalHiding_success_ordinaryOutcome_sound hidingResult
                  cases hidden with
                  | none =>
                      exact .terminatorRejected star.span fromToken.span
                        starParsed fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start path.span
                          (.wildcard path none) result)
                  | some clause =>
                      exact .terminatorRejected star.span fromToken.span
                        starParsed fromParsed pathParsed hidingParsed
                        (finish_reject_ordinaryOutcome_sound start clause.span
                          (.wildcard path (some clause)) result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportDeclarationOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for complete import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem keyword_reject_tokenKindAbsentAt
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.keyword value) := by
  by_cases present : isKeyword input value = true
  · rcases keyword_eq_ok_of_isKeyword_eq_true value context present with
      ⟨token, parsed⟩
    rw [parsed] at result
    contradiction
  · exact keywordAbsentAt_of_isKeyword_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem keyword_reject_state_eq
    (value : HardKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : keyword value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.keyword value) context
    (· == .keyword value) result

private theorem dispatchSymbolPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.ImportDispatchTokenPresentAt
      input.declarativeRemainder 0 (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .importDecl present with
    ⟨token, parsed⟩
  refine ⟨token.span, ?_⟩
  simpa only [State.declarativeRemainder, Nat.add_zero] using
    (symbol_success_exactTokenParses value .importDecl parsed).1

/-- Every executable complete-import rejection records the leading keyword or
the exact rejection of the uniquely committed payload branch. -/
theorem importDecl_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : importDecl input = .reject failure rejected) :
    DeclarativeGrammar.ImportDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold importDecl at result
  cases keywordResult : keyword .importKw .importDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .importKw .importDecl
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .importKw .importDecl keywordResult)
  | ok keyword afterKeyword =>
      simp only [bind, keywordResult, getState] at result
      have keywordParsed := keyword_success_exactTokenParses .importKw
        .importDecl keywordResult
      by_cases starPresent : isSymbol afterKeyword .star
      · simp only [starPresent, if_true] at result
        have starGuard := dispatchSymbolPresentAt_of_isSymbol_eq_true .star
          starPresent
        by_cases asPresent :
            afterKeyword.peekOffsetKind? 1 == some (.keyword .asKw)
        · simp only [asPresent, if_true] at result
          exact .namespaceImportRejected keyword.span keywordParsed starGuard
            (importDispatchAsPresentAt_of_peekOffsetKind_eq_true asPresent)
            (namespaceImport_reject_ordinaryOutcome_sound keyword.span result)
        · have asAbsent :
              (afterKeyword.peekOffsetKind? 1 ==
                some (.keyword .asKw)) = false :=
            Bool.eq_false_iff.mpr asPresent
          simp only [asAbsent, Bool.false_eq_true, if_false] at result
          exact .wildcardImportRejected keyword.span keywordParsed starGuard
            (asAbsentAt_of_peekOffsetKind_eq_false asAbsent)
            (wildcardImport_reject_ordinaryOutcome_sound keyword.span result)
      · have starAbsentBool : isSymbol afterKeyword .star = false :=
          Bool.eq_false_iff.mpr starPresent
        simp only [starAbsentBool, Bool.false_eq_true, if_false] at result
        have starAbsent : DeclarativeGrammar.TokenKindAbsentAt
            afterKeyword.tokens afterKeyword.window.endIndex
              (afterKeyword.cursor + 0) (.symbol .star) := by
          simpa using
            symbolAbsentAt_of_isSymbol_eq_false .star starAbsentBool
        by_cases leftBracePresent : isSymbol afterKeyword .leftBrace
        · simp only [leftBracePresent, if_true] at result
          exact .selectiveImportRejected keyword.span keywordParsed
            starAbsent
            (dispatchSymbolPresentAt_of_isSymbol_eq_true .leftBrace
              leftBracePresent)
            (selectiveImport_reject_ordinaryOutcome_sound keyword.span result)
        · have leftBraceAbsentBool :
              isSymbol afterKeyword .leftBrace = false :=
            Bool.eq_false_iff.mpr leftBracePresent
          simp only [leftBraceAbsentBool, Bool.false_eq_true, if_false] at result
          have leftBraceAbsent : DeclarativeGrammar.TokenKindAbsentAt
              afterKeyword.tokens afterKeyword.window.endIndex
                (afterKeyword.cursor + 0) (.symbol .leftBrace) := by
            simpa using
              symbolAbsentAt_of_isSymbol_eq_false .leftBrace
                leftBraceAbsentBool
          exact .plainImportRejected keyword.span keywordParsed
            starAbsent leftBraceAbsent
            (plainImport_reject_ordinaryOutcome_sound keyword.span result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportDeclarationOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for import declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package complete-import success and exact prioritized rejection. -/
theorem importDecl_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : ImportDecl},
      importDecl input = .ok declaration output →
        DeclarativeGrammar.ImportDeclOrdinaryParses
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      importDecl input = .reject failure rejected →
        DeclarativeGrammar.ImportDeclRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨importDecl_success_ordinaryOutcome_sound,
    importDecl_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive complete-import outcomes. -/
theorem importDecl_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ImportDeclOrdinaryParses
      DeclarativeGrammar.ImportDeclRejects :=
  DeclarativeGrammar.importDeclDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WildcardImportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for wildcard import payloads. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package wildcard-import success and exact stagewise rejection. -/
theorem wildcardImport_ordinaryOutcome_sound (start : SourceSpan) :
    (∀ {input output : State} {declaration : ImportDecl},
      ImportInternals.wildcardImport start input = .ok declaration output →
        DeclarativeGrammar.WildcardImportOrdinaryParses start
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.wildcardImport start input = .reject failure rejected →
        DeclarativeGrammar.WildcardImportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨wildcardImport_success_ordinaryOutcome_sound start,
    wildcardImport_reject_ordinaryOutcome_sound start⟩

/-- Re-export deterministic and exclusive wildcard-import outcomes. -/
theorem wildcardImport_ordinaryOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.WildcardImportOrdinaryParses start)
      DeclarativeGrammar.WildcardImportRejects :=
  DeclarativeGrammar.wildcardImportDeterministicOutcomeSpec start

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.HidingClauseOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for required and optional hiding. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package required hiding-clause success and exact sequential rejection. -/
theorem hidingClause_ordinaryOutcome_sound :
    (∀ {input output : State} {clause : HidingClause},
      ImportInternals.hidingClause input = .ok clause output →
        DeclarativeGrammar.HidingClauseOrdinaryParses
          input.declarativeRemainder clause output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.hidingClause input = .reject failure rejected →
        DeclarativeGrammar.HidingClauseRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨hidingClause_success_ordinaryOutcome_sound,
    hidingClause_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive required hiding outcomes. -/
theorem hidingClause_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.HidingClauseOrdinaryParses
      DeclarativeGrammar.HidingClauseRejects :=
  DeclarativeGrammar.hidingClauseDeterministicOutcomeSpec

/-- Package guarded optional hiding success and exact committed rejection. -/
theorem optionalHiding_ordinaryOutcome_sound :
    (∀ {input output : State} {hidden : Option HidingClause},
      ImportInternals.optionalHiding input = .ok hidden output →
        DeclarativeGrammar.OptionalHidingOrdinaryParses
          input.declarativeRemainder hidden output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ImportInternals.optionalHiding input = .reject failure rejected →
        DeclarativeGrammar.OptionalHidingRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨optionalHiding_success_ordinaryOutcome_sound,
    optionalHiding_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive optional hiding outcomes. -/
theorem optionalHiding_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalHidingOrdinaryParses
      DeclarativeGrammar.OptionalHidingRejects :=
  DeclarativeGrammar.optionalHidingDeterministicOutcomeSpec

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportSelectionExactnessProperties
/-! Unconditional exact executable outcomes for selected names and hiding clauses. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export full exactness of selectedAlias outcomes. -/
theorem selectedAlias_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedAliasOrdinaryParses
      DeclarativeGrammar.SelectedAliasRejects :=
  DeclarativeGrammar.selectedAliasExactOutcomeSpec

/-- Successful selectedAlias results agree on their complete AST and remainder. -/
theorem selectedAlias_success_result_unique
    {input leftOutput rightOutput : State} {left right : Option Identifier}
    (leftResult : ImportInternals.selectedAlias input = .ok left leftOutput)
    (rightResult : ImportInternals.selectedAlias input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedAlias_exactOutcomeSpec).successResultUnique
    (selectedAlias_success_ordinaryOutcome_sound leftResult)
    (selectedAlias_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedAlias results agree on their complete declarative endpoint. -/
theorem selectedAlias_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectedAlias input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectedAlias input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedAlias_exactOutcomeSpec).rejectOutputUnique
    (selectedAlias_reject_ordinaryOutcome_sound leftResult)
    (selectedAlias_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of selectedImport outcomes. -/
theorem selectedImport_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportOrdinaryParses
      DeclarativeGrammar.SelectedImportRejects :=
  DeclarativeGrammar.selectedImportExactOutcomeSpec

/-- Successful selectedImport results agree on their complete AST and remainder. -/
theorem selectedImport_success_result_unique
    {input leftOutput rightOutput : State} {left right : SelectedImport}
    (leftResult : selectedImport input = .ok left leftOutput)
    (rightResult : selectedImport input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImport_exactOutcomeSpec).successResultUnique
    (selectedImport_success_ordinaryOutcome_sound leftResult)
    (selectedImport_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedImport results agree on their complete declarative endpoint. -/
theorem selectedImport_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : selectedImport input = .reject leftFailure leftOutput)
    (rightResult : selectedImport input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImport_exactOutcomeSpec).rejectOutputUnique
    (selectedImport_reject_ordinaryOutcome_sound leftResult)
    (selectedImport_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of selectedImports outcomes. -/
theorem selectedImports_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectedImportsOrdinaryParses
      DeclarativeGrammar.SelectedImportsRejects :=
  DeclarativeGrammar.selectedImportsExactOutcomeSpec

/-- Successful selectedImports results agree on their complete AST and remainder. -/
theorem selectedImports_success_result_unique
    {input leftOutput rightOutput : State} {left right : NonemptyDelimitedList SelectedImport}
    (leftResult : ImportInternals.selectedImports input = .ok left leftOutput)
    (rightResult : ImportInternals.selectedImports input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImports_exactOutcomeSpec).successResultUnique
    (selectedImports_success_ordinaryOutcome_sound leftResult)
    (selectedImports_success_ordinaryOutcome_sound rightResult)

/-- Rejected selectedImports results agree on their complete declarative endpoint. -/
theorem selectedImports_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectedImports input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectedImports input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectedImports_exactOutcomeSpec).rejectOutputUnique
    (selectedImports_reject_ordinaryOutcome_sound leftResult)
    (selectedImports_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of hidingClause outcomes. -/
theorem hidingClause_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.HidingClauseOrdinaryParses
      DeclarativeGrammar.HidingClauseRejects :=
  DeclarativeGrammar.hidingClauseExactOutcomeSpec

/-- Successful hidingClause results agree on their complete AST and remainder. -/
theorem hidingClause_success_result_unique
    {input leftOutput rightOutput : State} {left right : HidingClause}
    (leftResult : ImportInternals.hidingClause input = .ok left leftOutput)
    (rightResult : ImportInternals.hidingClause input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (hidingClause_exactOutcomeSpec).successResultUnique
    (hidingClause_success_ordinaryOutcome_sound leftResult)
    (hidingClause_success_ordinaryOutcome_sound rightResult)

/-- Rejected hidingClause results agree on their complete declarative endpoint. -/
theorem hidingClause_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.hidingClause input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.hidingClause input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (hidingClause_exactOutcomeSpec).rejectOutputUnique
    (hidingClause_reject_ordinaryOutcome_sound leftResult)
    (hidingClause_reject_ordinaryOutcome_sound rightResult)

/-- Re-export full exactness of optionalHiding outcomes. -/
theorem optionalHiding_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalHidingOrdinaryParses
      DeclarativeGrammar.OptionalHidingRejects :=
  DeclarativeGrammar.optionalHidingExactOutcomeSpec

/-- Successful optionalHiding results agree on their complete AST and remainder. -/
theorem optionalHiding_success_result_unique
    {input leftOutput rightOutput : State} {left right : Option HidingClause}
    (leftResult : ImportInternals.optionalHiding input = .ok left leftOutput)
    (rightResult : ImportInternals.optionalHiding input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalHiding_exactOutcomeSpec).successResultUnique
    (optionalHiding_success_ordinaryOutcome_sound leftResult)
    (optionalHiding_success_ordinaryOutcome_sound rightResult)

/-- Rejected optionalHiding results agree on their complete declarative endpoint. -/
theorem optionalHiding_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.optionalHiding input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.optionalHiding input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (optionalHiding_exactOutcomeSpec).rejectOutputUnique
    (optionalHiding_reject_ordinaryOutcome_sound leftResult)
    (optionalHiding_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportExactnessProperties
/-! Unconditional exact executable outcomes for every complete import form. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export full exactness of plainImport outcomes at the fixed outer start. -/
theorem plainImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.PlainImportOrdinaryParses start)
      DeclarativeGrammar.PlainImportRejects :=
  DeclarativeGrammar.plainImportExactOutcomeSpec start

/-- Successful plainImport results agree on their complete AST and remainder. -/
theorem plainImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.plainImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.plainImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (plainImport_exactOutcomeSpec start).successResultUnique
    (plainImport_success_ordinaryOutcome_sound start leftResult)
    (plainImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected plainImport results agree on their complete declarative endpoint. -/
theorem plainImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.plainImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.plainImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (plainImport_exactOutcomeSpec start).rejectOutputUnique
    (plainImport_reject_ordinaryOutcome_sound start leftResult)
    (plainImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of namespaceImport outcomes at the fixed outer start. -/
theorem namespaceImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.NamespaceImportOrdinaryParses start)
      DeclarativeGrammar.NamespaceImportRejects :=
  DeclarativeGrammar.namespaceImportExactOutcomeSpec start

/-- Successful namespaceImport results agree on their complete AST and remainder. -/
theorem namespaceImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.namespaceImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.namespaceImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (namespaceImport_exactOutcomeSpec start).successResultUnique
    (namespaceImport_success_ordinaryOutcome_sound start leftResult)
    (namespaceImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected namespaceImport results agree on their complete declarative endpoint. -/
theorem namespaceImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.namespaceImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.namespaceImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (namespaceImport_exactOutcomeSpec start).rejectOutputUnique
    (namespaceImport_reject_ordinaryOutcome_sound start leftResult)
    (namespaceImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of wildcardImport outcomes at the fixed outer start. -/
theorem wildcardImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.WildcardImportOrdinaryParses start)
      DeclarativeGrammar.WildcardImportRejects :=
  DeclarativeGrammar.wildcardImportExactOutcomeSpec start

/-- Successful wildcardImport results agree on their complete AST and remainder. -/
theorem wildcardImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.wildcardImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.wildcardImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (wildcardImport_exactOutcomeSpec start).successResultUnique
    (wildcardImport_success_ordinaryOutcome_sound start leftResult)
    (wildcardImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected wildcardImport results agree on their complete declarative endpoint. -/
theorem wildcardImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.wildcardImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.wildcardImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (wildcardImport_exactOutcomeSpec start).rejectOutputUnique
    (wildcardImport_reject_ordinaryOutcome_sound start leftResult)
    (wildcardImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of selectiveImport outcomes at the fixed outer start. -/
theorem selectiveImport_exactOutcomeSpec (start : SourceSpan) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.SelectiveImportOrdinaryParses start)
      DeclarativeGrammar.SelectiveImportRejects :=
  DeclarativeGrammar.selectiveImportExactOutcomeSpec start

/-- Successful selectiveImport results agree on their complete AST and remainder. -/
theorem selectiveImport_success_result_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : ImportInternals.selectiveImport start input = .ok left leftOutput)
    (rightResult : ImportInternals.selectiveImport start input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectiveImport_exactOutcomeSpec start).successResultUnique
    (selectiveImport_success_ordinaryOutcome_sound start leftResult)
    (selectiveImport_success_ordinaryOutcome_sound start rightResult)

/-- Rejected selectiveImport results agree on their complete declarative endpoint. -/
theorem selectiveImport_reject_output_unique (start : SourceSpan)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ImportInternals.selectiveImport start input = .reject leftFailure leftOutput)
    (rightResult : ImportInternals.selectiveImport start input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectiveImport_exactOutcomeSpec start).rejectOutputUnique
    (selectiveImport_reject_ordinaryOutcome_sound start leftResult)
    (selectiveImport_reject_ordinaryOutcome_sound start rightResult)

/-- Re-export full exactness of importDecl outcomes. -/
theorem importDecl_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ImportDeclOrdinaryParses
      DeclarativeGrammar.ImportDeclRejects :=
  DeclarativeGrammar.importDeclExactOutcomeSpec

/-- Successful importDecl results agree on their complete AST and remainder. -/
theorem importDecl_success_result_unique
    {input leftOutput rightOutput : State} {left right : ImportDecl}
    (leftResult : importDecl input = .ok left leftOutput)
    (rightResult : importDecl input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importDecl_exactOutcomeSpec).successResultUnique
    (importDecl_success_ordinaryOutcome_sound leftResult)
    (importDecl_success_ordinaryOutcome_sound rightResult)

/-- Rejected importDecl results agree on their complete declarative endpoint. -/
theorem importDecl_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : importDecl input = .reject leftFailure leftOutput)
    (rightResult : importDecl input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (importDecl_exactOutcomeSpec).rejectOutputUnique
    (importDecl_reject_ordinaryOutcome_sound leftResult)
    (importDecl_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WildcardImportSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.NamespaceImportSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.ImportDeclSoundnessProperties
/-! Aggregate diagnostic-free soundness of all canonical import forms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every diagnostic-free successful import follows its declarative grammar. -/
theorem importDecl_success_sound {input next : State}
    {declaration : ImportDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.ImportDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  cases shape : declaration.value with
  | plain path =>
      exact .ofPlain (importDecl_plain_success_sound diagnosticFree
        ⟨path, shape⟩ result)
  | «namespace» path alias =>
      exact .ofNamespace (importDecl_namespace_success_sound diagnosticFree
        ⟨path, alias, shape⟩ result)
  | wildcard path hidden =>
      exact .ofWildcard (importDecl_wildcard_success_sound diagnosticFree
        ⟨path, hidden, shape⟩ result)
  | selected selection path hidden =>
      exact .ofSelected (importDecl_selected_success_sound diagnosticFree
        ⟨selection, path, hidden, shape⟩ result)

/-- Aggregate import soundness composes with source-provenance validity. -/
theorem importDecl_success_sound_and_validFor {input next : State}
    {declaration : ImportDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : importDecl input = .ok declaration next) :
    DeclarativeGrammar.ImportDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨importDecl_success_sound diagnosticFree result, ?_⟩
  have valid := importDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.WildcardImportNoHidingSoundnessProperties
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
end
