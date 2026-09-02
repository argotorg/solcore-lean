import Solcore.Syntax.DeclarativeImportDeclOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.PlainImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.WildcardImportOrdinaryRejectionSoundnessProperties

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
