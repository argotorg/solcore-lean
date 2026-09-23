import Solcore.Syntax.DeclarativeImportDeclOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.NamespaceImportOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.PlainImportOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.SelectiveImportOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Parser.WildcardImportOrdinarySuccessSoundnessProperties

/-! Broad ordinary-success reflection for complete import declarations. -/

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
