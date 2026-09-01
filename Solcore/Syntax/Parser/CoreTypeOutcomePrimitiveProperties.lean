import Solcore.Syntax.DeclarativeCoreTypeOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Executable lookahead bridges shared by exact Core-type outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Positive hard-keyword lookahead determines its primitive parse. -/
theorem keyword_eq_ok_of_isKeyword_eq_true (value : HardKeyword)
    (context : ParseContext) {input : State}
    (present : isKeyword input value = true) :
    ∃ token, keyword value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isKeyword State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      have accepted : (token.value == .keyword value) = true := by
        simpa using present
      refine ⟨token, ?_⟩
      unfold keyword acceptToken
      simp only [found, accepted, ↓reduceIte]

/-- Positive contextual-word lookahead determines its primitive parse. -/
theorem contextual_eq_ok_of_isContextual_eq_true
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (present : isContextual input value = true) :
    ∃ token, contextual value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isContextual State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      refine ⟨token, ?_⟩
      unfold contextual acceptToken
      simp only [found, present, ↓reduceIte]

/-- Offset-one symbol lookahead is current lookahead after one exact token. -/
theorem isSymbol_advanced_eq_true_of_peekOffsetKind_eq_true
    (value : Symbol) {input : State}
    (present : (input.peekOffsetKind? 1 == some (.symbol value)) = true) :
    isSymbol { input with cursor := input.cursor + 1 } value = true := by
  have shifted :
      ({ input with cursor := input.cursor + 1 } : State).peekKind? =
        input.peekOffsetKind? 1 := rfl
  unfold isSymbol
  rw [shifted]
  exact present

/-- A failed composite contextual-symbol guard excludes that exact pair. -/
theorem contextualSymbolPairAbsentAt_of_guard_eq_false
    (keywordValue : ContextualKeyword) (following : Symbol) {input : State}
    (absent : (isContextual input keywordValue &&
      (input.peekOffsetKind? 1 == some (.symbol following))) = false) :
    DeclarativeGrammar.ContextualSymbolPairAbsentAt
      input.declarativeRemainder keywordValue following := by
  rintro ⟨keywordSpan, followingSpan, keywordToken, followingToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := keywordSpan
      value := .identifier keywordValue.spelling
    } at keywordToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := followingSpan
      value := .symbol following
    } at followingToken
  have keywordPresent : isContextual input keywordValue = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [keywordToken.1, ↓reduceIte, keywordToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have followingPresent :
      (input.peekOffsetKind? 1 == some (.symbol following)) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [followingToken.1, ↓reduceIte, followingToken.2,
      Option.map_some]
    change instBEqTokenKind.beq (.symbol following)
      (.symbol following) = true
    simp only [instBEqTokenKind.beq]
    change instBEqSymbol.beq following following = true
    unfold instBEqSymbol.beq
    cases following <;> rfl
  rw [keywordPresent, followingPresent] at absent
  contradiction

/-- Failed generic identifier lookahead excludes every identifier spelling. -/
theorem identifierAbsentAt_of_isIdentifier_eq_false {input : State}
    (absent : isIdentifier input = false) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .identifier text } at token
  unfold isIdentifier State.peekKind? State.peek? at absent
  simp only [token.1, ↓reduceIte, token.2, Option.map_some] at absent
  contradiction

/-- Positive generic identifier lookahead exposes its exact current token. -/
theorem identifierPresentAt_of_isIdentifier_eq_true {input : State}
    (present : isIdentifier input = true) :
    ∃ span text, DeclarativeGrammar.TokenAt input.tokens
      input.window.endIndex input.cursor { span, value := .identifier text } := by
  unfold isIdentifier State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present
      all_goals try contradiction
      case identifier text =>
        exact ⟨span, text, tokenAt_of_peek?_eq_some found⟩

end Solcore.Syntax.Parser
