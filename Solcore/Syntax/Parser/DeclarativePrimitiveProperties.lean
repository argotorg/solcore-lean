import Solcore.Syntax.DeclarativeGrammar
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.StateCursorProperties

/-! Primitive bridges from parser success to exact declarative tokens. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace State

/-- Forget parser-only state while retaining the active grammar remainder. -/
def declarativeRemainder (state : State) : DeclarativeGrammar.Remainder := {
  tokens := state.tokens
  endIndex := state.window.endIndex
  cursor := state.cursor
}

end State

/-- A successful current-token lookup is an exact declarative token. -/
theorem tokenAt_of_peek?_eq_some {input : State} {token : Token}
    (found : input.peek? = some token) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor token :=
  ⟨State.cursor_lt_endIndex_of_peek?_eq_some found,
    State.getElem?_eq_some_of_peek?_eq_some found⟩

/-- A failed symbol lookahead excludes that symbol at the grammar cursor. -/
theorem symbolAbsentAt_of_isSymbol_eq_false (value : Symbol)
    {input : State} (absent : isSymbol input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.symbol value) := by
  rintro ⟨span, inside, found⟩
  unfold isSymbol State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  change instBEqTokenKind.beq (.symbol value) (.symbol value) = false at absent
  simp only [instBEqTokenKind.beq] at absent
  change instBEqSymbol.beq value value = false at absent
  unfold instBEqSymbol.beq at absent
  cases value <;> contradiction

/-- A failed keyword lookahead excludes that keyword at the grammar cursor. -/
theorem keywordAbsentAt_of_isKeyword_eq_false (value : HardKeyword)
    {input : State} (absent : isKeyword input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.keyword value) := by
  rintro ⟨span, inside, found⟩
  unfold isKeyword State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some] at absent
  change instBEqTokenKind.beq (.keyword value) (.keyword value) = false at absent
  simp only [instBEqTokenKind.beq] at absent
  change instBEqHardKeyword.beq value value = false at absent
  unfold instBEqHardKeyword.beq at absent
  cases value <;> contradiction

/-- Failed contextual lookahead excludes its identifier spelling. -/
theorem contextualAbsentAt_of_isContextual_eq_false
    (value : ContextualKeyword) {input : State}
    (absent : isContextual input value = false) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens
      input.window.endIndex input.cursor (.identifier value.spelling) := by
  rintro ⟨span, inside, found⟩
  unfold isContextual State.peekKind? State.peek? at absent
  simp only [inside, ↓reduceIte, found, Option.map_some,
    TokenKind.isContextual] at absent
  have same : (value.spelling == value.spelling) = true :=
    beq_iff_eq.mpr rfl
  rw [same] at absent
  contradiction

private theorem acceptToken_ok_tokenAt_of_kind (kind : TokenKind)
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (acceptsKind : ∀ actual, accepts actual = true → actual = kind)
    {input next : State} {token : Token}
    (result : acceptToken expected context accepts input =
      .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := kind
    } ∧ next = { input with cursor := input.cursor + 1 } := by
  unfold acceptToken at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      next accepted =>
        have kindEq : current.value = kind := acceptsKind current.value accepted
        cases result
        have tokenEq : token = { span := token.span, value := kind } := by
          rcases token with ⟨span, value⟩
          simp only at kindEq ⊢
          subst value
          rfl
        rw [← tokenEq]
        exact ⟨tokenAt_of_peek?_eq_some found, rfl⟩
      next rejected =>
        unfold rejectAt at result
        contradiction

private theorem keyword_accepts_kind (value : HardKeyword)
    {actual : TokenKind}
    (accepted : (actual == .keyword value) = true) :
    actual = .keyword value := by
  change instBEqTokenKind.beq actual (.keyword value) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case keyword actual =>
    change instBEqHardKeyword.beq actual value = true at accepted
    unfold instBEqHardKeyword.beq at accepted
    cases actual <;> cases value <;>
      first | rfl | cases accepted

/-- Keyword success exposes the exact located keyword token consumed. -/
theorem keyword_ok_tokenAt (value : HardKeyword) (context : ParseContext)
    {input next : State} {token : Token}
    (result : keyword value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .keyword value
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.keyword value) (.keyword value) context
    (· == .keyword value)
    (fun actual accepted =>
      keyword_accepts_kind value (actual := actual) accepted) result

private theorem symbol_accepts_kind (value : Symbol) {actual : TokenKind}
    (accepted : (actual == .symbol value) = true) :
    actual = .symbol value := by
  change instBEqTokenKind.beq actual (.symbol value) = true at accepted
  cases actual <;> simp only [instBEqTokenKind.beq] at accepted
  all_goals try { contradiction }
  case symbol actual =>
    change instBEqSymbol.beq actual value = true at accepted
    unfold instBEqSymbol.beq at accepted
    cases actual <;> cases value <;>
      first | rfl | cases accepted

/-- Symbol success exposes the exact located symbol token consumed. -/
theorem symbol_ok_tokenAt (value : Symbol) (context : ParseContext)
    {input next : State} {token : Token}
    (result : symbol value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .symbol value
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.symbol value) (.symbol value) context
    (· == .symbol value)
    (fun actual accepted =>
      symbol_accepts_kind value (actual := actual) accepted) result

private theorem contextual_accepts_kind (value : ContextualKeyword)
    {actual : TokenKind} (accepted : actual.isContextual value = true) :
    actual = .identifier value.spelling := by
  cases actual <;> simp only [TokenKind.isContextual] at accepted
  all_goals try { contradiction }
  case identifier text =>
    have equal : text = value.spelling := beq_iff_eq.mp accepted
    subst text
    rfl

/-- Contextual-keyword success exposes its exact identifier token. -/
theorem contextual_ok_tokenAt (value : ContextualKeyword)
    (context : ParseContext) {input next : State} {token : Token}
    (result : contextual value context input = .ok token next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := token.span
      value := .identifier value.spelling
    } ∧ next = { input with cursor := input.cursor + 1 } :=
  acceptToken_ok_tokenAt_of_kind (.identifier value.spelling)
    (.contextual value) context (fun kind => kind.isContextual value)
    (fun actual accepted =>
      contextual_accepts_kind value (actual := actual) accepted) result

/-- Raw identifier success exposes the exact identifier token consumed. -/
theorem rawIdentifier_ok_tokenAt (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : rawIdentifier context input = .ok name next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    } ∧ next = { input with cursor := input.cursor + 1 } := by
  unfold rawIdentifier at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        cases result
        exact ⟨⟨State.cursor_lt_endIndex_of_peek?_eq_some found,
          State.getElem?_eq_some_of_peek?_eq_some found⟩, rfl⟩

/-- Checked identifier success retains the exact token despite diagnostics. -/
theorem identifier_ok_tokenAt (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : identifier context input = .ok name next) :
    DeclarativeGrammar.TokenAt input.tokens input.window.endIndex input.cursor {
      span := name.span
      value := .identifier name.value
    } ∧ next.tokens = input.tokens ∧ next.window = input.window ∧
      next.cursor = input.cursor + 1 := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | invariant error => simp [raw] at result
  | reject failure rejected => simp [raw] at result
  | ok parsed afterName =>
      have rawSound := rawIdentifier_ok_tokenAt context raw
      simp only [raw] at result
      split at result <;> cases result
      · rw [rawSound.2]
        exact ⟨rawSound.1, by simp [State.emit],
          by simp [State.emit], by simp [State.emit]⟩
      · rw [rawSound.2]
        exact ⟨rawSound.1, rfl, rfl, rfl⟩

end Solcore.Syntax.Parser
