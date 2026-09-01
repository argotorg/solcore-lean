import Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Literal

/-!
Bridges between executable atom-dispatch lookaheads and the independent
declarative starter predicates.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem isCoreLiteral_eq_true_of_decimalTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .decimalLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem isCoreLiteral_eq_true_of_hexadecimalTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .hexadecimalLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem isCoreLiteral_eq_true_of_stringTokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .stringLiteral spelling }) :
    isCoreLiteral input = true := by
  unfold isCoreLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative literal presence makes the executable literal guard true. -/
theorem isCoreLiteral_eq_true_of_coreLiteralStartsAt {input : State}
    (starts : DeclarativeGrammar.CoreLiteralStartsAt
      input.declarativeRemainder) :
    isCoreLiteral input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, spelling, token⟩
  · exact isCoreLiteral_eq_true_of_decimalTokenAt token
  · exact isCoreLiteral_eq_true_of_hexadecimalTokenAt token
  · exact isCoreLiteral_eq_true_of_stringTokenAt token

/-- A false executable literal guard excludes the declarative starter. -/
theorem not_coreLiteralStartsAt_of_isCoreLiteral_eq_false {input : State}
    (absent : isCoreLiteral input = false) :
    ¬ DeclarativeGrammar.CoreLiteralStartsAt input.declarativeRemainder := by
  intro starts
  rw [isCoreLiteral_eq_true_of_coreLiteralStartsAt starts] at absent
  contradiction

private theorem isKeyword_eq_true_of_tokenAt (keyword : HardKeyword)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword keyword }) :
    isKeyword input keyword = true := by
  unfold isKeyword State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  change instBEqTokenKind.beq (.keyword keyword) (.keyword keyword) = true
  simp only [instBEqTokenKind.beq]
  change instBEqHardKeyword.beq keyword keyword = true
  unfold instBEqHardKeyword.beq
  cases keyword <;> rfl

private theorem isIdentifier_eq_true_of_tokenAt {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .identifier spelling }) :
    isIdentifier input = true := by
  unfold isIdentifier State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/--
Declarative Boolean-or-identifier presence makes the executable disjunctive
name guard true, including both hard-keyword Boolean spellings.
-/
theorem expressionNameGuard_eq_true_of_expressionNameStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ExpressionNameStartsAt
      input.declarativeRemainder) :
    (isBooleanValue input || isIdentifier input) = true := by
  rcases starts with ⟨span, token⟩ | ⟨span, token⟩ |
      ⟨span, spelling, token⟩
  · have present := isKeyword_eq_true_of_tokenAt .trueKw token
    simp [isBooleanValue, present]
  · have present := isKeyword_eq_true_of_tokenAt .falseKw token
    simp [isBooleanValue, present]
  · have present := isIdentifier_eq_true_of_tokenAt token
    simp [present]

/-- A false Boolean-or-identifier guard excludes every expression name. -/
theorem not_expressionNameStartsAt_of_expressionNameGuard_eq_false
    {input : State}
    (absent : (isBooleanValue input || isIdentifier input) = false) :
    ¬ DeclarativeGrammar.ExpressionNameStartsAt
      input.declarativeRemainder := by
  intro starts
  rw [expressionNameGuard_eq_true_of_expressionNameStartsAt starts] at absent
  contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
