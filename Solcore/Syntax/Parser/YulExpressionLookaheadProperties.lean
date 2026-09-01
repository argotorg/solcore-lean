import Solcore.Syntax.DeclarativeYulExpressionGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Yul.Expression

/-!
Bridges between executable inline-Yul expression guards and declarative token
starter predicates.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem startsYulLiteral_eq_true_of_tokenAt_decimal {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .decimalLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_hexadecimal {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .hexadecimalLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_string {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .stringLiteral spelling }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_true {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .trueKw }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulLiteral_eq_true_of_tokenAt_false {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .falseKw }) :
    startsYulLiteral input = true := by
  unfold startsYulLiteral State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative Yul-literal presence makes the executable first guard true. -/
theorem startsYulLiteral_eq_true_of_yulLiteralStartsAt {input : State}
    (starts : DeclarativeGrammar.YulLiteralStartsAt
      input.declarativeRemainder) :
    startsYulLiteral input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, spelling, token⟩ |
      ⟨span, token⟩ | ⟨span, token⟩
  · exact startsYulLiteral_eq_true_of_tokenAt_decimal token
  · exact startsYulLiteral_eq_true_of_tokenAt_hexadecimal token
  · exact startsYulLiteral_eq_true_of_tokenAt_string token
  · exact startsYulLiteral_eq_true_of_tokenAt_true token
  · exact startsYulLiteral_eq_true_of_tokenAt_false token

/-- A false executable literal guard excludes every declarative Yul literal. -/
theorem not_yulLiteralStartsAt_of_startsYulLiteral_eq_false {input : State}
    (absent : startsYulLiteral input = false) :
    ¬ DeclarativeGrammar.YulLiteralStartsAt
      input.declarativeRemainder := by
  intro starts
  rw [startsYulLiteral_eq_true_of_yulLiteralStartsAt starts] at absent
  contradiction

private theorem startsYulName_eq_true_of_tokenAt_identifier {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .identifier spelling }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_marked {input : State}
    {span : SourceSpan} {spelling : String}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .yulIdentifier spelling }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_underscore {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol .underscore }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

private theorem startsYulName_eq_true_of_tokenAt_fallback {input : State}
    {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .keyword .fallbackKw }) :
    startsYulName input = true := by
  unfold startsYulName State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]

/-- Declarative Yul-name presence makes the executable second guard true. -/
theorem startsYulName_eq_true_of_yulNameStartsAt {input : State}
    (starts : DeclarativeGrammar.YulNameStartsAt input.declarativeRemainder) :
    startsYulName input = true := by
  rcases starts with ⟨span, spelling, token⟩ |
      ⟨span, spelling, token⟩ | ⟨span, token⟩ | ⟨span, token⟩
  · exact startsYulName_eq_true_of_tokenAt_identifier token
  · exact startsYulName_eq_true_of_tokenAt_marked token
  · exact startsYulName_eq_true_of_tokenAt_underscore token
  · exact startsYulName_eq_true_of_tokenAt_fallback token

/-- A false executable name guard excludes every declarative Yul name. -/
theorem not_yulNameStartsAt_of_startsYulName_eq_false {input : State}
    (absent : startsYulName input = false) :
    ¬ DeclarativeGrammar.YulNameStartsAt input.declarativeRemainder := by
  intro starts
  rw [startsYulName_eq_true_of_yulNameStartsAt starts] at absent
  contradiction

end Solcore.Syntax.Parser
