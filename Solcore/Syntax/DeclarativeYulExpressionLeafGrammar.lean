import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent leaf grammar for inline-Yul expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact diagnostic-free grammar of one inline-Yul name.

The first three constructors are Yul-specific spellings.  The ordinary
identifier constructor records the checked identifier parser's sole
diagnostic boundary: a spelling containing `-` is accepted operationally but
is not a diagnostic-free grammar success.
-/
inductive YulNameParses :
    Remainder → Syntax.YulIdentifier → Remainder → Prop where
  | marked {input : Remainder} {span : SourceSpan} {text : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulIdentifier text
      }) :
      YulNameParses input {
        span
        value := text
      } { input with cursor := input.cursor + 1 }
  | underscore {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .underscore
      }) :
      YulNameParses input {
        span
        value := "_"
      } { input with cursor := input.cursor + 1 }
  | fallbackKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .fallbackKw
      }) :
      YulNameParses input {
        span
        value := "fallback"
      } { input with cursor := input.cursor + 1 }
  | identifier {input output : Remainder} {name : Syntax.YulIdentifier}
      (hyphenAbsent : name.value.toList.contains '-' = false)
      (parsed : IdentifierParses input name output) :
      YulNameParses input name output

/-- Exact grammar of one literal admitted by inline Yul. -/
inductive YulLiteralParses :
    Remainder → Syntax.YulLiteral → Remainder → Prop where
  | decimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .decimalLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .decimal spelling
      } { input with cursor := input.cursor + 1 }
  | hexadecimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .hexadecimalLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .hexadecimal spelling
      } { input with cursor := input.cursor + 1 }
  | string {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .stringLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .string spelling
      } { input with cursor := input.cursor + 1 }
  | trueKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .trueKw
      }) :
      YulLiteralParses input {
        span
        value := .boolean true
      } { input with cursor := input.cursor + 1 }
  | falseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .falseKw
      }) :
      YulLiteralParses input {
        span
        value := .boolean false
      } { input with cursor := input.cursor + 1 }

end Solcore.Syntax.DeclarativeGrammar
