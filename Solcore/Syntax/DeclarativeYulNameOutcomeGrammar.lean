import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeYulNamesGrammar

/-!
Parser-independent ordinary outcomes for one Yul name and one nonempty Yul
name sequence.  Ordinary success retains diagnosed identifier spellings;
rejection records the exact rejected remainder.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token-kind decision for ordinary Yul names. -/
def tokenKindStartsOrdinaryYulName : TokenKind → Bool
  | .identifier _
  | .yulIdentifier _
  | .symbol .underscore
  | .keyword .fallbackKw => true
  | _ => false

/-- One ordinary Yul-name success, including a diagnosed hyphenated ordinary
identifier. -/
inductive YulNameOrdinaryParses :
    Remainder → Syntax.YulIdentifier → Remainder → Prop where
  | marked {input : Remainder} {span : SourceSpan} {text : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulIdentifier text
      }) :
      YulNameOrdinaryParses input {
        span
        value := text
      } { input with cursor := input.cursor + 1 }
  | underscore {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .underscore
      }) :
      YulNameOrdinaryParses input {
        span
        value := "_"
      } { input with cursor := input.cursor + 1 }
  | fallbackKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .fallbackKw
      }) :
      YulNameOrdinaryParses input {
        span
        value := "fallback"
      } { input with cursor := input.cursor + 1 }
  | identifier {input output : Remainder} {name : Syntax.YulIdentifier}
      (parsed : IdentifierParses input name output) :
      YulNameOrdinaryParses input name output

/-- Exact binary rejection of one ordinary Yul name. -/
inductive YulNameRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (noSuccess : ¬ ∃ name output,
        YulNameOrdinaryParses input name output) :
      YulNameRejects input input

/-- Parser-independent public value of a nonempty Yul name sequence. -/
structure YulNamesOrdinaryValue where
  span : SourceSpan
  names : NonemptyList Syntax.YulIdentifier

/-- Ordinary non-consuming assembly of a forward-order name sequence. -/
inductive FinishYulNamesOrdinaryParses
    (first last : Syntax.YulIdentifier)
    (tailRev : List Syntax.YulIdentifier) :
    Remainder → YulNamesOrdinaryValue → Remainder → Prop where
  | parsed {input : Remainder} :
      FinishYulNamesOrdinaryParses first last tailRev input {
        span := SourceSpan.cover first.span last.span
        names := { head := first, tail := tailRev.reverse }
      } input

/-- Comma-prioritized ordinary success after the first Yul name. -/
inductive YulNamesTailOrdinaryParses (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      YulNamesOrdinaryValue → Remainder → Prop where
  | done {input : Remainder} {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {value : YulNamesOrdinaryValue} {output : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma))
      (finished : FinishYulNamesOrdinaryParses first last tailRev input value
        output) :
      YulNamesTailOrdinaryParses first input last tailRev value output
  | next {input afterName output : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {value : YulNamesOrdinaryValue}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameParsed : YulNameOrdinaryParses
        { input with cursor := input.cursor + 1 } name afterName)
      (tail : YulNamesTailOrdinaryParses first afterName name
        (name :: tailRev) value output) :
      YulNamesTailOrdinaryParses first input last tailRev value output

/-- Ordinary success of one nonempty, non-trailing Yul name sequence. -/
inductive YulNamesOrdinaryParses :
    Remainder → YulNamesOrdinaryValue → Remainder → Prop where
  | parsed {input afterFirst output : Remainder}
      {first : Syntax.YulIdentifier} {value : YulNamesOrdinaryValue}
      (firstParsed : YulNameOrdinaryParses input first afterFirst)
      (tail : YulNamesTailOrdinaryParses first afterFirst first [] value
        output) :
      YulNamesOrdinaryParses input value output

/-- Exact ordinary rejection after a successfully parsed first Yul name. -/
inductive YulNamesTailRejects (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      Remainder → Prop where
  | commaNameRejected {input rejected : Remainder}
      {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameRejected : YulNameRejects
        { input with cursor := input.cursor + 1 } rejected) :
      YulNamesTailRejects first input last tailRev rejected
  | laterRejected {input afterName rejected : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameParsed : YulNameOrdinaryParses
        { input with cursor := input.cursor + 1 } name afterName)
      (tailRejected : YulNamesTailRejects first afterName name
        (name :: tailRev) rejected) :
      YulNamesTailRejects first input last tailRev rejected

/-- Exact binary rejection of the public nonempty Yul name sequence. -/
inductive YulNamesRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : YulNameRejects input rejected) :
      YulNamesRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.YulIdentifier}
      (firstParsed : YulNameOrdinaryParses input first afterFirst)
      (tailRejected : YulNamesTailRejects first afterFirst first [] rejected) :
      YulNamesRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
