import Solcore.Syntax.DeclarativeYulExpressionLeafGrammar

/-!
Parser-independent grammar for nonempty, non-trailing inline-Yul name
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming result assembled by `finishYulNames`. -/
inductive FinishYulNamesParses
    (first last : Syntax.YulIdentifier) (tailRev : List Syntax.YulIdentifier) :
    Remainder → SourceSpan → NonemptyList Syntax.YulIdentifier →
      Remainder → Prop where
  | parsed {input : Remainder} :
      FinishYulNamesParses first last tailRev input
        (SourceSpan.cover first.span last.span) {
          head := first
          tail := tailRev.reverse
        } input

/-- Exact comma-prioritized tail of a Yul name sequence.

There is no trailing-comma constructor: after a comma, another strict
`YulNameParses` transition is required before recursion can continue.
-/
inductive YulNamesTailParses (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      SourceSpan → NonemptyList Syntax.YulIdentifier → Remainder →
        Prop where
  | done {input : Remainder} {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      {output : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma))
      (finished : FinishYulNamesParses first last tailRev input span names
        output) :
      YulNamesTailParses first input last tailRev span names output
  | next {input afterComma afterName output : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nameParsed : YulNameParses afterComma name afterName)
      (progress : afterComma.cursor < afterName.cursor)
      (tail : YulNamesTailParses first afterName name (name :: tailRev)
        span names output) :
      YulNamesTailParses first input last tailRev span names output

/-- Exact public grammar of one nonempty Yul name sequence. -/
inductive YulNamesParses :
    Remainder → SourceSpan → NonemptyList Syntax.YulIdentifier →
      Remainder → Prop where
  | parsed {input afterFirst output : Remainder}
      {first : Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      (firstParsed : YulNameParses input first afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tail : YulNamesTailParses first afterFirst first [] span names output) :
      YulNamesParses input span names output

end Solcore.Syntax.DeclarativeGrammar
