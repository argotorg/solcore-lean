import Solcore.Syntax.DeclarativeYulBlockGrammar
import Solcore.Syntax.DeclarativeYulExpressionGrammar

/-!
Parser-independent grammar for inline-Yul switch arms and statements.

The case list is forward ordered and maximal at the first token that is not
`case`.  The optional default branch records the parser's keyword priority.
Only the diagnostic-free, nonempty switch result has a statement constructor.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of one `case literal { ... }` arm. -/
inductive YulCaseArmParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulCase → Remainder → Prop where
  | parsed {input afterMarker afterLiteral output : Remainder}
      {literal : Syntax.YulLiteral} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalParsed : YulLiteralParses afterMarker literal afterLiteral)
      (bodyParsed : YulBlockParses statementParses afterLiteral bodySpan body
        output) :
      YulCaseArmParses statementParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .arm literal body
      } output

/-- Forward, maximal sequence of switch cases. -/
inductive YulCaseListParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → List Syntax.YulCase → Remainder → Prop where
  | done {input : Remainder}
      (caseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .caseKw)) :
      YulCaseListParses statementParses input [] input
  | next {input afterArm output : Remainder} {arm : Syntax.YulCase}
      {arms : List Syntax.YulCase}
      (armParsed : YulCaseArmParses statementParses input arm afterArm)
      (progress : input.cursor < afterArm.cursor)
      (tail : YulCaseListParses statementParses afterArm arms output) :
      YulCaseListParses statementParses input (arm :: arms) output

/-- Prioritized optional `default { ... }` branch.

The two optional indices stay aligned: both are absent, or both contain the
span and forward body of the same parsed block.
-/
inductive OptionalYulDefaultParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Option SourceSpan → Option (List Syntax.YulStmt) →
      Remainder → Prop where
  | absent {input : Remainder}
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalYulDefaultParses statementParses input none none input
  | present {input afterMarker output : Remainder}
      {body : List Syntax.YulStmt} (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyParsed : YulBlockParses statementParses afterMarker bodySpan body
        output) :
      OptionalYulDefaultParses statementParses input (some bodySpan)
        (some body) output

/-- Endpoint selection performed by the executable switch parser. -/
def yulSwitchEnd (scrutineeSpan : SourceSpan) (cases : List Syntax.YulCase)
    (defaultSpan : Option SourceSpan) : SourceSpan :=
  match defaultSpan with
  | some bodySpan => bodySpan
  | none => match cases.reverse with
    | last :: _ => last.span
    | [] => scrutineeSpan

/-- Exact diagnostic-free grammar of a nonempty inline-Yul switch. -/
inductive YulSwitchStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {head : Syntax.YulCase}
      {tail : List Syntax.YulCase} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : expressionParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListParses statementParses afterScrutinee
        (head :: tail) afterCases)
      (defaultParsed : OptionalYulDefaultParses statementParses afterCases
        defaultSpan defaultBody output) :
      YulSwitchStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span (head :: tail) defaultSpan)
        value := .switch scrutinee { head, tail } defaultBody
      } output

end Solcore.Syntax.DeclarativeGrammar
