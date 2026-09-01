import Solcore.Syntax.DeclarativeYulNamesGrammar

/-!
Parser-independent grammar for the basic inline-Yul statement forms.

The grammar is parameterized by the public inline-Yul expression relation.
It retains the optional `:=` priority of `let`, the nonempty target sequence
of assignment, and the allow-empty/trailing-comma argument grammar of the
source-level `return(...)` builtin.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized optional initializer of an inline-Yul `let`. -/
inductive YulLetInitializerParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Option Syntax.YulExpr → Remainder → Prop where
  | absent {input : Remainder}
      (operatorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .colonEqual)) :
      YulLetInitializerParses expressionParses input none input
  | present {input afterOperator output : Remainder}
      {value : Syntax.YulExpr} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueParsed : expressionParses afterOperator value output) :
      YulLetInitializerParses expressionParses input (some value) output

/-- Final span selected for an inline-Yul `let`. -/
def yulLetEnd (namesSpan : SourceSpan)
    (initializer : Option Syntax.YulExpr) : SourceSpan :=
  initializer.map (fun value => value.span) |>.getD namesSpan

/-- Exact grammar of one inline-Yul `let` declaration. -/
inductive YulLetStatementParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterNames output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier}
      {initializer : Option Syntax.YulExpr}
      (markerSpan namesSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesParses afterMarker namesSpan names afterNames)
      (initializerParsed : YulLetInitializerParses expressionParses afterNames
        initializer output) :
      YulLetStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan (yulLetEnd namesSpan initializer)
        value := .letDecl names initializer
      } output

/-- Exact grammar of one nonempty inline-Yul assignment. -/
inductive YulAssignmentParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterNames afterOperator output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier} {value : Syntax.YulExpr}
      (namesSpan operatorSpan : SourceSpan)
      (namesParsed : YulNamesParses input namesSpan names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueParsed : expressionParses afterOperator value output) :
      YulAssignmentParses expressionParses input {
        span := SourceSpan.cover namesSpan value.span
        value := .assign names value
      } output

/-- Exact lifting of one inline-Yul expression into statement position. -/
inductive YulExpressionStatementParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} {expression : Syntax.YulExpr}
      (expressionParsed : expressionParses input expression output) :
      YulExpressionStatementParses expressionParses input {
        span := expression.span
        value := .expression expression
      } output

/-- Exact grammar of source-level `return(...)` as a synthesized Yul call. -/
inductive YulReturnBuiltinParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (argumentsParsed : TrailingDelimitedListParses .leftParen .rightParen
        expressionParses afterMarker arguments output) :
      YulReturnBuiltinParses expressionParses input {
        span := SourceSpan.cover markerSpan arguments.span
        value := .expression {
          span := SourceSpan.cover markerSpan arguments.span
          value := .call { span := markerSpan, value := "return" } arguments
        }
      } output

end Solcore.Syntax.DeclarativeGrammar
