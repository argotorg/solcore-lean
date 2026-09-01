import Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryGrammar

/-!
Parser-independent ordinary outcomes at the public Core atom rewind and
recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before public atom recovery. -/
inductive ExpressionAtomBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomBoundaryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      ExpressionAtomBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      ExpressionAtomBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      ExpressionAtomBoundaryStops input
  | rightBracket {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBracket }) :
      ExpressionAtomBoundaryStops input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      ExpressionAtomBoundaryStops input
  | question {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .question }) :
      ExpressionAtomBoundaryStops input
  | colon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .colon }) :
      ExpressionAtomBoundaryStops input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      ExpressionAtomBoundaryStops input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      ExpressionAtomBoundaryStops input
  | elseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .keyword .elseKw }) :
      ExpressionAtomBoundaryStops input

/-- A Core rejection retains its failed cursor while preserving the token
carrier and active window needed for the public cursor rewind. -/
def CoreAtomRejectsWithPreservedWindow
    (coreRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, coreRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Ordinary public atom success is a direct Core success or a recovery that
starts at the original cursor after a window-preserving Core rejection. -/
inductive ExpressionAtomOrdinaryParses
    (coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | core {input output : Remainder} {expression : Syntax.Expr}
      (parsed : coreOrdinary input expression output) :
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output
  | recovered {input output : Remainder} {expression : Syntax.Expr}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ ExpressionAtomBoundaryStops input)
      (recovered : ExpressionAtomRecoveryParses input expression output) :
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output

/-- Exact public atom rejection after the Core failure is rewound. -/
inductive ExpressionAtomRejects
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (stops : ExpressionAtomBoundaryStops input) :
      ExpressionAtomRejects coreRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ ExpressionAtomBoundaryStops input)
      (recoveryRejected : ExpressionAtomRecoveryRejects input rejected) :
      ExpressionAtomRejects coreRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
