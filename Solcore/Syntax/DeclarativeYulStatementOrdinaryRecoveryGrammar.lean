import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Parser-independent ordinary outcomes for the outer recovering Yul-statement
layer.  The terminated core relations remain abstract so their recursive
outcomes can be supplied by one preceding fuel level.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming rejection boundary of one Yul statement layer. -/
inductive YulStatementRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      YulStatementRejects input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightBrace
      }) :
      YulStatementRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      YulStatementRejects input input

/-- Exact scan performed after statement recovery consumes its first token. -/
inductive YulStatementRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.YulStmt → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : YulStatementRejects input input) :
      YulStatementRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {statement : Syntax.YulStmt}
      (continues : ¬ YulStatementRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : YulStatementRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } statement output) :
      YulStatementRecoveryScanParses first last input statement output

/-- Ordinary success of one outer recovering statement layer.

The rejected remainder of the terminated attempt is retained as evidence even
though the executable layer rewinds its cursor before starting recovery.
-/
inductive YulStatementLayerOrdinaryParses
    (terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (terminatedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | terminated {input output : Remainder} {statement : Syntax.YulStmt}
      (parsed : terminatedOrdinary input statement output) :
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output
  | recovered {input failed output : Remainder} {token : Token}
      {statement : Syntax.YulStmt}
      (terminatedRejected : terminatedRejects input failed)
      (continues : ¬ YulStatementRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : YulStatementRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } statement output) :
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output

end Solcore.Syntax.DeclarativeGrammar
