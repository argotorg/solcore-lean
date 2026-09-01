import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent grammar for keyword-only Yul statements and optional
statement semicolons.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One keyword-only inline-Yul control statement. -/
inductive YulControlTokenParses
    (keyword : HardKeyword) (statementValue : Syntax.YulStmtValue) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        output) :
      YulControlTokenParses keyword statementValue input {
        span := markerSpan
        value := statementValue
      } output

/-- Prioritized optional semicolon after an already parsed Yul statement. -/
inductive OptionalYulSemicolonParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | absent {input : Remainder} {value : Syntax.YulStmt}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      OptionalYulSemicolonParses input value input
  | present {input output : Remainder} {value : Syntax.YulStmt}
      (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      OptionalYulSemicolonParses input value output

/-- One supplied non-terminating Yul statement followed by its maximal
optional semicolon. -/
def YulStatementTerminatedParses
    (coreParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (input : Remainder) (value : Syntax.YulStmt)
    (output : Remainder) : Prop :=
  ∃ afterCore,
    coreParses input value afterCore ∧
    OptionalYulSemicolonParses afterCore value output

end Solcore.Syntax.DeclarativeGrammar
