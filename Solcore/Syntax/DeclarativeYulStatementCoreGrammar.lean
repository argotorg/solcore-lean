import Solcore.Syntax.DeclarativeCoreYulStatementBasicGrammar
import Solcore.Syntax.DeclarativeYulFunctionGrammar
import Solcore.Syntax.DeclarativeYulStatementControlGrammar
import Solcore.Syntax.DeclarativeYulStatementCorePriorityGrammar
import Solcore.Syntax.DeclarativeYulSwitchGrammar

/-! Exact parser-independent grammar for the public Yul statement layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact outcomes of the transactional name-start assignment choice. -/
inductive YulNameStatementChoiceParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | assignment {input output : Remainder} {value : Syntax.YulStmt}
      (nameStart : YulNameStartAt input)
      (parsed : YulAssignmentParses expressionParses input value output) :
      YulNameStatementChoiceParses expressionParses fallback input value output
  | rewound {input output : Remainder} {value : Syntax.YulStmt}
      (nameStart : YulNameStartAt input)
      (assignmentRejected : fallback.rejects input)
      (parsed : YulExpressionStatementParses expressionParses input value
        output) :
      YulNameStatementChoiceParses expressionParses fallback input value output

/-- Exact clean grammar of the complete ordered `yulStatementCore`. -/
inductive YulStatementCoreParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | block {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (parsed : YulBlockStatementParses statementParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | letDecl {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (parsed : YulLetStatementParses expressionParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | ifThen {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (parsed : YulIfStatementParses statementParses expressionParses input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | forLoop {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (parsed : YulForStatementParses statementParses expressionParses input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | switch {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (parsed : YulSwitchStatementParses statementParses expressionParses
        input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | functionDef {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (parsed : YulFunctionStatementParses statementParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | returnBuiltin {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (parsed : YulReturnBuiltinParses expressionParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | leave {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (parsed : YulControlTokenParses .leaveKw .leave input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | break {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (parsed : YulControlTokenParses .breakKw .break input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | continue {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (parsed : YulControlTokenParses .continueKw .continue input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | nameChoice {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (parsed : YulNameStatementChoiceParses expressionParses fallback input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | expressionFallback {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (parsed : YulExpressionStatementParses expressionParses input value
        output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output

/-- One exact core statement followed by its maximal optional semicolon. -/
def YulStatementTerminatedLayerParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :=
  YulStatementTerminatedParses
    (YulStatementCoreParses statementParses expressionParses fallback)

/-- Clean recovery-layer success is exactly an unchanged terminated success. -/
abbrev YulStatementLayerParses := YulStatementTerminatedLayerParses

end Solcore.Syntax.DeclarativeGrammar
