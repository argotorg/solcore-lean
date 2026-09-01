import Solcore.Syntax.DeclarativeCoreAssemblyStatementOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreAssignmentStatementOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreForStatementOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreMatchStatementOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementIfOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementLayerSelectionOutcomeProperties
import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementWhileOutcomeGrammar

/-! Concrete ordinary relations for the ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive success relation selected for each recognized Core
statement stage.  The final stage has no primary parser. -/
def StatementLayerPrimaryOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    StatementLayerStage → Remainder → Syntax.Statement → Remainder → Prop
  | .letGuard => LetStatementOrdinaryParses expressionOrdinary
  | .returnGuard => ReturnStatementOrdinaryParses expressionOrdinary
  | .matchGuard => MatchStatementOrdinaryParses statementOrdinary
      expressionOrdinary patternOrdinary
  | .forGuard => ForStatementOrdinaryParses statementOrdinary
      expressionOrdinary
  | .whileGuard => WhileStatementOrdinaryParses expressionOrdinary
      statementOrdinary
  | .ifGuard => IfStatementOrdinaryParses expressionOrdinary
      statementOrdinary
  | .assemblyGuard => AssemblyStatementOrdinaryParses
  | .blockGuard => BlockStatementOrdinaryParses statementOrdinary
  | .breakGuard => TerminatedControlStatementOrdinaryParses .breakKw
      .breakStmt
  | .continueGuard => TerminatedControlStatementOrdinaryParses .continueKw
      .continueStmt
  | .fallback => fun _ _ _ => False

/-- Exact rejection relation selected for each recognized Core statement
stage.  The final stage has no primary parser. -/
def StatementLayerPrimaryRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :
    StatementLayerStage → Remainder → Remainder → Prop
  | .letGuard => LetStatementRejects expressionOrdinary expressionRejects
      TypeExprRejects
  | .returnGuard => ReturnStatementRejects expressionOrdinary
      expressionRejects
  | .matchGuard => MatchStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects
  | .forGuard => ForStatementRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects
  | .whileGuard => WhileStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects
  | .ifGuard => IfStatementRejects expressionOrdinary expressionRejects
      statementOrdinary statementRejects
  | .assemblyGuard => AssemblyStatementRejects
  | .blockGuard => BlockStatementRejects statementOrdinary statementRejects
  | .breakGuard => TerminatedControlStatementRejects .breakKw
  | .continueGuard => TerminatedControlStatementRejects .continueKw
  | .fallback => fun _ _ => False

/-- Concrete ordinary success of one prioritized Core statement layer. -/
abbrev StatementLayerOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :=
  StatementLayerSelectionOrdinaryParses
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementOrdinaryParses expressionOrdinary)

/-- Concrete exact rejection of one prioritized Core statement layer. -/
abbrev StatementLayerRejects
    (statementOrdinary :
      Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (patternOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (patternRejects : Remainder → Remainder → Prop) :=
  StatementLayerSelectionRejects
    (StatementLayerPrimaryOrdinaryParses statementOrdinary expressionOrdinary
      patternOrdinary)
    (StatementLayerPrimaryRejects statementOrdinary statementRejects
      expressionOrdinary expressionRejects patternOrdinary patternRejects)
    (AssignmentOrExpressionStatementRejects expressionOrdinary
      expressionRejects)

end Solcore.Syntax.DeclarativeGrammar
