import Solcore.Syntax.DeclarativeCoreAssemblyStatementGrammar
import Solcore.Syntax.DeclarativeCoreForStatementGrammar
import Solcore.Syntax.DeclarativeCoreMatchStatementGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlGrammar
import Solcore.Syntax.DeclarativeCoreStatementSimpleGrammar

/-! Exact parser-independent grammar for one ordered Core statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordered decision points in the executable Core statement dispatcher. -/
inductive StatementLayerStage where
  | letGuard
  | returnGuard
  | matchGuard
  | forGuard
  | whileGuard
  | ifGuard
  | assemblyGuard
  | blockGuard
  | breakGuard
  | continueGuard
  | fallback

/--
Evidence that every guard before the indexed dispatcher stage is absent.
Each transition adds exactly the token-kind absence checked by the executable
lookahead chain.
-/
inductive StatementLayerPrefixAbsent (input : Remainder) :
    StatementLayerStage → Prop where
  | start : StatementLayerPrefixAbsent input .letGuard
  | afterLet
      (prior : StatementLayerPrefixAbsent input .letGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw)) :
      StatementLayerPrefixAbsent input .returnGuard
  | afterReturn
      (prior : StatementLayerPrefixAbsent input .returnGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .returnKw)) :
      StatementLayerPrefixAbsent input .matchGuard
  | afterMatch
      (prior : StatementLayerPrefixAbsent input .matchGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .matchKw)) :
      StatementLayerPrefixAbsent input .forGuard
  | afterFor
      (prior : StatementLayerPrefixAbsent input .forGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .forKw)) :
      StatementLayerPrefixAbsent input .whileGuard
  | afterWhile
      (prior : StatementLayerPrefixAbsent input .whileGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.identifier ContextualKeyword.while.spelling)) :
      StatementLayerPrefixAbsent input .ifGuard
  | afterIf
      (prior : StatementLayerPrefixAbsent input .ifGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .ifKw)) :
      StatementLayerPrefixAbsent input .assemblyGuard
  | afterAssembly
      (prior : StatementLayerPrefixAbsent input .assemblyGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .assemblyKw)) :
      StatementLayerPrefixAbsent input .blockGuard
  | afterBlock
      (prior : StatementLayerPrefixAbsent input .blockGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBrace)) :
      StatementLayerPrefixAbsent input .breakGuard
  | afterBreak
      (prior : StatementLayerPrefixAbsent input .breakGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .breakKw)) :
      StatementLayerPrefixAbsent input .continueGuard
  | afterContinue
      (prior : StatementLayerPrefixAbsent input .continueGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .continueKw)) :
      StatementLayerPrefixAbsent input .fallback

/-- Exact clean grammar for the complete prioritized statement dispatcher. -/
inductive StatementLayerParses
    (statementParses : Remainder → Syntax.Statement → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (patternParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (yulBodyParses : Remainder → SourceSpan → List Syntax.YulStmt →
      Remainder → Prop) :
    Remainder → Syntax.Statement → Remainder → Prop where
  | letBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .letGuard)
      (parsed : LetStatementParses expressionParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | returnBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .returnGuard)
      (parsed : ReturnStatementParses expressionParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | matchBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .matchGuard)
      (parsed : MatchStatementParses statementParses expressionParses
        patternParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | forBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .forGuard)
      (parsed : ForStatementParses statementParses expressionParses input value
        output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | whileBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .whileGuard)
      (parsed : WhileStatementParses expressionParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | ifBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .ifGuard)
      (parsed : IfStatementParses expressionParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | assemblyBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .assemblyGuard)
      (parsed : AssemblyStatementParses yulBodyParses input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | blockBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .blockGuard)
      (parsed : BlockStatementParses
        (CoreBlockParses statementParses .require) input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | breakBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .breakGuard)
      (parsed : TerminatedControlStatementParses .breakKw .breakStmt input
        value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | continueBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .continueGuard)
      (parsed : TerminatedControlStatementParses .continueKw .continueStmt
        input value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output
  | fallbackBranch {input output} {value : Syntax.Statement}
      (priority : StatementLayerPrefixAbsent input .fallback)
      (parsed : AssignmentOrExpressionStatementParses expressionParses input
        value output) :
      StatementLayerParses statementParses expressionParses patternParses
        yulBodyParses input value output

end Solcore.Syntax.DeclarativeGrammar
