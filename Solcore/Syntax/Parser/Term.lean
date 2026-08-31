import Solcore.Syntax.Parser.Statement.Control

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def statementLayer (nestedStatement : Parser Statement)
    (expression : Parser Expr) (pattern : Parser Pattern) : Parser Statement :=
    fun state =>
  if isKeyword state .letKw then letStatement expression state
  else if isKeyword state .returnKw then returnStatement expression state
  else if isKeyword state .matchKw then
    matchStatement nestedStatement expression pattern state
  else if isKeyword state .forKw then
    forStatement nestedStatement expression state
  else if isContextual state .while then
    whileStatement nestedStatement expression state
  else if isKeyword state .ifKw then
    ifStatement nestedStatement expression state
  else if isKeyword state .assemblyKw then assemblyStatement state
  else if isSymbol state .leftBrace then blockStatement nestedStatement state
  else if isKeyword state .breakKw then breakStatement state
  else if isKeyword state .continueKw then continueStatement state
  else assignmentOrExpressionStatement expression state

mutual

private def coreExpressionWithFuel : Nat → Parser Expr
  | 0 => fun state =>
      .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1 => expressionLayer
      (coreExpressionWithFuel fuel)
      (isolateBlock (coreBlock (coreStatementWithFuel fuel) .require))

private def corePatternWithFuel : Nat → Parser Pattern
  | 0 => fun state =>
      .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1 => patternLayer
      (corePatternWithFuel fuel)
      (coreExpressionWithFuel fuel)

private def coreStatementWithFuel : Nat → Parser Statement
  | 0 => fun state =>
      .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1 => statementLayer
      (coreStatementWithFuel fuel)
      (coreExpressionWithFuel fuel)
      (corePatternWithFuel fuel)

end

/-- Parse one complete canonical Core expression. -/
def expression : Parser Expr := fun state =>
  coreExpressionWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core pattern. -/
def pattern : Parser Pattern := fun state =>
  corePatternWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core statement. -/
def statement : Parser Statement := fun state =>
  coreStatementWithFuel (state.remainingCount + 1) state

/-- Parse one canonical Core block with an explicit root-tail policy. -/
def block (policy : TailExpressionPolicy) : Parser Block := fun state =>
  coreBlock (coreStatementWithFuel (state.remainingCount + 1)) policy state

end Solcore.Syntax.Parser
