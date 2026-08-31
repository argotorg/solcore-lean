import Solcore.Syntax.Parser.Statement.Control

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-!
Chumsky's statement `choice` rewinds a rejected recognized branch before trying
the final assignment-or-expression branch.  Keep that behavior explicit: the
fallback supplies the recovered statement and cursor, while the more precise
failure reached by the recognized branch supplies the sole diagnostic.
-/
private def recognizedStatementOrFallback
    (primary fallback : Parser Statement) : Parser Statement := fun state =>
  match primary state with
  | .ok value next => .ok value next
  | .reject failure _ =>
      match fallback state with
      | .ok value next =>
          let reset := { next with diagnosticsRev := state.diagnosticsRev }
          .ok value (reset.emit failure.toDiagnostic)
      | .reject _ _ => .reject failure state
      | .invariant error => .invariant error
  | .invariant error => .invariant error

private def statementLayer (nestedStatement : Parser Statement)
    (expression : Parser Expr) (pattern : Parser Pattern) : Parser Statement :=
    fun state =>
  let fallback := assignmentOrExpressionStatement expression
  if isKeyword state .letKw then
    recognizedStatementOrFallback (letStatement expression) fallback state
  else if isKeyword state .returnKw then
    recognizedStatementOrFallback (returnStatement expression) fallback state
  else if isKeyword state .matchKw then
    recognizedStatementOrFallback
      (matchStatement nestedStatement expression pattern) fallback state
  else if isKeyword state .forKw then
    recognizedStatementOrFallback
      (forStatement nestedStatement expression) fallback state
  else if isContextual state .while then
    recognizedStatementOrFallback
      (whileStatement nestedStatement expression) fallback state
  else if isKeyword state .ifKw then
    recognizedStatementOrFallback
      (ifStatement nestedStatement expression) fallback state
  else if isKeyword state .assemblyKw then
    recognizedStatementOrFallback assemblyStatement fallback state
  else if isSymbol state .leftBrace then
    recognizedStatementOrFallback
      (blockStatement nestedStatement) fallback state
  else if isKeyword state .breakKw then
    recognizedStatementOrFallback breakStatement fallback state
  else if isKeyword state .continueKw then
    recognizedStatementOrFallback continueStatement fallback state
  else fallback state

namespace TermInternals

mutual

def coreExpressionWithFuel : Nat → Parser Expr
  | 0 => fun state =>
      .invariant (.fuelExhausted .expression state.currentSpan)
  | fuel + 1 => expressionLayer
      (coreExpressionWithFuel fuel)
      (isolateBlock (coreBlock (coreStatementWithFuel fuel) .require))

def corePatternWithFuel : Nat → Parser Pattern
  | 0 => fun state =>
      .invariant (.fuelExhausted .pattern state.currentSpan)
  | fuel + 1 => patternLayer
      (corePatternWithFuel fuel)
      (coreExpressionWithFuel fuel)

def coreStatementWithFuel : Nat → Parser Statement
  | 0 => fun state =>
      .invariant (.fuelExhausted .statement state.currentSpan)
  | fuel + 1 => statementLayer
      (coreStatementWithFuel fuel)
      (coreExpressionWithFuel fuel)
      (corePatternWithFuel fuel)

end

end TermInternals

/-- Parse one complete canonical Core expression. -/
def expression : Parser Expr := fun state =>
  TermInternals.coreExpressionWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core pattern. -/
def pattern : Parser Pattern := fun state =>
  TermInternals.corePatternWithFuel (state.remainingCount + 1) state

/-- Parse one complete canonical Core statement. -/
def statement : Parser Statement := fun state =>
  TermInternals.coreStatementWithFuel (state.remainingCount + 1) state

/-- Parse one canonical Core block with an explicit root-tail policy. -/
def block (policy : TailExpressionPolicy) : Parser Block := fun state =>
  coreBlock
    (TermInternals.coreStatementWithFuel (state.remainingCount + 1))
    policy state

end Solcore.Syntax.Parser
