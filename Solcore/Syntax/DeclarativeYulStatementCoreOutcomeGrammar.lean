import Solcore.Syntax.DeclarativeTransactionalFallbackOutcomeProperties
import Solcore.Syntax.DeclarativeYulBlockStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulFunctionOutcomeProperties
import Solcore.Syntax.DeclarativeYulLetOrdinaryOutcomeProperties
import Solcore.Syntax.DeclarativeYulNameStatementOutcomeProperties
import Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties
import Solcore.Syntax.DeclarativeYulSwitchOutcomeProperties

/-!
Parser-independent ordinary successes and exact rejections for the prioritized
inline-Yul statement-core dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- An exact current token-kind selected by a statement-core guard. -/
def YulStatementCoreTokenAt (input : Remainder) (kind : TokenKind) : Prop :=
  ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := kind }

/-- Positive evidence for the executable guard at one dispatcher stage. -/
def YulStatementCoreGuardAt (input : Remainder) :
    YulStatementCoreStage → Prop
  | .blockGuard => YulStatementCoreTokenAt input (.symbol .leftBrace)
  | .letGuard => YulStatementCoreTokenAt input (.keyword .letKw)
  | .ifGuard => YulStatementCoreTokenAt input (.keyword .ifKw)
  | .forGuard => YulStatementCoreTokenAt input (.keyword .forKw)
  | .switchGuard => YulStatementCoreTokenAt input (.keyword .switchKw)
  | .functionGuard => YulStatementCoreTokenAt input (.keyword .functionKw)
  | .returnGuard => YulStatementCoreTokenAt input (.keyword .returnKw)
  | .leaveGuard => YulStatementCoreTokenAt input (.keyword .leaveKw)
  | .breakGuard => YulStatementCoreTokenAt input (.keyword .breakKw)
  | .continueGuard => YulStatementCoreTokenAt input (.keyword .continueKw)
  | .nameGuard => YulNameStartAt input
  | .fallback => True

/-- Ordinary outcome of a recognized primary and expression-statement
fallback, both run transactionally from the original remainder. -/
abbrev YulRecognizedStatementOrdinaryParses
    (primaryParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (primaryRejects : Remainder → Remainder → Prop) :=
  TransactionalFallbackOrdinaryParses primaryParses primaryRejects
    YulExpressionStatementOrdinaryParses

/-- Exact nonconsuming rejection of a recognized primary and its expression
fallback. -/
abbrev YulRecognizedStatementRejects
    (primaryRejects : Remainder → Remainder → Prop) :=
  TransactionalFallbackRejects primaryRejects
    YulExpressionStatementRejects

/-- Ordinary success of the complete prioritized statement-core dispatcher. -/
inductive YulStatementCoreOrdinaryParsesAt
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    YulStatementCoreStage → Remainder → Syntax.YulStmt → Remainder → Prop where
  | block {input output statement}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (guard : YulStatementCoreGuardAt input .blockGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulBlockStatementOrdinaryParses statementOrdinary)
        (YulBlockStatementRejects statementOrdinary statementRejects)
        input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .blockGuard input statement output
  | letDecl {input output statement}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (guard : YulStatementCoreGuardAt input .letGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        YulLetStatementOrdinaryParses YulLetStatementRejects input statement
        output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .letGuard input statement output
  | ifThen {input output statement}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (guard : YulStatementCoreGuardAt input .ifGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulIfStatementOrdinaryParses statementOrdinary)
        (YulIfStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .ifGuard input statement output
  | forLoop {input output statement}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (guard : YulStatementCoreGuardAt input .forGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulForStatementOrdinaryParses statementOrdinary)
        (YulForStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .forGuard input statement output
  | switch {input output statement}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (guard : YulStatementCoreGuardAt input .switchGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulSwitchStatementOrdinaryParses statementOrdinary)
        (YulSwitchStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .switchGuard input statement output
  | functionDef {input output statement}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (guard : YulStatementCoreGuardAt input .functionGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulFunctionStatementOrdinaryParses statementOrdinary)
        (YulFunctionStatementRejects statementOrdinary statementRejects) input
        statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .functionGuard input statement output
  | returnBuiltin {input output statement}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (guard : YulStatementCoreGuardAt input .returnGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        YulReturnBuiltinOrdinaryParses YulReturnBuiltinRejects input statement
        output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .returnGuard input statement output
  | leave {input output statement}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (guard : YulStatementCoreGuardAt input .leaveGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .leaveKw .leave)
        (YulControlTokenRejects .leaveKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .leaveGuard input statement output
  | break {input output statement}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (guard : YulStatementCoreGuardAt input .breakGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .breakKw .break)
        (YulControlTokenRejects .breakKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .breakGuard input statement output
  | continue {input output statement}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (guard : YulStatementCoreGuardAt input .continueGuard)
      (parsed : YulRecognizedStatementOrdinaryParses
        (YulControlTokenOrdinaryParses .continueKw .continue)
        (YulControlTokenRejects .continueKw) input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .continueGuard input statement output
  | nameChoice {input output statement}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (guard : YulStatementCoreGuardAt input .nameGuard)
      (parsed : YulNameStatementOrdinaryParses input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .nameGuard input statement output
  | expressionFallback {input output statement}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (parsed : YulExpressionStatementOrdinaryParses input statement output) :
      YulStatementCoreOrdinaryParsesAt statementOrdinary statementRejects
        .fallback input statement output

/-- Ordinary success at the uniquely selected statement-core stage. -/
def YulStatementCoreOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (input : Remainder) (statement : Syntax.YulStmt) (output : Remainder) :
    Prop :=
  ∃ stage, YulStatementCoreOrdinaryParsesAt statementOrdinary
    statementRejects stage input statement output

/-- Exact rejection of the uniquely selected statement-core branch. -/
inductive YulStatementCoreRejectsAt
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    YulStatementCoreStage → Remainder → Remainder → Prop where
  | block {input rejected}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (guard : YulStatementCoreGuardAt input .blockGuard)
      (rejection : YulRecognizedStatementRejects
        (YulBlockStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .blockGuard
        input rejected
  | letDecl {input rejected}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (guard : YulStatementCoreGuardAt input .letGuard)
      (rejection : YulRecognizedStatementRejects YulLetStatementRejects input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .letGuard
        input rejected
  | ifThen {input rejected}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (guard : YulStatementCoreGuardAt input .ifGuard)
      (rejection : YulRecognizedStatementRejects
        (YulIfStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .ifGuard
        input rejected
  | forLoop {input rejected}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (guard : YulStatementCoreGuardAt input .forGuard)
      (rejection : YulRecognizedStatementRejects
        (YulForStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .forGuard
        input rejected
  | switch {input rejected}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (guard : YulStatementCoreGuardAt input .switchGuard)
      (rejection : YulRecognizedStatementRejects
        (YulSwitchStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .switchGuard
        input rejected
  | functionDef {input rejected}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (guard : YulStatementCoreGuardAt input .functionGuard)
      (rejection : YulRecognizedStatementRejects
        (YulFunctionStatementRejects statementOrdinary statementRejects) input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects
        .functionGuard input rejected
  | returnBuiltin {input rejected}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (guard : YulStatementCoreGuardAt input .returnGuard)
      (rejection : YulRecognizedStatementRejects YulReturnBuiltinRejects input
        rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .returnGuard
        input rejected
  | leave {input rejected}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (guard : YulStatementCoreGuardAt input .leaveGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .leaveKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .leaveGuard
        input rejected
  | break {input rejected}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (guard : YulStatementCoreGuardAt input .breakGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .breakKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .breakGuard
        input rejected
  | continue {input rejected}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (guard : YulStatementCoreGuardAt input .continueGuard)
      (rejection : YulRecognizedStatementRejects
        (YulControlTokenRejects .continueKw) input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects
        .continueGuard input rejected
  | nameChoice {input rejected}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (guard : YulStatementCoreGuardAt input .nameGuard)
      (rejection : YulNameStatementRejects input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .nameGuard
        input rejected
  | expressionFallback {input rejected}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (rejection : YulExpressionStatementRejects input rejected) :
      YulStatementCoreRejectsAt statementOrdinary statementRejects .fallback
        input rejected

/-- Exact rejection at the uniquely selected statement-core stage. -/
def YulStatementCoreRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop)
    (input rejected : Remainder) : Prop :=
  ∃ stage, YulStatementCoreRejectsAt statementOrdinary statementRejects
    stage input rejected

end Solcore.Syntax.DeclarativeGrammar
