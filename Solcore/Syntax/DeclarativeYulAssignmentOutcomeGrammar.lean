import Solcore.Syntax.DeclarativeYulNameOutcomeGrammar
import Solcore.Syntax.DeclarativeYulStatementCorePriorityGrammar

/-!
Executable-independent ordinary rejection of one transactional inline-Yul
assignment attempt.

The relation retains the exact rejected remainder.  Successful name prefixes
use the ordinary name-sequence grammar because they may already have emitted a
diagnostic before a later stage rejects and the caller rewinds the attempt.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact binary rejection of a transactional inline-Yul assignment. -/
inductive YulAssignmentRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | namesRejected {input rejected : Remainder}
      (namesRejected : YulNamesRejects input rejected) :
      YulAssignmentRejects expressionRejects input rejected
  | operatorAbsent {input afterNames : Remainder}
      {names : YulNamesOrdinaryValue}
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorAbsent : TokenKindAbsentAt afterNames.tokens
        afterNames.endIndex afterNames.cursor (.symbol .colonEqual)) :
      YulAssignmentRejects expressionRejects input afterNames
  | expressionRejected
      {input afterNames afterOperator rejected : Remainder}
      {names : YulNamesOrdinaryValue}
      (operatorSpan : SourceSpan)
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueRejected : expressionRejects afterOperator rejected) :
      YulAssignmentRejects expressionRejects input rejected

/-- Existential projection used by the transactional statement fallback. -/
def YulAssignmentFallbackRejects
    (expressionRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, YulAssignmentRejects expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
