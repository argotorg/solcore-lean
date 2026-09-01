import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreStatementControlGrammar

/-! Ordinary outcomes for Core block and terminated-control statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev TerminatedControlStatementOrdinaryParses :=
  TerminatedControlStatementParses

/-- Exact marker or semicolon rejection of `break` and `continue`. -/
inductive TerminatedControlStatementRejects (keyword : HardKeyword) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword keyword)) :
      TerminatedControlStatementRejects keyword input input
  | semicolonMissing {input afterMarker : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        afterMarker)
      (semicolonAbsent : TokenKindAbsentAt afterMarker.tokens
        afterMarker.endIndex afterMarker.cursor (.symbol .semicolon)) :
      TerminatedControlStatementRejects keyword input afterMarker

/-- Diagnostic-inclusive block statement success. -/
abbrev BlockStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop) :=
  BlockStatementParses
    (CoreBlockOrdinaryParses statementOrdinary .require)

/-- Exact raw-block rejection propagated through `blockStatement`. -/
abbrev BlockStatementRejects
    (statementOrdinary : Remainder → Syntax.Statement → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :=
  CoreBlockRejects statementOrdinary statementRejects .require

end Solcore.Syntax.DeclarativeGrammar
