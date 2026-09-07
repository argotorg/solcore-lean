import Solcore.Syntax.DeclarativeCoreStatementControlLeafOutcomeGrammar
import Solcore.Syntax.DeclarativeRejectionDiagnosticGrammar

/-! Independent exact traces for keyword-plus-semicolon control statements.
Both success and rejection are silent; the first missing token fixes the report. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed control statement retains both exact tokens and emits no event.
Context parameters permit direct composition with other statement traces. -/
def TerminatedControlStatementTraceParses (keyword : HardKeyword)
    (statementValue : Syntax.StatementValue) (_source : SourceId) (_endByte : Nat)
    (input : Remainder) (statement : Syntax.Statement) (output : Remainder)
    (trace : List ParseDiagnostic) : Prop :=
  TerminatedControlStatementOrdinaryParses keyword statementValue input statement output ∧ trace = []

/-- Keyword rejection takes priority; semicolon rejection requires the exact
successful keyword. The final report is uncommitted, so the trace remains empty. -/
inductive TerminatedControlStatementTraceRejects (keyword : HardKeyword)
    (source : SourceId) (endByte : Nat) :
    Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop where
  | markerMissing {input : Remainder} {diagnostic : ParseDiagnostic}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword keyword))
      (reported : RejectAtReports source endByte { head := .keyword keyword, tail := [] }
        .statement input diagnostic) :
      TerminatedControlStatementTraceRejects keyword source endByte input input diagnostic []
  | semicolonMissing {input afterMarker : Remainder} {diagnostic : ParseDiagnostic}
      (markerSpan : SourceSpan)
      (marker : ExactTokenParses (.keyword keyword) input markerSpan afterMarker)
      (absent : TokenKindAbsentAt afterMarker.tokens afterMarker.endIndex
        afterMarker.cursor (.symbol .semicolon))
      (reported : RejectAtReports source endByte { head := .symbol .semicolon, tail := [] }
        .statement afterMarker diagnostic) :
      TerminatedControlStatementTraceRejects keyword source endByte input afterMarker diagnostic []

abbrev BreakStatementTraceParses := TerminatedControlStatementTraceParses .breakKw .breakStmt
abbrev ContinueStatementTraceParses := TerminatedControlStatementTraceParses .continueKw .continueStmt
abbrev BreakStatementTraceRejects := TerminatedControlStatementTraceRejects .breakKw
abbrev ContinueStatementTraceRejects := TerminatedControlStatementTraceRejects .continueKw

end Solcore.Syntax.DeclarativeGrammar
