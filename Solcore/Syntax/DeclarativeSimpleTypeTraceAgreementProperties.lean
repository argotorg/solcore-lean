import Solcore.Syntax.DeclarativeTraceOutcomeAgreement
import Solcore.Syntax.DeclarativeProxyTypeTraceGrammar
import Solcore.Syntax.DeclarativeProxyTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeTraceGrammar
import Solcore.Syntax.DeclarativeComptimeTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Heterogeneous child agreement lifts through raw proxy and comptime types.
All comparisons are directly between the two child relations. No same-relation
type uniqueness, recursive existence, progress, or carrier law is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem simpleTrace_absent_conflicts_token {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

theorem proxyTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement (ProxyTypeTraceParses leftParses) (ProxyTypeTraceRejects leftRejects)
      (ProxyTypeTraceParses rightParses) (ProxyTypeTraceRejects rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]

/-- Marker, opening, child, and closing failures retain their first-failure
order on both sides. The child trace is the only emitted event sequence. -/
theorem comptimeTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement
      (ComptimeTypeTraceParses leftParses) (ComptimeTypeTraceRejects leftParses leftRejects)
      (ComptimeTypeTraceParses rightParses) (ComptimeTypeTraceRejects rightParses rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, simpleTrace_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
