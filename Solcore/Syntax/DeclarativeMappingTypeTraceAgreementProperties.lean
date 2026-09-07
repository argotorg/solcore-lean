import Solcore.Syntax.DeclarativeTraceOutcomeAgreement
import Solcore.Syntax.DeclarativeMappingTypeTraceGrammar
import Solcore.Syntax.DeclarativeMappingTypeRejectionTraceGrammar
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Raw mapping outcomes agree across distinct child relations. Both child
positions use heterogeneous agreement, keeping key events before value events
and the exact first failed stage. No recursive uniqueness is assumed. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

variable
  {leftParses rightParses : SourceId → Nat → Remainder → Syntax.TypeExpr → Remainder → List ParseDiagnostic → Prop}
  {leftRejects rightRejects : SourceId → Nat → Remainder → Remainder → ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

private theorem mappingTrace_absent_conflicts_token {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : ExactTokenParses kind input span output) : False := absent ⟨span, token.1⟩

theorem mappingTypeTraceOutcomeAgreement
    (children : TraceOutcomeAgreement leftParses leftRejects rightParses rightRejects source endByte) :
    TraceOutcomeAgreement
      (MappingTypeTraceParses leftParses) (MappingTypeTraceRejects leftParses leftRejects)
      (MappingTypeTraceParses rightParses) (MappingTypeTraceRejects rightParses rightRejects) source endByte := by
  rcases children with ⟨successAgree, rejectAgree, successRejectDisjoint, rejectSuccessDisjoint⟩
  constructor
  · intro input left right afterLeft afterRight leftTrace rightTrace leftParsed rightParsed
    cases leftParsed <;> cases rightParsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique]
  · intro input afterLeft afterRight leftReport rightReport leftTrace rightTrace leftRejected rightRejected
    cases leftRejected <;> cases rightRejected <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token,
        RejectAtReports.diagnostic_unique]
  · intro input value output events rejected report trace parsed rejection
    cases parsed <;> cases rejection <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token]
  · intro input rejected report trace value output events rejection parsed
    cases rejection <;> cases parsed <;>
      grind (ematch := 12) only [ExactTokenParses.result_unique, mappingTrace_absent_conflicts_token]

end Solcore.Syntax.DeclarativeGrammar
