import Solcore.Syntax.DeclarativeCoreBlockRejectionTraceProperties
import Solcore.Syntax.DeclarativeIsolatedBlockTraceProperties

/-! Joint exactness of raw and isolated Core block traces. The only abstract
premises concern statement outcomes at the explicit source and byte boundary.
No premise asserts that an outcome exists or that a concrete parser implements it. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact statement outcomes at one source/window context, including complete
event lists and the report that remains uncommitted on ordinary rejection. -/
structure StatementTraceExactOutcomeSpec
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (statementRejects : SourceId → Nat → Remainder → Remainder →
      ParseDiagnostic → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) : Prop where
  successResultUnique : ∀ {input left right afterLeft afterRight leftTrace rightTrace},
    statementTrace source endByte input left afterLeft leftTrace →
    statementTrace source endByte input right afterRight rightTrace →
      left = right ∧ afterLeft = afterRight ∧ leftTrace = rightTrace
  rejectResultUnique : ∀ {input afterLeft afterRight leftReport rightReport leftTrace rightTrace},
    statementRejects source endByte input afterLeft leftReport leftTrace →
    statementRejects source endByte input afterRight rightReport rightTrace →
      afterLeft = afterRight ∧ leftReport = rightReport ∧ leftTrace = rightTrace
  successRejectDisjoint : ∀ {input rejected diagnostic trace},
    statementRejects source endByte input rejected diagnostic trace →
      ¬ ∃ statement output events, statementTrace source endByte input statement output events

variable
  {statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
    Remainder → List ParseDiagnostic → Prop}
  {statementRejects : SourceId → Nat → Remainder → Remainder →
    ParseDiagnostic → List ParseDiagnostic → Prop}
  {source : SourceId} {endByte : Nat}

/-- Statement exactness determines raw block ASTs, remainders, reports, and
traces under either tail policy, including rejecting paths with no validation. -/
theorem coreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (statements : StatementTraceExactOutcomeSpec statementTrace statementRejects source endByte) :
    BlockTraceExactOutcomeSpec (CoreBlockTraceParses statementTrace policy)
      (CoreBlockTraceRejects statementTrace statementRejects policy) source endByte where
  successResultUnique := CoreBlockTraceParses.result_unique statements.successResultUnique
  rejectResultUnique := CoreBlockTraceRejects.result_unique statements.successResultUnique
    statements.rejectResultUnique statements.successRejectDisjoint
  successRejectDisjoint := CoreBlockTraceRejects.disjoint_success statements.successResultUnique
    statements.successRejectDisjoint

/-- The same source's statement laws at every captured end byte determine
isolated blocks, including recovery to an empty body with one committed report. -/
theorem isolatedCoreBlockTraceExactOutcomeSpec (policy : CoreBlockTailPolicy)
    (statements : ∀ childEndByte,
      StatementTraceExactOutcomeSpec statementTrace statementRejects source childEndByte) :
    BlockTraceExactOutcomeSpec
      (IsolatedBlockTraceParses (CoreBlockTraceParses statementTrace policy)
        (CoreBlockTraceRejects statementTrace statementRejects policy))
      (IsolatedBlockTraceRejects (CoreBlockTraceRejects statementTrace statementRejects policy))
      source endByte :=
  isolatedBlockTraceExactOutcomeSpec (fun childEndByte =>
    coreBlockTraceExactOutcomeSpec policy (statements childEndByte))

end Solcore.Syntax.DeclarativeGrammar
