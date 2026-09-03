import Solcore.Syntax.DeclarativePragmaItemsRejectionTraceGrammar
import Solcore.Syntax.DeclarativePragmaTraceProperties
import Solcore.Syntax.DeclarativeRejectionDiagnosticProperties

/-! Prefix erasure and exact functionality for rejected pragma item traces. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prefix refinement preserves the established rejecting tail grammar. -/
theorem PragmaItemsTailRejectedPrefix.ordinary
    {input rejected : Remainder} {consumed : List Syntax.Identifier}
    (parsed : PragmaItemsTailRejectedPrefix input consumed rejected) :
    PragmaItemsTailRejects input rejected := by
  induction parsed with
  | identifierRejected span comma absent rejected =>
      exact .identifierRejected span ⟨span, comma.1⟩ comma absent rejected
  | laterRejected span comma absent item tail ih =>
      exact .laterRejected span ⟨span, comma.1⟩ comma absent item ih

/-- Every established tail rejection has its independently retained prefix. -/
theorem PragmaItemsTailRejects.exists_prefix
    {input rejected : Remainder} (rejection : PragmaItemsTailRejects input rejected) :
    ∃ consumed, PragmaItemsTailRejectedPrefix input consumed rejected := by
  induction rejection with
  | identifierRejected span _ comma absent rejected =>
      exact ⟨[], .identifierRejected span comma absent rejected⟩
  | laterRejected span _ comma absent item tail ih =>
      rcases ih with ⟨consumed, rejected⟩
      exact ⟨_, .laterRejected span comma absent item rejected⟩

/-- Complete prefix refinement erases to the established item rejection. -/
theorem PragmaItemsRejectedPrefix.ordinary
    {input rejected : Remainder} {consumed : List Syntax.Identifier}
    (parsed : PragmaItemsRejectedPrefix input consumed rejected) :
    PragmaItemsRejects input rejected := by
  cases parsed with
  | firstIdentifierRejected absent rejected => exact .firstIdentifierRejected absent rejected
  | tailRejected absent first tail => exact .tailRejected absent first tail.ordinary

/-- Every established item rejection has a successful-prefix refinement. -/
theorem PragmaItemsRejects.exists_prefix
    {input rejected : Remainder} (rejection : PragmaItemsRejects input rejected) :
    ∃ consumed, PragmaItemsRejectedPrefix input consumed rejected := by
  cases rejection with
  | firstIdentifierRejected absent rejected =>
      exact ⟨[], .firstIdentifierRejected absent rejected⟩
  | tailRejected absent first tail =>
      rcases tail.exists_prefix with ⟨consumed, rejected⟩
      exact ⟨_, .tailRejected absent first rejected⟩

/-- The rejected tail determines every prior name and the final remainder. -/
theorem PragmaItemsTailRejectedPrefix.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    (leftParsed : PragmaItemsTailRejectedPrefix input left afterLeft)
    (rightParsed : PragmaItemsTailRejectedPrefix input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have endpoint := pragmaItemsTailExactOutcomeSpec.rejectOutputUnique
    leftParsed.ordinary rightParsed.ordinary
  refine ⟨?_, endpoint⟩
  induction leftParsed generalizing right afterRight with
  | identifierRejected span comma absent rejected =>
      cases rightParsed with
      | identifierRejected => rfl
      | laterRejected rightSpan rightComma rightAbsent rightItem rightTail =>
          have same := comma.output_unique rightComma
          cases same
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rejected
            ⟨_, _, rightItem⟩)
  | laterRejected span comma absent item tail ih =>
      cases rightParsed with
      | identifierRejected rightSpan rightComma rightAbsent rightRejected =>
          have same := comma.output_unique rightComma
          cases same
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightRejected
            ⟨_, _, item⟩)
      | laterRejected rightSpan rightComma rightAbsent rightItem rightTail =>
          have same := comma.output_unique rightComma
          cases same
          rcases item.result_unique rightItem with ⟨rfl, rfl⟩
          have tailEq := ih rightTail endpoint
          rw [tailEq]

/-- Full item rejection uniquely fixes its hidden successful prefix. -/
theorem PragmaItemsRejectedPrefix.result_unique
    {input afterLeft afterRight : Remainder} {left right : List Syntax.Identifier}
    (leftParsed : PragmaItemsRejectedPrefix input left afterLeft)
    (rightParsed : PragmaItemsRejectedPrefix input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  have endpoint := pragmaItemsExactOutcomeSpec.rejectOutputUnique
    leftParsed.ordinary rightParsed.ordinary
  refine ⟨?_, endpoint⟩
  cases leftParsed with
  | firstIdentifierRejected absent rejected =>
      cases rightParsed with
      | firstIdentifierRejected => rfl
      | tailRejected rightAbsent rightFirst rightTail =>
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rejected
            ⟨_, _, rightFirst⟩)
  | tailRejected absent first tail =>
      cases rightParsed with
      | firstIdentifierRejected rightAbsent rightRejected =>
          exact False.elim (identifierExactOutcomeSpec.successRejectDisjoint rightRejected
            ⟨_, _, first⟩)
      | tailRejected rightAbsent rightFirst rightTail =>
          rcases first.result_unique rightFirst with ⟨rfl, rfl⟩
          rw [(tail.result_unique rightTail).1]

/-- Fixed context and rejected input determine the endpoint, report, and events. -/
theorem PragmaItemsTailTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaItemsTailTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaItemsTailTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  rcases left with ⟨leftPrefix, leftParsed, leftEvents, leftReport⟩
  rcases right with ⟨rightPrefix, rightParsed, rightEvents, rightReport⟩
  rcases leftParsed.result_unique rightParsed with ⟨rfl, rfl⟩
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trace_unique rightEvents⟩

/-- Complete item rejection also fixes every externally visible trace field. -/
theorem PragmaItemsTraceRejects.result_unique
    {source : SourceId} {endByte : Nat} {input afterLeft afterRight : Remainder}
    {leftDiagnostic rightDiagnostic : ParseDiagnostic}
    {leftTrace rightTrace : List ParseDiagnostic}
    (left : PragmaItemsTraceRejects source endByte input afterLeft leftDiagnostic leftTrace)
    (right : PragmaItemsTraceRejects source endByte input afterRight rightDiagnostic rightTrace) :
    afterLeft = afterRight ∧ leftDiagnostic = rightDiagnostic ∧ leftTrace = rightTrace := by
  rcases left with ⟨leftPrefix, leftParsed, leftEvents, leftReport⟩
  rcases right with ⟨rightPrefix, rightParsed, rightEvents, rightReport⟩
  rcases leftParsed.result_unique rightParsed with ⟨rfl, rfl⟩
  exact ⟨rfl, leftReport.diagnostic_unique rightReport, leftEvents.trace_unique rightEvents⟩

end Solcore.Syntax.DeclarativeGrammar
