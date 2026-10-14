import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodTerminalSupport

/-! Exact cached compilation authenticates assignment inventories at the full
original method source, retaining its own selector rather than an ordinary header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
open Core Frontend SourceInference
open CallablePreparedMethodSelection (Cached)
open CallableIndexedOwnedMethodPrincipal (Principal)
open CallableIndexedOwnedPreparedStagedMethodTerminalSupport (DiagnosticAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}

/-- A genuine cached compiler and its diagnostic receipt select the same
member of the actual program inventory. -/
theorem cached_member (cached : Cached compiled row) (diagnostic : DiagnosticAt cached) :
    ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some issued ∧
      cached.compilation.own ∈ issued.program.base.functions := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  have sameBase : cached.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := cached.compilation.diagnostic
  rw [sameBase] at selected
  exact ⟨issued, present, List.mem_of_find?_eq_some selected⟩

/-- The original complete cached Source supplies the authentic preparation;
its assignment tokens are not regenerated from a subbody or native code. -/
theorem cached_assignments (cached : Cached compiled row) (diagnostic : DiagnosticAt cached) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare cached.named.specialized.function.typedBody first =
      .ok cached.compilation.own.assignments := by
  obtain ⟨issued, present, lowered⟩ := diagnostic.actual
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have programAccepted := CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted
  have sameBase : cached.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := cached.compilation.diagnostic
  rw [sameBase] at selected
  exact SourceCoreProgramFaultSites.prepare_assignments_at programAccepted
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled cached.selected cached.compilation.hook) selected

/-- The same inventory belongs to the method principal's complete Source
body, including its actual specialization and dictionary frame. -/
theorem method_assignments {method : ExecutableImplMethods.CheckedMethod}
    (principal : Principal compiled method) (diagnostic : DiagnosticAt principal.cached) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare principal.sourceBody.source first =
      .ok principal.cached.compilation.own.assignments := by
  rw [← principal.source_eq]
  exact cached_assignments principal.cached diagnostic

/-- Any genuine cached assignment operand is interpreted by the actual
public receiver, with all table inclusion obligations closed internally. -/
theorem cached_operands (cached : Cached compiled row) (diagnostic : DiagnosticAt cached)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep cached.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := cached_member cached diagnostic
  exact CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_operands compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance
