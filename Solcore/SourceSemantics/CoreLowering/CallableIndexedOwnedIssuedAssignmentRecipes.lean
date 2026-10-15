import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentProvenance

/-! Exact public issuance turns a retained contextual compilation into its
original assignment preparation and receiver interpretation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaIssuedRecipes (IssuedAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}

/-- The existing named diagnostic receipt retains the genuine unchanged base. -/
theorem of_prepared {row : SourceSpecialization.SpecializedFunction}
    (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared) :
    IssuedAt compiled.indexed prepared.diagnostics := by
  obtain ⟨issued, present, lowered⟩ := receipt.actual
  refine ⟨issued, present, ?_⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩

/-- Actual method cache issuance has the same complete table provenance. -/
theorem of_cached {row : SourceSpecialization.SpecializedFunction}
    (cached : CallablePreparedMethodSelection.Cached compiled row)
    (receipt : CallableIndexedOwnedPreparedStagedMethodTerminalSupport.DiagnosticAt cached) :
    IssuedAt compiled.indexed cached.diagnostics := by
  obtain ⟨issued, present, lowered⟩ := receipt.actual
  refine ⟨issued, present, ?_⟩
  rw [lowered]
  cases compiled.indexed.base.callableContext <;> exact ⟨rfl, rfl⟩

/-- The exact same retained compilation selects its actual own table. -/
theorem compilation_member (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics) :
    ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some issued ∧
      compilation.own ∈ issued.program.base.functions := by
  obtain ⟨issued, present, sameBase, _samePlaces⟩ := receipt
  have selected := compilation.diagnostic
  rw [sameBase] at selected
  exact ⟨issued, present, List.mem_of_find?_eq_some selected⟩

/-- Full original-source preparation is preserved through closure-body views;
only authentic membership of the owning named cache is required. -/
theorem assignments_prepared {index : Nat}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics) :
    ∃ first, SourceCoreAssignmentFaultSites.prepare (source named) first = .ok compilation.own.assignments := by
  obtain ⟨issued, present, sameBase, _samePlaces⟩ := receipt
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  have found := compilation.diagnostic
  rw [sameBase] at found
  exact SourceCoreProgramFaultSites.prepare_assignments_at
    (CallableIndexedOwnedPublicDiagnosticReceipts.data_place_base accepted)
    (CallableIndexedActualNamedSourceReceipts.cached_record compiled selected compilation.hook) found

/-- The compilation used by the lowerer supplies the public operand relation. -/
theorem operands (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (receipt : IssuedAt compiled.indexed diagnostics)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := compilation_member compilation receipt
  exact CallableIndexedOwnedPublicAssignmentDiagnostics.receiver_operands compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
