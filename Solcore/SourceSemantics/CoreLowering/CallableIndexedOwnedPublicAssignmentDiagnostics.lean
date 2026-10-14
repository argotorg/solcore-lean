import Solcore.SourceSemantics.CoreLowering.ProgramAssignmentDiagnosticInclusion
import Solcore.SourceSemantics.CoreLowering.CompatibleProgramAssignmentPreparation
import Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDecodedCallFaults
import Solcore.SourceSemantics.CoreLowering.GenericAssignmentDiagnosticCertificates

/-! Genuine assignment table entries survive the actual whole-program collection,
compatible receiver rebuilding, and callable diagnostic append. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicAssignmentDiagnostics
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables
open RecursiveNamedPublicSpecializationMeaning

/-- Any actual cache-row assignment diagnostic reaches the exact public
receiver. The result applies equally to named, method, and closure-owned rows
whenever their compiler receipt selects this original program inventory. -/
theorem receiver_assignment_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {own : SourceCoreProgramFaultSites.Function} (member : own ∈ issued.program.base.functions)
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (decoded : own.assignments.diagnostic? token = some diagnostic) :
    completion.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨prefixBase, prefixAccepted, suffix, retained⟩ := CompatibleProgramAssignmentPreparation.prepare_prefix accepted
  have sameBase : prefixBase = base := Except.ok.inj (prefixAccepted.symm.trans reserved.baseAccepted)
  subst prefixBase
  have actualMember : own ∈ base.functions := by simpa only [reserved.sameBase] using member
  obtain ⟨positive, ordinary, found, _baseDecoded⟩ :=
    ProgramAssignmentDiagnosticInclusion.prepare_assignment_diagnostic reserved.baseAccepted actualMember decoded
  have fixedFound : issued.fixed.find? (fun row => decide (row.1 = token)) = some (token, diagnostic) := by
    rw [retained, List.find?_append, found]
    rfl
  have below : token.val < issued.nextReason :=
    reserved.fixedBelow (token, diagnostic) (List.mem_of_find?_eq_some fixedFound)
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  rw [table, appendCallable_diagnostic_of_below
    ((CompatiblePublicCallableAllocationReceipts.of_compiled compiled present).below below)]
  obtain ⟨fresh, _freshAccepted, actualTable, _origins⟩ := issued.tableForRegistry_receipt rebuilt
  rw [actualTable, reserved.sameRoot]
  simp only [SourceCoreFaultSites.Table.diagnostic?, positive, ordinary, ↓reduceIte,
    List.find?_append, fixedFound]
  rfl

/-- The exact table-indexed operand relation is included in the public
semantic decoder using only authentic compilation and receiver receipts. -/
theorem receiver_operands (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {own : SourceCoreProgramFaultSites.Function} (member : own ∈ issued.program.base.functions)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  cases reason <;> simp only [GenericAssignmentDiagnostics.OperandRep] at represented
  next operator =>
    obtain ⟨diagnostic, rawType, decoded, error⟩ := represented
    apply CallableIndexedOwnedPublicDecodedCallFaults.of_assignment
    refine ⟨diagnostic, receiver_assignment_diagnostic compiled receiver present member decoded, ?_⟩
    rw [error]
    exact .operand operator rawType

/-- The real second-pass Prepared receipt selects its unchanged function
assignment inventory, including the optional callable root-table replacement. -/
theorem prepared_member {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared) :
    ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked),
      compiled.indexed.base.diagnostics = some issued ∧
      prepared.compilation.own ∈ issued.program.base.functions := by
  obtain ⟨issued, present, lowered⟩ := receipt.actual
  have sameBase : prepared.diagnostics.base = issued.program.base := by
    rw [lowered]
    cases compiled.indexed.base.callableContext <;> rfl
  have selected := prepared.compilation.diagnostic
  rw [sameBase] at selected
  exact ⟨issued, present, List.mem_of_find?_eq_some selected⟩

/-- Named compiled assignment operands need no supplied inclusion law. -/
theorem prepared_operands {compiled : SourceCoreUnifiedCompilation.Compiled}
    {row : SourceSpecialization.SpecializedFunction} (prepared : Prepared compiled row)
    (receipt : CallableIndexedOwnedPublicDiagnosticReceipts.Receipt prepared)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {reason : Dynamic.SemanticFault} {token : Word}
    (represented : GenericAssignmentDiagnostics.OperandRep prepared.compilation.own.assignments reason token) :
    CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token := by
  obtain ⟨issued, present, member⟩ := prepared_member prepared receipt
  exact receiver_operands compiled receiver present member represented

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicAssignmentDiagnostics
