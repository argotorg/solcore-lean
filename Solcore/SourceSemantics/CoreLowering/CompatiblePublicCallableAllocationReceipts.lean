import Solcore.SourceSemantics.CoreLowering.CompatiblePublicDiagnosticPriority
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicDiagnosticReceipts

/-! The actual compatible factory retains its optional callable allocation.
Sealed compilation supplies the producer receipts used by decoder priority;
the selected Source occurrence remains an independent authentic receipt. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
open Core Frontend SourceInference
open CallableIndexedOwnedPublicFaultReceiverTables

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {value : β} (accepted : action >>= next = .ok value) :
    ∃ intermediate, action = .ok intermediate ∧ next intermediate = .ok value := by
  cases action with
  | error error => cases accepted
  | ok intermediate => exact ⟨intermediate, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {f : ε → δ} {value : α}
    (accepted : action.mapError f = .ok value) : action = .ok value := by
  cases action <;> cases accepted <;> rfl

/-- Optional absence and actual checked allocation retain their original cases. -/
def AllocationAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCompatibleFunctions.Prepared checked)
    (issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)) : Prop :=
  match prepared.callableDiagnostics with
  | none => True
  | some callable => ∃ contracts, SourceCoreCallableFaultSites.prepare prepared.plan contracts
      issued.program.rootTable issued.nextReason = .ok callable

theorem of_catalog {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : SourceCoreCompatibleCatalog.Checked} {ownership : checked.signatures = program.signatures}
    {fuel : Nat} {prepared : SourceCoreCompatibleFunctions.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (accepted : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok prepared)
    (present : prepared.diagnostics = some issued) : AllocationAt prepared issued := by
  unfold SourceCoreCompatibleFunctions.prepareWithCatalog at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals0, _, accepted⟩ := bind_ok accepted
  obtain ⟨contexts, _, accepted⟩ := bind_ok accepted
  obtain ⟨functions, _, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    cases present
  · obtain ⟨diagnostics, _, accepted⟩ := bind_ok accepted
    split at accepted
    · obtain ⟨contracts, _, accepted⟩ := bind_ok accepted
      obtain ⟨callable, allocated, accepted⟩ := bind_ok accepted
      simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨locals, _, accepted⟩ := bind_ok accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      cases present
      exact ⟨contracts, mapError_ok allocated⟩
    · simp only [pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨closures, _, accepted⟩ := bind_ok accepted
      obtain ⟨sourceInputs, _, accepted⟩ := bind_ok accepted
      obtain ⟨entries, _, accepted⟩ := bind_ok accepted
      cases accepted
      trivial

theorem of_automatic {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan} {fuel : Nat}
    {automatic : SourceCoreCompatibleFunctions.Automatic}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial automatic.checked)}
    (accepted : SourceCoreCompatibleFunctions.prepare program plan fuel = .ok automatic)
    (present : automatic.prepared.diagnostics = some issued) : AllocationAt automatic.prepared issued := by
  unfold SourceCoreCompatibleFunctions.prepare at accepted
  obtain ⟨executable, _, accepted⟩ := bind_ok accepted
  obtain ⟨locals, _, accepted⟩ := bind_ok accepted
  dsimp only at accepted
  split at accepted
  · cases accepted
  · obtain ⟨base, made, accepted⟩ := bind_ok accepted
    cases accepted
    exact of_catalog made present

theorem of_compiled (compiled : SourceCoreUnifiedCompilation.Compiled)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued) : AllocationAt compiled.indexed.base issued := by
  rw [SourceCoreUnifiedPreparationCertificates.indexed_base compiled.indexedPrepared] at present ⊢
  exact of_automatic compiled.compatiblePrepared present

/-- A token below the real producer endpoint stays below an actual callable
allocation, including the genuine absent-table case. -/
theorem AllocationAt.below {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked)}
    (allocation : AllocationAt prepared.base issued) {token : Word}
    (below : token.val < issued.nextReason) : BelowCallable prepared token := by
  cases present : prepared.base.callableDiagnostics with
  | none => simp only [BelowCallable, present]
  | some callable =>
    obtain ⟨contracts, allocated⟩ := (by simpa only [AllocationAt, present] using allocation :
      ∃ contracts, SourceCoreCallableFaultSites.prepare prepared.base.plan contracts
        issued.program.rootTable issued.nextReason = .ok callable)
    exact (by simpa only [BelowCallable, present] using
      CompatibleCallableDiagnosticBounds.below_unknown allocated below)

/-- Actual sealed compilation discharges diagnostic and callable preparation;
the member is still the genuine issued read selected by its Source adapter. -/
theorem receiver_read_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {read : SourceCoreFaultSites.ReadSite} (member : read ∈ issued.program.rootTable.reads) :
    completion.result.diagnostics.diagnostic? read.reason = some {
      error := .uninitializedLocal read.binder
      site := .occurrence read.expression.occurrence
      span := some read.span } := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  have actualMember : read ∈ base.rootTable.reads := by simpa only [reserved.sameRoot] using member
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  rw [table, appendCallable_diagnostic_of_below ((of_compiled compiled present).below
    (reserved.readsBelow read actualMember))]
  exact CompatiblePublicDiagnosticPriority.read_diagnostic reserved rebuilt actualMember

/-- The same factory receipts preserve the raw missing-default error. The
actual selected MissingSite and receiving metadata remain required. -/
theorem receiver_missing_diagnostic (compiled : SourceCoreUnifiedCompilation.Compiled)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial compiled.compatible.checked)}
    (present : compiled.indexed.base.diagnostics = some issued)
    {site : SourceCoreCompatibleDataPlaceFaultSites.MissingSite} (member : site ∈ issued.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : CompatiblePayload.MetadataRep completion.result.context.registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType) :
    ∃ diagnostic, completion.result.diagnostics.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  obtain ⟨root, sources, accepted⟩ := CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨base, extra, reserved⟩ := CompatiblePlaceMissingPreparationRanges.prepare_reserved_receipt accepted
  obtain ⟨actual, rebuilt, table⟩ := receiver
  rw [present] at rebuilt
  rw [table, appendCallable_diagnostic_of_below ((of_compiled compiled present).below
    (CompatiblePublicDiagnosticPriority.missing_token_below reserved rebuilt member metadata))]
  exact CompatiblePlaceMissingPreparationRanges.table_diagnostic accepted rebuilt member metadata keyView valueView

end Solcore.SourceSemantics.CoreLowering.CompatiblePublicCallableAllocationReceipts
