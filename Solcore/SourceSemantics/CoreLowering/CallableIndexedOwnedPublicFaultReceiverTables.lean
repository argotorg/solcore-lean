import Solcore.Frontend.SourceCoreCallableIndexedPrograms

/-! The actual indexed run retains the table rebuilt for its own raw registry.
The receipt records the existing optional base table and the exact callable
append. It does not assume decoder coverage or reorder table priorities. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
open Core Frontend SourceInference

variable {checked : SourceCoreCompatibleCatalog.Checked}

/-- The same callable rows appended by the public indexed runner. -/
def appendCallable (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (table : SourceCoreFaultSites.Table) : SourceCoreFaultSites.Table :=
  match prepared.base.callableDiagnostics with
  | none => table
  | some diagnostics => {table with additional := table.additional ++
      diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

/-- Appending disjoint rows preserves the existing decoder's exact priority. -/
theorem diagnostic_append {table : SourceCoreFaultSites.Table}
    {extra : List (Word × SourceCoreFaultSites.Diagnostic)} {token : Word}
    (disjoint : extra.find? (fun item => decide (item.1 = token)) = none) :
    ({table with additional := table.additional ++ extra}).diagnostic? token = table.diagnostic? token := by
  simp only [SourceCoreFaultSites.Table.diagnostic?, List.find?_append, disjoint]
  cases table.additional.find? (fun item => decide (item.1 = token)) <;> rfl

/-- The genuine numerical range boundary excludes only the appended callable
rows. It does not assume a decoder law for unrelated Source occurrences. -/
theorem appendCallable_diagnostic {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {callable : SourceCoreCallableFaultSites.Program} {table : SourceCoreFaultSites.Table} {token : Word}
    (present : prepared.base.callableDiagnostics = some callable)
    (below : token.val < callable.unknown.val) :
    (appendCallable prepared table).diagnostic? token = table.diagnostic? token := by
  rw [appendCallable, present]
  apply diagnostic_append
  apply List.find?_eq_none.mpr
  intro item member
  have lower := (List.mem_filter.mp member).2
  have lower' : callable.unknown.val ≤ item.1.val := of_decide_eq_true lower
  intro equalBool
  have equal : item.1 = token := of_decide_eq_true equalBool
  have same := congrArg Fin.val equal
  omega

/-- This is the actual callable-table range check, including the absent-table
case. It concerns the one issued token rather than every Source expression. -/
def BelowCallable (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (token : Word) : Prop :=
  match prepared.base.callableDiagnostics with
  | none => True
  | some callable => token.val < callable.unknown.val

theorem appendCallable_diagnostic_of_below
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {table : SourceCoreFaultSites.Table} {token : Word}
    (below : BelowCallable prepared token) :
    (appendCallable prepared table).diagnostic? token = table.diagnostic? token := by
  cases present : prepared.base.callableDiagnostics with
  | none => simp only [appendCallable, present]
  | some callable =>
    exact appendCallable_diagnostic present (by simpa only [BelowCallable, present] using below)

/-- Actual base rebuilding and exact receiver identity are separate receipts.
The absent-base alternative keeps the original public fallback unchanged. -/
def IssuedAt (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry)
    (receiver : SourceCoreFaultSites.Table) : Prop :=
  ∃ base,
    (match prepared.base.diagnostics with
    | some diagnostics => diagnostics.tableForRegistry registry extension = .ok base
    | none => base = {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Word.zero}) ∧
    receiver = appendCallable prepared base

private def computed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts)
    (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry) :
    Except SourceCoreCallableIndexedPrograms.RunError SourceCoreFaultSites.Table := do
  let table ← match prepared.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry registry extension).mapError SourceCoreCallableIndexedPrograms.RunError.diagnostics
    | none => pure {
        owner := entry.key.declaration
        resultType := entry.sourceResultType
        reads := []
        escapedReason := Word.zero}
  pure (appendCallable prepared table)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : (action >>= next) = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {action : Except ε α} {map : ε → δ}
    {result : α} (accepted : action.mapError map = .ok result) : action = .ok result := by
  cases action <;> cases accepted <;> rfl

private theorem issued_of_computed
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {entry : SourceCoreCallableIndexedPrograms.Entry prepared.layouts}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : computed prepared entry registry extension = .ok table) :
    IssuedAt prepared entry registry extension table := by
  unfold computed at accepted
  cases present : prepared.base.diagnostics with
  | none =>
    simp only [present, pure, Except.pure, bind, Except.bind] at accepted
    cases accepted
    exact ⟨_, present ▸ rfl, rfl⟩
  | some diagnostics =>
    simp only [present] at accepted
    obtain ⟨base, rebuilt, accepted⟩ := bind_ok accepted
    cases accepted
    refine ⟨base, ?_, rfl⟩
    rw [present]
    exact mapError_ok rebuilt

/-- Finite inversion of the genuine public run exposes its own table receipt.
Encoding and native execution are not repeated; their actual returned values
remain the same completion fields. -/
theorem issued_of_runSource
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {key : SourceSpecialization.SpecializationKey} {arguments : List SourceTypedRuntime.Value}
    {fuel validationFuel : Nat} {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (accepted : prepared.runSource key arguments fuel validationFuel = .ok completion) :
    IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics := by
  unfold SourceCoreCallableIndexedPrograms.Prepared.runSource at accepted
  cases selected : prepared.find? key with
  | none =>
    rw [selected] at accepted
    change Except.error (SourceCoreCallableIndexedPrograms.RunError.missingEntry key) = .ok completion at accepted
    cases accepted
  | some entry =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨encoded, _encodedBy, accepted⟩ := bind_ok accepted
    obtain ⟨body, _bodyBy, accepted⟩ := bind_ok accepted
    split at accepted
    · simp [throw] at accepted
    · obtain ⟨native, _nativeBy, accepted⟩ := bind_ok accepted
      obtain ⟨table, tableBy, accepted⟩ := bind_ok accepted
      cases accepted
      apply issued_of_computed
      exact tableBy

/-- Resuming the actual native checkpoint keeps the original raw registry
and receiver table. No diagnostic factory is run again. -/
theorem IssuedAt.resume
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receipt : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics) (fuel : Nat) :
    IssuedAt prepared (completion.resume fuel).entry (completion.resume fuel).result.context.registry
      (completion.resume fuel).result.extension (completion.resume fuel).result.diagnostics := by
  unfold SourceCoreCallableIndexedPrograms.Completion.resume
  split <;> exact receipt

/-- The actual receiver decodes a retained ordinary read. Rebuilding uses
that completion's registry and extension, and the real table priorities
remain explicit until the authentic issuer supplies their receipts. -/
theorem read_diagnostic_of_issued
    {prepared : SourceCoreCallableIndexedPrograms.Prepared checked}
    {completion : SourceCoreCallableIndexedPrograms.Completion prepared}
    (receipt : IssuedAt prepared completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {issued : SourceCoreCompatibleDataPlaceFaultSites.Program
      (SourceCoreCompatibleValues.Context.initial checked)}
    (present : prepared.base.diagnostics = some issued)
    {base : SourceCoreFaultSites.Table}
    (rebuilt : issued.tableForRegistry completion.result.context.registry
      completion.result.extension = .ok base)
    {site : SourceCoreFaultSites.ReadSite}
    (positive : site.reason ≠ Word.zero)
    (ordinary : site.reason ≠ base.escapedReason)
    (noBoundary : base.additional.find? (fun candidate => decide (candidate.1 = site.reason)) = none)
    (found : base.reads.find? (fun candidate => decide (candidate.reason = site.reason)) = some site)
    (below : BelowCallable prepared site.reason) :
    completion.result.diagnostics.diagnostic? site.reason = some {
      error := .uninitializedLocal site.binder
      site := .occurrence site.expression.occurrence
      span := some site.span
    } := by
  obtain ⟨actual, actualBy, receiver⟩ := receipt
  rw [present] at actualBy
  have same : actual = base := Except.ok.inj (actualBy.symm.trans rebuilt)
  subst actual
  rw [receiver, appendCallable_diagnostic_of_below below]
  exact SourceCoreFaultSites.Table.read_diagnostic positive ordinary noBoundary found

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceiverTables
