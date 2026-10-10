import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSecondCallGateRejection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedReceivingPreparedShapeInterpretations

/-! An original selected call row keeps its diagnostic through the actual
receiving-registry rebuild and the public callable append. The preappend table
decodes only below the real issuer endpoint; callable rejection tokens lie at
or above the later allocator boundary. Original and substituted call metadata
remain separate. No decoder inclusion or execution law is supplied. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
open Core Frontend SourceInference SourceTypedRuntime GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedIndirectSourceAdapters
open CallableIndexedOwnedSelectedCallCodebookReceipts (Selected)
open CallableIndexedOwnedPreparedSecondCallGateRejection
open CallableIndexedOwnedPublicFaultReceiverTables

/-- Every reason selected from this actual inventory is at or above the
allocator boundary, including its authentic unknown-descriptor fallback. -/
theorem reason_at_lower_bound {contracts : SourceCoreStageCodebook.Table}
    {base : SourceCoreFaultSites.Table} {minimum : Nat}
    {program : SourceCoreCallableFaultSites.Program}
    (receipt : CallableFaultDiagnosticPreparation.Receipt contracts base minimum program)
    (caller : SourceSpecialization.SpecializationKey) (call : ExpressionId)
    (descriptor : Word) (phase : SourceCoreCallableFaultSites.Phase) (error : RuntimeError) :
    program.unknown.val ≤ (program.reasonAt caller call descriptor phase error).val := by
  unfold SourceCoreCallableFaultSites.Program.reasonAt
  split
  · rename_i site found
    have member := List.mem_of_find?_eq_some found
    have high := (receipt.inventory.bounds site member).1
    rw [receipt.unknown]
    omega
  · exact Nat.le_refl _

private theorem filtered_find {rows : List (Word × SourceCoreFaultSites.Diagnostic)}
    {unknown token : Word} (high : unknown.val ≤ token.val) :
    (rows.filter (fun item => unknown.val ≤ item.1.val)).find?
        (fun item => decide (item.1 = token)) =
      rows.find? (fun item => decide (item.1 = token)) := by
  rw [List.find?_filter]
  congr 1
  funext item
  by_cases same : item.1 = token
  · simp [same, high]
  · simp [same]

/-- The actual receiving base has no lookup at a high callable token. The
literal filter retains the same first matching callable row. -/
theorem receiver_lookup (compiled : SourceCoreUnifiedCompilation.Compiled)
    {native : SourceCoreGeneralFunctions.CallableContext}
    (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    {token : Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (high : native.diagnostics.unknown.val ≤ token.val)
    (decoded : native.diagnostics.rootTable.diagnostic? token = some diagnostic) :
    completion.result.diagnostics.diagnostic? token = some diagnostic := by
  obtain ⟨issued, present, callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have allocatedReceipt := CallableFaultDiagnosticPreparation.prepare_receipt allocated
  have boundary : issued.nextReason ≤ native.diagnostics.unknown.val := by
    rw [allocatedReceipt.unknown]
    exact Nat.le_max_right _ _
  obtain ⟨root, sources, accepted⟩ :=
    CallableIndexedOwnedPublicDiagnosticReceipts.compiled_diagnostics compiled present
  obtain ⟨actual, rebuilt, sameReceiver⟩ := receiver
  rw [present] at rebuilt
  have absent : actual.diagnostic? token = none := by
    cases found : actual.diagnostic? token with
    | none => rfl
    | some original =>
        have below := CallableIndexedOwnedReceivingPreparedShapeInterpretations.decoded_token_below
          accepted rebuilt found
        omega
  obtain ⟨extra, _expanded, sameBase, _origins⟩ := issued.tableForRegistry_receipt rebuilt
  have sameEscaped : actual.escapedReason = native.diagnostics.rootTable.escapedReason := by
    rw [sameBase, allocatedReceipt.table]
  have sameReads : actual.reads = native.diagnostics.rootTable.reads := by
    rw [sameBase, allocatedReceipt.table]
  have nonzero : token ≠ Word.zero := by
    intro zero
    simp [zero, SourceCoreFaultSites.Table.diagnostic?] at absent
  have notEscaped : token ≠ actual.escapedReason := by
    intro escaped
    have escapedNonzero : actual.escapedReason ≠ Word.zero := by
      rw [← escaped]
      exact nonzero
    simp [SourceCoreFaultSites.Table.diagnostic?, escaped, escapedNonzero] at absent
  have additionalAbsent : actual.additional.find? (fun item => decide (item.1 = token)) = none := by
    cases found : actual.additional.find? (fun item => decide (item.1 = token)) with
    | none => rfl
    | some pair =>
        simp [SourceCoreFaultSites.Table.diagnostic?, nonzero, notEscaped, found] at absent
  have originalNotEscaped : token ≠ native.diagnostics.rootTable.escapedReason := by
    rwa [sameEscaped] at notEscaped
  rw [sameReceiver, appendCallable, callablePresent]
  simp only [SourceCoreFaultSites.Table.diagnostic?, nonzero, notEscaped,
    originalNotEscaped, if_false, List.find?_append, additionalAbsent,
    Option.none_or, filtered_find high, sameReads] at decoded ⊢
  exact decoded

private theorem issued_reason {table : SourceCoreStageCodebook.Table}
    {caller : SourceSpecialization.SpecializationKey} {call : ExpressionId}
    {actualReason : SourceCoreCallableContracts.ReasonAt} {site : SourceCoreCallableContracts.Callsite}
    (issued : SourceCoreCallableContracts.prepareCallsite table caller call actualReason = .ok site) :
    site.reasonAt = actualReason := by
  unfold SourceCoreCallableContracts.prepareCallsite at issued
  split at issued
  · cases issued; rfl
  · cases issued

section OriginalRow
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext}
  (prepared : Prepared compiler native)
  (stages : RecursiveNamedPreparedStageContracts.Prepared compiled native)
  {sidecar : SourceCoreStageContracts.Sidecar} {row : SourceCoreStageCodebook.Decision}
  {originalNode : ExpressionNode} {originalMetadata : IndirectCallResolution}
  (selected : Selected sidecar prepared.site callee ids originalMetadata originalNode row)

include stages selected in
/-- The original selected metadata, same actual site and sealed allocation
construct the raw arity diagnostic. No equality to the substituted node is used. -/
theorem original_diagnostic (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      native.diagnostics.rootTable.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  have member := List.mem_of_find?_eq_some selected.found
  change row ∈ prepared.site.table.casesAt prepared.site.caller prepared.site.call at member
  have contained := (List.mem_filter.mp member).1
  rw [prepared.table] at contained
  obtain ⟨_issuer, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have decoded := CallableFaultDiagnosticPreparation.prepared_after_arguments allocated contained
    (rejected_row selected different)
  rw [issued_reason prepared.prepared]
  exact decoded

include stages selected in
/-- The original row's concrete second-gate reason reaches the actual public
receiving table through its genuine rebuild and filtered callable append. -/
theorem receiving_diagnostic
    {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
    (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
      completion.result.extension completion.result.diagnostics)
    (different : row.entry.parameterCount ≠ ids.length) :
    ∃ diagnostic,
      completion.result.diagnostics.diagnostic?
        (prepared.site.reasonAt row.caller row.call row.entry.id .beforeApplication
          (.argumentArityMismatch row.entry.parameterCount ids.length)) = some diagnostic ∧
      diagnostic.error = .argumentArityMismatch row.entry.parameterCount ids.length := by
  obtain ⟨diagnostic, decoded, error⟩ := original_diagnostic compiler prepared stages selected different
  obtain ⟨_issued, _present, _callablePresent, allocated⟩ :=
    CallableIndexedOwnedPublicCallableDiagnostics.of_compiled compiled stages.present
  have high := reason_at_lower_bound (CallableFaultDiagnosticPreparation.prepare_receipt allocated)
    row.caller row.call row.entry.id .beforeApplication
    (.argumentArityMismatch row.entry.parameterCount ids.length)
  rw [← issued_reason prepared.prepared] at high
  exact ⟨diagnostic, receiver_lookup compiled stages receiver high decoded, error⟩

end OriginalRow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedReceivingCallRejectionDiagnostics
