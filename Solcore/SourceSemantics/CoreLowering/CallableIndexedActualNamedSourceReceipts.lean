import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedParameterProjections
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedFormation
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageContracts
import Solcore.SourceSemantics.CoreLowering.LambdaSourceAlignment

/-! Actual cached preparation and the accepted indexed hook select the same
complete named specialization. Source attribution uses this factory record
and the independent named agreement. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : (action >>= next) = .ok value) :
    ∃ input, action = .ok input ∧ next input = .ok value := by
  cases action with
  | error error => cases accepted
  | ok input => exact ⟨input, rfl, accepted⟩

private theorem prepared_key {program : CheckedProgram} {representation : SourceCoreGeneralFunctions.Representation}
    {row : SourceSpecialization.SpecializedFunction} {named : SourceCoreGeneralFunctions.Function}
    (accepted : SourceCoreGeneralFunctions.prepareFunctionWithRepresentation program representation row = .ok named) :
    named.signature.key = row.key := by
  unfold SourceCoreGeneralFunctions.prepareFunctionWithRepresentation at accepted
  obtain ⟨discarded, _, accepted⟩ := bind_ok accepted
  cases discarded
  by_cases staged : (row.function.returnComptime && !representation.allowStaged) = true
  · simp [staged, throw, bind, Except.bind] at accepted
  · simp only [staged] at accepted
    cases shape : row.function.type <;>
      simp only [shape, pure, Except.pure, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted <;>
      try contradiction
    rename_i parameter result
    by_cases mismatch : result ≠ row.function.inferredBodyType
    · simp [mismatch] at accepted
    · simp only [mismatch, ↓reduceIte] at accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      obtain ⟨_, _, accepted⟩ := bind_ok accepted
      cases accepted
      rfl

/-- The canonical sidecar contains its actual exact selection equation. -/
theorem sidecar_record {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {sidecar : SourceCoreStageContracts.Sidecar}
    (accepted : SourceCoreStageContracts.prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.exactSpecialization plan key = .ok sidecar.caller := by
  unfold SourceCoreStageContracts.prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; rfl
        · cases accepted

private theorem exact_member {plan : SourceCompilationPlan.Plan} {key : SourceCompilationPlan.Key}
    {original candidate : SourceSpecialization.SpecializedFunction}
    (accepted : SourceCompilationPlan.exactSpecialization plan key = .ok original)
    (member : candidate ∈ plan.specializations) (same : candidate.key = key) : candidate = original := by
  unfold SourceCompilationPlan.exactSpecialization at accepted
  split at accepted
  · cases accepted
  · next selected found =>
    cases accepted
    have retained : candidate ∈ plan.specializations.filter (fun item => decide (item.key = key)) :=
      List.mem_filter.mpr ⟨member, by simpa using same⟩
    rw [found] at retained
    exact List.mem_singleton.mp retained
  · cases accepted

/-- The actual table authenticates the named entry selected by this hook. -/
theorem hook_record_exists (compiled : SourceCoreUnifiedCompilation.Compiled)
    {named : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (hook : SourceCoreCallableIndexedAncestry.namedBody compiled.indexed.ancestry named body = .ok output) :
    ∃ row, SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok row := by
  obtain ⟨origin, _, selected, _, _⟩ := CallableIndexedFormation.namedBody_receipt compiled.indexed.ancestry hook
  let table := compiled.indexed.ancestry.graph.inputs.callable.table
  have owned : table.idAt? (.named named.signature.key) = some origin := selected
  cases made : SourceCoreCallableContracts.descriptor table (.named named.signature.key) with
  | error error =>
    unfold SourceCoreCallableContracts.descriptor at made
    split at made
    · next absent => rw [owned] at absent; cases absent
    · cases made
  | ok descriptor =>
    obtain ⟨entry, member, originEq, _⟩ := CallEntryCertificates.descriptor_entry descriptor
    have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
      compiled.indexed.ancestry.graph.inputs.callableSelected
    have authenticated := CallEntryCertificates.prepareWithProjection_authenticates prepared.accepted entry member
    unfold CallEntryCertificates.Authenticated at authenticated
    rw [originEq] at authenticated
    generalize countEq : entry.parameterCount = count at authenticated
    generalize contractEq : entry.contract = contract at authenticated
    cases authenticated with
    | named accepted =>
      obtain ⟨receipt⟩ := CallContractCertificates.named_of_accepted accepted
      exact ⟨receipt.sidecar.caller, sidecar_record receipt.prepared⟩

/-- Cached full-row preparation identifies the exact record selected by the
same hook, including every source node and ordered requirement row. -/
theorem cached_record (compiled : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (selected : compiled.indexed.base.functions[index]? = some named)
    (hook : SourceCoreCallableIndexedAncestry.namedBody compiled.indexed.ancestry named body = .ok output) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized := by
  obtain ⟨row, member, prepared⟩ := RecursiveNamedPreparedParameterProjections.cached_preparation compiled selected
  have namedEq := (SourceCoreGeneralFunctions.prepareFunctionWithRepresentation_inputs prepared).1
  have key := prepared_key prepared
  have member : row ∈ compiled.indexed.base.plan.specializations := by
    rw [CallableIndexedPreparedInventories.indexed_base compiled.indexedPrepared]
    exact List.mem_reverse.mp (List.mem_of_getElem? member)
  obtain ⟨original, found⟩ := hook_record_exists compiled hook
  have same := exact_member found member key.symm
  rw [namedEq, same]
  exact found

variable {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {program : Program}

/-- The cached slot and accepted hook are fields of the original header. -/
theorem header_record (compiled : SourceCoreUnifiedCompilation.Compiled)
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program) :
    SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan header.named.signature.key = .ok header.named.specialized :=
  cached_record compiled header.selected header.hook

/-- Named agreement transports only the independently authenticated source. -/
theorem header_source (compiled : SourceCoreUnifiedCompilation.Compiled)
    (header : RecursiveNamedCatalog.Header compiled.indexed.ancestry values definitions program) :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      header.named.signature.key [] header.function.source ∧ NodeOccurrencesUnique header.function.source := by
  refine ⟨?_, header.unique⟩
  rw [header.agreement.source]
  exact .original (header_record compiled header)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
