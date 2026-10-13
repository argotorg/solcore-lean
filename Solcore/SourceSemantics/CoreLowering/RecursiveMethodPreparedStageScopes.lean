import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodPrincipal

/-! The actual method cache row and authenticated codebook descriptor select
its staged body scope. The full method dictionary stays attached; no ordinary
function declaration or body execution is inferred from the compiler row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
open Frontend SourceInference SourceCoreStageContracts
open CallContractCertificates CallEntryCertificates
open CallableIndexedOwnedMethodPrincipal

private theorem exact_key {plan : SourceCompilationPlan.Plan} {key : Key}
    {row : SourceSpecialization.SpecializedFunction}
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok row) : row.key = key := by
  unfold SourceCompilationPlan.exactSpecialization at record
  split at record <;> try contradiction
  rename_i selected selectedEq
  cases record
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [selectedEq]
    simp
  exact of_decide_eq_true (List.mem_filter.mp member).2

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {native : SourceCoreGeneralFunctions.CallableContext}
  {method : ExecutableImplMethods.CheckedMethod}

/-- Real descriptor authentication fixes the complete sidecar. Independent
method authority supplies its Source body and chosen dictionary. -/
theorem selected_of_descriptor
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (principal : Principal compiled method)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named principal.named.signature.key)) :
    ∃ sidecar : Sidecar,
      prepareSidecar compiled.indexed.base.plan method.specialized.key = .ok sidecar ∧
      sidecar.caller = method.specialized ∧
      (RecursiveNamedPreparedStageScopes.registry actual).Closure principal.sourceFunction
        (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction) := by
  obtain ⟨entry, member, origin, _⟩ := descriptor_entry descriptor
  have authenticated := actual.entries_authenticated entry member
  unfold CallEntryCertificates.Authenticated at authenticated
  rw [origin] at authenticated
  generalize count_eq : entry.parameterCount = count at authenticated
  generalize contract_eq : entry.contract = contract at authenticated
  cases authenticated with
  | named issued =>
    obtain ⟨receipt⟩ := named_of_accepted issued
    have same := RecursiveNamedPreparedStageScopes.sidecar_caller receipt.prepared principal.record
    have sameMethod : receipt.sidecar.caller = method.specialized := same.trans principal.cached.same
    have keyEq : principal.named.signature.key = method.specialized.key :=
      (exact_key principal.record).symm.trans (congrArg (fun row : SourceSpecialization.SpecializedFunction => row.key) principal.cached.same)
    have prepared : prepareSidecar compiled.indexed.base.plan method.specialized.key = .ok receipt.sidecar := by
      simpa only [keyEq] using receipt.prepared
    exact ⟨receipt.sidecar, prepared, sameMethod,
      .method principal.selected principal.source_frame.roots receipt.sidecar prepared sameMethod⟩

/-- The original stage analysis and declaration substitution remain those of
the actual selected method, with no lexical local instantiation. -/
theorem original_stages
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (principal : Principal compiled method)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.named principal.named.signature.key)) :
    ∃ sidecar : Sidecar,
      (RecursiveNamedPreparedStageScopes.registry actual).Closure principal.sourceFunction
        (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction) ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).origin.declarationSubstitution = method.specialized.parameterSubstitution ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).origin.localSubstitution = [] ∧
      (RecursiveStageRegistry.scope sidecar [] principal.sourceFunction).evidence = principal.dictionary ∧
      SourceStageAnalysis.analyzeFunction method.specialized.function = .ok method.specialized.stageAnalysis := by
  obtain ⟨sidecar, _, same, selected⟩ := selected_of_descriptor actual principal descriptor
  exact ⟨sidecar, selected, by simp only [RecursiveStageRegistry.scope_declarationSubstitution, same],
    rfl, rfl, by simpa only [same] using sidecar.analyzed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodPreparedStageScopes
