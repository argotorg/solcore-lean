import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCatalog
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPreparedStageScopes
import Solcore.SourceSemantics.Staging.SelectedBodyPreservation

/-! Authentic registry scopes select cached original definitions. Successful
checking supplies the source-owner equality for the invoked definition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic

theorem exact_member {plan : Plan} {key : Key}
    {row : SourceSpecialization.SpecializedFunction}
    (selected : SourceCompilationPlan.exactSpecialization plan key = .ok row) :
    row ∈ plan.specializations := by
  unfold SourceCompilationPlan.exactSpecialization at selected
  split at selected <;> try contradiction
  rename_i actual found
  cases selected
  have member : row ∈ plan.specializations.filter (fun candidate => decide (candidate.key = key)) := by
    rw [found]
    simp
  exact (List.mem_filter.mp member).1

theorem sidecar_metadata {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) :
    SourceCompilationPlan.validateSpecializationMetadataWith true sidecar.caller = .ok () := by
  unfold prepareSidecar at accepted
  cases selected : SourceCompilationPlan.exactSpecialization plan key with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok caller =>
    simp only [selected, Except.mapError, bind, Except.bind] at accepted
    cases valid : SourceCompilationPlan.validateSpecializationMetadataWith true caller with
    | error error => simp [valid, Functor.discard, Functor.mapConst, Except.map] at accepted
    | ok value =>
      cases value
      simp only [valid] at accepted
      dsimp [Functor.discard, Functor.mapConst, Except.map] at accepted
      split at accepted
      · cases accepted
      · split at accepted
        · cases accepted; exact valid
        · cases accepted

theorem sidecar_owners {plan : Plan} {key : Key} {sidecar : Sidecar}
    (accepted : prepareSidecar plan key = .ok sidecar) :
    sidecar.caller.key.declaration = sidecar.caller.declaration ∧
      sidecar.caller.function.typedBody.owner = sidecar.caller.declaration := by
  have valid := sidecar_metadata accepted
  have coherent : SourceCompilationPlan.specializationOwnershipCoherent sidecar.caller = true := by
    by_cases same : SourceCompilationPlan.specializationOwnershipCoherent sidecar.caller = true
    · exact same
    · simp [SourceCompilationPlan.validateSpecializationMetadataWith, same, throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at valid
  have fields := of_decide_eq_true coherent
  exact ⟨fields.1, fields.2.2⟩

theorem selected_owner {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}
    (selected : RecursiveNamedPreparedStageScopes.Selected compiled native function scope) :
    ∃ row ∈ compiled.indexed.base.plan.specializations,
      function.source.owner = row.declaration := by
  cases selected with
  | anonymous receipt =>
    obtain ⟨sidecar, active, prepared, rfl, owner⟩ := receipt.original
    exact ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup prepared),
      owner.trans (sidecar_owners prepared).1⟩
  | named prepared sidecar issued same =>
    refine ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup issued), ?_⟩
    change prepared.named.specialized.function.typedBody.owner = sidecar.caller.declaration
    rw [prepared.same, ← same]
    exact (sidecar_owners issued).2
  | method selection statements sidecar issued same =>
    refine ⟨sidecar.caller, exact_member (LambdaSourceAlignment.sidecar_lookup issued), ?_⟩
    simpa only [same, Staging.Recursive.methodView, Staging.Recursive.globalView,
      CallableCoercionMethodInstantiation.bodyInstance] using (sidecar_owners issued).2

theorem ordinary_certificate {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    {row : SourceSpecialization.SpecializedFunction}
    (member : row ∈ compiled.indexed.base.plan.specializations)
    {instantiation : DeclarationInstantiation} {body : BodyInstance}
    (instantiates : FunctionInstantiates (Program.ofChecked compiled.sourceProgram) instantiation body)
    (owner : body.source.owner = row.declaration) :
    ∃ inputTypes lexicalContext facts,
      FunctionInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        instantiation body inputTypes lexicalContext facts := by
  have sourceOwner : body.source.owner = instantiation.declaration := by
    cases instantiates with
    | @intro signature definition _ signatureMember definitionMember declarationEq
        ownerEq _ sourceEq _ _ =>
      obtain ⟨generic, genericMember, rfl⟩ := List.mem_map.mp definitionMember
      obtain ⟨_, _, header⟩ := checkedFunctionHeaderWellFormed_ofCheckProgram checked genericMember
      simpa [sourceEq, StructuralSubstitution.applyTypedSource, FunctionDefinition.ofChecked,
        BodyDefinition.ofChecked] using header.source_owner.trans (ownerEq.trans declarationEq.symm)
  have signature : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
      row.declaration = signature.id := by
    cases instantiates with
    | intro signatureMember _ declarationEq _ _ _ _ _ =>
      exact ⟨_, signatureMember, owner.symm.trans (sourceOwner.trans declarationEq)⟩
  obtain ⟨signature, signatureMember, declaration⟩ := signature
  have origin := SelectedCompilationCatalog.ordinary_origin compiled bodies.signatures member signatureMember declaration
  obtain ⟨request, selectedSignature, generic, selectedSignatureMember, genericMember, _, accepted⟩ := origin
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row compiled member
  have valid := bodies.ordinary generic
    ⟨cached.index, cached.named, selectedSignature, request.parameterSubstitution, cached.selected,
      selectedSignatureMember, genericMember, by simpa only [cached.same] using accepted⟩
  have genericOwner : (FunctionDefinition.ofChecked generic).body.owner = instantiation.declaration := by
    exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.2.symm.trans
      (owner.symm.trans sourceOwner)
  exact instantiates.certificate_of_valid bodies.signatures bodies.function_ids
    (List.mem_map.mpr ⟨generic, genericMember, rfl⟩) genericOwner valid

theorem globals {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram) :
    Staging.Recursive.SelectedPreservation.GlobalBodiesTyped
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) := by
  intro instantiation body evidence roots scope instantiates _ selected
  obtain ⟨row, member, owner⟩ := selected_owner selected
  exact ordinary_certificate bodies checked member instantiates owner

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryGlobals
