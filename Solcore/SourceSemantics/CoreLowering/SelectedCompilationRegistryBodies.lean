import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
import Solcore.SourceSemantics.Staging.SelectedPreservationContracts

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies
open Frontend SourceInference TypeSystem SourceCoreStageContracts
open Solcore.SourceSemantics.Dynamic
open SelectedCompilationRegistryMethodCertificates (Ranges)

private theorem function_impl_ne {program : CheckedProgram}
    (catalog : SignatureCatalogWellFormed program.signatures)
    {signature : ProgramFunctionSignature} (member : signature ∈ program.signatures.functions)
    {implementation : ProgramImplementationSignature}
    (implMember : implementation ∈ program.signatures.implementations) :
    signature.id ≠ implementation.id := by
  have unique := catalog.declaration_ids
  simp only [signatureDeclarationIds] at unique
  have separated := (List.nodup_append.mp (List.nodup_append.mp unique).1).2.2
  apply separated signature.id
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map.mpr ⟨signature, member, rfl⟩)))
    implementation.id (List.mem_map.mpr ⟨implementation, implMember, rfl⟩)

private theorem instantiated_owner {program : CheckedProgram} {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok program)
    {implementation : ProgramImplementationSignature} {method : ProgramImplMethodSignature}
    {trait : ProgramTraitSignature} {definition : MethodDefinition}
    {substitution : ParameterSubstitution} {body : BodyInstance}
    (instantiates : TraitMethodInstantiates (Program.ofChecked program)
      implementation method trait definition substitution body) :
    body.source.owner = implementation.id := by
  cases instantiates with
  | intro _ _ _ _ definitionMember _ owner _ _ sourceEq _ _ =>
    obtain ⟨retained, retainedMember, rfl⟩ := List.mem_map.mp definitionMember
    obtain ⟨_, _, _, _, _, _, _, header⟩ := checkedMethodHeaderWellFormed_ofCheckProgram checked retainedMember
    rw [sourceEq]
    exact header.source_owner.trans owner

private theorem row_owner {signature : ProgramFunctionSignature} {generic : CheckedFunction}
    {supplied : ParameterSubstitution} {row : SourceSpecialization.SpecializedFunction}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok row) :
    row.function.typedBody.owner = signature.id := by
  rw [RecursiveNamedSpecializationBodyFacts.body accepted]
  exact (RecursiveNamedSpecializationBodyFacts.identities accepted).2.1.trans
    (RecursiveNamedSpecializationBodyFacts.identities accepted).1.symm

private theorem method_view_injective {left right : BodyInstance}
    {leftEvidence rightEvidence : EvidenceEnvironment} {leftRoots rightRoots : List StatementId}
    (same : Staging.Recursive.methodView left leftEvidence leftRoots =
      Staging.Recursive.methodView right rightEvidence rightRoots) : left = right := by
  have context := congrArg Dynamic.Closure.context same
  have source := congrArg Dynamic.Closure.source same
  have result := congrArg Dynamic.Closure.resultType same
  cases left
  cases right
  simp only [Staging.Recursive.methodView, Staging.Recursive.globalView] at context source result
  cases context
  cases source
  cases result
  rfl

/-- The exact final row is checked as a method origin. Other registry entry
kinds are excluded by the original owner catalog and occurrence forest. -/
theorem methods {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled) :
    Staging.Recursive.SelectedPreservation.MethodBodiesTyped
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) := by
  intro context evidence dictionary traitName methodName requirements body roots child method rootsEq selected
  have graph : OccurrenceGraphClosed body.source := by
    cases method with
    | intro _ _ _ _ _ _ _ _ _ _ _ instantiates _ _ =>
      exact SelectedCompilationRegistryLambdaExclusion.method_graph checked instantiates
  have owner : ∃ implementation ∈ compiled.sourceProgram.signatures.implementations,
      body.source.owner = implementation.id := by
    cases method with
    | intro _ _ implementationMember _ _ _ _ _ _ _ _ instantiates _ _ =>
      exact ⟨_, implementationMember, instantiated_owner checked instantiates⟩
  generalize viewEq : Staging.Recursive.methodView body dictionary roots = view at selected
  change RecursiveNamedPreparedStageScopes.Selected compiled native view child at selected
  cases selected with
  | @anonymous function scope receipt =>
    apply False.elim
    apply SelectedCompilationRegistryLambdaExclusion.anonymous_ne_whole_body receipt
    · simpa only [← viewEq, Staging.Recursive.methodView, Staging.Recursive.globalView] using graph
    · simpa only [← viewEq, Staging.Recursive.methodView, Staging.Recursive.globalView] using rootsEq
  | @named row prepared sidecar issued same =>
    obtain ⟨implementation, implMember, owner⟩ := owner
    obtain ⟨request, signature, generic, signatureMember, _, _, accepted⟩ := prepared.origin
    have sourceEq := congrArg (fun closure : Dynamic.Closure => closure.source.owner) viewEq
    change body.source.owner = prepared.named.specialized.function.typedBody.owner at sourceEq
    rw [prepared.same] at sourceEq
    exact False.elim (function_impl_ne bodies.signatures signatureMember implMember
      ((row_owner accepted).symm.trans (sourceEq.symm.trans owner)))
  | @method selectedMethod callerContext callerEvidence selectedDictionary selectedTrait selectedName selectedRequirements
      selectedRoots selection statements sidecar issued same =>
    have bodyEq := method_view_injective viewEq
    have member : selectedMethod.specialized ∈ compiled.indexed.base.plan.specializations := by
      rw [← same]
      exact SelectedCompilationRegistryGlobals.exact_member (LambdaSourceAlignment.sidecar_lookup issued)
    have origin := CallablePreparedFinalCatalogOrigins.of_default_preparation
      (SourceCoreUnifiedPreparationCertificates.compiled_planPrepared compiled) selectedMethod.specialized member
    have certificate : ∃ types lexical facts, BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
        (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram selectedMethod) types lexical facts := by
      generalize rowEq : selectedMethod.specialized = row at origin member
      cases origin with
      | ordinary ordinary =>
        obtain ⟨implementation, implMember, owner⟩ := owner
        obtain ⟨request, signature, generic, signatureMember, _, _, accepted⟩ := ordinary
        have sameOwner : row.function.typedBody.owner = implementation.id := by
          rw [← rowEq]
          rw [bodyEq] at owner
          exact owner
        exact False.elim (function_impl_ne bodies.signatures signatureMember implMember
          ((row_owner accepted).symm.trans sameOwner))
      | method origin =>
        simpa only [CallableCoercionMethodInstantiation.bodyInstance, rowEq] using
          SelectedCompilationRegistryMethodCertificates.of_origin bodies checked ranges origin member
    exact SelectedCompilationMethodCertificateTransport.selected checked method (bodyEq.symm ▸ certificate)

/-- Actual checker success, selected original body typing and the existing
finite raw-range receipts certify the unchanged compiler registry. -/
theorem of_checked {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) :=
  ⟨bodies.signatures, SelectedCompilationRegistryGlobals.globals actual bodies checked,
    methods actual bodies checked ranges⟩

theorem of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    {native : SourceCoreGeneralFunctions.CallableContext}
    (actual : RecursiveNamedPreparedStageContracts.Prepared compiled native)
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (RecursiveNamedPreparedStageScopes.registry actual) :=
  of_checked actual bodies checked (SelectedCompilationRegistryMethodCertificates.ranges_of_profile profile)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryBodies
