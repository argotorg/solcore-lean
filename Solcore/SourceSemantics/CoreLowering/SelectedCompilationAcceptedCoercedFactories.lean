import Solcore.SourceSemantics.CoreLowering.CompilerCoercedExpressionProfile
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedFactories

/-! The same returned-lambda compiler receipt exposes the inner constrained
direct call. Its full evidence suffix and accepted argument actions are used
before issuing the existing coerced closure certificate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3200000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedCoercedFactories
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (context)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedNamedSyntaxAdmission (DirectSite)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Supported)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open AcceptedNamedFactoryAdmission (Produced)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {row : SourceSpecialization.SpecializedFunction}
  (prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row)
  {instantiation : DeclarationInstantiation}
  {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
  (aligned : RecursiveNamedPreparedHeaders.Prepared.HeaderAt prepared instantiation header)
  {rows : List SourceSpecialization.SpecializedFunction}

private theorem origin_owner : ∃ signature ∈ compiled.sourceProgram.signatures.functions,
    prepared.named.specialized.function.typedBody.owner = signature.id := by
  obtain ⟨request, signature, generic, member, _genericMember, _resolved, accepted⟩ := prepared.origin
  have identities := RecursiveNamedSpecializationBodyFacts.identities accepted
  have fields := CallableCoercionBodyProvenance.specialization_fields accepted
  refine ⟨signature, member, ?_⟩
  rw [prepared.same, fields.1, SourceSpecialization.applyCheckedFunction_bodyOwner,
    identities.2.1, identities.1]

include aligned in
theorem of_produced (produced : Produced prepared header)
    (profile : CompilerCoercedExpressionProfile.Profile compiled prepared.named
      header.function.source rows produced.certificate.returnExpression)
    (supported : ∀ instantiation, DirectSite rows instantiation → Supported compiled.indexed.base.plan instantiation) :
    Nonempty (CallableIndexedOwnedPreparedCoercedClosureAdmission.BodyCertificate compiled
      prepared.named rows [produced.certificate.returnStatement]) := by
  have generated := produced.inner.generated
  change SourceCoreFunctions.lowerExpressionWithPolicy produced.action.root.selected.policy
    produced.action.root.selected.lowerBody (min produced.inner.childFuel produced.action.fuel)
    (context compiled.indexed prepared.named) header.function.source produced.compiler.bodyScope
    produced.certificate.returnExpression header.reasonAt = .ok produced.inner.child at generated
  generalize fuelEq : min produced.inner.childFuel produced.action.fuel = fuel at generated
  cases fuel with
  | zero => simp only [SourceCoreFunctions.lowerExpressionWithPolicy] at generated; cases generated
  | succ predecessor =>
    obtain ⟨head⟩ := AcceptedNamedExpressionFlow.Head.of_accepted generated
    have same : head.node = profile.node := Option.some.inj (head.found.symm.trans profile.found)
    obtain ⟨receipt⟩ := AcceptedCoercedDirectExpressionReceipt.of_head produced.action.root head
      (same ▸ profile.form) (supported _ profile.direct) (same ▸ profile.coercions) profile.initializer
    have children : ∀ argument ∈ profile.arguments,
        GeneralSyntax header.function.source argument (fun _ => False) :=
      AcceptedCoercedDirectExpressionReceipt.children produced.action.root receipt profile.children
    have terminal := produced.inner.terminal
    have metadata := profile.metadata
    have source := (CallableIndexedOwnedPreparedNamedSourceAdmissionTransport.header_data prepared aligned).1
    obtain ⟨signature, member, owner⟩ := origin_owner prepared
    exact ⟨{
      expression := produced.certificate.returnExpression
      node := profile.node
      callee := profile.callee
      arguments := profile.arguments
      instantiation := profile.instantiation
      terminal := Eq.mp (congrArg (fun source =>
        CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal source
          produced.certificate.returnExpression [produced.certificate.returnStatement]) source) terminal
      found := Eq.mp (congrArg (fun source => source.lookupExpression?
        produced.certificate.returnExpression = some profile.node) source) profile.found
      form := profile.form
      coercions := profile.coercions
      requirements := profile.requirements
      children := fun argument member => Eq.mp (congrArg (fun source =>
        GeneralSyntax source argument (fun _ => False)) source) (children argument member)
      initializer := profile.initializer
      direct := profile.direct
      metadata := Eq.mp (congrArg (fun source =>
        CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
          compiled.indexed prepared.named source (fun _ => False)) source) metadata
      signature := signature
      signatureMember := member
      sourceOwner := owner }⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationAcceptedCoercedFactories
