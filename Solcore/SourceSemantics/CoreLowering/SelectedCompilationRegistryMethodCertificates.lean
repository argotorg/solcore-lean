import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodCertificateTransport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryLambdaExclusion
import Solcore.SourceSemantics.CoreLowering.CompilerProgramStaticProfile

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
open Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.Dynamic

/-- The existing flat profile retains the complete raw replacement range at
all actual cache positions, including method rows. -/
def Ranges (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop :=
  ∀ (index : Nat) (named : SourceCoreGeneralFunctions.Function), compiled.indexed.base.functions[index]? = some named →
    SourceSemantics.ParameterSubstitution.RangeWellFormed
      (Context.ofSignatures compiled.sourceProgram.signatures) named.specialized.parameterSubstitution

theorem ranges_of_profile {compiled : SourceCoreUnifiedCompilation.Compiled}
    (profile : CompilerProgramStaticProfile.StaticProfile compiled) : Ranges compiled := by
  intro index named selected
  have bound : index < compiled.indexed.base.functions.length := by
    exact List.getElem?_eq_some_iff.mp selected |>.1
  obtain ⟨row⟩ := profile.rows ⟨index, bound⟩
  have same : compiled.indexed.base.functions[index] = named := by
    exact List.getElem?_eq_some_iff.mp selected |>.2
  rw [same] at row
  cases row with
  | ordinary eligible _ _ => exact eligible.range
  | method _ range _ _ => exact range

/-- A final method origin supplies its complete original checker body. Its
retained raw range permits the same structural instance certificate used by
actual invocation, with no requirement that a body view determine a method ID. -/
theorem of_origin {compiled : SourceCoreUnifiedCompilation.Compiled}
    (bodies : SelectedCompilationBodyTyping.Bodies compiled)
    {raw : Workspace.RawWorkspace} {fuel : Nat}
    (checked : Frontend.checkProgram raw fuel = .ok compiled.sourceProgram)
    (ranges : Ranges compiled)
    {method : ExecutableImplMethods.CheckedMethod}
    (origin : CallableCoercionBodyProvenance.Selection compiled.sourceProgram method)
    (member : method.specialized ∈ compiled.indexed.base.plan.specializations) :
    ∃ types lexical facts, BodyInstanceTypingCertificate (Program.ofChecked compiled.sourceProgram)
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method)
      types lexical facts := by
  obtain ⟨cached⟩ := CallablePreparedMethodSelection.cached_row compiled member
  have range := ranges cached.index cached.named cached.selected
  rw [cached.same] at range
  obtain ⟨retained, retainedMember, retainedId, complete⟩ :=
    origin.retained (CallableMethodBodyCoherence.of_checked checked)
  let receipt : CallableCoercionBodyProvenance.Certificate compiled.sourceProgram method :=
    ⟨origin, retained, retainedMember, retainedId, complete⟩
  have valid := bodies.methods retained
    ⟨cached.index, cached.named, method, cached.selected, cached.same,
      origin, retainedMember, retainedId, complete⟩
  have owner : retained.checked.declaration = origin.implementation.id := by
    rw [← complete]
    exact checkFunctionBody_success_declaration origin.bodyChecked
  have traitMember : origin.trait ∈ compiled.sourceProgram.signatures.traits :=
    List.mem_of_find?_eq_some origin.traitLookup
  have traitOwner : origin.declaration.traitMethod.trait = origin.trait.id := by
    have found := origin.traitLookup
    unfold ProgramSignatures.trait? at found
    have same : decide (origin.trait.id = origin.declaration.traitMethod.trait) = true :=
      List.find?_some (p := fun trait : ProgramTraitSignature =>
        decide (trait.id = origin.declaration.traitMethod.trait)) found
    exact (of_decide_eq_true same).symm
  have exactSubstitution : SourceSemantics.ParameterSubstitution.Exact
      method.specialized.parameterSubstitution origin.implementation.parameters := by
    refine ⟨(bodies.signatures.implementations_semantic origin.implementation origin.implementationMember).parameters_nodup, ?_⟩
    rw [SourceSemantics.ParameterSubstitution.domain,
      SourceSpecialization.specializeFunction_parameterDomain origin.specialized]
    rfl
  have instantiates : TraitMethodInstantiates (Program.ofChecked compiled.sourceProgram)
      origin.implementation origin.declaration origin.trait (MethodDefinition.ofChecked retained)
      method.specialized.parameterSubstitution
      (CallableCoercionMethodInstantiation.bodyInstance compiled.sourceProgram method) := by
    apply TraitMethodInstantiates.intro origin.implementationMember origin.methodMember
      traitMember traitOwner (List.mem_map.mpr ⟨retained, retainedMember, rfl⟩)
      (retainedId.trans origin.methodId) owner exactSubstitution range
    · exact receipt.body
    · exact receipt.result.1
    · change declarationContext compiled.sourceProgram.signatures method.specialized.function.typedBody.owner []
        method.specialized.assumptions method.specialized.function.solvedRequirements = _
      rw [receipt.owner, receipt.assumptions, receipt.ledger]
      change declarationContext compiled.sourceProgram.signatures origin.implementation.id [] _ _ =
        declarationContext compiled.sourceProgram.signatures retained.checked.declaration [] _ _
      rw [owner]
      rfl
  obtain ⟨types, lexical, facts, certificate⟩ := instantiates.certificate_of_valid bodies.signatures valid
  exact ⟨types, lexical, facts, certificate.toBodyInstanceTypingCertificate⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRegistryMethodCertificates
