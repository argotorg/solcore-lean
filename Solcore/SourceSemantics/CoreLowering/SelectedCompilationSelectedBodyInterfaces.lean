import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfileBinders
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationBodyTyping
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCoercionInterfaces
import Solcore.SourceSemantics.SourceInferenceSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces
open Frontend SourceInference TypeSystem
open ExecutableCoercionInterfaces ExecutableBinderInterfaces
open SelectedCompilationBodyTyping CompilerProgramStaticProfile

private theorem original_interfaces {compiled : SourceCoreUnifiedCompilation.Compiled}
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : compiled.indexed.base.functions[index]? = some named)
    {signature : ProgramFunctionSignature} {generic : CheckedFunction} {supplied : ParameterSubstitution}
    (accepted : SourceSpecialization.specializeFunction signature generic supplied = .ok named.specialized) :
    BodyInterfaces compiled.sourceProgram.signatures generic := by
  apply SelectedCompilationCoercionInterfaces.of_applied (substitution := named.specialized.parameterSubstitution)
  rw [← (CallableCoercionBodyProvenance.specialization_fields accepted).1]
  exact SelectedCompilationCoercionInterfaces.cached compiled selected

/-- The actual selected ordinary definition receives both executable
interfaces and source-wide monomorphism from existing checker/compiler facts. -/
theorem ordinary {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (profile : StaticProfile compiled) {generic : CheckedFunction}
    (selected : OrdinarySource compiled generic) :
    BodyInterfaces compiled.sourceProgram.signatures generic ∧ SourceMonomorphic generic.typedBody := by
  obtain ⟨index, named, signature, supplied, cached, _, member, accepted⟩ := selected
  obtain ⟨_, _, bodyChecked⟩ := Frontend.checkProgram_success_function_body checked member
  exact ⟨original_interfaces cached accepted,
    SelectedCompilationProfileBinders.of_profile profile cached accepted
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed bodyChecked)⟩

/-- Methods retain their genuine selected method identity and complete
original checker carrier. No ordinary-origin or whole-program typing fact is used. -/
theorem method {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : Frontend.checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (profile : StaticProfile compiled) {retained : CheckedImplementationMethod}
    (selected : MethodSource compiled retained) :
    BodyInterfaces compiled.sourceProgram.signatures retained.checked ∧
      SourceMonomorphic retained.checked.typedBody := by
  obtain ⟨index, named, method, cached, same, selection, member, _, identical⟩ := selected
  have accepted : SourceSpecialization.specializeFunction
      (selection.implementation.functionSignatureOfMethodWithTrait selection.trait selection.declaration)
      retained.checked selection.supplied = .ok named.specialized := by
    simpa only [identical, same] using selection.specialized
  obtain ⟨_, _, _, _, _, _, _, bodyChecked⟩ := Frontend.checkProgram_success_method_body checked member
  exact ⟨original_interfaces cached accepted,
    SelectedCompilationProfileBinders.of_profile profile cached accepted
      (SourceInferenceSoundness.checkFunctionBody_success_occurrenceGraphClosed bodyChecked)⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationSelectedBodyInterfaces
