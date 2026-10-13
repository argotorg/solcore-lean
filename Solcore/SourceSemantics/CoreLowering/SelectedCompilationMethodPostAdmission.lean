import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodBodySupport

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload

theorem preserved {compiled : SourceCoreUnifiedCompilation.Compiled}
    {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (sourceAt : CallablePreparedMethodRuntimeProfileFactory.SourceAt principal.cached.compilation
      (.initial compiled.compatible.checked) principal.sourceBody principal.dictionary)
    (certified : SelectedCompilationMethodBodySupport.Certified principal sourceAt)
    {before after : Dynamic.Heap} {value : Dynamic.Value}
    (typed : Dynamic.ValueHasType sourceAt.context after value principal.sourceBody.resultType)
    (heap : Dynamic.HeapWellTyped sourceAt.context after)
    (metadata : Dynamic.HeapMetadataExtend before after) :
    Dynamic.ExpressionEvaluationPreserved principal.sourceBody.context before after value principal.sourceBody.resultType := by
  obtain ⟨_, certificate⟩ := certified
  have runtime := certificate.sourceRuntimeValid
  have fields := RecursiveNamedInitialContextValidity.mono_fields sourceAt.extended
  have supports : Dynamic.TypeContextSupports sourceAt.context principal.sourceBody.context :=
    Dynamic.TypeContextSupports.ofClosed fields.signatures.symm
      (fields.targetClosed runtime.closed) runtime.closed sourceAt.closed runtime.residual_variables_open
  exact ⟨typed.transportContext supports, heap.transportContext supports, metadata⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPostAdmission
