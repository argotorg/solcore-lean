import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure

/-! Actual calls through retained handles expose the original independent
Source callable and its exact application at the same returned session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- Packed public input, the retained callable and the actual completion
determine the ordered Source arguments and both Source outcome witnesses. -/
theorem Issued.reflect_direct_scalar_plain
    (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (scalar : ScalarOutput)
    {parameter hostParameter : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter scalar.sourceType)
    (handleType : entry.handle.sourceType = .function hostParameter scalar.sourceType)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {completion : SourceCoreExecution.Completion artifact}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.succeeded completion)))
    (output : completion.value = scalar.publicValue)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram)
        entry.source sources.length ∧
      ∃ next : issued.State anchor completion.session entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.value scalar.source) next.heap ∧
      Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram)
        anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
        before.heap entry.source sources scalar.source next.heap := by
  obtain ⟨sources, packing, arity, next, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member scalar entryType handleType input invoked output invocation
  exact ⟨sources, packing, arity, next, size, trace, trace.sound.value_plain⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
