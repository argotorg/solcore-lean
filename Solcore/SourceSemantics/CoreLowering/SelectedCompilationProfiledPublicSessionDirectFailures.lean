import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectFailureForward
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure

/-! Actual failed calls through retained handles preserve their original
callable, full dictionary, exact heap and complete prior history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- The original constructor determines whether the fault is an ordinary
Dynamic fault or a rejected stage guard. -/
def DirectFailureProjection (program : Program) (context : Context)
    (invocation : Staging.Recursive.Scope) (before : Dynamic.Heap)
    (callable : Dynamic.Value) (arguments : List Dynamic.Value)
    (failure : Staging.Recursive.Failure) (after : Dynamic.Heap) : Prop :=
  match failure with
  | .semantic reason => Dynamic.CallableFaults program context invocation.evidence
      (Staging.Recursive.callableEvidence callable) before callable arguments reason after
  | .stage origin call reason => Staging.Recursive.Generated origin call reason

theorem Profiled.reflect_direct_failure
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {returned : SourceCoreExecution.Session artifact} {reason : Word}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ failure, ∃ next : issued.toIssued.State anchor returned entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.fault failure) next.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        next.receiving.result.diagnostics failure reason :=
  SelectedCompilationPublicSessionDirectFailureStep.State.invoke_failure
    issued.support issued.registryBodies issued.prepared before entry member entryType input invoked invocation

theorem Profiled.reflect_direct_failure_plain
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {options : SourceCoreExecution.RunOptions}
    {returned : SourceCoreExecution.Session artifact} {reason : Word}
    (invoked : session.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ sources, Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ failure, ∃ next : issued.toIssued.State anchor returned entries,
      ∃ size, Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
        (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.fault failure) next.heap ∧
      DirectFailureProjection (Program.ofChecked recipe.compiled.sourceProgram) anchor.function.context
        invocation before.heap entry.source sources failure next.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
        next.receiving.result.diagnostics failure reason := by
  obtain ⟨sources, packing, arity, failure, next, size, trace, diagnostic⟩ :=
    issued.reflect_direct_failure before entry member entryType input invoked invocation
  refine ⟨sources, packing, arity, failure, next, size, trace, ?_, diagnostic⟩
  cases failure with
  | semantic reason => exact trace.sound.semanticFault_plain
  | stage origin call reason => exact trace.sound.stage_origin rfl

theorem Profiled.forward_direct_failure
    (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok checkpoint)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) sourceSize
      invocation anchor.function.context before.heap entry.source sources (.fault failure) after) :
    SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt
      issued.catalog.rows anchor issued.initial issued.support.profile recipe entries failure checkpoint after :=
  SelectedCompilationPublicSessionDirectFailureForward.forward_call
    issued.support issued.registryBodies issued.prepared before entry member entryType input accepted ready packing arity trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
