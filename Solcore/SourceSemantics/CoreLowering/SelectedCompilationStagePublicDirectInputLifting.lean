import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectCallableLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSessionDirectFailures
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicHistorySourceInputs

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

/-- Ordinary successful application fixes the genuine unpacked arity. -/
theorem arity_of_value {program : Program} {context : Context}
    {caller invocation : Dynamic.EvidenceEnvironment} {before after : Dynamic.Heap}
    {function value : Dynamic.Value} {arguments : List Dynamic.Value}
    (trace : Dynamic.CallableApplies program context caller invocation before function arguments value after) :
    RecursivePublicCallableArity.Arity program function arguments.length := by
  cases trace with
  | builtin applied =>
    have length := (applied.preserves (context := context) (heap := before)).1.length_eq
    exact length ▸ .builtin _
  | global instantiates _ _ invoked =>
    cases invoked with
    | returned _ _ _ allocated _ _ => exact allocated.length_eq ▸ .global instantiates
    | unit _ _ _ _ allocated _ _ => exact allocated.length_eq ▸ .global instantiates
  | closure _ _ _ allocated _ _ => exact allocated.length_eq ▸ .closure _
  | closureUnit _ _ _ _ allocated _ _ => exact allocated.length_eq ▸ .closure _

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Profiled recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

/-- The real packed input registry and retained history provide every physical
argument needed to lift an ordinary call through its complete callable value. -/
theorem lift_call
    (state : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries)
    {parameter result : TypeSystem.Ty}
    (entryType : entry.sourceType = .function parameter result)
    {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument packedSource)
    {inputFuel : Nat} {checkpoint : SourceCoreExecution.Checkpoint artifact}
    (accepted : session.startHandlePacked entry.handle argument inputFuel = .ok checkpoint)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram)
      entry.source sources.length)
    {plain : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : FunctionCallBody.Outcome (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
      state.heap entry.source sources plain after) :
    Staging.Recursive.Lifting.ApplicationLift (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) invocation
      anchor.function.context state.heap entry.source sources plain after := by
  obtain ⟨nativeCheckpoint, _atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start state.atSession accepted
  have imported := (state.history.semantic.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
      started, _parameterView, _resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible state.atRecipe
      state.history.semantic.current.1 imported original
  obtain ⟨receiving, _indexed, contextAt, receiver, extended, retained, _represented, _typed, _diagnostics⟩ :=
    RecursiveNamedPublicActualRegistryStart.packed_input state.history.semantic state.registry
      member entryType input started
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving.result.context.registry := by
    rw [contextAt]
    exact .refl _
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨currentImported, calleeRelated, calleeTyped⟩ := retained.current.2.2.2.2 entry member
  have callableEq := started.callable_eq currentImported
  rw [entryType] at calleeRelated calleeTyped
  rw [← callableEq] at calleeRelated
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    calleeRelated.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at calleeRelated
  obtain ⟨packedRelated, packedTyped⟩ :=
    started.history_input_compatible retained input parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := retained.current
  exact SelectedCompilationStagePublicDirectCallableLifting.lifts_packed
    issued.support receiver (state.extension.trans extended) state.caller state.history.physical stable
    (SelectedCompilationPublicHistorySourceInputs.header_runtime issued.support.bodyTyping anchor)
    heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated packing arity trace

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStagePublicDirectInputLifting
