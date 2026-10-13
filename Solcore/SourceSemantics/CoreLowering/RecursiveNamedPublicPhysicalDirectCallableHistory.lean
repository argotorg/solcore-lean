import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableApplicationBounds

/-! Actual history and input encoding supply direct callable arguments.
The retained callable may be named, builtin or a closure. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open RecursiveNamedPublicDirectPackedInputMeaning (StartAt)
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

variable {recipe : Recipe}
variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}

section Meaning
variable {initial completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support recipe.compiled headers keys initial)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (extension : SourceCoreRawMetadata.Extends initial.result.context.registry completion.result.context.registry)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority recipe.compiled mapping store)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functions" => CallableIndexedOwnedPreparedPhysicalProgramSupport.functions support
local notation "callStages" => CallableIndexedOwnedPreparedPhysicalProgramSupport.stages recipe.compiled
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include history member entryType input started parameterView metadata in
private theorem current_inputs :
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      (.function parameter result) entry.source callable
      (CallableContract.functionType nativeParameter nativeResult) ∧
    Dynamic.ValueHasType anchor.function.context before entry.source (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, represented, typed⟩ := history.current.2.2.2.2 entry member
  have callableEq := started.callable_eq imported
  rw [entryType] at represented typed
  rw [← callableEq] at represented
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    represented.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at represented
  obtain ⟨packedRelated, packedTyped⟩ := started.history_input_compatible history input parameterView.symm metadata
  exact ⟨represented, typed, packedRelated, packedTyped⟩

include support in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor support.wellFormed
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- Actual current history and packed encoding close the direct native result
against independent Source execution, including the ordered Source arguments. -/
theorem completed_reflects_at_arity
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs support history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  exact RecursiveNamedPublicPhysicalDirectCallableApplicationBounds.reflects_packed_at_arity support receiver extension caller physical stable
    (anchor_runtime support) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    (invocation := invocation) measured

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
theorem completed_reflects
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before entry.source sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨sources, packing, _arity, meaning⟩ := completed_reflects_at_arity support receiver extension history physical entry member entryType input
    started parameterView metadata completed invocation
  exact ⟨sources, packing, meaning⟩

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- The actual callable, encoded input and genuine Source arity derive native
completion for every sufficient fuel, including effects before a Source fault. -/
theorem has_sufficient_fuel_at_arity {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs support history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    RecursiveNamedPublicPhysicalDirectCallableApplicationBounds.preserves_packed support receiver extension caller physical stable
      (anchor_runtime support) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include support receiver extension physical
  history entry member entryType input started parameterView metadata in
/-- Source success supplies the arity without an additional boundary receipt. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value sourceResult) after value finalStore finalMap finalWorld callFaults := by
  exact has_sufficient_fuel_at_arity support receiver extension history physical entry member entryType input started parameterView metadata
    packing (.of_value trace) trace

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalDirectCallableHistory
