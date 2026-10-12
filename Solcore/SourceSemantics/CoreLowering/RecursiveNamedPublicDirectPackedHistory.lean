import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedApplicationBounds

/-! Actual history and input encoding supply direct closure arguments. Both
finite completion and sufficient native fuel use the same captured state and
complete returned caller, with Source and host raw signatures kept distinct. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedHistory
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
variable {completion : SourceCoreCallableIndexedPrograms.Completion recipe.compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt recipe.compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared recipe.compiled
    recipe.compiled.indexed.ancestry.graph.inputs.callable)
  (profile : recipe.compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations recipe.compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends recipe.compiled.compatible.checked.staticRegistry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers →
    CallableIndexedOwnedPreparedStagedNamedBodies.Body header)
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodiesSupport.Support headers keys bodyRegistry header
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) (namedTerminals header member) semanticFaults)
  (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {caller : Caller headers keys mapping world before store}
  {artifact : Artifact} {session : Session artifact} {entries : List Entry}
  (history : History headers keys
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    completion.result.context.registry anchor session mapping world before store caller entries)
  (entry : Entry) (member : entry ∈ entries)
  {parameter result actualParameter actualResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)
  {checkpoint : Checkpoint artifact} {inputFuel : Nat}
  {nativeParameter nativeResult : Core.Ty} {callable packed : Core.Value}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
    actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
  (parameterView : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType actualParameter)
  (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include history member entryType entrySource input started parameterView metadata in
private theorem current_inputs :
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      (.function parameter result) (.closure function) callable
      (CallableContract.functionType nativeParameter nativeResult) ∧
    Dynamic.ValueHasType anchor.function.context before (.closure function) (.function parameter result) ∧
    ValueRep recipe.compiled.compatible.checked completion.result.context.registry functions mapping world
      parameter packedSource packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context before packedSource parameter := by
  obtain ⟨imported, represented, typed⟩ := history.current.2.2.2.2 entry member
  have callableEq := started.callable_eq imported
  rw [entryType, entrySource] at represented typed
  rw [← callableEq] at represented
  have nativeTypeEq : entry.nativeType = CallableContract.functionType nativeParameter nativeResult :=
    represented.runtime_hasType.type_eq.symm.trans started.callableTyped.type_eq
  rw [nativeTypeEq] at represented
  obtain ⟨packedRelated, packedTyped⟩ := started.history_input_compatible history input parameterView.symm metadata
  exact ⟨represented, typed, packedRelated, packedTyped⟩

include wellFormed in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor wellFormed
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType entrySource input started parameterView metadata in
/-- Actual current history and packed encoding close the direct native result
against independent Source execution, including the ordered Source arguments. -/
theorem completed_reflects
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ sources,
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
          invocation anchor.function.context before (.closure function) sources outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs profile history entry member entryType entrySource input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  exact RecursiveNamedPublicDirectClosureApplicationBounds.reflects_packed receiver stagePrepared profile
    observations extension semantic family namedTerminals namedSupport wellFormed caller stable
    (anchor_runtime wellFormed) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    (invocation := invocation) measured

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType entrySource input started parameterView metadata in
/-- An independent application of this actual encoded input has sufficient
native fuel at the original checkpoint and retains the full semantic post. -/
theorem has_sufficient_fuel {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    (arity : sources.length = function.parameters.length)
    {sourceSize : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before (.closure function) sources outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ executionFuel, required ≤ executionFuel → checkpoint.NativeDone executionFuel value finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨calleeRelated, calleeTyped, packedRelated, packedTyped⟩ :=
    current_inputs profile history entry member entryType entrySource input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    RecursiveNamedPublicDirectClosureApplicationBounds.preserves_packed receiver stagePrepared profile
      observations extension semantic family namedTerminals namedSupport wellFormed caller stable
      (anchor_runtime wellFormed) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedHistory
