import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues

/-! Independent successful Source execution of named, builtin and closure
handles closes native execution and public Word export at the actual history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableWordPreservation
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
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
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
  {parameter : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter .word)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)


local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Every genuine public resume with enough native fuel and at least one
output-validation step succeeds with the Source Word and the actual reached
history. Raw result annotations may differ from the retained Source type. -/
theorem public_resume_has_sufficient_fuel
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {word : Core.Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value (.word word)) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ required finalStore finalMap finalWorld,
      (∀ executionFuel, required ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word (.word word)) finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context .word .word
        (.value (.word word)) after (.inRight .word (.word word)) finalStore finalMap finalWorld callFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧ publicCompletion.value = .word word ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation
            (.inRight .word (.word word)) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions completion.result.context.registry anchor actual.session
            finalMap finalWorld after finalStore reached entries ∧
          actual.session.RegistryAt encodedValues.registry := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  change SourceCoreRawMetadata.runtimeType actualResult = .word at resultView
  have projected := started.resultProjection
  rw [← recipe.compiled.compatible.checked.catalog.project_runtimeType actualResult, resultView] at projected
  have nativeWord : nativeResult = .word := (Except.ok.inj projected).symm
  subst nativeResult
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata packing trace
  have valueEq : value = .inRight .word (.word word) := by
    have represented := resultAt.1
    cases represented with
    | value related =>
        obtain ⟨actual, sourceEq, nativeEq⟩ := CompatibleExpressionPrimitives.word_fields related
        cases Dynamic.Value.word.inj sourceEq
        rw [nativeEq]
  subst value
  refine ⟨required, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome bound outputBound resumed
  have completed := enough executionFuel bound
  obtain ⟨publicCompletion, succeeded, publicValue⟩ :=
    resumed.runtime_word_succeeded atCheckpoint completed started.requested resultView (by omega)
  have actualResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion) :=
    succeeded ▸ resumed
  obtain ⟨actual, generation, actualValue, actualStore, actualCompleted, exported,
      valueAt, sourceAt, fuelAt, sessionAt⟩ := actualResume.indexed_succeeded atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, retained⟩ := history.after_packed_success started.original exported resultAt
  exact ⟨publicCompletion, actual, generation, reached, succeeded, publicValue, exported,
    ⟨valueAt, sourceAt, fuelAt, sessionAt⟩, related, retained, started.returned_registry exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableWordPreservation
