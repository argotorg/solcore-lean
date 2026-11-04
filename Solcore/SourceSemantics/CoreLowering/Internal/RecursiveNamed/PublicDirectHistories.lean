import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.PhysicalPublic
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.NamedEvidenceRoots
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectClosureApplications
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicFunctionHistory
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicNestedInputs
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicDirectApplications
import Solcore.SourceSemantics.Staging.RecursiveFaultPreservation
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveValues

/-!
# Recursive named public results: direct histories

Histories of direct calls through a handle: meaning of the handle and its packed input, failures, preservation of words and functions, and registry extension.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
/-! Actual declaration frames supply the callable type and independent Source
runtime needed to preserve the state of a failed public invocation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
open Core Frontend SourceInference
open CallableIndexedOwnedFunctionValues (Header NamedSourceAt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))

include wellFormed

theorem header_runtime
    (header : Header compiled (Program.ofChecked compiled.sourceProgram)) :
    Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram)
      header.function.context header.function.source := by
  obtain ⟨_, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate header wellFormed
  rw [header.frame.context, header.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

theorem source_function_type
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source) :
    header.named.specialized.function.type =
      .function (TypeSystem.Ty.productMany header.types) header.function.resultType := by
  obtain ⟨types, context, facts, certificate⟩ := sourceAt.frame.instantiated.certificate wellFormed
  have extended := header.extended
  rw [sourceAt.frame.source, sourceAt.frame.context, sourceAt.frame.parameters] at extended
  have typesEq := (Dynamic.MonoBindersExtend.bodyTypes_eq certificate.typing.inputs_extend).symm.trans
    (Dynamic.MonoBindersExtend.bodyTypes_eq extended)
  have actualType : source.instantiation.type = header.named.specialized.function.type := by
    rw [sourceAt.retained]
    rfl
  rw [← actualType, certificate.callable_type, typesEq, sourceAt.frame.result]

theorem source_typed
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {source : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD source)
    (anchor : Header compiled (Program.ofChecked compiled.sourceProgram)) (heap : Dynamic.Heap) :
    Dynamic.ValueHasType anchor.function.context heap (.global source)
      (.function (TypeSystem.Ty.productMany header.types) header.function.resultType) := by
  rw [← source_function_type wellFormed sourceAt]
  exact RecursiveNamedPublicCurrentFactoryValues.source_typed sourceAt anchor heap

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistorySourceInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
/-! The actual direct-handle checkpoint supplies selection, packed input and
native execution. Retained Source meaning is taken from the current caller,
then the established body family reflects that same native application. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursivePublicApplicationResult (ResultAt)
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)

/-- The actual packed Unit encoder and authenticated selection determine the
complete initial native call. No payload representation is assumed here. -/
theorem unit_initial {recipe : Recipe} {artifact : Artifact} {session : Session artifact}
    {handle : SourceCorePublicValues.Handle} {checkpoint : Checkpoint artifact} {fuel oldFuel : Nat}
    {result : TypeSystem.Ty} {native : Core.Value} {world : StoreTyping} {store : Store}
    (atRecipe : ArtifactRecipe artifact recipe)
    (nativeAt : session.NativeAt world store)
    (handleType : handle.sourceType = .function .unit result)
    (imported : session.EncodesAt oldFuel (.function .unit result) (.function handle) native)
    (started : checkpoint.HandleStart session handle .unit fuel) :
    ∃ nativeResult,
      recipe.compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      native.type = CallableContract.functionType .unit nativeResult ∧
      CheckpointInitial checkpoint CallableIndexedLambdaCalls.applyPayload
        (native :: .unit :: SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  obtain ⟨parameter, actualResult, nativeParameter, nativeResult, callable, registry, raw, encodedValues,
    selected, _registryAt, encoded, _valuesAt, _rawRegistry, _owner, _typed, requested, payloadType, initial⟩ := started.details
  obtain ⟨rfl, rfl⟩ := selected.signature handleType
  have nativeParameterEq : nativeParameter = .unit :=
    (Except.ok.inj selected.spec.2.2.1).symm
  have callableEq := selected.callable_eq imported
  have packedEq := encoded.unit
  have typed := selected.spec.2.2.2.2.2.1.type_eq
  rw [nativeParameterEq, callableEq] at typed
  refine ⟨nativeResult, selected.spec.2.2.2.1, requested, payloadType, typed, ?_⟩
  cases session
  rename_i sessionAuthority actualWorld actualStore stored environmentTyped slots values owner sourcePrefix
  change actualWorld = world ∧ actualStore = store at nativeAt
  rcases nativeAt with ⟨rfl, rfl⟩
  rw [callableEq, packedEq] at initial
  cases checkpoint
  exact initial

/-- The facade's accepted start selects the same indexed session and original
checkpoint, without starting a second invocation. -/
theorem recover_handle_start {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {artifact : Artifact} {session : Session artifact}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value} {fuel : Nat}
    (atSession : publicSession.IndexedAt session)
    (accepted : publicSession.startHandlePacked handle argument fuel = .ok publicCheckpoint) :
    ∃ checkpoint : Checkpoint artifact,
      publicCheckpoint.IndexedAt checkpoint ∧ checkpoint.HandleStart session handle argument fuel := by
  rcases publicArtifact with ⟨publicCompiled, opened⟩
  cases opened with
  | empty selected => exact False.elim atSession
  | indexed actualRecipe selected actualArtifact recipeAt =>
    rcases publicSession with ⟨actualSession⟩
    rcases atSession with ⟨rfl, sameSession⟩
    have same : actualSession = session := eq_of_heq sameSession
    subst actualSession
    obtain ⟨foundRecipe, foundArtifact, foundSession, checkpoint,
      _openedAt, atFound, atCheckpoint, startEq⟩ :=
      SourceCoreExecution.Session.startHandlePacked_indexed (compiled := publicCompiled)
        (checkpoint := publicCheckpoint) rfl accepted
    have artifactEq : actualArtifact = foundArtifact := atFound.1
    cases artifactEq
    have sessionEq : session = foundSession := eq_of_heq atFound.2
    cases sessionEq
    exact ⟨checkpoint, atCheckpoint, Session.startHandlePacked_receipt session startEq⟩

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}

section Meaning
variable {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends compiled.compatible.checked.staticRegistry
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
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {scope : SourceCoreLocalCell.Scope} {mapping : LocationMap} {world : StoreTyping}
  {before : Dynamic.Heap} {store : Store} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)
  (heapTyped : Dynamic.HeapWellTyped context before)
  {function : Dynamic.Closure} {native : Core.Value} {result : TypeSystem.Ty}
  (calleeTyped : Dynamic.ValueHasType context before (.closure function) (.function .unit result))
  {nativeType : Core.Ty}
  (calleeRelated : ValueRep compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world (.function .unit result) (.closure function) native
    nativeType)
  (parameters : function.parameters = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable {recipe : Recipe} {artifact : Artifact} {session : Session artifact}
  {checkpoint : Checkpoint artifact} {handle : SourceCorePublicValues.Handle}
  {inputFuel oldFuel : Nat}
  (prepared : Recipe.prepare compiled = .ok recipe)
  (atRecipe : ArtifactRecipe artifact recipe)
  (nativeAt : session.NativeAt world store)
  (handleType : handle.sourceType = .function .unit result)
  (imported : session.EncodesAt oldFuel (.function .unit result) (.function handle) native)

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated parameters heaps
  prepared atRecipe nativeAt handleType imported in
/-- Finite completion of the actual direct checkpoint constructs an independent
Source application and the complete returned caller postcondition. -/
theorem completed_reflects_unit
    (started : checkpoint.HandleStart session handle .unit inputFuel)
    {executionFuel : Nat} {value : Core.Value} {finalStore : Store}
    (completed : checkpoint.NativeDone executionFuel value finalStore)
    (invocation : Staging.Recursive.Scope) :
    ∃ nativeResult,
      compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      ∃ sourceSize outcome after finalMap finalWorld,
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
          invocation context before (.closure function) [] outcome after ∧
        ResultAt (registry := completion.result.context.registry) functions caller context result nativeResult
          outcome after value finalStore finalMap finalWorld callFaults := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨nativeResult, projected, requested, payloadType, nativeTypeEq, initial⟩ :=
    unit_initial atRecipe nativeAt handleType imported started
  have typeEq : nativeType = CallableContract.functionType .unit nativeResult :=
    calleeRelated.runtime_hasType.type_eq.symm.trans nativeTypeEq
  have related := calleeRelated
  rw [typeEq] at related
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (initial.native_done_iff.mp completed))
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectClosureApplicationBounds.reflects_unit receiver stagePrepared profile
      observations extension semantic family namedTerminals namedSupport wellFormed caller stable runtime
      heapTyped calleeTyped related parameters heaps (invocation := invocation) measured
  exact ⟨nativeResult, projected, requested, payloadType, sourceSize, outcome, after, finalMap, finalWorld,
    trace, resultAt⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
  wellFormed caller stable runtime heapTyped calleeTyped calleeRelated parameters heaps
  prepared atRecipe nativeAt handleType imported in
/-- One successful public invokePacked call retains its actual indexed start,
export, value and session alongside independent Source execution. -/
theorem public_invoke_succeeded_reflects_unit
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt handle .unit options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (nativeResult : Core.Ty) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping),
      checkpoint.HandleStart session handle .unit options.inputValidationFuel ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      compiled.compatible.checked.catalog.project result = .ok nativeResult ∧
      checkpoint.ResultTypeAt result ∧ checkpoint.PayloadTypeAt nativeResult ∧
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) callStages sourceSize
        invocation context before (.closure function) [] outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, started⟩ := recover_handle_start atSession accepted
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨nativeResult, projected, requested, payloadType, sourceSize, outcome, after, finalMap, finalWorld,
    trace, resultAt⟩ :=
    completed_reflects_unit receiver stagePrepared profile observations extension semantic family
      namedTerminals namedSupport wellFormed caller stable runtime heapTyped calleeTyped calleeRelated
      parameters heaps prepared atRecipe nativeAt handleType imported started completed invocation
  exact ⟨checkpoint, actual, generation, value, finalStore, nativeResult, sourceSize, outcome, after, finalMap, finalWorld,
    started, exported, ⟨valueEq, typeEq, budgetEq, sessionAt⟩, projected, requested, payloadType, trace, resultAt⟩
end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectHandleMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
/-! Packed host arguments keep the original encoder and current function
history. Structural input descriptions supply Source values; no representation
or body execution law is a premise. Inputs that register new raw metadata need
an actual extension into the chosen receiving registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistory (History Entry Caller)
open CallableIndexedOwnedFunctionValues (Header)

/-- The actual direct startup, including its complete packed input and current
native store. Packing has no implicit host-list arity convention. -/
structure StartAt {artifact : Artifact} (session : Session artifact)
    (handle : SourceCorePublicValues.Handle) (argument : SourceCorePublicValues.Value) (fuel : Nat)
    (checkpoint : Checkpoint artifact) (recipe : Recipe) (world : StoreTyping) (store : Store)
    (parameter result : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
    (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context) : Prop where
  recipe_eq : ArtifactRecipe artifact recipe
  state : session.NativeAt world store
  original : checkpoint.HandleStart session handle argument fuel
  selected : session.HandleSelectionAt handle parameter result nativeParameter nativeResult callable
  parameterProjection : recipe.compiled.compatible.checked.catalog.project parameter = .ok nativeParameter
  resultProjection : recipe.compiled.compatible.checked.catalog.project result = .ok nativeResult
  requested : checkpoint.ResultTypeAt result
  payloadType : checkpoint.PayloadTypeAt nativeResult
  callableTyped : RuntimeValueHasType world callable (CallableContract.functionType nativeParameter nativeResult)
    recipe.compiled.indexed.layouts.definitions
  packedTyped : RuntimeValueHasType world packed nativeParameter recipe.compiled.indexed.layouts.definitions
  initial : CheckpointInitial checkpoint CallableIndexedLambdaCalls.applyPayload
    (callable :: packed :: SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) store
  values : CheckpointValues checkpoint encodedValues
  owner : encodedValues.checked = recipe.compiled.compatible.checked
  raw : ∃ (before : SourceCoreRawMetadata.Registry)
    (encoded : SourceCoreCompatibleValues.Extended before Core.Value),
    session.RegistryAt before ∧ before.signatures = recipe.compiled.compatible.checked.signatures ∧
    session.RawEncodedAt fuel before parameter argument encoded ∧
    encoded.value = packed ∧ encoded.registry = encodedValues.registry

/-- Inverting the successful original startup derives all input and state
receipts. The real selection fixes the requested raw signature. -/
theorem of_original {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ parameter result nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        parameter result nativeParameter nativeResult callable packed encodedValues := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, before, raw, encodedValues,
    selected, registryAt, encoded, valuesAt, rawRegistry, owner, packedTyped, requested, payloadType, initial⟩ :=
    started.details
  have selectedSpec := selected.spec
  cases session
  rename_i sessionAuthority actualWorld actualStore stored environmentTyped slots values valuesOwner sourcePrefix
  change actualWorld = world ∧ actualStore = store at nativeAt
  rcases nativeAt with ⟨rfl, rfl⟩
  have beforeOwner : before.signatures = recipe.compiled.compatible.checked.signatures := by
    change values.registry = before at registryAt
    rw [← registryAt]
    exact values.registryOwner.trans
      (congrArg SourceCoreCompatibleCatalog.Checked.signatures valuesOwner)
  refine ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, raw.value, encodedValues,
    ⟨rfl, ⟨rfl, rfl⟩, started, selected, selectedSpec.2.2.1, selectedSpec.2.2.2.1,
      requested, payloadType, selectedSpec.2.2.2.2.2.1, packedTyped, ?_, ?_, owner,
      before, raw, registryAt, beforeOwner, encoded, rfl, rawRegistry.symm⟩⟩
  · cases checkpoint
    exact initial
  · cases checkpoint
    exact valuesAt

/-- Whole function exports can identify the exact selected raw signature. -/
theorem actual_start {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
    {parameter result : TypeSystem.Ty}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (handleType : handle.sourceType = .function parameter result)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        parameter result nativeParameter nativeResult callable packed encodedValues := by
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩ :=
    of_original atRecipe nativeAt started
  obtain ⟨rfl, rfl⟩ := actual.selected.signature handleType
  exact ⟨nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩

/-- Prior real import proves compatibility with the selected raw signature.
Source annotations remain independent from annotations erased by a containing
product's original encoder and decoder. -/
theorem actual_start_compatible {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {checkpoint : Checkpoint artifact} {fuel oldFuel : Nat} {world : StoreTyping} {store : Store}
    {parameter result : TypeSystem.Ty} {native : Core.Value}
    (atRecipe : ArtifactRecipe artifact recipe) (nativeAt : session.NativeAt world store)
    (imported : session.EncodesAt oldFuel (.function parameter result) (.function handle) native)
    (started : checkpoint.HandleStart session handle argument fuel) :
    ∃ actualParameter actualResult nativeParameter nativeResult callable packed encodedValues,
      StartAt session handle argument fuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result := by
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual⟩ :=
    of_original atRecipe nativeAt started
  have actualView := actual.selected.spec.2.1
  have importedView := imported.function_type
  have same := TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  exact ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues, actual, same⟩

section Inputs
variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
  {checkpoint : Checkpoint artifact} {fuel : Nat} {world : StoreTyping} {store : Store}
  {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
  {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
  (started : StartAt session handle argument fuel checkpoint recipe world store
    parameter result nativeParameter nativeResult callable packed encodedValues)

include started

/-- Existing history supplies current meanings for every nested handle. The
actual encoder supplies the packed native payload and all registry changes. -/
theorem StartAt.history_input_compatible
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value} {sourceParameter : TypeSystem.Ty}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      sourceParameter argument source)
    (compatible : SourceCoreRawMetadata.runtimeType parameter = SourceCoreRawMetadata.runtimeType sourceParameter)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  have current := history.current
  obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
    receipt started.recipe_eq
    (fun entry member => (current.2.2.2.2 entry member).1)
    (fun entry member => (current.2.2.2.2 entry member).2.1)
    (fun entry member => (current.2.2.2.2 entry member).2.2)
  obtain ⟨before, encoded, _registry, owner, accepted, valueEq, registryEq⟩ := started.raw
  have typed := started.packedTyped
  rw [← valueEq] at typed
  have extended : SourceCoreRawMetadata.Extends encoded.registry receiving := registryEq ▸ metadata
  have represented := meaning owner compatible accepted started.parameterProjection typed extended
  rw [valueEq] at represented
  exact ⟨represented, sourceTyped⟩

/-- Exact source signatures are the reflexive compatibility case. -/
theorem StartAt.history_input
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world parameter source packed nativeParameter ∧
      Dynamic.ValueHasType anchor.function.context heap source parameter :=
  started.history_input_compatible history receipt rfl metadata

/-- A whole-function export retains literal requested result type equality. -/
theorem StartAt.requested_exact {expectedParameter expectedResult : TypeSystem.Ty}
    (handleType : handle.sourceType = .function expectedParameter expectedResult) :
    checkpoint.ResultTypeAt expectedResult := by
  have same := started.selected.signature handleType
  exact same.2 ▸ started.requested

/-- The retained callee encoding identifies exactly the original selected
native callable, including its captured environment. -/
theorem StartAt.callable_eq {oldFuel : Nat} {expected : TypeSystem.Ty} {native : Core.Value}
    (imported : session.EncodesAt oldFuel expected (.function handle) native) : callable = native :=
  started.selected.callable_eq imported

/-- Actual simple input encoding preserves the session's metadata registry. -/
theorem StartAt.simple_registry (simple : SimplePublic argument)
    {registry : SourceCoreRawMetadata.Registry} (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  have same := started.original.simple_registry simple
  have values := started.values
  cases checkpoint
  change _ = encodedValues at values
  dsimp only at same
  rw [values] at same
  exact same.trans atRegistry

/-- The real encoder preserves metadata for arbitrary products of simple
values and retained function handles. -/
theorem StartAt.function_tree_registry (simple : FunctionTreeSimple argument)
    {registry : SourceCoreRawMetadata.Registry} (atRegistry : session.RegistryAt registry) :
    encodedValues.registry = registry := by
  obtain ⟨before, encoded, beforeAt, _owner, accepted, _value, registryEq⟩ := started.raw
  have encodedRegistry := accepted.function_tree_registry simple
  have beforeEq : before = registry := beforeAt.symm.trans atRegistry
  exact registryEq.symm.trans (encodedRegistry.trans beforeEq)

/-- Metadata-free packed input trees derive their receiving condition from
the actual session registry, including handles at arbitrary product depth. -/
theorem StartAt.history_input_function_tree
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)}
    {receiving registry : SourceCoreRawMetadata.Registry}
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {mapping : LocationMap} {heap : Dynamic.Heap} {caller : Caller headers keys mapping world heap store}
    {entries : List Entry} {source : Dynamic.Value}
    (history : History headers keys functions receiving anchor session mapping world heap store caller entries)
    (receipt : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context
      parameter argument source)
    (simple : FunctionTreeSimple argument) (atRegistry : session.RegistryAt registry)
    (extension : SourceCoreRawMetadata.Extends registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      parameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source parameter := by
  apply started.history_input history receipt
  rw [started.function_tree_registry simple atRegistry]
  exact extension

/-- The successful exporter returns the very metadata context retained by
this startup, allowing the next invocation to use the actual registry. -/
theorem StartAt.returned_registry
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {native : Core.Value} {finalStore : Store} {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel outputFuel generation native finalStore completion) :
    completion.session.RegistryAt encodedValues.registry := by
  have registry := started.original.returned_registry succeeded
  have values := started.values
  cases checkpoint
  change _ = encodedValues at values
  dsimp only at registry
  rw [values] at registry
  exact registry
end Inputs
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedInputMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
/-! Actual history and input encoding supply direct callable arguments.
The retained callable may be named, builtin or a closure. Source and host raw
signatures remain distinct, and the complete returned caller is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
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

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
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

include wellFormed in
private theorem anchor_runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
    anchor.function.context anchor.function.source := by
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor wellFormed
  rw [anchor.frame.context, anchor.frame.source]
  exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
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
    current_inputs profile history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨size, measured⟩ := evaluation_has_size
    (runStateful_evaluation_sound (started.initial.native_done_iff.mp completed))
  exact RecursiveNamedPublicDirectCallableApplicationBounds.reflects_packed_at_arity receiver stagePrepared profile
    observations extension semantic family namedTerminals namedSupport wellFormed caller stable
    (anchor_runtime wellFormed) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
    (invocation := invocation) measured

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
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
  obtain ⟨sources, packing, _arity, meaning⟩ := completed_reflects_at_arity receiver stagePrepared profile observations
    extension semantic family namedTerminals namedSupport wellFormed history entry member entryType input
    started parameterView metadata completed invocation
  exact ⟨sources, packing, meaning⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
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
    current_inputs profile history entry member entryType input started parameterView metadata
  obtain ⟨_native, heaps, stable, heapTyped, _entries⟩ := history.current
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableApplicationBounds.preserves_packed receiver stagePrepared profile
      observations extension semantic family namedTerminals namedSupport wellFormed caller stable
      (anchor_runtime wellFormed) heapTyped calleeTyped calleeRelated heaps packedTyped packedRelated
      (tail := SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) packing arity trace
  obtain ⟨required, enough⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨value, finalStore, finalMap, finalWorld, required,
    fun fuel bound => started.initial.native_done_iff.mpr (enough fuel bound), resultAt⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
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
  exact has_sufficient_fuel_at_arity receiver stagePrepared profile observations extension semantic family
    namedTerminals namedSupport wellFormed history entry member entryType input started parameterView metadata
    packing (.of_value trace) trace

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
/-! The successful public packed-call receipt supplies the original startup
and completion. Current function history and structural input descriptions
close argument meaning and preserve the resulting caller and earlier handles.
Metadata-free trees derive the receiving condition from the actual session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
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
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- Scalars and handles at arbitrary product depth use their original public
encoding. The actual callable row determines the Source argument vector, including
the distinction between zero parameters and one Unit-valued parameter. -/
theorem public_invoke_succeeded_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      encodedValues.registry = sourceRegistry ∧ actual.session.RegistryAt sourceRegistry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have current := history.current
  have imported := (current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe current.1 imported original
  have registryEq := started.function_tree_registry simple atRegistry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry := by
    rw [registryEq]
    exact receiving
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success original exported resultAt
  have returnedRegistry := started.returned_registry exported
  rw [registryEq] at returnedRegistry
  exact ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after, finalMap,
    finalWorld, reached, started, parameterView, resultView, exported,
    ⟨valueEq, typeEq, budgetEq, sessionAt⟩, packing, trace, resultAt, related, returnedHistory,
    registryEq, returnedRegistry⟩


include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Metadata-bearing packed values use the same public continuation when their
actual encoded registry extends into the receiving registry. The callee's
Source signature follows from history and the original selection. -/
theorem public_resume_succeeded
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {executionFuel outputFuel : Nat}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
    SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (sources : List Dynamic.Value)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.NativeDone executionFuel value finalStore ∧
      checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  have actualView := started.selected.spec.2.1
  have importedView := imported.function_type
  obtain ⟨parameterView, resultView⟩ :=
    TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success started.original exported resultAt
  exact ⟨parameterView, resultView, actual, generation, value, finalStore, sources, sourceSize, outcome,
    after, finalMap, finalWorld, reached, completed, exported, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    packing, trace, resultAt, related, returnedHistory, started.returned_registry exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallablePublicHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
/-! A real input encoder may extend the current metadata table. The entire
history moves to that table without changing its session, heap, captures or
ordered entries. No metadata can be recovered from a larger unrelated table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession CallableIndexedOwnedFunctionState
open RecursiveNamedPublicFunctionHistory (History Entry Caller Result IssuedEntry)

private theorem outcome_extend
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {registry future : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {type : Core.Ty}
    {faults : RecursiveStageMeaning.FaultRep} {outcome : Staging.Recursive.Outcome} {native : Core.Value}
    (represented : RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world sourceType type faults outcome native)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    RecursiveStageMeaning.ResultRepresentsFor
      (CompatibleAmbientHeap.payloadModel checked future functions) mapping world sourceType type faults outcome native := by
  cases represented with
  | value related => exact .value (related.extend extension (.refl _) (.refl _))
  | fault related => exact .fault related

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
  {registry future : SourceCoreRawMetadata.Registry}
  {anchor : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {caller : Caller headers keys mapping world heap store}

private theorem named_result
    {owner : CallableIndexedOwnedFunctionValues.OwnedKey keys}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {capture : CallableIndexedOwnedFunctionValues.NamedCapture headers owner.key header mapping world}
    {arguments : List Core.Value} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : Result (functions := functions) (receiving := registry) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    Result (functions := functions) (receiving := future) (anchor := anchor)
      owner caller header capture arguments outcome after native finalStore finalMap finalWorld faults :=
  ⟨result.1, outcome_extend result.2.1 extension,
    CompatibleHeap.HeapRepresents.extend_registry result.2.2.1 extension, result.2.2.2⟩

private theorem packed_result
    {sourceType : TypeSystem.Ty} {nativeType : Core.Ty}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    {native : Core.Value} {finalStore : Store} {finalMap : LocationMap} {finalWorld : StoreTyping}
    {faults : RecursiveStageMeaning.FaultRep}
    (result : RecursivePublicApplicationResult.ResultAt (registry := registry) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    RecursivePublicApplicationResult.ResultAt (registry := future) functions caller
      anchor.function.context sourceType nativeType outcome after native finalStore finalMap finalWorld faults :=
  ⟨outcome_extend result.1 extension,
    CompatibleHeap.HeapRepresents.extend_registry result.2.1 extension, result.2.2⟩

private theorem issued_entry {artifact : Artifact} {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry) :
    IssuedEntry headers keys functions future anchor before after entry := by
  cases receipt with
  | named prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      exact .named prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded wellFormed
  | builtin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .builtin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded
  | physicalNamed prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      exact .physicalNamed prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded wellFormed
  | physicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      exact .physicalNamedSelected prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded certified
  | physicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .physicalBuiltin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded
  | preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      exact .preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry future faults profile anchor
        issuance atRecipe handleValue encoded certified
  | preparedPhysicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      exact .preparedPhysicalBuiltin prepared headers keys bodyRegistry future faults profile anchor issuance atRecipe handleValue encoded

/-- Only a forward extension of the actual metadata table is used. Every
historical result, including a failed call, keeps its original state and order. -/
theorem extend_history {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (extension : SourceCoreRawMetadata.Extends registry future) :
    History headers keys functions future anchor session mapping world heap store caller entries := by
  induction history with
  | first sameCompiled started selected succeeded result reached post addition =>
      exact .first sameCompiled started selected succeeded (named_result result extension) reached post addition
  | next prior sameCompiled started selected succeeded result reached post addition ih =>
      exact .next ih sameCompiled started selected succeeded (named_result result extension) reached post addition
  | first_export_error sameCompiled started selected exported result reached post =>
      exact .first_export_error sameCompiled started selected exported (named_result result extension) reached post
  | next_export_error prior sameCompiled started selected exported result reached post ih =>
      exact .next_export_error ih sameCompiled started selected exported (named_result result extension) reached post
  | first_failed sameCompiled started selected failed result reached post heapTyped =>
      exact .first_failed sameCompiled started selected failed (named_result result extension) reached post heapTyped
  | failed prior sameCompiled started selected failed result reached post heapTyped ih =>
      exact .failed ih sameCompiled started selected failed (named_result result extension) reached post heapTyped
  | packed_next prior started succeeded result reached post addition ih =>
      exact .packed_next ih started succeeded (packed_result result extension) reached post addition
  | packed_failed prior started failed result reached post heapTyped ih =>
      exact .packed_failed ih started failed (packed_result result extension) reached post heapTyped
  | packed_export_error prior started exported result reached post ih =>
      exact .packed_export_error ih started exported (packed_result result extension) reached post
  | issued prior continued ih => exact .issued ih continued
  | remember_issued prior receipt ih => exact .remember_issued ih (issued_entry receipt)
  | restored prior restored ih => exact .restored ih restored

/-- A history retains the genuine entry selected by its first named startup,
including when that call failed or later handles were restored. -/
theorem indexed_entry {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ entry, entry ∈ compiled.indexed.entries := by
  induction history with
  | first _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | first_export_error _ _ selected _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | next_export_error _ _ _ _ _ _ _ _ ih => exact ih
  | first_failed _ _ selected _ _ _ _ _ =>
      obtain ⟨_, entry, member, _⟩ := selected
      exact ⟨entry, member⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The first actual root fixes a retained named header even if its result
contains no function handle. Later session transitions preserve that origin. -/
theorem named_header {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ header, header ∈ headers := by
  induction history with
  | first _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | first_export_error _ _ selected _ _ _ _ => exact ⟨_, selected.1⟩
  | next_export_error _ _ _ _ _ _ _ _ ih => exact ih
  | first_failed _ _ selected _ _ _ _ _ => exact ⟨_, selected.1⟩
  | next _ _ _ _ _ _ _ _ _ ih => exact ih
  | failed _ _ _ _ _ _ _ _ _ ih => exact ih
  | packed_next _ _ _ _ _ _ _ ih => exact ih
  | packed_failed _ _ _ _ _ _ _ ih => exact ih
  | packed_export_error _ _ _ _ _ _ ih => exact ih
  | issued _ _ ih => exact ih
  | remember_issued _ _ ih => exact ih
  | restored _ _ ih => exact ih

/-- The retained named row gives the genuine compiler diagnostic inventory.
No fallback entry or unrelated native execution is used. -/
theorem diagnostics_present {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries) :
    ∃ program, compiled.indexed.base.diagnostics = some program := by
  obtain ⟨header, _⟩ := named_header history
  obtain ⟨diagnostics, _, actual, _⟩ := NamedCalls.compiled_at compiled.indexed header.selected
  exact ⟨diagnostics, actual⟩

/-- The original accepted packed encoder supplies the extension. This keeps
history at the exact table used to decode this call's eventual public result. -/
theorem at_packed_start
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe}
    {handle : SourceCorePublicValues.Handle} {argument : SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries := by
  obtain ⟨before, encoded, actualRegistry, _owner, _accepted, _value, sameRegistry⟩ := started.raw
  have same : before = registry := actualRegistry.symm.trans atRegistry
  have extended : SourceCoreRawMetadata.Extends registry encodedValues.registry := by
    rw [← same, ← sameRegistry]
    exact encoded.preserves
  exact ⟨extended, extend_history history extended⟩

/-- Named startup extends the same history using the complete actual ordered
input vector, including values that introduce constructor or mapping metadata. -/
theorem at_named_start
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} {root : Root recipe.compiled}
    {key : SourceCoreIndexedSession.Key} {arguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat} {checkpoint : Checkpoint artifact} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicStartMeaning.StartAt session key arguments inputFuel
      checkpoint recipe root world store native encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries := by
  have extended := started.original.metadata_extension atRegistry
  have actual := started.values
  cases checkpoint
  change _ = encodedValues at actual
  dsimp only at extended
  rw [actual] at extended
  exact ⟨extended, extend_history history extended⟩

/-- Current handle identity and the actual packed encoder derive input meaning
in the very table used by public output decoding. Heap and capture meaning
come from the retained history, with no receiving-registry assumption. -/
theorem at_packed_input
    {artifact : Artifact} {session : Session artifact} {entries : List Entry}
    {recipe : Recipe} (sameCompiled : recipe.compiled = compiled)
    {entry : Entry} (member : entry ∈ entries)
    {sourceParameter sourceResult : TypeSystem.Ty}
    (entryType : entry.sourceType = .function sourceParameter sourceResult)
    {argument : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context sourceParameter argument source)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {parameter result : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (history : History headers keys functions registry anchor session mapping world heap store caller entries)
    (atRegistry : session.RegistryAt registry)
    (started : RecursiveNamedPublicDirectPackedInputMeaning.StartAt session entry.handle argument inputFuel
      checkpoint recipe world store parameter result nativeParameter nativeResult callable packed encodedValues) :
    SourceCoreRawMetadata.Extends registry encodedValues.registry ∧
    History headers keys functions encodedValues.registry anchor session mapping world heap store caller entries ∧
    ValueRep compiled.compatible.checked encodedValues.registry functions mapping world
      sourceParameter source packed nativeParameter ∧
    Dynamic.ValueHasType anchor.function.context heap source sourceParameter := by
  cases sameCompiled
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, _resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨extended, current⟩ := at_packed_start history atRegistry started
  obtain ⟨represented, typed⟩ := started.history_input_compatible current input parameterView (.refl _)
  exact ⟨extended, current, represented, typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryRegistryExtension
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
/-! Direct language failure retains old handles in the actual returned session.
The original public completion and independent fault preservation derive the
Source fault and final heap typing, including effects before the failure. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
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
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- A genuine failed public resumption reflects to Source and keeps earlier
captures at its returned heap without a final heap typing premise. -/
theorem public_resume_failed_at_arity
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      RecursivePublicCallableArity.Arity (Program.ofChecked recipe.compiled.sourceProgram) entry.source sources.length ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨imported, _represented, calleeTyped⟩ := history.current.2.2.2.2 entry member
  rw [entryType] at imported
  rw [entryType] at calleeTyped
  have actualView := started.selected.spec.2.1
  have importedView := imported.function_type
  obtain ⟨parameterView, _resultView⟩ :=
    TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  obtain ⟨actual, _generation, value, finalStore, completed, failed, sessionAt⟩ :=
    resumed.indexed_failed atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.completed_reflects_at_arity receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata completed invocation
  obtain ⟨failure, outcomeEq⟩ : ∃ failure, outcome = .fault failure := by
    have represented := resultAt.1
    cases represented with
    | value _ => have impossible := failed.2.1; cases impossible
    | fault _ => exact ⟨_, rfl⟩
  subst outcome
  obtain ⟨_packedRelated, packedTyped⟩ := started.history_input_compatible history input parameterView metadata
  obtain ⟨_facts, certificate⟩ := RecursiveNamedHeaderSourceTyping.certificate anchor wellFormed
  have runtime : Dynamic.SourceRuntimeValid (Program.ofChecked recipe.compiled.sourceProgram)
      anchor.function.context anchor.function.source := by
    rw [anchor.frame.context, anchor.frame.source]
    exact certificate.toBodyInstanceTypingCertificate.sourceRuntimeValid
  have preserved := Staging.Recursive.FaultPreservation.applies wellFormed runtime history.current.2.2.2.1
    calleeTyped packing packedTyped trace
  obtain ⟨reached, related, retained⟩ :=
    history.after_packed_failure started.original failed resultAt preserved.1
  have registry : actual.RegistryAt encodedValues.registry := by
    have same := failed.2.2.2.2.1
    have values := started.values
    exact congrArg SourceCoreCompatibleValues.Context.registry (same.trans values)
  exact ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld,
    reached, failed, sessionAt, packing, arity, trace, resultAt, related, retained, registry⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
theorem public_resume_failed
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {executionFuel outputFuel : Nat} {reason : Word}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.failed reason publicSession))
    (invocation : Staging.Recursive.Scope) :
    ∃ (actual : Session artifact) (value : Core.Value) (finalStore : Store)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.FailedResultAt executionFuel value finalStore reason actual ∧
      publicSession.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      actual.RegistryAt encodedValues.registry := by
  obtain ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, _arity, rest⟩ := public_resume_failed_at_arity
    receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport
      wellFormed history entry member entryType input started metadata atCheckpoint resumed invocation
  exact ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld, reached, failed, sessionAt, packing, rest⟩

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- Actual public invocation recovers its own startup and failed resumption.
Inputs consisting of scalars, handles and products derive metadata identity. -/
theorem public_invoke_failed_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession returned : SourceCoreExecution.Session publicArtifact}
    {options : SourceCoreExecution.RunOptions} {reason : Word}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.failed reason returned)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Session artifact)
      (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (failure : Staging.Recursive.Failure)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
      returned.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.fault failure) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.fault failure) after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual
        finalMap finalWorld after finalStore reached entries ∧
      encodedValues.registry = sourceRegistry ∧ actual.RegistryAt sourceRegistry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe history.current.1 imported original
  have registryEq := started.function_tree_registry simple atRegistry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry := by
    rw [registryEq]
    exact receiving
  obtain ⟨actual, value, finalStore, sources, sourceSize, failure, after, finalMap, finalWorld,
    reached, failed, sessionAt, packing, trace, resultAt, related, retained, registry⟩ :=
    public_resume_failed receiver stagePrepared profile observations extension semantic family namedTerminals
      namedSupport wellFormed history entry member entryType input started metadata
      atCheckpoint resumed invocation
  rw [registryEq] at registry
  exact ⟨checkpoint, actual, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, failure, after, finalMap,
    finalWorld, reached, started, parameterView, resultView, failed, sessionAt, packing,
    trace, resultAt, related, retained, registryEq, registry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFailures
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation
/-! Independent successful Source execution of function-valued calls closes
the actual public export and adds that function to the same returned history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation
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
  {parameter outputParameter outputResult : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter (.function outputParameter outputResult))
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)


local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

private theorem selected_function {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {handle : SourceCorePublicValues.Handle} (same : value = .function handle)
    {source : Dynamic.Value} {native : Core.Value} {nativeType : Core.Ty} {fuel : Nat} :
    RecursiveNamedPublicOutputSelections.Selected
      (same.symm ▸ (RecursiveNamedPublicOutputSelections.Selection.function (type := type)))
      source native nativeType fuel [⟨type, source, handle, native, nativeType, fuel⟩] := by
  cases same
  exact .function

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input in
/-- Actual Source execution implies public function export for every sufficient
native budget and every positive output budget. The authentic issuer/slot
receipt is supplied by initialization and retained by real session events. -/
theorem public_resume_has_sufficient_fuel
    (exportsReady : session.ExportsReady)
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {invocation : Staging.Recursive.Scope} {sources : List Dynamic.Value}
    (packing : Dynamic.ValuesPack sources packedSource)
    {sourceSize : Nat} {sourceResult : Dynamic.Value} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
      invocation anchor.function.context before entry.source sources (.value sourceResult) after)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint) :
    ∃ required payload finalStore finalMap finalWorld,
      (∀ executionFuel, required ≤ executionFuel →
        checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore) ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context
        (.function outputParameter outputResult) nativeResult
        (.value sourceResult) after (.inRight .word payload) finalStore finalMap finalWorld callFaults ∧
      ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
        required ≤ executionFuel → 1 ≤ outputFuel →
        publicCheckpoint.ResumeAt executionFuel outputFuel outcome →
        ∃ (publicCompletion : SourceCoreExecution.Completion publicArtifact)
          (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
          (handle : SourceCorePublicValues.Handle)
          (reached : Caller headers keys finalMap finalWorld after finalStore),
          outcome = .succeeded publicCompletion ∧ publicCompletion.value = .function handle ∧
          handle.sourceType = actualResult ∧
          checkpoint.SucceededResultAt executionFuel outputFuel generation (.inRight .word payload) finalStore actual ∧
          publicCompletion.IndexedAt actual ∧ Relates caller reached ∧
          History headers keys functions completion.result.context.registry anchor actual.session
            finalMap finalWorld after finalStore reached
            (entries ++ [⟨.function outputParameter outputResult, sourceResult, handle, payload, nativeResult, outputFuel⟩]) ∧
          actual.session.RegistryAt encodedValues.registry ∧ actual.session.ExportsReady := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨parameterView, resultView⟩ := TypeSystem.Ty.function.inj
    (started.selected.spec.2.1.symm.trans imported.function_type.symm)
  obtain ⟨value, finalStore, finalMap, finalWorld, required, enough, resultAt⟩ :=
    RecursiveNamedPublicDirectCallableHistory.has_sufficient_fuel receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType input
      started parameterView.symm metadata packing trace
  have success : ∃ payload, value = .inRight .word payload := by
    have represented := resultAt.1
    cases represented with
    | value related => exact ⟨_, rfl⟩
  obtain ⟨payload, rfl⟩ := success
  have ready := started.original.initial_registry.exportsReady exportsReady
  refine ⟨required, payload, finalStore, finalMap, finalWorld, enough, resultAt, ?_⟩
  intro executionFuel outputFuel outcome bound outputBound resumed
  have completed := enough executionFuel bound
  obtain ⟨publicCompletion, handle, succeeded, publicValue, sourceType, _publicReady⟩ :=
    resumed.runtime_function_succeeded atCheckpoint ready completed started.requested resultView (by omega)
  have actualResume : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion) :=
    succeeded ▸ resumed
  obtain ⟨actual, generation, actualValue, actualStore, actualCompleted, exported,
      valueAt, sourceAt, fuelAt, sessionAt⟩ := actualResume.indexed_succeeded atCheckpoint
  have same := completed.symm.trans actualCompleted
  cases same
  obtain ⟨reached, related, post⟩ := resultAt.2.2.2.2.2.2
  have actualValue : actual.value = .function handle := valueAt.symm.trans publicValue
  let selection : RecursiveNamedPublicOutputSelections.Selection (.function outputParameter outputResult) actual.value :=
    actualValue.symm ▸ .function
  have selected : RecursiveNamedPublicOutputSelections.Selected selection sourceResult payload nativeResult outputFuel
      [⟨.function outputParameter outputResult, sourceResult, handle, payload, nativeResult, outputFuel⟩] := by
    exact selected_function actualValue
  have retained := History.packed_next history started.original exported resultAt reached ⟨related, post⟩
    (.selectCompatible started.requested resultView.symm rfl rfl selection selected)
  exact ⟨publicCompletion, actual, generation, handle, reached, succeeded, publicValue, sourceType, exported,
    ⟨valueAt, sourceAt, fuelAt, sessionAt⟩, related, retained, started.returned_registry exported,
    exported.exportsReady ready⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableFunctionPreservation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
/-! Direct successful output collection reuses the actual export and full
Source result. Selected function leaves join the same returned history even
when the host request and Source result differ by erased annotations. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
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
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics


private theorem selected_of_cast {sourceType : TypeSystem.Ty}
    {first second : SourceCorePublicValues.Value} (same : first = second)
    {selection : RecursiveNamedPublicOutputSelections.Selection sourceType first}
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty} {fuel : Nat} {entries : List Entry}
    (selected : RecursiveNamedPublicOutputSelections.Selected
      (same ▸ selection : RecursiveNamedPublicOutputSelections.Selection sourceType second)
      source native type fuel entries) :
    RecursiveNamedPublicOutputSelections.Selected selection source native type fuel entries := by
  cases same
  exact selected

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType input atRecipe in
/-- The public invocation keeps all previous handles and appends the selected
function leaves of this same actual output. No Source representation or raw
result equality is supplied by the caller. -/
theorem public_invoke_succeeded_collects_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (selection : RecursiveNamedPublicOutputSelections.Selection result publicCompletion.value)
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (source : Dynamic.Value) (payload : Core.Value)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore) (added : List Entry),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before entry.source sources (.value source) after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        (.value source) after value finalStore finalMap finalWorld callFaults ∧
      value = .inRight .word payload ∧
      RecursiveNamedPublicOutputSelections.Selected selection source payload nativeResult options.outputValidationFuel added ∧
      added.map Entry.handle = selection.handles ∧ Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached (entries ++ added) ∧
      encodedValues.registry = sourceRegistry ∧ actual.session.RegistryAt sourceRegistry := by
  obtain ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
      nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after,
      finalMap, finalWorld, _previousReached, started, parameterView, resultView, succeeded, actualAt,
      packing, trace, resultAt, _previousRelated, _previousHistory, registryEq, returnedRegistry⟩ :=
    RecursiveNamedPublicDirectCallablePublicHistory.public_invoke_succeeded_function_tree
      receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
      history entry member entryType input atRecipe atRegistry receiving simple atSession invoked invocation
  obtain ⟨reached, source, payload, added, sourceValue, nativeValue, selected, handles, related, retained⟩ :=
    history.collect_packed_success started.original started.requested resultView.symm succeeded resultAt
      (actualAt.1 ▸ selection)
  have originalSelection := selected_of_cast actualAt.1 selected
  have originalHandles := handles.trans (RecursiveNamedPublicOutputSelections.Selection.handles_cast actualAt.1 selection)
  rw [sourceValue] at trace resultAt
  exact ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult, nativeParameter,
    nativeResult, callable, packed, encodedValues, sources, sourceSize, source, payload, after, finalMap,
    finalWorld, reached, added, started, parameterView, resultView, succeeded, actualAt, packing, trace,
    resultAt, nativeValue, originalSelection, originalHandles, related, retained, registryEq, returnedRegistry⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableOutputHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectCallableWordPreservation
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedHistory
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedPublicHistory
/-! The successful public packed-call receipt supplies the original startup
and completion. Current function history and structural input descriptions
close argument meaning and preserve the resulting caller and earlier handles.
Metadata-free trees derive the receiving condition from the actual session. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedPublicHistory
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
  {parameter result : TypeSystem.Ty}
  (entryType : entry.sourceType = .function parameter result)
  {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)

  (atRecipe : ArtifactRecipe artifact recipe)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType entrySource input atRecipe in
/-- Scalars and handles at arbitrary product depth use their original public
encoding. Actual closure arity determines the Source argument vector, including
the distinction between zero parameters and one Unit-valued parameter. -/
theorem public_invoke_succeeded_function_tree
    {sourceRegistry : SourceCoreRawMetadata.Registry}
    (atRegistry : session.RegistryAt sourceRegistry)
    (receiving : SourceCoreRawMetadata.Extends sourceRegistry completion.result.context.registry)
    (simple : FunctionTreeSimple argument)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicSession : SourceCoreExecution.Session publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {options : SourceCoreExecution.RunOptions}
    (atSession : publicSession.IndexedAt session)
    (invoked : publicSession.InvokeAt entry.handle argument options (.ok (.succeeded publicCompletion)))
    (invocation : Staging.Recursive.Scope) :
    ∃ (checkpoint : Checkpoint artifact) (actual : Completion artifact)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (finalStore : Store)
      (actualParameter actualResult : TypeSystem.Ty) (nativeParameter nativeResult : Core.Ty)
      (callable packed : Core.Value) (encodedValues : SourceCoreCompatibleValues.Context)
      (sources : List Dynamic.Value) (sourceSize : Nat) (outcome : Staging.Recursive.Outcome)
      (after : Dynamic.Heap) (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      StartAt session entry.handle argument options.inputValidationFuel checkpoint recipe world store
        actualParameter actualResult nativeParameter nativeResult callable packed encodedValues ∧
      SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
      SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
      checkpoint.SucceededResultAt options.executionFuel options.outputValidationFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before (.closure function) sources outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      encodedValues.registry = sourceRegistry ∧ actual.session.RegistryAt sourceRegistry := by
  obtain ⟨publicCheckpoint, accepted, resumed⟩ := invoked
  obtain ⟨checkpoint, atCheckpoint, original⟩ :=
    RecursiveNamedPublicDirectHandleMeaning.recover_handle_start atSession accepted
  have current := history.current
  have imported := (current.2.2.2.2 entry member).1
  rw [entryType] at imported
  obtain ⟨actualParameter, actualResult, nativeParameter, nativeResult, callable, packed, encodedValues,
    started, parameterView, resultView⟩ :=
    RecursiveNamedPublicDirectPackedInputMeaning.actual_start_compatible atRecipe current.1 imported original
  have registryEq := started.function_tree_registry simple atRegistry
  have metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry := by
    rw [registryEq]
    exact receiving
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectPackedHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType entrySource input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success original exported resultAt
  have returnedRegistry := started.returned_registry exported
  rw [registryEq] at returnedRegistry
  exact ⟨checkpoint, actual, generation, value, finalStore, actualParameter, actualResult,
    nativeParameter, nativeResult, callable, packed, encodedValues, sources, sourceSize, outcome, after, finalMap,
    finalWorld, reached, started, parameterView, resultView, exported,
    ⟨valueEq, typeEq, budgetEq, sessionAt⟩, packing, arity, trace, resultAt, related, returnedHistory,
    registryEq, returnedRegistry⟩


include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType entrySource input in
/-- Metadata-bearing packed values use the same public continuation when their
actual encoded registry extends into the receiving registry. The callee's
Source signature follows from history and the original selection. -/
theorem public_resume_succeeded
    {inputFuel : Nat} {checkpoint : Checkpoint artifact}
    {actualParameter actualResult : TypeSystem.Ty} {nativeParameter nativeResult : Core.Ty}
    {callable packed : Core.Value} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session entry.handle argument inputFuel checkpoint recipe world store
      actualParameter actualResult nativeParameter nativeResult callable packed encodedValues)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry completion.result.context.registry)
    {publicArtifact : SourceCoreExecution.Artifact}
    {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    {executionFuel outputFuel : Nat}
    (atCheckpoint : publicCheckpoint.IndexedAt checkpoint)
    (resumed : publicCheckpoint.ResumeAt executionFuel outputFuel (.succeeded publicCompletion))
    (invocation : Staging.Recursive.Scope) :
    SourceCoreRawMetadata.runtimeType actualParameter = SourceCoreRawMetadata.runtimeType parameter ∧
    SourceCoreRawMetadata.runtimeType actualResult = SourceCoreRawMetadata.runtimeType result ∧
    ∃ (actual : Completion artifact) (generation : SourceCorePublicValues.ExportGeneration)
      (value : Core.Value) (finalStore : Store) (sources : List Dynamic.Value)
      (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
      (finalMap : LocationMap) (finalWorld : StoreTyping)
      (reached : Caller headers keys finalMap finalWorld after finalStore),
      checkpoint.NativeDone executionFuel value finalStore ∧
      checkpoint.SucceededResultAt executionFuel outputFuel generation value finalStore actual ∧
      publicCompletion.IndexedAt actual ∧
      Dynamic.ValuesPack sources packedSource ∧ sources.length = function.parameters.length ∧
      Staging.Recursive.Size.Applies (Program.ofChecked recipe.compiled.sourceProgram) callStages sourceSize
        invocation anchor.function.context before (.closure function) sources outcome after ∧
      ResultAt (registry := completion.result.context.registry) functions caller anchor.function.context result nativeResult
        outcome after value finalStore finalMap finalWorld callFaults ∧
      Relates caller reached ∧
      History headers keys functions completion.result.context.registry anchor actual.session
        finalMap finalWorld after finalStore reached entries ∧
      actual.session.RegistryAt encodedValues.registry := by
  have imported := (history.current.2.2.2.2 entry member).1
  rw [entryType] at imported
  have actualView := started.selected.spec.2.1
  have importedView := imported.function_type
  obtain ⟨parameterView, resultView⟩ :=
    TypeSystem.Ty.function.inj (actualView.symm.trans importedView.symm)
  obtain ⟨actual, generation, value, finalStore, completed, exported, valueEq, typeEq, budgetEq, sessionAt⟩ :=
    resumed.indexed_succeeded atCheckpoint
  obtain ⟨sources, packing, arity, sourceSize, outcome, after, finalMap, finalWorld, trace, resultAt⟩ :=
    RecursiveNamedPublicDirectPackedHistory.completed_reflects receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType entrySource input
      started parameterView.symm metadata completed invocation
  obtain ⟨reached, related, returnedHistory⟩ := history.after_packed_success started.original exported resultAt
  exact ⟨parameterView, resultView, actual, generation, value, finalStore, sources, sourceSize, outcome,
    after, finalMap, finalWorld, reached, completed, exported, ⟨valueEq, typeEq, budgetEq, sessionAt⟩,
    packing, arity, trace, resultAt, related, returnedHistory, started.returned_registry exported⟩

end Meaning
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectPackedPublicHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectWordPreservation
/-! Independent successful Source execution closes both native execution and
actual public Word export, retaining the same returned heap and history. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectWordPreservation
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
  {function : Dynamic.Closure} (entrySource : entry.source = .closure function)
  {argument : SourceCorePublicValues.Value} {packedSource : Dynamic.Value}
  (input : RecursiveNamedPublicFunctionHistoryInputs.Input entries anchor.function.context parameter argument packedSource)


local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "callStages" => RecursiveNamedPreparedStageScopes.registry stagePrepared
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include receiver stagePrepared profile observations extension semantic family namedTerminals namedSupport wellFormed
  history entry member entryType entrySource input in
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
      invocation anchor.function.context before (.closure function) sources (.value (.word word)) after)
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
  have arity : sources.length = function.parameters.length := by
    cases trace with
    | closure _ _ _ _copy allocate _ _ => exact allocate.length_eq.symm
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
    RecursiveNamedPublicDirectPackedHistory.has_sufficient_fuel receiver stagePrepared profile observations extension
      semantic family namedTerminals namedSupport wellFormed history entry member entryType entrySource input
      started parameterView.symm metadata packing arity trace
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
end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicDirectWordPreservation
end
