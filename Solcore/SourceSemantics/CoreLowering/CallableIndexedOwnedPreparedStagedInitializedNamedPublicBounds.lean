import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBootstrapRootState
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicBootstrapInitialization
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNamedArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds

/-! A named handle issued from the actual initialized session reaches the
public semantics with its original global slot, installed code and captured
environment. A retained inventory packet supplies the independent Source
function and dictionary. The single raw parameter has that function type;
initial state and argument representation are constructed internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNamedPublicBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedBootstrapRootState (keys owner)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds (OrdinarySequenceFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  (inputs : List (Input compiled)) (rows : Inventory inputs)
  (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
      bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (family : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association (headers rows) (keys compiled) bodyRegistry semanticFaults
      mapping world function native bindings parameterCore resultCore), OrdinarySequenceFor stagePrepared association)
  (namedTerminals : ∀ header, header ∈ headers rows → Terminal header)
  (namedSupport : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (keys compiled) bodyRegistry header (RecursiveNamedPreparedStageScopes.registry stagePrepared)
      (namedTerminals header member) semanticFaults)
  {beforePlan : SourceCompilationPlan.Plan} {planFuel planBudget : Nat}
  (acceptedPlan : SourceCompilationPlan.prepareExecutablePlanEvidenceWithBudget
    compiled.sourceProgram beforePlan planFuel planBudget = .ok compiled.indexed.base.plan)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {recipe : SourceCoreIndexedSession.Recipe}
  (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  {root : SourceCoreIndexedSession.Root compiled}
  {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  (selected : RecursiveNamedPublicRootMeaning.RootSelection
    (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
    (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
  {importedInput : Input compiled}
  (importedPacket : CallableIndexedOwnedPreparedFiniteNamedInventories.Issued importedInput)
  (importedMember : Inventory.HasRow importedPacket rows)
  {issuanceFuel : Nat}
  {binding : CallableIndexedParameterCertificates.Binding}
  (sole : header.bindings = [binding])
  (rawType : binding.1.scheme.body = importedPacket.header.named.specialized.function.type)
  {publicCompiled : SourceCoreExecution.Compiled} {publicArtifact : SourceCoreExecution.Artifact}
  {publicBootstrap : SourceCoreExecution.Bootstrap publicArtifact}
  {bootstrapSession publicSession : SourceCoreExecution.Session publicArtifact}
  {publicCheckpoint : SourceCoreExecution.Checkpoint publicArtifact}
  {nativeArtifact : SourceCoreIndexedSession.Artifact}
  {nativeSession : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeIssuer : SourceCoreIndexedSession.Session nativeArtifact}
  {nativeIssued : SourceCoreIndexedSession.Completion nativeArtifact}
  {nativeCheckpoint : SourceCoreIndexedSession.Checkpoint nativeArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {bootstrapFuel : Nat} {options : SourceCoreExecution.RunOptions}
  {world : StoreTyping} {store : Store} {payloads : Environment}
  {encodedValues : SourceCoreCompatibleValues.Context}
  (opened : publicArtifact.IndexedAt publicCompiled recipe nativeArtifact)
  (fresh : publicBootstrap.FreshAt)
  (ready : publicBootstrap.ReadyAt bootstrapFuel bootstrapSession)
  (sameRuntime : bootstrapSession.SameRuntime publicSession)
  (atSession : publicSession.IndexedAt nativeSession)
  (atCheckpoint : publicCheckpoint.IndexedAt nativeCheckpoint)
  (started : RecursiveNamedPublicStartMeaning.StartAt nativeSession key publicArguments
    options.inputValidationFuel nativeCheckpoint recipe
    ((SourceCoreIndexedSession.Recipe.prepare_compiled prepared).symm ▸ root)
    world store payloads encodedValues)
  (issuance : nativeIssuer.NamedIssuedAt importedPacket.header.named.signature.key issuanceFuel nativeIssued)
  (issuedSession : nativeIssued.session = nativeSession)
  (singleInput : publicArguments = [nativeIssued.value])
  {inputHandle : SourceCorePublicValues.Handle}
  (handleValue : nativeIssued.value = .function inputHandle)
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {function : Dynamic.GlobalFunction}
  (sourceAt : CallableIndexedOwnedFunctionValues.NamedSourceAt header rawD function)
  {invocation : Staging.Recursive.Scope} {context : SourceSemantics.Context}
  (supports : Dynamic.TypeContextSupports header.context context)

local notation "namedArguments" => [Dynamic.Value.global
  (CallableNamedReversal.global (CallableNamedMetadata.global
    importedPacket.header.named.specialized importedInput.prepared.available))]
local notation "rootHeaders" => headers rows
local notation "rootKeys" => keys compiled
local notation "rootOwner" => owner compiled
local notation "rootFunctions" => CallableIndexedOwnedContextualCellOrigins.functions rootHeaders rootKeys bodyRegistry semanticFaults profile
local notation "rootModel" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry rootFunctions
local notation "rootFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include importedMember distinct wellFormed prepared selected opened fresh ready sameRuntime atSession started issuance issuedSession sole rawType singleInput handleValue in
/-- This proof is consumed immediately by the public endpoints below. The
runtime-preservation receipt fixes the initial store/world; the argument producer uses
the caller's receiving metadata without identifying two registries. -/
private theorem initial_arguments :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      CallableIndexedOwnedIndirectExpressionHeads.StableRows caller ∧
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)[header.slot]? =
        some (.cellRef (OptionalCell.cellType header.named.signature.functionType)
          ((rootOwner).key.locations header)) ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
        rootFunctions [] world ⟨[]⟩ store ∧
      Dynamic.HeapWellTyped header.function.context ⟨[]⟩ ∧
      CallableIndexedParameterMeaning.Arguments rootModel [] world header.bindings namedArguments payloads ∧
      Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ namedArguments header.types := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨value, booted, worldEq, storeEq, _nativeAt, _registryAt, _initializedStart⟩ :=
    CallableIndexedOwnedPublicBootstrapInitialization.at_started prepared opened fresh ready sameRuntime atSession started
  subst world
  subst store
  obtain ⟨_result, _storeEq, caller, stable, heaps, globals, heapTyped⟩ :=
    CallableIndexedOwnedPreparedBootstrapRootState.of_completed wellFormed inputs rows prepared distinct
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry semanticFaults profile) completion.result.context.registry booted
  have issuedStart := started
  rw [← issuedSession] at issuedStart
  obtain ⟨represented, argumentsTyped⟩ :=
    RecursiveNamedPublicNamedArgumentReceipts.StartAt.named_arguments_receiving
      prepared inputs rows importedPacket importedMember bodyRegistry completion.result.context.registry
      semanticFaults profile caller issuance issuedStart selected sole rawType singleInput handleValue wellFormed
  exact ⟨caller, stable, globals header selected.member, heaps,
    heapTyped header.function.context, represented, argumentsTyped⟩

include importedMember distinct receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started issuance issuedSession sole rawType singleInput handleValue sourceAt supports in
/-- Actual bootstrap and actual public input encoding construct every initial
state premise before the existing public success endpoint is invoked. -/
theorem public_run_succeeded_reflects
    {publicCompletion : SourceCoreExecution.Completion publicArtifact}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.succeeded publicCompletion)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      ∃ (actual : SourceCoreIndexedSession.Completion nativeArtifact)
        (generation : SourceCorePublicValues.ExportGeneration) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.SucceededResultAt options.executionFuel options.outputValidationFuel
          generation value finalStore actual ∧
        publicCompletion.value = actual.value ∧ publicCompletion.sourceType = actual.sourceType ∧
        publicCompletion.boundaryFuel = actual.boundaryFuel ∧ publicCompletion.session.IndexedAt actual.session ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context ⟨[]⟩
          (.global function) namedArguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    initial_arguments (inputs := inputs) (rows := rows) (importedPacket := importedPacket)
      (importedMember := importedMember) (distinct := distinct)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime) (atSession := atSession)
      (started := started) (issuance := issuance) (issuedSession := issuedSession)
      (sole := sole) (rawType := rawType) (singleInput := singleInput) (handleValue := handleValue)
  refine ⟨caller, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include importedMember distinct receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started issuance issuedSession sole rawType singleInput handleValue sourceAt supports in
/-- Actual public failure uses the same produced initial pool and input
relation. Staged failures retain their original nested scope and token. -/
theorem public_run_failed_reflects
    {returned : SourceCoreExecution.Session publicArtifact} {reason : Word}
    (publicStart : publicSession.start key publicArguments options.inputValidationFuel = .ok publicCheckpoint)
    (publicRun : publicSession.RunAt key publicArguments options (.ok (.failed reason returned)))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      ∃ (actual : SourceCoreIndexedSession.Session nativeArtifact) (value : Value) (finalStore : Store)
        (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
        (sourceSize : Nat) (outcome : Staging.Recursive.Outcome) (after : Dynamic.Heap)
        (finalMap : LocationMap) (finalWorld : StoreTyping),
        nativeCheckpoint.FailedResultAt options.executionFuel value finalStore reason actual ∧
        returned.IndexedAt actual ∧
        Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) sourceSize invocation context ⟨[]⟩
          (.global function) namedArguments outcome after ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context outcome after value finalStore finalMap finalWorld rootFaults := by
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    initial_arguments (inputs := inputs) (rows := rows) (importedPacket := importedPacket)
      (importedMember := importedMember) (distinct := distinct)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime) (atSession := atSession)
      (started := started) (issuance := issuance) (issuedSession := issuedSession)
      (sole := sole) (rawType := rawType) (singleInput := singleInput) (handleValue := handleValue)
  refine ⟨caller, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_run_failed_reflects
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      publicStart atCheckpoint publicRun descriptor

include importedMember distinct receiver observations extension semantic family namedTerminals namedSupport acceptedPlan wellFormed
  prepared selected opened fresh ready sameRuntime atSession atCheckpoint started issuance issuedSession sole rawType singleInput handleValue sourceAt supports in
/-- A supported staged Word result reaches the original public checkpoint
at sufficient native fuel. Input and export budgets remain independent. -/
theorem public_word_preserved
    (outputWord : header.output = .word) (resultWord : header.function.resultType = .word)
    (outputBudget : Nat) (positive : 0 < outputBudget)
    {size : Nat} {word : Word} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram)
      (RecursiveNamedPreparedStageScopes.registry stagePrepared) size invocation context ⟨[]⟩
      (.global function) namedArguments (.value (.word word)) after) :
    ∃ caller : State rootHeaders rootKeys
        ⟨[], [], world, ⟨[]⟩, store, SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩,
      ∃ (capture : CallableIndexedOwnedFunctionValues.NamedCapture rootHeaders (rootOwner).key header [] world)
        (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) (required : Nat),
        (∀ fuel, required ≤ fuel → ∀ outcome, publicCheckpoint.ResumeAt fuel outputBudget outcome →
          ∃ exported, outcome = .succeeded exported ∧ exported.value = .word word) ∧
        CallableIndexedOwnedPreparedStagedTerminalNamedInvocationBounds.ResultAt
          (registry := completion.result.context.registry) (payloads := payloads)
          (scope := []) (canonical := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed)
          rootFunctions rootOwner caller header capture context (.value (.word word)) after
            (.inRight .word (.word word)) finalStore finalMap finalWorld rootFaults := by
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    initial_arguments (inputs := inputs) (rows := rows) (importedPacket := importedPacket)
      (importedMember := importedMember) (distinct := distinct)
      (profile := profile) (wellFormed := wellFormed) (prepared := prepared) (selected := selected)
      (opened := opened) (fresh := fresh) (ready := ready) (sameRuntime := sameRuntime) (atSession := atSession)
      (started := started) (issuance := issuance) (issuedSession := issuedSession)
      (sole := sole) (rawType := rawType) (singleInput := singleInput) (handleValue := handleValue)
  refine ⟨caller, ?_⟩
  exact CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.public_word_preserved
      (stagePrepared := stagePrepared) (receiver := receiver) (profile := profile)
      (observations := observations) (extension := extension) (semantic := semantic)
      (family := family) (namedTerminals := namedTerminals) (namedSupport := namedSupport)
      (acceptedPlan := acceptedPlan) (wellFormed := wellFormed) (selected := selected)
      (owner := rootOwner) (caller := caller) (globalReference := globalReference) (stable := stable)
      (heapTyped := heapTyped) (argumentsTyped := argumentsTyped) (represented := represented)
      (heaps := heaps) (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared) (started := started)
      atCheckpoint outputWord resultWord outputBudget positive trace

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedInitializedNamedPublicBounds
