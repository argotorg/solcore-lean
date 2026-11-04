import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.PublicSupport
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicActualRegistry
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.ProgramAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.AcceptedFactories
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PreparedMethodRoots
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.EligibleSelected
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.CertifiedPublicSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectBounds
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.PublicDirectSessions
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.SourceCompiledCachedActualBody
import Solcore.SourceSemantics.SourceCompiledCachedMethodValidity
import Solcore.SourceSemantics.SourceCompiledActualInitializerBarriers
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.ActualInvocationAllocation

/-!
# Public sessions from actual compilation

From the actual public compilation to an issued session. The raw receipt keeps the exact
compiler artifact, checking budget and prepared recipe, so later consumers cannot choose
another compilation or checker run.

Main declarations:
- `SelectedCompilationRawPublicReceipt.Receipt` and
  `SelectedCompilationRawPublicReceipt.of_compile`, the receipt of a public compilation;
- `SelectedCompilationRawPublicReceipt.Receipt.checker_bodies`,
  `SelectedCompilationRawPublicReceipt.Receipt.checker_profiled` and
  `SelectedCompilationRawPublicReceipt.Receipt.checker_initial_row`, which connect it to
  body validity and the profiled session;
- `SelectedCompilationCertifiedPublicSession.Issued`,
  `SelectedCompilationCertifiedPublicSession.Profiled` and
  `SelectedCompilationCertifiedPublicSession.Initial`, the sessions;
- `SelectedCompilationCertifiedPublicSession.of_checked` and
  `SelectedCompilationCertifiedPublicSession.of_checked_profile`, which issue them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
/-! Raw public compiler success retains the exact Core compiler artifact,
checking budget and prepared recipe. Later semantic consumers use this actual
receipt instead of choosing another source compilation or checker execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Frontend SourceInference
open RecursiveNamedPreparedStageContracts

structure Receipt (raw : Workspace.RawWorkspace) (seeds : List SourceCompiler.Seed)
    (options : SourceCompiler.Options) (publicCompiled : SourceCompiler.Compiled)
    (recipe : SourceCoreIndexedSession.Recipe) where
  source : SourceCoreCompiler.Compiled
  compiled : SourceCoreCompiler.compile raw seeds options = .ok source
  artifact : source.artifact? = some recipe.compiled
  prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe
  publicChecked : SourceCompiler.compileChecked recipe.compiled.sourceProgram seeds options = .ok publicCompiled
  selected : PublicRecipe publicCompiled recipe

theorem of_compile {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (accepted : SourceCompiler.compile raw seeds options = .ok publicCompiled)
    (selected : PublicRecipe publicCompiled recipe) :
    Nonempty (Receipt raw seeds options publicCompiled recipe) := by
  unfold SourceCoreExecution.compile at accepted
  cases sourceAccepted : SourceCoreCompiler.compile raw seeds options with
  | error error => simp [sourceAccepted, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
      simp only [sourceAccepted, Except.mapError, bind, Except.bind] at accepted
      have checked := SourceCoreCompiler.compile_checked_source sourceAccepted
      have sourceChecked : SourceCoreCompiler.compileChecked source.program seeds options = .ok source := by
        simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using sourceAccepted
      have publicChecked : SourceCompiler.compileChecked source.program seeds options = .ok publicCompiled := by
        simpa only [SourceCoreExecution.compileChecked, sourceChecked, Except.mapError, bind, Except.bind] using accepted
      obtain ⟨actual, again, artifact, prepared⟩ := public_compilation publicChecked selected
      have same : actual = source := Except.ok.inj (again.symm.trans sourceChecked)
      subst actual
      refine ⟨⟨source, sourceAccepted, artifact, prepared, ?_, selected⟩⟩
      simpa only [(source.artifact_fields artifact).1] using publicChecked

theorem Receipt.checked {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
    {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
    {recipe : SourceCoreIndexedSession.Recipe}
    (receipt : Receipt raw seeds options publicCompiled recipe) :
    checkProgram raw options.checkingFuel = .ok recipe.compiled.sourceProgram := by
  simpa only [(receipt.source.artifact_fields receipt.artifact).1] using
    SourceCoreCompiler.compile_checked_source receipt.compiled

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionRegistry
/-! The actual input encoder selects the receiving metadata table. Historical
Source results and physical cache authority move together to that table. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (Input compiled)} {rows : Inventory inputs}
  {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {profile : compiled.compatible.checked.catalog.callableContracts = true}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem State.at_named_request
    (prepared : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : State rows anchor initial profile recipe session entries)
    {checkpoint : SourceCoreExecution.Checkpoint artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {inputFuel : Nat}
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers rows) prepared
      checkpoint state.session key publicArguments inputFuel state.world state.store) :
    ∃ receiving : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed,
      receiving.result.context = request.encodedValues ∧
      CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed receiving.entry
        receiving.result.context.registry receiving.result.extension receiving.result.diagnostics ∧
      SourceCoreRawMetadata.Extends initial.result.context.registry receiving.result.context.registry ∧
      RecursiveNamedPublicPhysicalHistory.History (headers := headers rows) (keys := keys compiled)
        (functions := functions rows initial profile) (receiving := receiving.result.context.registry)
        (anchor := anchor) state.session state.mapping state.world state.heap state.store state.caller entries := by
  have sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨receiving, _member, contextAt, issued, extended, retained, _diagnostic⟩ :=
    RecursiveNamedPublicActualRegistryNamedStart.named_start state.history.semantic state.registry request.started
  exact ⟨receiving, contextAt, issued, state.extension.trans extended, retained, state.history.physical⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionState
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
/-! A checked program certificate issues one automatic catalog and its complete
physical support. Later public starts retain the same Source heap and history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall)

structure Issued (recipe : SourceCoreIndexedSession.Recipe) where
  prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe
  catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog recipe.compiled
  initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  support : SelectedCompilationPhysicalProgramSupport.Support recipe.compiled
    (headers catalog.rows) (keys recipe.compiled) initial

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The authentic selected public entry supplies the diagnostic receiver. The
checker receipt keeps its original budget when the support is issued. -/
theorem of_checked
    (certificate : SelectedCompilationPreparedProgramCertificates.Certificate recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  obtain ⟨initial, _sameEntry, registry, received⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry recipe.compiled entry
      recipe.compiled.compatible.checked.staticRegistry (.refl _)
  obtain ⟨catalog, ⟨support⟩⟩ := SelectedCompilationProgramSupportIssuer.issue certificate bodies prepared received registry member checked
  exact ⟨⟨prepared, catalog, initial, support⟩⟩

abbrev Issued.State (issued : Issued recipe)
    (anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) :=
  SelectedCompilationPublicSessionState.State issued.catalog.rows anchor issued.initial
    issued.support.profile recipe session entries

/-- The real current history supplies the native state used by the front door.
The original entry's full instantiation determines the actual first cache row. -/
theorem Issued.recover_start_entry (issued : Issued recipe)
    {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.State anchor session entries)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry state.heap body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store,
      CallableNamedMetadata.Matches request.header.named.specialized entry.instantiation := by
  exact SelectedCompilationCatalogFrontdoor.recover_start_entry issued.catalog issued.support.bodyTyping.signatures issued.prepared state.atRecipe
    state.history.semantic.current.1 state.atSession target valid ordinaryReturn ordinaryParameters call.started

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionRows
/-! A full eligible cached row and its singleton physical slot identify the
actual first matching public root, including when unrelated keys repeat. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog Eligible)
open SelectedCompilationPublicSessionState (StartedCall)

abbrev EligibleRow := CertifiedPublicSession.EligibleRow

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {key : SourceCoreIndexedSession.Key}

variable {recipe : SourceCoreIndexedSession.Recipe}

theorem Issued.recover_start_row (issued : Issued recipe)
    {anchor : CallableIndexedOwnedFunctionValues.Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List RecursiveNamedPublicFunctionHistory.Entry}
    (state : issued.State anchor session entries)
    {publicArguments : List SourceCorePublicValues.Value} {options : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments options) (row : EligibleRow recipe.compiled key) :
    ∃ request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store,
      request.header.named = row.named := by
  apply RecursiveNamedPublicPhysicalFrontdoor.recover_start_at_with issued.prepared
    issued.catalog.inputs issued.catalog.rows state.atRecipe state.history.semantic.current.1 state.atSession
    (fun _ header => header.named = row.named) _ call.started
  intro root selected
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) selected)
  exact row.selected issued.catalog
    (SourceCoreIndexedSession.Recipe.prepare_roots issued.prepared (List.mem_of_find?_eq_some selected)) rootKey

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
/-! A genuine fresh bootstrap, its finite resume history and the actual public
start construct the first Source heap and returned physical function history.
The static program package supplies body meaning internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall FunctionCall State SourceCall)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

abbrev Started := @RecursiveNamedPublicPhysicalSessionInitial.Started

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

/-- The registry fact follows from actual bootstrap and simple public encoding;
it is not supplied as an initial-state representation assumption. -/
theorem Started.registry {call : StartedCall session key publicArguments options}
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value) :
    start.encodedValues.registry = recipe.compiled.compatible.checked.staticRegistry := by
  obtain ⟨_bootstrap, initialized, _value, _store, _atBootstrap, initialState,
      initializedAt, _done, booted⟩ := start.ready.indexed start.opened start.fresh
  have same : initialized = start.nativeSession := initializedAt.unique start.atSession
  subst initialized
  exact start.started.simple_registry (booted.registry_at initialState) simple

/-- Initial data argument admission and actual compilation yield the first
returned handle together with Source execution and the complete physical history. -/
theorem first_function
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : FunctionCall session key publicArguments options)
    (start : Started rows prepared header call.toCall.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (descriptor : SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (invocation : Staging.Recursive.Scope) :
    ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
      entry.sourceType = header.function.resultType ∧ entry.handle = call.handle ∧
      ∃ state : State rows anchor initial support.profile recipe call.completion.session [entry],
        SourceCall anchor header invocation ⟨[]⟩ arguments (.value entry.source) state.heap := by
  have startupRegistry := start.registry rows prepared header simple
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry initial.result.context.registry := by
    rw [startupRegistry, support.registry]
    exact .refl _
  obtain ⟨rawD, function, sourceAt⟩ :=
    (CallableIndexedOwnedPreparedFiniteNamedInventories.source_receipts rows).receipts header start.selected.member
  obtain ⟨physicalCaller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct)
      (profile := support.profile) (completion := initial)
      (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  have supports := (SelectedCompilationPublicReturnedValues.header_context_supports header anchor support.bodyTyping).2
  obtain ⟨actual, generation, value, finalStore, capture, sourceSize, outcome, after,
      finalMap, finalWorld, succeeded, valueEq, _typeEq, _budgetEq, returnedAt, trace, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.public_run_succeeded_reflects
      (stagePrepared := stagePrepared recipe.compiled) (completion := initial)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (packet := support.bodies header start.selected.member)
      (reflectsBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.reflects_bodies support support.issued (.refl _)
          header start.selected.member selected budget)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := physicalCaller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := physicalCaller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := supports)
      (sameCompiled := SourceCoreIndexedSession.Recipe.prepare_compiled prepared)
      (started := start.started) (invocation := invocation)
      call.started start.atCheckpoint call.executed descriptor
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result physicalCaller.physical result
  have returnedRegistry := start.started.returned_registry succeeded
  rw [startupRegistry] at returnedRegistry
  have atRecipe : start.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType] at requested
  obtain ⟨returnedCaller, source, payload, sourceValue, _nativeValue, _related, retained⟩ :=
    RecursiveNamedPublicFunctionHistory.first_remembered rfl start.started start.selected requested succeeded result
      (valueEq.symm.trans call.returned)
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨header.function.resultType, source, call.handle, payload, header.output, options.outputValidationFuel⟩
  let state : State rows anchor initial support.profile recipe call.completion.session [entry] := {
    artifact := start.artifact, session := actual.session, mapping := finalMap, world := finalWorld,
    heap := after, store := finalStore, caller := returnedCaller, atSession := returnedAt,
    atRecipe := start.started.recipe_eq, receiving := initial, issued := support.issued,
    extension := .refl _, registry := support.registry.symm ▸ returnedRegistry,
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨entry, rfl, rfl, state, rawD, function, sourceSize, sourceAt, sourceValue ▸ trace⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitial
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialForward
/-! Independent initial Source success determines execution and export budgets.
Every sufficiently fueled public resume retains its actual new handle, the same
Source heap and all initialized physical cells. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialForward
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open SelectedCompilationPublicSessionState (StartedCall State SourceCall)
open SelectedCompilationPublicSessionInitial (Started)
open SelectedCompilationPhysicalProgramSupport (Support stagePrepared)

variable {recipe : SourceCoreIndexedSession.Recipe}
  {inputs : List (Input recipe.compiled)} (rows : Inventory inputs)
  (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
  (anchor header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
  {initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed}
  (support : Support recipe.compiled (headers rows) (keys recipe.compiled) initial)
  {publicArtifact : SourceCoreExecution.Artifact}
  {session : SourceCoreExecution.Session publicArtifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

def ForwardAt (call : StartedCall session key publicArguments options)
    (source : Dynamic.Value) (after : Dynamic.Heap) : Prop :=
  ∃ requiredExecution requiredOutput,
    ∀ executionFuel outputFuel (outcome : SourceCoreExecution.Outcome publicArtifact),
      requiredExecution ≤ executionFuel → requiredOutput ≤ outputFuel →
      call.checkpoint.ResumeAt executionFuel outputFuel outcome →
      ∃ completion : SourceCoreExecution.Completion publicArtifact,
        outcome = .succeeded completion ∧ completion.session.ExportsReady ∧
        ∃ entry : RecursiveNamedPublicFunctionHistory.Entry,
          entry.sourceType = header.function.resultType ∧ entry.source = source ∧
          completion.value = .function entry.handle ∧ entry.handle.sourceType = header.function.resultType ∧
          ∃ returned : State rows anchor initial support.profile recipe completion.session [entry], returned.heap = after

theorem first_function
    (distinct : (inputs.map (fun input => input.prepared.index)).Nodup)
    (call : StartedCall session key publicArguments options)
    (start : Started rows prepared header call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      header.function.context publicArguments header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty}
    (functionResult : SourceCoreRawMetadata.runtimeType header.function.resultType = .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor header invocation ⟨[]⟩ arguments (.value source) after) :
    ForwardAt rows anchor header support call source after := by
  have startupRegistry := start.registry rows prepared header simple
  have metadata : SourceCoreRawMetadata.Extends start.encodedValues.registry initial.result.context.registry := by
    rw [startupRegistry, support.registry]
    exact .refl _
  obtain ⟨caller, stable, globalReference, heaps, heapTyped, represented, argumentsTyped⟩ :=
    SelectedCompilationPublicInitialArguments.initial_data_arguments
      (inputs := inputs) (rows := rows) (distinct := distinct) (completion := initial)
      (profile := support.profile) (bodyRegistry := initial.result.context.registry)
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults initial.result.diagnostics)
      (bodyTyping := support.bodyTyping) (prepared := prepared) (selected := start.selected)
      (opened := start.opened) (fresh := start.fresh) (ready := start.ready)
      (sameRuntime := SourceCoreExecution.Session.SameRuntime.refl session) (atSession := start.atSession)
      (started := start.started) (inputTypes := inputTypes) (inputMeanings := inputMeanings) (metadata := metadata)
  obtain ⟨rawD, function, sourceSize, sourceAt, applied⟩ := trace
  obtain ⟨capture, value, finalStore, finalMap, finalWorld, requiredExecution, enough, result⟩ :=
    SelectedCompilationPublicBodyInvocationBounds.preserves_root
      (stagePrepared := stagePrepared recipe.compiled) (completion := initial)
      (functions := SelectedCompilationPhysicalProgramSupport.functions support)
      (owner := CallableIndexedOwnedPreparedBootstrapRootState.owner recipe.compiled)
      (packet := support.bodies header start.selected.member)
      (preservesBodies := fun budget {child} selected =>
        SelectedCompilationPhysicalProgramSupport.preserves_bodies support support.issued (.refl _)
          header start.selected.member selected budget)
      (keyPhysical := CallableIndexedOwnedPreparedPhysicalBootstrap.key_physical _ _)
      (physical := caller.physical) (bodyTyping := support.bodyTyping)
      (selected := start.selected) (caller := caller.base.val)
      (globalReference := globalReference) (stable := stable) (heapTyped := heapTyped)
      (represented := represented) (argumentsTyped := argumentsTyped) (heaps := heaps)
      (sourceAt := sourceAt) (supports := (SelectedCompilationPublicReturnedValues.header_context_supports
        header anchor support.bodyTyping).2) applied
  obtain ⟨payload, rfl⟩ : ∃ payload, value = .inRight .word payload := by
    have representedResult := result.2.1
    cases representedResult with
    | value represented => exact ⟨_, rfl⟩
  have completes : ∀ executionFuel, requiredExecution ≤ executionFuel →
      start.checkpoint.NativeDone executionFuel (.inRight .word payload) finalStore :=
    fun fuel bound => start.started.initial.native_done_iff.mpr (enough fuel bound)
  have representedResult : CompatiblePayload.ValueRep recipe.compiled.compatible.checked
      initial.result.context.registry (SelectedCompilationPhysicalProgramSupport.functions support)
      finalMap finalWorld header.function.resultType source payload header.output := by
    have representedResult := result.2.1
    cases representedResult with
    | value related => exact related
  have shape : SourceCorePublicOutputShapes.Output recipe.compiled.compatible.checked start.encodedValues.registry
      (finalStore.map Core.Value.type) recipe.program.layouts.definitions header.function.resultType payload := by
    have shaped := CompatiblePublicOutputShapes.ValueRep.output representedResult
    rw [support.registry, ← startupRegistry] at shaped
    rw [result.2.2.1.runtime_hasTypes.world_eq] at shaped
    exact shaped
  have checkpointRegistry : start.checkpoint.RegistryAt start.encodedValues.registry := by
    have values := start.started.values
    generalize checkpointEq : start.checkpoint = checkpoint at values ⊢
    cases checkpoint
    change _ = start.encodedValues at values
    exact congrArg SourceCoreCompatibleValues.Context.registry values
  have atRecipe : start.artifact.RecipeAt recipe := by
    have convert : ∀ (artifact : SourceCoreIndexedSession.Artifact),
        RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe → artifact.RecipeAt recipe :=
      fun artifact atRecipe => by cases artifact; exact atRecipe
    exact convert _ start.started.recipe_eq
  have requested := start.started.original.result_type_at atRecipe start.started.selected
  have resultType := (RecursiveNamedPublicRootSourceSignature.inputs_and_result start.selected).2
  rw [resultType] at requested
  have checkpointReady := start.started.original.initial_registry.exportsReady
    (start.atSession.exportsReady_iff.mp (start.ready.exportsReady start.authority))
  obtain ⟨requiredOutput, exports⟩ := call.checkpoint.output_succeeded_uniform
    start.atCheckpoint atRecipe checkpointRegistry checkpointReady requested shape
  refine ⟨requiredExecution, max requiredOutput 1, ?_⟩
  intro executionFuel outputFuel outcome executionBound outputBound resumed
  obtain ⟨completion, actual, generation, succeeded, exported, actualAt, returnedReady⟩ :=
    exports executionFuel (completes executionFuel executionBound) outputFuel (Nat.le_trans (Nat.le_max_left _ _) outputBound) outcome resumed
  have requestedRaw := requested
  obtain ⟨exportedCompletion, handle, sameOutcome, functionValue, handleType, _ready⟩ :=
    SourceCoreExecution.Checkpoint.ResumeAt.runtime_function_succeeded start.atCheckpoint resumed checkpointReady
      (completes executionFuel executionBound) requested functionResult (by omega)
  have sameCompletion : exportedCompletion = completion :=
    SourceCoreExecution.Outcome.succeeded.inj (sameOutcome.symm.trans succeeded)
  subst exportedCompletion
  let entry : RecursiveNamedPublicFunctionHistory.Entry :=
    ⟨header.function.resultType, source, handle, payload, header.output, outputFuel⟩
  obtain ⟨reached, related, post⟩ := result.2.2.2.2.2.2.2
  have retained := RecursiveNamedPublicFunctionHistory.History.first rfl start.started start.selected exported result
    reached ⟨related, post⟩
    (.remember requestedRaw rfl rfl (actualAt.1.symm.trans functionValue))
  have physicalRetained := RecursiveNamedPublicPhysicalHistory.physical_of_result caller.physical result
  have returnedRegistry := start.started.returned_registry exported
  rw [startupRegistry, ← support.registry] at returnedRegistry
  let returned : State rows anchor initial support.profile recipe completion.session [entry] := {
    artifact := start.artifact
    session := actual.session
    mapping := finalMap
    world := finalWorld
    heap := after
    store := finalStore
    caller := reached
    atSession := actualAt.2.2.2
    atRecipe := start.started.recipe_eq
    receiving := initial
    issued := support.issued
    extension := .refl _
    registry := returnedRegistry
    history := ⟨retained, physicalRetained⟩ }
  exact ⟨completion, succeeded, actualAt.2.2.2.exportsReady_iff.mpr returnedReady,
    entry, rfl, rfl, functionValue, handleType, returned, rfl⟩


end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialForward
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionInitial
/-! Real compile, opening, bootstrap and startup receipts issue the initial
catalog, diagnostics and physical support and recover its selected Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open SelectedCompilationPublicSessionState (StartedCall FunctionCall SourceCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

structure Initial (issued : Issued recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options) where
  header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)
  start : SelectedCompilationPublicSessionInitial.Started issued.catalog.rows issued.prepared header call

private theorem recipe_unique {compiled : SourceCoreExecution.Compiled}
    {first second : SourceCoreIndexedSession.Recipe}
    (left : RecursiveNamedPreparedStageContracts.PublicRecipe compiled first)
    (right : RecursiveNamedPreparedStageContracts.PublicRecipe compiled second) : first = second := by
  cases compiled
  exact Option.some.inj (left.symm.trans right)

/-- The entry used to issue diagnostics is recovered from the actual selected
root. The caller supplies Source admission and the original program certificate. -/
theorem from_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (certificate : SelectedCompilationPreparedProgramCertificates.Certificate recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same := recipe_unique atArtifact.compiled_recipe selected
  cases same
  have rootIssued := SourceCoreIndexedSession.Recipe.prepare_roots prepared
    (List.mem_of_find?_eq_some started.selected)
  obtain ⟨publicEntry, member, _shape⟩ := rootIssued
  obtain ⟨issued⟩ := of_checked certificate bodies prepared member checked
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) started.selected)
  obtain ⟨header, rootSelected, matched⟩ := SelectedCompilationCatalogFrontdoor.selected_entry issued.catalog bodies.signatures (root := root) ⟨publicEntry, member, _shape⟩
    (by simpa only [rootKey] using target) valid ordinaryReturn ordinaryParameters
  exact ⟨issued, ⟨header, {
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started, selected := rootSelected,
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩, matched⟩

/-- A genuine eligible cache row can select the same initial receipt before
public input typing is supplied. Its singleton global slot fixes the full row. -/
theorem from_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (certificate : SelectedCompilationPreparedProgramCertificates.Certificate recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      initial.header.named = row.named := by
  obtain ⟨actualRecipe, nativeArtifact, nativeSession, checkpoint, root, world, store, native,
      encodedValues, atArtifact, prepared, _source, atSession, atCheckpoint, started⟩ :=
    RecursiveNamedPublicExecutionMeaning.actual_start compiled opened call.started
  have same := recipe_unique atArtifact.compiled_recipe selected
  cases same
  have rootIssued := SourceCoreIndexedSession.Recipe.prepare_roots prepared
    (List.mem_of_find?_eq_some started.selected)
  obtain ⟨publicEntry, member, _shape⟩ := rootIssued
  obtain ⟨issued⟩ := of_checked certificate bodies prepared member checked
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) started.selected)
  obtain ⟨header, rootSelected, namedEq⟩ := row.selected issued.catalog
    (root := root) ⟨publicEntry, member, _shape⟩ rootKey
  exact ⟨issued, ⟨header, {
    publicCompiled := publicCompiled, artifact := nativeArtifact, nativeSession := nativeSession,
    checkpoint := checkpoint, root := root, world := world, store := store, native := native,
    encodedValues := encodedValues, opened := atArtifact, atSession := atSession,
    atCheckpoint := atCheckpoint, started := started, selected := rootSelected,
    bootstrap := bootstrap, bootstrapFuel := bootstrapFuel, fresh := fresh,
    authority := authority, ready := ready }⟩, namedEq⟩

/-- The actual named compilation hook retains its callable descriptor. -/
theorem header_descriptor
    (header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)) :
    Nonempty (SourceCoreCallableContracts.Descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key)) := by
  obtain ⟨origin, index, metadata, found, _history, _emitted⟩ :=
    CallableIndexedFormation.namedBody_history recipe.compiled.indexed.ancestry header.hook
  cases h : SourceCoreCallableContracts.descriptor recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key) with
  | error _ =>
    unfold SourceCoreCallableContracts.descriptor at h
    split at h
    · rename_i missing
      rw [found] at missing
      contradiction
    · contradiction
  | ok descriptor => exact ⟨descriptor⟩

variable {issued : Issued recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.forward_function
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {parameter resultType : TypeSystem.Ty}
    (functionResult : SourceCoreRawMetadata.runtimeType initial.header.function.resultType = .function parameter resultType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value source) after) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows initial.header
      initial.header issued.support call source after :=
  SelectedCompilationPublicSessionInitialForward.first_function issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings functionResult trace

theorem Initial.reflect_function
    {call : FunctionCall session key publicArguments options}
    (initial : Initial issued call.toCall.toStartedCall)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = initial.header.function.resultType ∧ retained.handle = call.handle ∧
      ∃ state : issued.State initial.header call.completion.session [retained],
        SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value retained.source) state.heap := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact SelectedCompilationPublicSessionInitial.first_function issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCompilerCertifiedPublicSession
/-! Finite checks of the complete compiled cache supply the program certificate
used by authentic public initialization. Each compiler receipt is reconstructed
inside the producer; callers retain the original checking and startup receipts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState (StartedCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The original successful checker receipt authenticates retained method bodies.
The static profile covers all actual cached rows and original lambda nodes. -/
theorem of_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact of_checked certificate bodies prepared member checked

/-- Real bootstrap and startup select the original entry in the automatically
issued catalog. Static profile checks replace a supplied program certificate. -/
theorem from_profile_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact from_initial_start checked compiled selected certificate bodies opened call
    bootstrap fresh authority ready target valid ordinaryReturn ordinaryParameters

/-- A complete eligible cached row identifies the actual first root while the
same compiler-derived certificate supplies its physical program support. -/
theorem from_profile_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      initial.header.named = row.named := by
  obtain ⟨certificate⟩ := SelectedCompilationProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) bodies profile
  exact from_initial_row checked compiled selected certificate bodies opened call
    bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationProfiledPublicSession
/-! Retain the original static profile and checker receipt when issuing a public
session. The same finite cache checks then supply preservation on every fault. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState (StartedCall)

structure Profiled (recipe : SourceCoreIndexedSession.Recipe) extends Issued recipe where
  staticProfile : CompilerProgramStaticProfile.StaticProfile recipe.compiled
  checked : ∃ raw checkingFuel, checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram

variable {recipe : SourceCoreIndexedSession.Recipe}

theorem Profiled.registryBodies (issued : Profiled recipe) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages recipe.compiled) := by
  obtain ⟨raw, fuel, checked⟩ := issued.checked
  exact SelectedCompilationRegistryBodies.of_profile
    (SelectedCompilationPhysicalProgramSupport.stagePrepared recipe.compiled)
    issued.support.bodyTyping checked issued.staticProfile

/-- The original successful checker receipt authenticates retained method bodies.
The static profile covers all actual cached rows and original lambda nodes. -/
theorem profiled_of_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Profiled recipe) := by
  obtain ⟨issued⟩ := of_profile profile bodies prepared member checked
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩⟩

/-- Real bootstrap and startup select the original entry in the automatically
issued catalog. Static profile checks replace a supplied program certificate. -/
theorem from_profiled_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨issued, initial, matched⟩ := from_profile_initial_start checked compiled selected
    profile bodies opened call bootstrap fresh authority ready target valid ordinaryReturn ordinaryParameters
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

/-- A complete eligible cached row identifies the actual first root while the
same compiler-derived certificate supplies its physical program support. -/
theorem from_profiled_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (bodies : SelectedCompilationBodyTyping.Bodies recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named := by
  obtain ⟨issued, initial, matched⟩ := from_profile_initial_row checked compiled selected
    profile bodies opened call bootstrap fresh authority ready row
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationActualCheckedPublicProfile
/-! The actual raw public compilation supplies original ordinary and method
body validity to public session issuance. Only barriers at reached inference calls and
the existing compiler profile remain explicit unfinished producer obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Core Frontend SourceInference
open SourceCompiledGeneralizedSoundness
open SelectedCompilationCertifiedPublicSession
open SelectedCompilationPublicSessionState (StartedCall)

variable {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
  {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem Receipt.actual_bodies (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  compile_cached_bodies_of_actual_barriers receipt.compiled receipt.artifact barriers

/-- Public issuance consumes the same accepted body checks for every cached
ordinary function and implementation method. -/
theorem Receipt.actual_profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile (receipt.actual_bodies barriers) receipt.prepared member receipt.checked

/-- The real bootstrap and started call use checker-derived original body
validity. No independent body-typing or program-certificate input is needed. -/
theorem Receipt.actual_initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedActualBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {runOptions : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments runOptions)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named :=
  from_profiled_initial_row receipt.checked receipt.publicChecked receipt.selected
    profile (receipt.actual_bodies barriers) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicProfile
/-! The actual raw public compilation supplies original ordinary and method
body validity to public session issuance. The exact initializer barriers and
the existing compiler profile remain explicit unfinished producer obligations. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Core Frontend SourceInference
open SourceCompiledGeneralizedSoundness
open SelectedCompilationCertifiedPublicSession
open SelectedCompilationPublicSessionState (StartedCall)

variable {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
  {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem Receipt.bodies (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  compile_cached_bodies_of_barriers receipt.compiled receipt.artifact barriers

/-- Public issuance consumes the same accepted body checks for every cached
ordinary function and implementation method. -/
theorem Receipt.profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile (receipt.bodies barriers) receipt.prepared member receipt.checked

/-- The real bootstrap and started call use checker-derived original body
validity. No independent body-typing or program-certificate input is needed. -/
theorem Receipt.initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (barriers : CachedBodyInitializerBarriers receipt.source recipe.compiled options.checkingFuel)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {runOptions : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments runOptions)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named :=
  from_profiled_initial_row receipt.checked receipt.publicChecked receipt.selected
    profile (receipt.bodies barriers) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckerPublicProfile
/-! The actual public compilation supplies checker-derived body validity and
public session issuance. The compiler profile remains a separate obligation;
initializer barriers and original-body typing are derived here. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
open Core Frontend SourceInference
open SelectedCompilationCertifiedPublicSession
open SelectedCompilationPublicSessionState (StartedCall)

variable {raw : Workspace.RawWorkspace} {seeds : List SourceCompiler.Seed}
  {options : SourceCompiler.Options} {publicCompiled : SourceCompiler.Compiled}
  {recipe : SourceCoreIndexedSession.Recipe}

theorem Receipt.checker_bodies (receipt : Receipt raw seeds options publicCompiled recipe) :
    SelectedCompilationBodyTyping.Bodies recipe.compiled :=
  SourceCompiledActualInitializerBarriers.compile_cached_bodies receipt.compiled receipt.artifact

theorem Receipt.checker_profiled (receipt : Receipt raw seeds options publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries) :
    Nonempty (Profiled recipe) :=
  profiled_of_profile profile receipt.checker_bodies receipt.prepared member receipt.checked

/-- Real bootstrap and public call initialization consume the bodies derived
from the exact compilation receipt, without a separate initializer premise. -/
theorem Receipt.checker_initial_row (receipt : Receipt raw seeds options publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {runOptions : SourceCoreExecution.RunOptions}
    (call : StartedCall session key publicArguments runOptions)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named :=
  from_profiled_initial_row receipt.checked receipt.publicChecked receipt.selected
    profile receipt.checker_bodies opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationRawPublicReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedPublicSession
set_option autoImplicit false
set_option Elab.async false

namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
open Core Frontend SourceInference
open SelectedCompilationPublicSessionState (StartedCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- Construct the automatic catalog and issuer from actual checking and the selected compiler profile. -/
theorem of_checked_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  exact of_profile profile (SelectedCompilationCheckedBodyTyping.of_checked checked profile)
    prepared member checked

/-- Recover a started initial entry using body typing derived from the actual checker receipt. -/
theorem from_checked_profile_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  exact from_profile_initial_start checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready
    target valid ordinaryReturn ordinaryParameters

/-- Recover a started initial cache row using body typing derived from the actual checker receipt. -/
theorem from_checked_profile_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Issued recipe, ∃ initial : Initial issued call,
      initial.header.named = row.named := by
  exact from_profile_initial_row checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready row

/-- Retain the actual checker receipt and profile alongside the automatic public issuer. -/
theorem profiled_of_checked_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Profiled recipe) := by
  exact profiled_of_profile profile (SelectedCompilationCheckedBodyTyping.of_checked checked profile)
    prepared member checked

/-- Recover a profiled initial entry while retaining the original checker and startup receipts. -/
theorem from_checked_profiled_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  exact from_profiled_initial_start checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready
    target valid ordinaryReturn ordinaryParameters

/-- Recover a profiled initial cache row while retaining the original checker and startup receipts. -/
theorem from_checked_profiled_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : Profiled recipe, ∃ initial : Initial issued.toIssued call,
      initial.header.named = row.named := by
  exact from_profiled_initial_row checked compiled selected profile
    (SelectedCompilationCheckedBodyTyping.of_checked checked profile) opened call bootstrap fresh authority ready row

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
/-! Checked selected bodies and the complete actual substitution ranges issue
preservation for the unchanged registry. This also covers generalized local
bodies outside the older whole-cache static profile. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
open Core Frontend SourceInference

structure Certificate (compiled : SourceCoreUnifiedCompilation.Compiled) : Prop where
  checked : ∃ raw checkingFuel, checkProgram raw checkingFuel = .ok compiled.sourceProgram
  bodyTyping : SelectedCompilationBodyTyping.Bodies compiled
  ranges : SelectedCompilationRegistryMethodCertificates.Ranges compiled

theorem Certificate.registryBodies {compiled : SourceCoreUnifiedCompilation.Compiled}
    (certificate : Certificate compiled) :
    Staging.Recursive.SelectedPreservation.SelectedBodies
      (Program.ofChecked compiled.sourceProgram) (SelectedCompilationPhysicalProgramSupport.stages compiled) := by
  obtain ⟨raw, fuel, checked⟩ := certificate.checked
  exact SelectedCompilationRegistryBodies.of_checked
    (SelectedCompilationPhysicalProgramSupport.stagePrepared compiled)
    certificate.bodyTyping checked certificate.ranges

theorem of_checked {compiled : SourceCoreUnifiedCompilation.Compiled}
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok compiled.sourceProgram)
    (bodyTyping : SelectedCompilationBodyTyping.Bodies compiled)
    (ranges : SelectedCompilationRegistryMethodCertificates.Ranges compiled) : Certificate compiled :=
  ⟨⟨raw,checkingFuel,checked⟩,bodyTyping,ranges⟩

theorem of_profiled {recipe : SourceCoreIndexedSession.Recipe}
    (issued : SelectedCompilationCertifiedPublicSession.Profiled recipe) : Certificate recipe.compiled :=
  ⟨issued.checked, issued.support.bodyTyping,
    SelectedCompilationRegistryMethodCertificates.ranges_of_profile issued.staticProfile⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedNamedSupport
/-! The authentic check receipt, selected bodies and existing replacement
ranges supply both facets consumed by named execution. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry

theorem Certificate.namedSupport {compiled : Frontend.SourceCoreUnifiedCompilation.Compiled}
    (certificate : Certificate compiled) : SelectedCompilationNamedSupport.Support compiled :=
  ⟨certificate.bodyTyping, certificate.registryBodies⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationCheckedRegistry
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession
/-! Finite checks of the complete compiled cache supply the program certificate
used by authentic public initialization. Each compiler receipt is reconstructed
inside the producer; callers retain the original checking and startup receipts.
Whole-program profiles retain their actual checker and static profile in the
prepared physical session model, including the evidence used on failures. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The original successful checker receipt authenticates retained method bodies.
The static profile covers all actual cached rows and original lambda nodes. -/
theorem of_profile
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (SelectedCompilationCertifiedPublicSession.Profiled recipe) := by
  obtain ⟨certificate⟩ := AcceptedCompilerProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) wellFormed profile
  obtain ⟨issued⟩ := SelectedCompilationCertifiedPublicSession.of_checked certificate
    (SelectedCompilationBodyTyping.Bodies.of_program wellFormed) prepared member checked
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩⟩

/-- Real bootstrap and startup select the original entry in the automatically
issued catalog. Static profile checks replace a supplied program certificate. -/
theorem from_profile_initial_start
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    {entry : Dynamic.ProgramEntry} {body : Dynamic.BodyInstance}
    (target : SourceCompilationPlan.exactInstantiationKey recipe.compiled.indexed.base.plan entry.instantiation = .ok key)
    (valid : Dynamic.ProgramEntryValid (Program.ofChecked recipe.compiled.sourceProgram) entry ⟨[]⟩ body)
    (ordinaryReturn : entry.instantiation.returnComptime = false)
    (ordinaryParameters : ∀ flag ∈ entry.instantiation.parameterComptime, flag = false) :
    ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled recipe,
      ∃ initial : SelectedCompilationCertifiedPublicSession.Initial issued.toIssued call,
      CallableNamedMetadata.Matches initial.header.named.specialized entry.instantiation := by
  obtain ⟨certificate⟩ := AcceptedCompilerProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) wellFormed profile
  obtain ⟨issued, initial, matched⟩ := SelectedCompilationCertifiedPublicSession.from_initial_start
    checked compiled selected certificate (SelectedCompilationBodyTyping.Bodies.of_program wellFormed)
    opened call bootstrap fresh authority ready target valid ordinaryReturn ordinaryParameters
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

/-- A complete eligible cached row identifies the actual first root while the
same compiler-derived certificate supplies its physical program support. -/
theorem from_profile_initial_row
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram)
    {seeds : List SourceCompiler.Seed} {compileOptions : SourceCompiler.Options}
    {publicCompiled : SourceCoreExecution.Compiled}
    (compiled : SourceCoreExecution.compileChecked recipe.compiled.sourceProgram seeds compileOptions = .ok publicCompiled)
    (selected : RecursiveNamedPreparedStageContracts.PublicRecipe publicCompiled recipe)
    (profile : CompilerProgramStaticProfile.StaticProfile recipe.compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    (opened : artifact.CompiledAt publicCompiled)
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options)
    (bootstrap : SourceCoreExecution.Bootstrap artifact) {bootstrapFuel : Nat}
    (fresh : bootstrap.FreshAt) (authority : bootstrap.ExportAuthorityAt)
    (ready : bootstrap.ReadyAt bootstrapFuel session)
    (row : EligibleRow recipe.compiled key) :
    ∃ issued : SelectedCompilationCertifiedPublicSession.Profiled recipe,
      ∃ initial : SelectedCompilationCertifiedPublicSession.Initial issued.toIssued call,
      initial.header.named = row.named := by
  obtain ⟨certificate⟩ := AcceptedCompilerProgramAdmission.of_profile
    (CallableMethodBodyCoherence.of_checked checked) wellFormed profile
  obtain ⟨issued, initial, matched⟩ := SelectedCompilationCertifiedPublicSession.from_initial_row
    checked compiled selected certificate (SelectedCompilationBodyTyping.Bodies.of_program wellFormed)
    opened call bootstrap fresh authority ready row
  exact ⟨⟨issued, profile, ⟨raw, checkingFuel, checked⟩⟩, initial, matched⟩

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end
