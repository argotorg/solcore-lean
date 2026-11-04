import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedProgramAdmission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryCatalogPublicAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalSessions
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.MethodRoots
import Solcore.SourceSemantics.Staging.RecursiveCallableErasure

/-!
# Certified public sessions over recursive named rows

The certified session tower built directly on recursive named physical sessions: issuance, rows, initial calls, steps and the outcomes that reflect to Source. The `SelectedCompilationCertifiedPublicSession` theorems in the front have the same shape over selected compilations.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
/-! A checked program certificate issues one automatic catalog and its complete
physical support. Later public starts retain the same Source heap and history. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

structure Issued (recipe : SourceCoreIndexedSession.Recipe) where
  prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe
  catalog : CallableIndexedOwnedPreparedOrdinaryCatalogReceipts.Catalog recipe.compiled
  initial : CallableIndexedOwnedPublicFaultReceivers.Receiver recipe.compiled.indexed
  support : CallableIndexedOwnedPreparedPhysicalProgramSupport.Support recipe.compiled
    (headers catalog.rows) (keys recipe.compiled) initial

variable {recipe : SourceCoreIndexedSession.Recipe}

/-- The authentic selected public entry supplies the diagnostic receiver. The
checker receipt keeps its original budget when the support is issued. -/
theorem of_checked
    (certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate recipe.compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
    (prepared : SourceCoreIndexedSession.Recipe.prepare recipe.compiled = .ok recipe)
    {entry : SourceCoreCallableIndexedPrograms.Entry recipe.compiled.indexed.layouts}
    (member : entry ∈ recipe.compiled.indexed.entries)
    {raw : Workspace.RawWorkspace} {checkingFuel : Nat}
    (checked : checkProgram raw checkingFuel = .ok recipe.compiled.sourceProgram) :
    Nonempty (Issued recipe) := by
  obtain ⟨initial, _sameEntry, registry, received⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry recipe.compiled entry
      recipe.compiled.compatible.checked.staticRegistry (.refl _)
  obtain ⟨catalog, ⟨support⟩⟩ := certificate.issue wellFormed prepared received registry member checked
  exact ⟨⟨prepared, catalog, initial, support⟩⟩

abbrev Issued.State (issued : Issued recipe)
    (anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))
    {artifact : SourceCoreExecution.Artifact} (session : SourceCoreExecution.Session artifact)
    (entries : List RecursiveNamedPublicFunctionHistory.Entry) :=
  RecursiveNamedPublicPhysicalSessionState.State issued.catalog.rows anchor issued.initial
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
  exact issued.catalog.recover_start_entry issued.support.wellFormed issued.prepared state.atRecipe
    state.history.semantic.current.1 state.atSession target valid ordinaryReturn ordinaryParameters call.started

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionRows
/-! A full eligible cached row and its singleton physical slot identify the
actual first matching public root, including when unrelated keys repeat. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedOrdinaryCatalogReceipts (Catalog Eligible)
open RecursiveNamedPublicPhysicalSessionState (StartedCall)

structure EligibleRow (compiled : SourceCoreUnifiedCompilation.Compiled)
    (key : SourceCoreIndexedSession.Key) where
  named : SourceCoreGeneralFunctions.Function
  index : Nat
  global : SourceCoreCalls.Signature
  cached : compiled.indexed.base.functions[index]? = some named
  slot : CallableNamedMetadata.Slot compiled.indexed.base.globals index global
  globalKey : global.key = key
  eligible : Eligible compiled named.specialized

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {key : SourceCoreIndexedSession.Key}

/-- The singleton global slot fixes the entire selected cache row and index. -/
theorem EligibleRow.first_eq (row : EligibleRow compiled key)
    {named : SourceCoreGeneralFunctions.Function} {index : Nat}
    (found : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = key)) = some (named, index)) :
    named = row.named ∧ index = row.index := by
  have cached := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
  have global := CallableIndexedPreparedInventories.cached_global_at compiled cached
  have selectedKey : named.signature.key = key := of_decide_eq_true (List.find?_some
    (p := fun item : SourceCoreGeneralFunctions.Function × Nat => decide (item.1.signature.key = key)) found)
  have member : (named.signature, index) ∈ compiled.indexed.base.globals.zipIdx.filter
      (fun item => decide (item.1.key = row.global.key)) := by
    apply List.mem_filter.mpr
    exact ⟨List.mk_mem_zipIdx_iff_getElem?.mpr global,
      by simp only [selectedKey, row.globalKey, decide_true]⟩
  rw [row.slot] at member
  have same : (named.signature, index) = (row.global, row.index) := by simpa only [List.mem_singleton] using member
  have indexEq := (Prod.mk.inj same).2
  have namedEq : named = row.named := Option.some.inj ((indexEq ▸ cached).symm.trans row.cached)
  exact ⟨namedEq, indexEq⟩

theorem EligibleRow.selected (row : EligibleRow compiled key) (catalog : Catalog compiled)
    {root : SourceCoreIndexedSession.Root compiled} (issued : root.Issued compiled)
    (rootKey : root.key = key) :
    ∃ header, RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers catalog.rows) root header ∧
      header.named = row.named := by
  obtain ⟨entry, member, shape⟩ := issued
  have factory := shape
  obtain ⟨named, index, found, _namedKey, entryKey, _rest⟩ := factory
  have actual := found
  rw [← entryKey, rootKey] at actual
  obtain ⟨namedEq, indexEq⟩ := row.first_eq actual
  obtain ⟨header, retained, slot, same⟩ := catalog.header_at row.cached row.eligible
  refine ⟨header, RecursiveNamedPublicRootMeaning.selection_at retained member shape found ?_, same⟩
  exact slot.trans indexEq.symm

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

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionInitial
/-! Real compile, opening, bootstrap and startup receipts issue the initial
catalog, diagnostics and physical support and recover its selected Header. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall FunctionCall SourceCall)

variable {recipe : SourceCoreIndexedSession.Recipe}

structure Initial (issued : Issued recipe)
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
    {options : SourceCoreExecution.RunOptions} (call : StartedCall session key publicArguments options) where
  header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)
  start : RecursiveNamedPublicPhysicalSessionInitial.Started issued.catalog.rows issued.prepared header call

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
    (certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate recipe.compiled)
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
  obtain ⟨issued⟩ := of_checked certificate wellFormed prepared member checked
  have rootKey : root.key = key := of_decide_eq_true (List.find?_some
    (p := fun candidate : SourceCoreIndexedSession.Root recipe.compiled => decide (candidate.key = key)) started.selected)
  obtain ⟨header, rootSelected, matched⟩ := issued.catalog.selected_entry wellFormed (root := root) ⟨publicEntry, member, _shape⟩
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
    (certificate : CallableIndexedOwnedPreparedProgramAdmission.Certificate recipe.compiled)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram))
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
  obtain ⟨issued⟩ := of_checked certificate wellFormed prepared member checked
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
    RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows initial.header
      initial.header issued.support call source after :=
  RecursiveNamedPublicPhysicalSessionInitialForward.first_function issued.catalog.rows issued.prepared
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
  exact RecursiveNamedPublicPhysicalSessionInitial.first_function issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings descriptor invocation

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSteps
/-! Session steps use the automatically issued body families and the actual
input registry. Source traces and typed public inputs remain independent. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall FunctionCall Call SourceCall)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Issued.forward_function
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    {parameterType resultType : TypeSystem.Ty}
    (rawType : request.header.function.resultType = .function parameterType resultType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {source : Dynamic.Value}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value source) after) :
    RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe call parameterType resultType source after :=
  RecursiveNamedPublicPhysicalSessionFunctionForward.forward_function_at_input_registry issued.support
    issued.prepared state call request inputs rawType ready trace

theorem Issued.forward_scalar
    (scalar : ScalarOutput) (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after) :
    RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe scalar call after :=
  RecursiveNamedPublicPhysicalSessionScalarForward.forward_call_at_input_registry issued.support
    issued.prepared state scalar call request inputs rawType nativeType ready trace

theorem Issued.reflect_function
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = request.header.function.resultType ∧ retained.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : issued.State anchor call.completion.session (entries ++ [retained]),
        SourceCall anchor request.header invocation state.heap arguments (.value retained.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact RecursiveNamedPublicPhysicalSessionFunctionStep.State.make_typed_handle_at_input_registry issued.support
    issued.prepared state call request inputs descriptor invocation

theorem Issued.reflect_scalar
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State anchor call.completion.session entries,
      SourceCall anchor request.header invocation state.heap arguments (.value scalar.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact RecursiveNamedPublicPhysicalSessionScalarStep.State.finished_call_at_input_registry issued.support
    issued.prepared state scalar call returned request inputs rawType nativeType descriptor invocation

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionOutcomes
/-! Certified sessions can begin with scalar success or a Source fault. Later
failures retain the same physical history and use the actual input registry. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall Call SourceCall)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Issued recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.forward_scalar
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (scalar : ScalarOutput)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after) :
    RecursiveNamedPublicPhysicalSessionScalarForward.ForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe scalar call after :=
  RecursiveNamedPublicPhysicalSessionInitialScalarForward.first_scalar issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct scalar call initial.start simple
    inputTypes inputMeanings rawType nativeType trace

theorem Initial.reflect_scalar
    {call : Call session key publicArguments options} (initial : Initial issued call.toStartedCall)
    (scalar : ScalarOutput) (returned : call.completion.value = scalar.publicValue)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State initial.header call.completion.session [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.value scalar.source) after.heap := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact RecursiveNamedPublicPhysicalSessionInitialScalarStep.first_scalar issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct scalar call returned initial.start simple
    inputTypes inputMeanings rawType nativeType descriptor invocation

theorem Initial.forward_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after) :
    RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := []) issued.catalog.rows
      initial.header issued.initial issued.support.profile recipe failure call after :=
  RecursiveNamedPublicPhysicalSessionInitialFailureForward.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call initial.start simple
    inputTypes inputMeanings trace

theorem Initial.reflect_failure
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor initial.header
  exact RecursiveNamedPublicPhysicalSessionInitialFailureStep.first_failure issued.catalog.rows issued.prepared
    initial.header initial.header issued.support issued.catalog.distinct call returned reason failedCall initial.start simple
    inputTypes inputMeanings descriptor invocation

variable (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)

theorem Issued.forward_failure
    (call : StartedCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (ready : session.ExportsReady)
    {invocation : Staging.Recursive.Scope} {after : Dynamic.Heap} {failure : Staging.Recursive.Failure}
    (trace : SourceCall anchor request.header invocation state.heap arguments (.fault failure) after) :
    RecursiveNamedPublicPhysicalSessionFailureForward.FailureForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile recipe failure call after :=
  RecursiveNamedPublicPhysicalSessionFailureForward.forward_call_at_input_registry issued.support
    issued.prepared state call request inputs ready trace

theorem Issued.reflect_failure
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State anchor returned entries,
      SourceCall anchor request.header invocation state.heap arguments (.fault failure) after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨descriptor⟩ := header_descriptor request.header
  exact RecursiveNamedPublicPhysicalSessionFailureStep.State.failed_call_at_input_registry issued.support
    issued.prepared state call returned reason failedCall request inputs descriptor invocation

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionSourceOutcomes
/-! Actual public completions reflect to independent Dynamic applications at
the same issued session state. Failure keeps its semantic or staging origin
and the exact public diagnostic relation. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicPhysicalSessionState (StartedCall FunctionCall Call SourceCall PlainValue FailureProjection)
open RecursiveNamedPublicScalarResults (ScalarOutput)

variable {recipe : SourceCoreIndexedSession.Recipe} {issued : Issued recipe}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value}
  {options : SourceCoreExecution.RunOptions}

theorem Initial.reflect_function_plain
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
        PlainValue initial.header initial.header invocation ⟨[]⟩ arguments retained.source state.heap := by
  obtain ⟨retained, sourceType, handle, state, trace⟩ :=
    initial.reflect_function simple inputTypes inputMeanings invocation
  exact ⟨retained, sourceType, handle, state, trace.value_plain⟩

theorem Initial.reflect_scalar_plain
    {call : Call session key publicArguments options} (initial : Initial issued call.toStartedCall)
    (scalar : ScalarOutput) (returned : call.completion.value = scalar.publicValue)
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (rawType : initial.header.function.resultType = scalar.sourceType)
    (nativeType : initial.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State initial.header call.completion.session [],
      PlainValue initial.header initial.header invocation ⟨[]⟩ arguments scalar.source after.heap := by
  obtain ⟨after, trace⟩ := initial.reflect_scalar scalar returned simple inputTypes inputMeanings rawType nativeType invocation
  exact ⟨after, trace.value_plain⟩

/-- The semantic branch has a Dynamic fault; the stage branch retains the
actual rejected guard. Both retain the exact completed public state. -/
theorem Initial.reflect_failure_plain
    {call : StartedCall session key publicArguments options} (initial : Initial issued call)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (simple : ∀ value ∈ publicArguments, SourceCoreIndexedSession.SimplePublic value)
    (inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context publicArguments initial.header.types)
    {arguments : List Dynamic.Value}
    (inputMeanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State initial.header returned [],
      SourceCall initial.header initial.header invocation ⟨[]⟩ arguments (.fault failure) after.heap ∧
      FailureProjection initial.header initial.header invocation ⟨[]⟩ arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨failure, after, trace, diagnostic⟩ :=
    initial.reflect_failure returned reason failedCall simple inputTypes inputMeanings invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

variable (issued : Issued recipe)
  {anchor : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
  {entries : List RecursiveNamedPublicFunctionHistory.Entry}
  (state : issued.State anchor session entries)

theorem Issued.reflect_function_plain
    (call : FunctionCall session key publicArguments options)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ retained : RecursiveNamedPublicFunctionHistory.Entry,
      retained.sourceType = request.header.function.resultType ∧ retained.handle = call.handle ∧
      call.handle.sourceType = request.header.function.resultType ∧
      ∃ after : issued.State anchor call.completion.session (entries ++ [retained]),
        PlainValue anchor request.header invocation state.heap arguments retained.source after.heap := by
  obtain ⟨retained, sourceType, handle, handleType, after, trace⟩ :=
    issued.reflect_function state call request inputs invocation
  exact ⟨retained, sourceType, handle, handleType, after, trace.value_plain⟩

theorem Issued.reflect_scalar_plain
    (scalar : ScalarOutput) (call : Call session key publicArguments options)
    (returned : call.completion.value = scalar.publicValue)
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (rawType : request.header.function.resultType = scalar.sourceType)
    (nativeType : request.header.output = scalar.nativeType)
    (invocation : Staging.Recursive.Scope) :
    ∃ after : issued.State anchor call.completion.session entries,
      PlainValue anchor request.header invocation state.heap arguments scalar.source after.heap := by
  obtain ⟨after, trace⟩ := issued.reflect_scalar state scalar call returned request inputs rawType nativeType invocation
  exact ⟨after, trace.value_plain⟩

theorem Issued.reflect_failure_plain
    (call : StartedCall session key publicArguments options)
    (returned : SourceCoreExecution.Session artifact) (reason : Word)
    (failedCall : session.RunAt key publicArguments options (.ok (.failed reason returned)))
    (request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
      call.checkpoint state.session key publicArguments options.inputValidationFuel state.world state.store)
    {arguments : List Dynamic.Value}
    (inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (invocation : Staging.Recursive.Scope) :
    ∃ failure, ∃ after : issued.State anchor returned entries,
      SourceCall anchor request.header invocation state.heap arguments (.fault failure) after.heap ∧
      FailureProjection anchor request.header invocation state.heap arguments failure after.heap ∧
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults after.receiving.result.diagnostics failure reason := by
  obtain ⟨failure, after, trace, diagnostic⟩ :=
    issued.reflect_failure state call returned reason failedCall request inputs invocation
  exact ⟨failure, after, trace, trace.failure_plain, diagnostic⟩

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CertifiedPublicSessionDirectSourceOutcomes
/-! Actual calls through retained handles expose the original independent
Source callable and its exact application at the same returned session. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
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
        (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages recipe.compiled) size
        invocation anchor.function.context before.heap entry.source sources (.value scalar.source) next.heap ∧
      Dynamic.CallableApplies (Program.ofChecked recipe.compiled.sourceProgram)
        anchor.function.context invocation.evidence (Staging.Recursive.callableEvidence entry.source)
        before.heap entry.source sources scalar.source next.heap := by
  obtain ⟨sources, packing, arity, next, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member scalar entryType handleType input invoked output invocation
  exact ⟨sources, packing, arity, next, size, trace, trace.sound.value_plain⟩

end Solcore.SourceSemantics.CoreLowering.CertifiedPublicSession
end
