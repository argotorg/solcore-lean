import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedProgramCertificates
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionInitialForward

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
