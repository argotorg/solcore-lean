import Solcore.Test.SourceCoreRecursiveIndexCertifiedHeaders
import Solcore.Test.SourceCoreRecursiveIndexInputs
import Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarForward

/-! The original indexed closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreRecursiveIndex.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Profiled Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original index compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Profiled fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) where
  initial : Initial issued.toIssued (firstCall first).toCall.toStartedCall
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = first.handle
  handleType : first.handle.sourceType = closureType
  after : issued.toIssued.State initial.header first.completion.session [entry]
  trace : SelectedCompilationPublicSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Profiled fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure FunctionMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    {publicArguments : List SourceCorePublicValues.Value}
    (call : ObservedFunctionCall session row.row.key publicArguments)
    (arguments : List Dynamic.Value) (scope : Staging.Recursive.Scope) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key publicArguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments
  rawType : request.header.function.resultType = closureType
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = closureType
  after : issued.toIssued.State anchor call.completion.session (entries ++ [entry])
  trace : SelectedCompilationPublicSessionState.SourceCall anchor request.header scope before.heap arguments (.value entry.source) after.heap

theorem unit_input (entries : List Entry) (context : SourceSemantics.Context) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context .unit .unit .unit :=
  .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
    ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩

structure InvocationMeaning (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.toIssued.State anchor session entries)
    (entry : Entry)
    {handle : SourceCorePublicValues.Handle}
    (call : ObservedInvocation session handle .unit)
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = handle
  handleType : handle.sourceType = closureType
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments .unit
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.toIssued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Profiled fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨issued, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    (firstCall first).toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    initial.start.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed] initial.header.types := by
    rw [← actualEq, actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings [.word seed] [.word seed] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := firstCall first) (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  have raw : initial.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  exact ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, type.trans raw, handle,
    (initial_handle_type initial).trans raw, after, trace⟩⟩⟩

theorem make_meaning (before : issued.toIssued.State anchor session entries)
    (value : Core.Word) (call : ObservedFunctionCall session observed.makeRow.row.key [.word value])
    (scope : Staging.Recursive.Scope) :
    Nonempty (FunctionMeaning issued before observed.makeRow call [.word value] scope) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨request, namedEq⟩ := issued.toIssued.recover_start_row before call.toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value] := by
    rw [← actualEq, actual.make_input_types_source]
    exact .cons (word_input value) .nil
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.toIssued.reflect_function before call request inputs scope
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

theorem invocation_meaning (before : issued.toIssued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = closureType)
    (call : ObservedInvocation session handle .unit)
    (word : Core.Word) (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (InvocationMeaning issued before entry call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    SelectedCompilationPublicSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType)
      (unit_input entries anchor.function.context)
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, handleType, arguments, packing, arity, after, size, trace⟩⟩

theorem FirstMeaning.forward {stages : ObservedStages fixture observed.makeRow}
    {first : ObservedPublicRun fixture observed.makeRow} (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support (firstCall first).toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed] meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact meaning.initial.forward_function
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
    (parameter := .unit) (resultType := .word)
    (by rw [meaning.headerEq, meaning.actual.make_result_type]; rfl) meaning.trace

theorem FunctionMeaning.forward {before : issued.toIssued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {publicArguments : List SourceCorePublicValues.Value}
    {call : ObservedFunctionCall session row.row.key publicArguments}
    {arguments : List Dynamic.Value} {scope : Staging.Recursive.Scope}
    (meaning : FunctionMeaning issued before row call arguments scope) (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      call.toCall.toStartedCall .unit .word meaning.entry.source meaning.after.heap :=
  issued.toIssued.forward_function before call.toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem InvocationMeaning.forward {before : issued.toIssued.State anchor session entries}
    {entry : Entry} {word : Core.Word} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle .unit} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry call word scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle .unit runOptions.inputValidationFuel = .ok checkpoint ∧
      SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (.word word) checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact SelectedCompilationPublicSessionDirectScalarForward.forward_call issued.support issued.prepared
    before entry meaning.member (.word word) meaning.entryType (meaning.handleEq ▸ meaning.handleType)
    (unit_input entries anchor.function.context)
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreRecursiveIndex.CompilerProfile
