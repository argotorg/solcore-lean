import Solcore.Test.SourceCoreCanonicalScopedCertifiedHeaders
import Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionDirectScalarForward

/-! The original scoped closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreCanonicalScoped.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open CertifiedPublicSession (Issued Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original scoped closure compiler profile rejected")
  | some profile => pure ⟨profile, accepted⟩

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) where
  initial : Initial issued (firstCall first).toCall.toStartedCall
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = first.handle
  handleType : first.handle.sourceType = closureType
  after : issued.State initial.header first.completion.session [entry]
  trace : SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

structure FunctionMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (stages : ObservedStages fixture observed.makeRow) (value : Core.Word)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session observed.makeRow.row.key [.word value] runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture observed.makeRow.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value]
  rawType : request.header.function.resultType = closureType
  entry : Entry
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = closureType
  after : issued.State anchor call.completion.session (entries ++ [entry])
  trace : SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap [.word value] (.value entry.source) after.heap

def packedSource (next : Core.Word) (flag stop : Bool) : Dynamic.Value :=
  .product (.word next) (.product (.bool flag) (.bool stop))

theorem packed_input (entries : List Entry) (context : SourceSemantics.Context) (next : Core.Word) (flag stop : Bool) :
    RecursiveNamedPublicFunctionHistoryInputs.Input entries context parameterType
      (packed next flag stop) (packedSource next flag stop) := by
  exact .product
    (.data ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩
      ⟨.word next, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word next⟩)
    (.product
      (.data ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩
        ⟨.bool flag, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool flag⟩)
      (.data ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩
        ⟨.bool stop, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool stop⟩))

structure InvocationMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (entry : Entry) (next : Core.Word) (flag stop : Bool)
    {handle : SourceCorePublicValues.Handle}
    (call : ObservedInvocation session handle (packed next flag stop))
    (word : Core.Word) (scope : Staging.Recursive.Scope) where
  member : entry ∈ entries
  entryType : entry.sourceType = closureType
  handleEq : entry.handle = handle
  handleType : handle.sourceType = closureType
  arguments : List Dynamic.Value
  packing : Dynamic.ValuesPack arguments (packedSource next flag stop)
  arity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    entry.source arguments.length
  after : issued.State anchor call.completion.session entries
  size : Nat
  trace : Staging.Recursive.Size.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (CallableIndexedOwnedPreparedPhysicalProgramSupport.stages fixture.recipe.compiled)
    size scope anchor.function.context before.heap entry.source arguments (.value (.word word)) after.heap

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
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

theorem function_meaning (before : issued.State anchor session entries)
    (stages : ObservedStages fixture observed.makeRow) (value : Core.Word)
    (call : ObservedFunctionCall session observed.makeRow.row.key [.word value]) :
    Nonempty (FunctionMeaning issued before stages value call) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before (functionCall call).toCall.toStartedCall row
  obtain ⟨actual, actualEq⟩ := header_of_member observed.makeRow issued.catalog.rows
    request.selected.member ((congrArg (·.specialized) namedEq).trans rowEq)
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value] [.word value] := by
    rw [← actualEq, actual.make_input_types_source]
    exact .cons (.data ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩
      ⟨.word value, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word value⟩) .nil
  have raw : request.header.function.resultType = closureType := by
    rw [← actualEq]; exact actual.make_result_type
  obtain ⟨entry, type, handle, handleType, after, trace⟩ := issued.reflect_function before (functionCall call)
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, handleType.trans raw, after, trace⟩⟩

theorem invocation_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (handleType : handle.sourceType = closureType) (next : Core.Word) (flag stop : Bool)
    (call : ObservedInvocation session handle (packed next flag stop))
    (word : Core.Word) (returned : call.completion.value = .word word) (scope : Staging.Recursive.Scope) :
    Nonempty (InvocationMeaning issued before entry next flag stop call word scope) := by
  obtain ⟨arguments, packing, arity, after, size, trace⟩ :=
    RecursiveNamedPublicPhysicalSessionDirectScalarStep.State.invoke_scalar issued.support issued.prepared
      before entry member (.word word) entryType (handleEq ▸ handleType)
      (packed_input entries anchor.function.context next flag stop)
      (by simpa only [handleEq] using call.executed) returned scope
  exact ⟨⟨member, entryType, handleEq, handleType, arguments, packing, arity, after, size, trace⟩⟩

theorem FirstMeaning.forward {stages : ObservedStages fixture observed.makeRow}
    {first : ObservedPublicRun fixture observed.makeRow} (meaning : FirstMeaning issued stages first) :
    RecursiveNamedPublicPhysicalSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support (firstCall first).toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed] meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.make_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil
  exact meaning.initial.forward_function
    (by intro value member; cases List.mem_singleton.mp member; exact .word seed)
    inputTypes (.cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩ .nil)
    (parameter := parameterType) (resultType := .word)
    (by rw [meaning.headerEq, meaning.actual.make_result_type]; rfl) meaning.trace

theorem FunctionMeaning.forward {before : issued.State anchor session entries}
    {stages : ObservedStages fixture observed.makeRow} {value : Core.Word}
    {call : ObservedFunctionCall session observed.makeRow.row.key [.word value]}
    (meaning : FunctionMeaning issued before stages value call) (ready : session.ExportsReady) :
    RecursiveNamedPublicPhysicalSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      (functionCall call).toCall.toStartedCall parameterType .word meaning.entry.source meaning.after.heap :=
  issued.forward_function before (functionCall call).toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem InvocationMeaning.forward {before : issued.State anchor session entries}
    {entry : Entry} {next word : Core.Word} {flag stop : Bool} {handle : SourceCorePublicValues.Handle}
    {call : ObservedInvocation session handle (packed next flag stop)} {scope : Staging.Recursive.Scope}
    (meaning : InvocationMeaning issued before entry next flag stop call word scope)
    (ready : session.ExportsReady) :
    ∃ checkpoint, session.startHandlePacked handle (packed next flag stop) runOptions.inputValidationFuel = .ok checkpoint ∧
      RecursiveNamedPublicPhysicalSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor
        issued.initial issued.support.profile fixture.recipe entries (.word word) checkpoint meaning.after.heap := by
  obtain ⟨checkpoint, accepted, _resumed⟩ := call.executed
  refine ⟨checkpoint, accepted, ?_⟩
  exact RecursiveNamedPublicPhysicalSessionDirectScalarForward.forward_call issued.support issued.prepared
    before entry meaning.member (.word word) meaning.entryType (meaning.handleEq ▸ meaning.handleType)
    (packed_input entries anchor.function.context next flag stop)
    (by simpa only [meaning.handleEq] using accepted) ready meaning.packing meaning.trace

end Tests.SourceCoreCanonicalScoped.CompilerProfile
