import Solcore.Test.SourceCoreConstructorCallsCertifiedHeaders
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionIssuance
import Solcore.SourceSemantics.CoreLowering.CompilerCertifiedPublicSession
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarStep
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPublicSessionDirectScalarForward

/-! The original indexed closures are retained in one physical public session.
Each Source trace uses the actual selected Header and the reached Source heap. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreConstructorCalls.CompilerProfile
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationPublicSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

structure Observed (fixture : CompiledFixture) where
  value : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled
  accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled
    fixture.source_wellFormed = some value

def observe (fixture : CompiledFixture) : IO (Observed fixture) := do
  match accepted : CompilerProgramStaticProfile.validateProfile fixture.recipe.compiled fixture.source_wellFormed with
  | none => throw (IO.userError "original constructor compiler profile rejected")
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
  trace : SelectedCompilationPublicSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed] (.value entry.source) after.heap

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem first_meaning (profile : Observed fixture)
    (stages : ObservedStages fixture observed.makeRow)
    (first : ObservedPublicRun fixture observed.makeRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨row, rowEq⟩ := selected_row observed.makeRow
  obtain ⟨profiled, initial, namedEq⟩ := CertifiedPublicSession.from_profile_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued profile.value fixture.source_wellFormed first.opened
    (firstCall first).toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 100000 first.session from .single first.ready) row
  let issued := profiled.toIssued
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

structure NamedMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (call : ObservedNamed session row.row.key) where
  selected : IssuedRow issued row
  entry : Entry
  entryType : entry.sourceType = selected.packet.header.named.specialized.function.type
  source : entry.source = .global (CallableNamedReversal.global
    (CallableNamedMetadata.global selected.packet.header.named.specialized selected.input.prepared.available))
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = selected.packet.header.named.specialized.function.type
  after : issued.State anchor call.completion.session (entries ++ [entry])
  heapEq : after.heap = before.heap

theorem named_meaning (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (call : ObservedNamed session row.row.key) :
    Nonempty (NamedMeaning issued before row call) := by
  obtain ⟨selected⟩ := issued_row issued row
  have issuance : session.NamedIssuedAt selected.packet.header.named.signature.key issuanceFuel call.completion := by
    rw [← selected.headerEq, selected.actual.key]
    exact call.issued
  obtain ⟨entry, type, source, handle, handleType, after, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared
      before selected.packet selected.member issuance call.returned
  exact ⟨⟨selected, entry, type, source, handle, handleType, after, heap⟩⟩

structure BuiltinMeaning (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    (call : ObservedBuiltin session) where
  entry : Entry
  entryType : entry.sourceType = convertType
  source : entry.source = .builtin ⟨.wordFromInteger⟩
  handleEq : entry.handle = call.handle
  handleType : call.handle.sourceType = convertType
  after : issued.State anchor call.completion.session (entries ++ [entry])
  heapEq : after.heap = before.heap

theorem builtin_meaning (before : issued.State anchor session entries)
    (call : ObservedBuiltin session) : Nonempty (BuiltinMeaning issued before call) := by
  obtain ⟨entry, type, source, handle, handleType, after, heap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_builtin issued.prepared before
      .wordFromInteger call.issued call.returned
  exact ⟨⟨entry, type, source, handle, handleType, after, heap⟩⟩

end Tests.SourceCoreConstructorCalls.CompilerProfile
