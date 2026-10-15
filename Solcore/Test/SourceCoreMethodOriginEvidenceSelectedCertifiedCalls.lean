import Solcore.Test.SourceCoreMethodOriginEvidenceSelectedCertifiedMeaning
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationLegacyProgramCertificates

/-! Actual public start receipts choose each complete cached row. Reflection
and sufficient-fuel preservation use the single automatic catalog throughout. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
namespace Tests.SourceCoreMethodOriginEvidence.SelectedCertified
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreMethodOriginEvidence.Certified (selected_row header_of_member)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedFunctionValues (Header)
open RecursiveNamedPublicFunctionHistory (Entry)
open RecursiveNamedPublicPhysicalSessionState (SourceCall)
open SelectedCompilationCertifiedPublicSession (Issued Initial)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

theorem first_meaning
    (admission : ObservedProgramCertificate fixture observed)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) :
    ∃ issued : Issued fixture.recipe, Nonempty (FirstMeaning issued stages first) := by
  obtain ⟨issued, initial, namedEq⟩ := SelectedCompilationCertifiedPublicSession.from_initial_row
    (by rw [fixture.sameProgram]; exact fixture.checked)
    (by rw [fixture.sameProgram]; exact fixture.accepted)
    fixture.issued admission.certificate.to_prepared (SelectedCompilationBodyTyping.Bodies.of_program fixture.source_wellFormed) first.opened
    first.as_function_call.toCall.toStartedCall first.bootstrap first.fresh first.authority
    (show first.bootstrap.ReadyAt 102400 first.session from .single first.ready)
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    initial.start.selected.member namedEq
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      initial.header.types := by
    rw [← actualEq, actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  obtain ⟨entry, type, handle, after, trace⟩ := initial.reflect_function
    (call := first.as_function_call) (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
  refine ⟨issued, ⟨⟨initial, actual, actualEq.symm, entry, ?_, handle, after, trace⟩⟩⟩
  exact type.trans (by rw [← actualEq]; exact actual.word_result_type)

variable {issued : Issued fixture.recipe}
  {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
  {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
  {entries : List Entry}

theorem word_meaning (before : issued.State anchor session entries)
    (value next : Core.Word) (flag : Bool)
    (call : ObservedFunctionCall session observed.wordRow.row.key [.word value, .word next, .bool flag])
    (stages : ObservedStages fixture observed.wordRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.wordRow.toObservedRow stages call .word [.word value, .word next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.wordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.wordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.word value, .word next, .bool flag] [.word value, .word next, .bool flag] := by
    rw [← actualEq, actual.word_input_types]
    exact word_inputs value next flag
  have raw : request.header.function.resultType = closureType .word := by
    rw [← actualEq]; exact actual.word_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem bool_meaning (before : issued.State anchor session entries)
    (value next : Bool) (flag : Bool)
    (call : ObservedFunctionCall session observed.boolRow.row.key [.bool value, .bool next, .bool flag])
    (stages : ObservedStages fixture observed.boolRow.toObservedRow) :
    Nonempty (FunctionMeaning issued before observed.boolRow.toObservedRow stages call .bool [.bool value, .bool next, .bool flag]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toCall.toStartedCall
    (selected_row observed.boolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.boolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.bool value, .bool next, .bool flag] [.bool value, .bool next, .bool flag] := by
    rw [← actualEq, actual.bool_input_types]
    exact bool_inputs value next flag
  have raw : request.header.function.resultType = closureType .bool := by
    rw [← actualEq]; exact actual.bool_result_type
  obtain ⟨entry, type, handle, _handleType, after, trace⟩ := issued.reflect_function before call
    request inputs (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, entry, type.trans raw, handle, after, trace⟩⟩

theorem useWord_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .word)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Core.Word) (call : ObservedCall session observed.useWordRow.row.key [.function handle])
    (returned : call.completion.value = .word value)
    (stages : ObservedStages fixture observed.useWordRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useWordRow.toObservedRow stages call (.word value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useWordRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useWordRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useWord_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.word value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useWord_result_type]; rfl
  have native : request.header.output = (.word value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useWord_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.word value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

theorem useBool_meaning (before : issued.State anchor session entries)
    (entry : Entry) (member : entry ∈ entries) (entryType : entry.sourceType = closureType .bool)
    {handle : SourceCorePublicValues.Handle} (handleEq : entry.handle = handle)
    (value : Bool) (call : ObservedCall session observed.useBoolRow.row.key [.function handle])
    (returned : call.completion.value = .bool value)
    (stages : ObservedStages fixture observed.useBoolRow.toObservedRow) :
    Nonempty (ScalarMeaning issued before observed.useBoolRow.toObservedRow stages call (.bool value) [entry.source]) := by
  obtain ⟨request, namedEq⟩ := issued.recover_start_row before call.toStartedCall
    (selected_row observed.useBoolRow.toObservedRow)
  obtain ⟨actual, actualEq⟩ := header_of_member observed.useBoolRow.toObservedRow issued.catalog.rows
    request.selected.member namedEq
  have inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
      (request.header.bindings.map (fun binding => binding.1.scheme.body)) [.function handle] [entry.source] := by
    rw [← actualEq, actual.useBool_input_types, ← entryType, ← handleEq]
    exact .cons (.retained entry member) .nil
  have raw : request.header.function.resultType = (.bool value : ScalarOutput).sourceType := by
    rw [← actualEq, actual.useBool_result_type]; rfl
  have native : request.header.output = (.bool value : ScalarOutput).nativeType := by
    rw [← actualEq, actual.useBool_output]; rfl
  obtain ⟨after, trace⟩ := issued.reflect_scalar before (.bool value) call returned
    request inputs raw native (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
  exact ⟨⟨request, actual, actualEq.symm, inputs, raw, native, after, trace⟩⟩

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
