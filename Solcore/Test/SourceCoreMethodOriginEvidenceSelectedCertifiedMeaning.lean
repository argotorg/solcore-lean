import Solcore.Test.SourceCoreMethodOriginEvidenceCertifiedHeaders
import Solcore.Test.SourceCoreMethodOriginEvidenceSequenceForward
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationCertifiedPublicSessionSteps

/-! The original public calls retain Source heaps and handles in the catalog
issued from their program certificate. Each call keeps its actual selected Header. -/
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

structure FirstMeaning (issued : Issued fixture.recipe)
    (stages : ObservedStages fixture observed.wordRow.toObservedRow)
    (first : ObservedPublicRun fixture observed.wordRow.toObservedRow) where
  initial : Initial issued first.as_function_call.toCall.toStartedCall
  actual : ActualHeader fixture observed.wordRow.row
  headerEq : initial.header = actual.header
  entry : Entry
  entryType : entry.sourceType = closureType .word
  handleEq : entry.handle = first.handle
  after : issued.State initial.header first.completion.session [entry]
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall initial.header initial.header
    (RecursiveStageRegistry.scope stages.sidecar [] initial.header.function)
    ⟨[]⟩ [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] (.value entry.source) after.heap

structure FunctionMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedFunctionCall session row.row.key arguments)
    (resultType : TypeSystem.Ty) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = closureType resultType
  entry : Entry
  entryType : entry.sourceType = closureType resultType
  handleEq : entry.handle = call.handle
  after : issued.State anchor call.completion.session (entries ++ [entry])
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value entry.source) after.heap

structure ScalarMeaning
    (issued : Issued fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (before : issued.State anchor session entries)
    {signature : ProgramFunctionSignature} (row : ObservedRow fixture signature)
    (stages : ObservedStages fixture row)
    {arguments : List SourceCorePublicValues.Value} (call : ObservedCall session row.row.key arguments)
    (scalar : ScalarOutput) (sourceArguments : List Dynamic.Value) where
  request : RecursiveNamedPublicHistoryFrontdoor.Started (headers issued.catalog.rows) issued.prepared
    call.checkpoint before.session row.row.key arguments runOptions.inputValidationFuel before.world before.store
  actual : ActualHeader fixture row.row
  headerEq : request.header = actual.header
  inputs : RecursiveNamedPublicFunctionHistoryInputs.Inputs entries request.header.function.context
    (request.header.bindings.map (fun binding => binding.1.scheme.body)) arguments sourceArguments
  rawType : request.header.function.resultType = scalar.sourceType
  nativeType : request.header.output = scalar.nativeType
  after : issued.State anchor call.completion.session entries
  trace : RecursiveNamedPublicPhysicalSessionState.SourceCall anchor request.header
    (RecursiveStageRegistry.scope stages.sidecar [] request.header.function)
    before.heap sourceArguments (.value scalar.source) after.heap

theorem FirstMeaning.forward {issued : Issued fixture.recipe}
    {stages : ObservedStages fixture observed.wordRow.toObservedRow}
    {first : ObservedPublicRun fixture observed.wordRow.toObservedRow}
    (meaning : FirstMeaning issued stages first) :
    SelectedCompilationPublicSessionInitialForward.ForwardAt issued.catalog.rows meaning.initial.header
      meaning.initial.header issued.support first.as_function_call.toCall.toStartedCall meaning.entry.source meaning.after.heap := by
  have inputTypes : RecursiveNamedPublicDataArgumentReceipts.PublicDataTypes
      meaning.initial.header.function.context [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      meaning.initial.header.types := by
    rw [meaning.headerEq, meaning.actual.word_types]
    exact .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have inputMeanings : RecursiveNamedPublicDataInputs.Meanings
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true]
      [.word seed, .word (Core.Word.ofNatModulo 33), .bool true] :=
    .cons ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      (.cons ⟨.word (Core.Word.ofNatModulo 33), by simp [SourceCoreIndexedSession.DataInput.publicValue], .word _⟩
        (.cons ⟨.bool true, by simp [SourceCoreIndexedSession.DataInput.publicValue], .bool true⟩ .nil))
  have functionResult : SourceCoreRawMetadata.runtimeType meaning.initial.header.function.resultType =
      .function .unit .word := by
    rw [meaning.headerEq, meaning.actual.word_result_type]
    rfl
  exact meaning.initial.forward_function (word_simple seed (Core.Word.ofNatModulo 33) true)
    inputTypes inputMeanings functionResult meaning.trace

theorem FunctionMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedFunctionCall session row.row.key arguments}
    {resultType : TypeSystem.Ty} {sourceArguments : List Dynamic.Value}
    (meaning : FunctionMeaning issued before row stages call resultType sourceArguments)
    (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionFunctionForward.FunctionForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe
      call.toCall.toStartedCall .unit resultType meaning.entry.source meaning.after.heap :=
  issued.forward_function before call.toCall.toStartedCall meaning.request meaning.inputs meaning.rawType ready meaning.trace

theorem ScalarMeaning.forward {issued : Issued fixture.recipe}
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} {before : issued.State anchor session entries}
    {signature : ProgramFunctionSignature} {row : ObservedRow fixture signature}
    {stages : ObservedStages fixture row}
    {arguments : List SourceCorePublicValues.Value} {call : ObservedCall session row.row.key arguments}
    {scalar : ScalarOutput} {sourceArguments : List Dynamic.Value}
    (meaning : ScalarMeaning issued before row stages call scalar sourceArguments)
    (ready : session.ExportsReady) :
    SelectedCompilationPublicSessionScalarForward.ForwardAt (entries := entries)
      issued.catalog.rows anchor issued.initial issued.support.profile fixture.recipe scalar
      call.toStartedCall meaning.after.heap :=
  issued.forward_scalar before scalar call.toStartedCall meaning.request meaning.inputs
    meaning.rawType meaning.nativeType ready meaning.trace

end Tests.SourceCoreMethodOriginEvidence.SelectedCertified
