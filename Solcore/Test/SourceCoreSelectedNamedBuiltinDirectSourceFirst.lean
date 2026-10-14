import Solcore.Test.SourceCoreSelectedNamedBuiltinDirectReceipts
import Solcore.Test.SourceCoreSelectedNamedBuiltinDirectTraces
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageClosedDirectForward

/-! Genuine issuance authenticates three retained handles in one physical
history. The earlier completed identity call supplies that starting state.
Every direct ordinary trace below is built independently from Source nodes,
allocation, reads, and the builtin relation before any direct call completes. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 6000000
namespace Tests.SourceCoreSelectedNamedBuiltinDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open Tests.SourceCoreInitialLexicalFailure
open Tests.SourceCoreSelectedNamedBuiltinDirectTraces
open Tests.SourceCoreCertifiedLexicalFailure (FreshIdentity)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open RecursiveNamedPublicFunctionHistory (Entry)
open SelectedCompilationCertifiedPublicSession (Profiled)

variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}

def ValueConclusion (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries) (entry : Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope)
    (arguments : List Dynamic.Value) (value : RecursiveNamedPublicScalarResults.ScalarOutput) (after : Dynamic.Heap) : Prop :=
  (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation anchor.function.context
    state.heap entry.source arguments (.value value.source) after ∧
    SelectedCompilationPublicSessionDirectScalarForward.ForwardAt issued.catalog.rows anchor issued.initial
      issued.support.profile fixture.recipe entries value checkpoint after) ∨
  SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation arguments

def FaultConclusion (issued : Profiled fixture.recipe)
    {anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)}
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {entries : List Entry} (state : issued.toIssued.State anchor session entries) (entry : Entry)
    (checkpoint : SourceCoreExecution.Checkpoint artifact) (invocation : Staging.Recursive.Scope)
    (arguments : List Dynamic.Value) (reason : Dynamic.SemanticFault) (after : Dynamic.Heap) : Prop :=
  (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled) invocation anchor.function.context
    state.heap entry.source arguments (.fault (.semantic reason)) after ∧
    SelectedCompilationPublicSessionDirectFailureForward.FailureForwardAt issued.catalog.rows anchor issued.initial
      issued.support.profile fixture.recipe entries (.semantic reason) checkpoint after) ∨
  SelectedCompilationStageClosedDirectForward.StageStopped issued state entry checkpoint invocation arguments

structure Meaning (stages : ObservedStages fixture observed.identityRow)
    (fresh : FreshIdentity fixture observed) (calls : Handles fixture observed fresh) where
  issued : Profiled fixture.recipe
  anchor : Header fixture.recipe.compiled (Program.ofChecked fixture.recipe.compiled.sourceProgram)
  identity : Entry
  builtin : Entry
  failed : Entry
  identityHandle : identity.handle = calls.identity.handle
  builtinHandle : builtin.handle = calls.builtin.handle
  failedHandle : failed.handle = calls.failed.handle
  identityType : identity.sourceType = .function .word .word
  builtinType : builtin.sourceType = .function .integer .word
  failedType : failed.sourceType = .function .unit .word
  builtinSource : builtin.source = .builtin ⟨.wordFromInteger⟩
  state : issued.toIssued.State anchor calls.failed.completion.session [identity, builtin, failed]
  identityPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence identity.source) state.heap identity.source [.word seed] (.word seed)
    (appendWord state.heap (some (.word seed)))
  builtinPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence builtin.source) state.heap builtin.source [.integer integerArgument]
    (.word convertedWord) state.heap
  failedPlain : Dynamic.CallableFaults (Program.ofChecked fixture.recipe.compiled.sourceProgram)
    anchor.function.context (RecursiveStageRegistry.scope stages.sidecar [] anchor.function).evidence
    (Staging.Recursive.callableEvidence failed.source) state.heap failed.source []
    (.uninitializedLocation (nextLocation state.heap)) (appendWord state.heap none)
  identityForward : ValueConclusion issued state identity calls.identityCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.word seed] (.word seed)
    (appendWord state.heap (some (.word seed)))
  builtinForward : ValueConclusion issued state builtin calls.builtinCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.integer integerArgument]
    (.word convertedWord) state.heap
  failedForward : FaultConclusion issued state failed calls.failedCheckpoint
    (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) []
    (.uninitializedLocation (nextLocation state.heap)) (appendWord state.heap none)
  builtinOutput :
    (Staging.Recursive.Applies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      (SelectedCompilationPhysicalProgramSupport.stages fixture.recipe.compiled)
      (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) anchor.function.context
      state.heap builtin.source [.integer integerArgument] (.value (.word convertedWord)) state.heap ∧
      SelectedCompilationStageClosedDirectForward.Output.ForwardAt issued.catalog.rows anchor issued.initial
        issued.support.profile fixture.recipe [identity, builtin, failed] .word calls.builtinCheckpoint
        (.word convertedWord) state.heap) ∨
    SelectedCompilationStageClosedDirectForward.StageStopped issued state builtin calls.builtinCheckpoint
      (RecursiveStageRegistry.scope stages.sidecar [] anchor.function) [.integer integerArgument]

private theorem packet_type (issued : Profiled fixture.recipe) {input : Input fixture.recipe.compiled}
    (packet : Issued input) :
    packet.header.named.specialized.function.type =
      .function (TypeSystem.Ty.productMany packet.header.types) packet.header.function.resultType := by
  obtain ⟨facts, certificate⟩ := SelectedCompilationNamedArgumentRows.certified_at packet.sourceAt
    issued.support.bodyTyping
    (CallableIndexedOwnedSelectedNamedHeaderReceipts.reissued input.prepared packet.selected) packet.aligned
  have shape := certificate.callable_type
  change packet.header.named.specialized.function.type = _ at shape
  rw [← packet.sourceAt.frame.result] at shape
  exact shape

private theorem packet_at (issued : Profiled fixture.recipe) {signature : ProgramFunctionSignature}
    (row : ObservedRow fixture signature) :
    ∃ input : Input fixture.recipe.compiled, ∃ packet : Issued input,
      Inventory.HasRow packet issued.catalog.rows ∧
      ∃ actual : ActualHeader fixture row.row, actual.header = packet.header := by
  obtain ⟨selected, same⟩ := Tests.SourceCoreCertifiedLexicalFailure.eligible_row row
  obtain ⟨input, packet, member, _row, _index, named⟩ := issued.catalog.packet_at selected.cached selected.eligible
  obtain ⟨actual, equality⟩ := Tests.SourceCoreCertifiedLexicalFailure.header_of_member row issued.catalog.rows
    (Inventory.header_member member) ((congrArg (·.specialized) (packet.aligned.named.trans named)).trans same)
  exact ⟨input, packet, member, actual, equality⟩

theorem meaning (profile : CompilerProgramStaticProfile.StaticProfile fixture.recipe.compiled)
    (stages : ObservedStages fixture observed.identityRow)
    (fresh : FreshIdentity fixture observed) (calls : Handles fixture observed fresh) :
    Nonempty (Meaning stages fresh calls) := by
  obtain ⟨issued, ⟨before⟩⟩ := Tests.SourceCoreSelectedLexicalFailure.fresh_meaning profile stages fresh
  obtain ⟨identityInput, identityPacket, identityMember, identityActual, identityEq⟩ := packet_at issued observed.identityRow
  obtain ⟨failedInput, failedPacket, failedMember, failedActual, failedEq⟩ := packet_at issued observed.failedRow
  have identityKey : identityPacket.header.named.signature.key = observed.identityRow.row.key := by
    rw [← identityEq]; exact identityActual.key
  have failedKey : failedPacket.header.named.signature.key = observed.failedRow.row.key := by
    rw [← failedEq]; exact failedActual.key
  have identityType : identityPacket.header.named.specialized.function.type = .function .word .word := by
    rw [packet_type issued identityPacket, ← identityEq,
      Tests.SourceCoreSelectedLexicalSourceStart.identity_types identityActual, identityActual.identity_result_type]
    rfl
  have failedType : failedPacket.header.named.specialized.function.type = .function .unit .word := by
    rw [packet_type issued failedPacket, ← failedEq,
      Tests.SourceCoreSelectedLexicalSourceStart.failed_types failedActual, failedActual.failed_result_type]
    rfl
  obtain ⟨identity, identityTyped, identitySource, identityHandle, identityHandleType, namedState, _namedHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared before.after
      identityPacket identityMember (by simpa only [identityKey] using calls.identity.issued) calls.identity.returned
  obtain ⟨builtin, builtinTyped, builtinSource, builtinHandle, builtinHandleType, builtinState, _builtinHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_builtin issued.prepared namedState
      .wordFromInteger calls.builtin.issued calls.builtin.returned
  obtain ⟨failed, failedTyped, failedSource, failedHandle, failedHandleType, state, _failedHeap⟩ :=
    SelectedCompilationPublicSessionIssuance.State.remember_named issued.support issued.prepared builtinState
      failedPacket failedMember (by simpa only [failedKey] using calls.failed.issued) calls.failed.returned
  have identityTyped := identityTyped.trans identityType
  have failedTyped := failedTyped.trans failedType
  have ready := calls.failed.issued.exportsReady (calls.builtin.issued.exportsReady
    (calls.identity.issued.exportsReady (fresh.call.executed.exportsReady
      ((SourceCoreExecution.Bootstrap.ReadyAt.single fresh.ready).exportsReady fresh.authority))))
  let invocation := RecursiveStageRegistry.scope stages.sidecar [] before.initial.header.function
  have identityPlain := Tests.SourceCoreSelectedNamedBuiltinDirectTraces.ActualHeader.identity_call identityActual (identityEq.symm ▸ identityPacket.sourceAt)
    before.initial.header invocation state.heap seed
  have failedPlain := Tests.SourceCoreSelectedNamedBuiltinDirectTraces.ActualHeader.failed_call failedActual (failedEq.symm ▸ failedPacket.sourceAt)
    before.initial.header invocation state.heap
  rw [identityEq] at identityPlain
  rw [failedEq] at failedPlain
  change Dynamic.CallableApplies _ _ _ (Staging.Recursive.callableEvidence (.global _)) _ _ _ _ _ at identityPlain
  change Dynamic.CallableFaults _ _ _ (Staging.Recursive.callableEvidence (.global _)) _ _ _ _ _ at failedPlain
  rw [← identitySource] at identityPlain
  rw [← failedSource] at failedPlain
  have builtinPlain : Dynamic.CallableApplies (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      before.initial.header.function.context invocation.evidence
      (Staging.Recursive.callableEvidence builtin.source) state.heap builtin.source [.integer integerArgument]
      (.word convertedWord) state.heap := by
    rw [builtinSource]
    exact .builtin (.wordFromInteger integerArgument)
  have identityInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .word (.word seed) (.word seed) :=
    .data ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
      ⟨.word seed, by simp [SourceCoreIndexedSession.DataInput.publicValue], .word seed⟩
  have builtinInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .integer (.integer integerArgument) (.integer integerArgument) :=
    .data ⟨.integer integerArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer integerArgument⟩
      ⟨.integer integerArgument, by simp [SourceCoreIndexedSession.DataInput.publicValue], .integer integerArgument⟩
  have failedInput : RecursiveNamedPublicFunctionHistoryInputs.Input [identity, builtin, failed]
      before.initial.header.function.context .unit .unit .unit :=
    .data ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
      ⟨.unit, by simp [SourceCoreIndexedSession.DataInput.publicValue], .unit⟩
  have identityStarted := identityHandle.symm ▸ calls.identityStarted
  have builtinStarted := builtinHandle.symm ▸ calls.builtinStarted
  have failedStarted := failedHandle.symm ▸ calls.failedStarted
  have faultArity : RecursivePublicCallableArity.Arity (Program.ofChecked fixture.recipe.compiled.sourceProgram)
      failed.source 0 := by
    rw [failedSource]
    have actual := RecursivePublicCallableArity.Arity.global failedPacket.sourceAt.frame.instantiated
    have inputs : failedPacket.header.sourceBody.source.inputs = [] := by
      rw [← failedPacket.sourceAt.frame.source, ← failedEq, failedActual.source, observed.failedShape.inputs]
    simpa only [inputs, List.length_nil] using actual
  refine ⟨{
    issued := issued, anchor := before.initial.header,
    identity := identity, builtin := builtin, failed := failed,
    identityHandle := identityHandle, builtinHandle := builtinHandle, failedHandle := failedHandle,
    identityType := identityTyped, builtinType := builtinTyped, failedType := failedTyped,
    builtinSource := builtinSource, state := state,
    identityPlain := identityPlain, builtinPlain := builtinPlain, failedPlain := failedPlain,
    identityForward := ?_, builtinForward := ?_, failedForward := ?_, builtinOutput := ?_ }⟩
  · exact SelectedCompilationStageClosedDirectForward.scalar issued state identity (by simp)
      identityTyped identityInput identityStarted ready (Dynamic.ValuesPack.singleton (.word seed))
      (.word seed) rfl (by rw [identityHandle]; exact identityHandleType.trans identityType) identityPlain
  · exact SelectedCompilationStageClosedDirectForward.scalar issued state builtin (by simp)
      builtinTyped builtinInput builtinStarted ready (Dynamic.ValuesPack.singleton (.integer integerArgument))
      (.word convertedWord) rfl (by rw [builtinHandle]; exact builtinHandleType) builtinPlain
  · exact SelectedCompilationStageClosedDirectForward.fault issued state failed (by simp)
      failedTyped failedInput failedStarted ready Dynamic.ValuesPack.nil faultArity
      (.uninitializedLocation (nextLocation state.heap)) failedPlain
  · exact SelectedCompilationStageClosedDirectForward.output issued state builtin (by simp)
      builtinTyped builtinInput builtinStarted ready (Dynamic.ValuesPack.singleton (.integer integerArgument)) builtinPlain

end Tests.SourceCoreSelectedNamedBuiltinDirect
