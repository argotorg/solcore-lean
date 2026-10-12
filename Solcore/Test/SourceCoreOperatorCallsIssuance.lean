import Solcore.Test.SourceCoreOperatorCallsCommon
import Solcore.Test.SourceCoreOperatorCallsSelection
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicHistoryIssuance

/-! Real issuer receipts extend the retained history and authenticate exact raw
handle types. The Source heap remains the same across each issuance. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreOperatorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers Inventory)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)

private theorem indexed_artifact_eq
    {artifact : SourceCoreExecution.Artifact} {session : SourceCoreExecution.Session artifact}
    {leftArtifact rightArtifact : SourceCoreIndexedSession.Artifact}
    {left : SourceCoreIndexedSession.Session leftArtifact} {right : SourceCoreIndexedSession.Session rightArtifact}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : leftArtifact = rightArtifact := by
  rcases artifact with ⟨compilation, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected native atRecipe =>
      cases session
      exact first.1.symm.trans second.1

theorem identity_source_type {fixture : CompiledFixture} {observed : ObservedProgram fixture}
    {receiver : ObservedReceiver fixture observed} (support : PublicSupports receiver) :
    support.identityPacket.header.named.specialized.function.type = .function .word .word := by
  obtain ⟨facts, certified⟩ :=
    CallableIndexedOwnedPreparedCatalogGlobalIndirectInvocationBounds.source_certificate
      support.identityPacket.sourceAt fixture.source_wellFormed
  have shape := certified.callable_type
  change support.identityPacket.header.named.specialized.function.type = _ at shape
  rw [← support.identityPacket.sourceAt.frame.result, ← support.identityEq,
    support.identityHeader.identity_types, support.identityHeader.result_type] at shape
  rw [support.identityEq] at shape
  exact shape

section State
variable {fixture : CompiledFixture} {observed : ObservedProgram fixture}
  {receiver : ObservedReceiver fixture observed} {support : PublicSupports receiver}
  {publicArtifact : SourceCoreExecution.Artifact} {publicSession : SourceCoreExecution.Session publicArtifact}
  {entries : List Entry}

private theorem named_handle_type (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.identityRow.row.key) :
    call.handle.sourceType = .function .word .word := by
  obtain ⟨artifact, before, actual, beforeAt, issued, completedAt⟩ := call.issued
  cases indexed_artifact_eq state.atSession beforeAt
  have actualType := issued.function_source_type (completedAt.1.symm.trans call.returned)
  obtain ⟨expected, native, _same, sourceType, _fuel, _encoded, factory⟩ := issued.receipt
  have actualFactory : fixture.recipe.NamedCallableAt observed.identityRow.row.key expected native := by
    have atRecipe := state.atRecipe
    cases artifactEq : state.artifact
    rename_i authority actualRecipe
    rw [artifactEq] at atRecipe factory
    change actualRecipe = fixture.recipe at atRecipe
    cases atRecipe
    exact factory
  have keyEq : observed.identityRow.row.key = support.identityPacket.header.named.signature.key :=
    support.identityHeader.key.symm.trans (congrArg (fun header => header.named.signature.key) support.identityEq)
  rw [keyEq] at actualFactory
  obtain ⟨signature, index, specialized, location, closure, identity, descriptor,
    _global, _key, record, expectedType, _remaining⟩ := actualFactory.prepared fixture.recipePrepared
  have specializedEq := Except.ok.inj
    (record.symm.trans (CallableIndexedActualNamedSourceReceipts.header_record _ support.identityPacket.header))
  subst specialized
  exact actualType.trans (sourceType.trans (expectedType.trans (identity_source_type support)))

/-- Named issuance appends the compiler-selected identity global, preserving every
previous capture and the same actual heap. -/
theorem remember_named (state : RetainedState support publicSession entries)
    (call : ObservedNamed publicSession observed.identityRow.row.key) :
    ∃ entry : Entry,
      entry.sourceType = .function .word .word ∧
      entry.handle = call.handle ∧ call.handle.sourceType = .function .word .word ∧
      entry.source = .global (CallableNamedReversal.global (CallableNamedMetadata.global
        support.identityPacket.header.named.specialized support.identityInput.prepared.available)) ∧
      ∃ next : RetainedState support call.completion.session (entries ++ [entry]), next.heap = state.heap := by
  have member : Inventory.HasRow support.identityPacket support.rows := by
    rw [support.rowsEq]
    exact .here _
  have issued : publicSession.NamedIssuedAt support.identityPacket.header.named.signature.key issuanceFuel call.completion := by
    rw [← support.identityEq, support.identityHeader.key]
    exact call.issued
  obtain ⟨actual, native, actualAt, retained⟩ := RecursiveNamedPublicHistoryIssuance.named_remembered
    fixture.recipePrepared [support.identityInput, support.selectInput] support.rows support.identityPacket member
    receiver.completion.result.context.registry state.receiving.result.context.registry
    (CallableIndexedOwnedPublicDecodedCallFaults.faults receiver.completion.result.diagnostics)
    observed.profile state.history state.atRecipe state.atSession issued call.returned fixture.source_wellFormed
  have registry := (call.issued.same_runtime.indexed state.atSession actualAt.2.2.2).registry_at state.registry
  let entry : Entry := ⟨support.identityPacket.header.named.specialized.function.type,
    .global (CallableNamedReversal.global (CallableNamedMetadata.global
      support.identityPacket.header.named.specialized support.identityInput.prepared.available)), call.handle, native,
    Core.CallableContract.functionType support.identityPacket.header.named.signature.parameterType
      support.identityPacket.header.named.signature.resultType, issuanceFuel⟩
  refine ⟨entry, identity_source_type support, rfl, named_handle_type state call, rfl,
    ⟨state.artifact, actual.session, state.mapping, state.world, state.heap, state.store, state.caller,
      actualAt.2.2.2, state.atRecipe, state.receiving, state.issued, state.extension, registry, retained⟩, rfl⟩

end State
end Tests.SourceCoreOperatorCalls
