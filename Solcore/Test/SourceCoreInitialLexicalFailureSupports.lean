import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.Test.SourceCoreInitialLexicalFailureBodies

/-! Both authentic issuer packets produce complete static lexical support.
The Type-valued body dispatcher uses their actual physical slots. -/
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreInitialLexicalFailure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

private def selectTwo {compiled : SourceCoreUnifiedCompilation.Compiled}
    {left right : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (distinct : left.slot ≠ right.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (leftValue : property left) (rightValue : property right) :
    ∀ header, header ∈ [left, right] → property header := by
  intro header member
  if sameSlot : header.slot = left.slot then
    have same : header = left := by
      rcases List.mem_cons.mp member with same | rest
      · exact same
      · have same := List.mem_singleton.mp rest
        exact False.elim (distinct (sameSlot ▸ congrArg (·.slot) same))
    exact same.symm ▸ leftValue
  else
    have same : header = right := by
      rcases List.mem_cons.mp member with same | rest
      · exact False.elim (sameSlot (congrArg (·.slot) same))
      · exact List.mem_singleton.mp rest
    exact same.symm ▸ rightValue

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  failedInput : Input fixture.recipe.compiled
  identityInput : Input fixture.recipe.compiled
  failedRow : failedInput.row = observed.failedRow.row
  identityRow : identityInput.row = observed.identityRow.row
  failedPacket : Issued failedInput
  identityPacket : Issued identityInput
  failedHeader : ActualHeader fixture observed.failedRow.row
  identityHeader : ActualHeader fixture observed.identityRow.row
  failedEq : failedHeader.header = failedPacket.header
  identityEq : identityHeader.header = identityPacket.header
  rows : Inventory [failedInput, identityInput]
  rowsEq : rows = .cons failedPacket (.cons identityPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([failedInput, identityInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : failedHeader.header.slot ≠ identityHeader.header.slot
  terminals : ∀ header, header ∈ headers rows → Body header
  supports : ∀ header (member : header ∈ headers rows),
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (terminals header member) (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  family : ∀ {mapping world function native bindings parameter result}
    (association : CallableIndexedOwnedContextualTypedClosureReceipts.Association (headers rows)
      (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled) registry
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      mapping world function native bindings parameter result),
    CallableIndexedOwnedPreparedStagedOrdinarySequenceCallerBounds.OrdinarySequenceFor (actualStagePrepared fixture) association
  failedDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named failedHeader.header.named.signature.key)
  identityDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named identityHeader.header.named.signature.key)

def ActualHeader.descriptor {fixture : CompiledFixture} {signature : ProgramFunctionSignature}
    {observed : ObservedRow fixture signature}
    (stages : ObservedStages fixture observed) (actual : ActualHeader fixture observed.row) :
    SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
      (.named actual.header.named.signature.key) := by
  rw [actual.aligned.named, RecursiveNamedPreparedCallEvidence.Prepared.signature_key actual.prepared]
  exact stages.descriptor

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (failedStages : ObservedStages fixture observed.failedRow)
    (identityStages : ObservedStages fixture observed.identityRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨failedInput, identityInput, failedRow, identityRow, failedPacket, identityPacket,
    failedHeader, identityHeader, failedEq, identityEq, complete⟩ := observed.inventory
  let rows : Inventory [failedInput, identityInput] := .cons failedPacket (.cons identityPacket .nil)
  have headerList : headers rows = [failedHeader.header, identityHeader.header] := by
    simp only [rows, headers, failedEq, identityEq]
  have failedIndex : failedHeader.header.slot = observed.failedRow.index :=
    failedHeader.aligned.slot.trans (observed.failedRow.prepared_slot failedHeader.prepared).2
  have identityIndex : identityHeader.header.slot = observed.identityRow.index :=
    identityHeader.aligned.slot.trans (observed.identityRow.prepared_slot identityHeader.prepared).2
  have slotsDistinct : failedHeader.header.slot ≠ identityHeader.header.slot := by
    rw [failedIndex, identityIndex]
    exact observed.distinctSlots
  have inputDistinct : failedInput.prepared.index ≠ identityInput.prepared.index := by
    have left : failedHeader.header.slot = failedInput.prepared.index := by
      rw [failedEq]; exact failedPacket.aligned.slot
    have right : identityHeader.header.slot = identityInput.prepared.index := by
      rw [identityEq]; exact identityPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  obtain ⟨failedReceipt⟩ := failedHeader.failed_lexical_receipt
  obtain ⟨identityReceipt⟩ := identityHeader.identity_lexical_receipt
  let failedBody := failedHeader.lexical_body failedReceipt
  let identityBody := identityHeader.lexical_body identityReceipt
  obtain ⟨failedSupport⟩ := failedHeader.failed_support failedReceipt (headers rows) complete (registry := registry) receiver
  obtain ⟨identitySupport⟩ := identityHeader.identity_support identityReceipt (headers rows) complete (registry := registry) receiver
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectTwo slotsDistinct property
      ⟨failedBody, failedSupport⟩ ⟨identityBody, identitySupport⟩ header (headerList ▸ member)
  exact ⟨{
    failedInput := failedInput
    identityInput := identityInput
    failedRow := failedRow
    identityRow := identityRow
    failedPacket := failedPacket
    identityPacket := identityPacket
    failedHeader := failedHeader
    identityHeader := identityHeader
    failedEq := failedEq
    identityEq := identityEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family failedHeader identityHeader (actualStagePrepared fixture) association
    failedDescriptor := failedHeader.descriptor failedStages
    identityDescriptor := identityHeader.descriptor identityStages }⟩

end Tests.SourceCoreInitialLexicalFailure
