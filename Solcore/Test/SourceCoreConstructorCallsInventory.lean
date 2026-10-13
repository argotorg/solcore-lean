import Solcore.Test.SourceCoreConstructorCallsMakeSupport
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicPhysicalSessionState
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreConstructorCalls
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure ObservedReceiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed
  issued : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
    completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics
  registry : completion.result.context.registry = fixture.recipe.compiled.compatible.checked.staticRegistry

/-- The receiver is built directly at the genuine initial metadata registry. -/
theorem initial_receiver (fixture : CompiledFixture) (observed : ObservedProgram fixture) :
    Nonempty (ObservedReceiver fixture observed) := by
  obtain ⟨receiver, _entry, registry, issued⟩ :=
    CallableIndexedOwnedPublicFaultReceivers.Receiver.at_registry fixture.recipe.compiled observed.makeRow.entry
      fixture.recipe.compiled.compatible.checked.staticRegistry (.refl _)
  exact ⟨⟨receiver, issued, registry⟩⟩


structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    where
  makeInput : Input fixture.recipe.compiled
  readInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  readRow : readInput.row = observed.readRow.row
  makePacket : Issued makeInput
  readPacket : Issued readInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  readHeader : ActualHeader fixture observed.readRow.row
  makeEq : makeHeader.header = makePacket.header
  readEq : readHeader.header = readPacket.header
  rows : Inventory [makeInput, readInput]
  rowsEq : rows = .cons makePacket (.cons readPacket .nil)
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, readInput].map (fun input => input.prepared.index)).Nodup
  slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  readDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named readHeader.header.named.signature.key)

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow)
    (readStages : ObservedStages fixture observed.readRow)
    : Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨makeInput, readInput, makeRow, readRow, makePacket, readPacket,
    makeHeader, readHeader, makeEq, readEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, readInput] := .cons makePacket (.cons readPacket .nil)
  have headerList : headers rows = [makeHeader.header, readHeader.header] := by
    simp only [rows, headers, makeEq, readEq]
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have readIndex : readHeader.header.slot = observed.readRow.index :=
    readHeader.aligned.slot.trans (observed.readRow.prepared_slot readHeader.prepared).2
  have slotsDistinct : makeHeader.header.slot ≠ readHeader.header.slot := by
    rw [makeIndex, readIndex]
    exact observed.distinctSlots
  have inputDistinct : makeInput.prepared.index ≠ readInput.prepared.index := by
    have left : makeHeader.header.slot = makeInput.prepared.index := by
      rw [makeEq]; exact makePacket.aligned.slot
    have right : readHeader.header.slot = readInput.prepared.index := by
      rw [readEq]; exact readPacket.aligned.slot
    rw [← left, ← right]
    exact slotsDistinct
  exact ⟨{
    makeInput := makeInput
    readInput := readInput
    makeRow := makeRow
    readRow := readRow
    makePacket := makePacket
    readPacket := readPacket
    makeHeader := makeHeader
    readHeader := readHeader
    makeEq := makeEq
    readEq := readEq
    rows := rows
    rowsEq := rfl
    complete := complete
    distinct := by simp [inputDistinct]
    slotsDistinct := slotsDistinct
    makeDescriptor := makeHeader.descriptor makeStages
    readDescriptor := readHeader.descriptor readStages }⟩

end Tests.SourceCoreConstructorCalls
