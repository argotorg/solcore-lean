import Solcore.Test.SourceCoreRecursiveIndexMakeSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreRecursiveIndex
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodySupport (Support)

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


structure OrdinaryInventory (fixture : CompiledFixture) (observed : ObservedProgram fixture) where
  makeInput : Input fixture.recipe.compiled
  echoInput : Input fixture.recipe.compiled
  chooseInput : Input fixture.recipe.compiled
  selectInput : Input fixture.recipe.compiled
  makeRow : makeInput.row = observed.makeRow.row
  echoRow : echoInput.row = observed.echoRow.row
  chooseRow : chooseInput.row = observed.chooseRow.row
  selectRow : selectInput.row = observed.selectRow.row
  makePacket : Issued makeInput
  echoPacket : Issued echoInput
  choosePacket : Issued chooseInput
  selectPacket : Issued selectInput
  makeHeader : ActualHeader fixture observed.makeRow.row
  echoHeader : ActualHeader fixture observed.echoRow.row
  chooseHeader : ActualHeader fixture observed.chooseRow.row
  selectHeader : ActualHeader fixture observed.selectRow.row
  makeEq : makeHeader.header = makePacket.header
  echoEq : echoHeader.header = echoPacket.header
  chooseEq : chooseHeader.header = choosePacket.header
  selectEq : selectHeader.header = selectPacket.header
  rows : Inventory [makeInput, echoInput, chooseInput, selectInput]
  rowsEq : rows = .cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket (.nil))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([makeInput, echoInput, chooseInput, selectInput].map (fun input => input.prepared.index)).Nodup
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  echoDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named echoHeader.header.named.signature.key)
  chooseDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseHeader.header.named.signature.key)
  selectDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named selectHeader.header.named.signature.key)
theorem OrdinaryInventory.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture}
    (support : OrdinaryInventory fixture observed) :
    headers support.rows = [support.makeHeader.header, support.echoHeader.header, support.chooseHeader.header, support.selectHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.makeEq, support.echoEq, support.chooseEq, support.selectEq]

theorem ordinary_inventory (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow) :
    Nonempty (OrdinaryInventory fixture observed) := by
  obtain ⟨makeInput, echoInput, chooseInput, selectInput, makeRow, echoRow, chooseRow, selectRow, makePacket, echoPacket, choosePacket, selectPacket, makeHeader, echoHeader, chooseHeader, selectHeader, makeEq, echoEq, chooseEq, selectEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, echoInput, chooseInput, selectInput] :=
    .cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket (.nil))))
  have makeIndex : makeHeader.header.slot = observed.makeRow.index :=
    makeHeader.aligned.slot.trans (observed.makeRow.prepared_slot makeHeader.prepared).2
  have makeInputIndex : makeHeader.header.slot = makeInput.prepared.index := by
    rw [makeEq]; exact makePacket.aligned.slot
  have echoIndex : echoHeader.header.slot = observed.echoRow.index :=
    echoHeader.aligned.slot.trans (observed.echoRow.prepared_slot echoHeader.prepared).2
  have echoInputIndex : echoHeader.header.slot = echoInput.prepared.index := by
    rw [echoEq]; exact echoPacket.aligned.slot
  have chooseIndex : chooseHeader.header.slot = observed.chooseRow.index :=
    chooseHeader.aligned.slot.trans (observed.chooseRow.prepared_slot chooseHeader.prepared).2
  have chooseInputIndex : chooseHeader.header.slot = chooseInput.prepared.index := by
    rw [chooseEq]; exact choosePacket.aligned.slot
  have selectIndex : selectHeader.header.slot = observed.selectRow.index :=
    selectHeader.aligned.slot.trans (observed.selectRow.prepared_slot selectHeader.prepared).2
  have selectInputIndex : selectHeader.header.slot = selectInput.prepared.index := by
    rw [selectEq]; exact selectPacket.aligned.slot
  have makeEcho : makeHeader.header.slot ≠ echoHeader.header.slot := by
    rw [makeIndex, echoIndex]; exact observed.makeEcho
  have makeEchoInput : makeInput.prepared.index ≠ echoInput.prepared.index := by
    rw [← makeInputIndex, ← echoInputIndex]; exact makeEcho
  have makeChoose : makeHeader.header.slot ≠ chooseHeader.header.slot := by
    rw [makeIndex, chooseIndex]; exact observed.makeChoose
  have makeChooseInput : makeInput.prepared.index ≠ chooseInput.prepared.index := by
    rw [← makeInputIndex, ← chooseInputIndex]; exact makeChoose
  have makeSelect : makeHeader.header.slot ≠ selectHeader.header.slot := by
    rw [makeIndex, selectIndex]; exact observed.makeSelect
  have makeSelectInput : makeInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← makeInputIndex, ← selectInputIndex]; exact makeSelect
  have echoChoose : echoHeader.header.slot ≠ chooseHeader.header.slot := by
    rw [echoIndex, chooseIndex]; exact observed.echoChoose
  have echoChooseInput : echoInput.prepared.index ≠ chooseInput.prepared.index := by
    rw [← echoInputIndex, ← chooseInputIndex]; exact echoChoose
  have echoSelect : echoHeader.header.slot ≠ selectHeader.header.slot := by
    rw [echoIndex, selectIndex]; exact observed.echoSelect
  have echoSelectInput : echoInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← echoInputIndex, ← selectInputIndex]; exact echoSelect
  have chooseSelect : chooseHeader.header.slot ≠ selectHeader.header.slot := by
    rw [chooseIndex, selectIndex]; exact observed.chooseSelect
  have chooseSelectInput : chooseInput.prepared.index ≠ selectInput.prepared.index := by
    rw [← chooseInputIndex, ← selectInputIndex]; exact chooseSelect
  exact ⟨{
    makeInput := makeInput
    echoInput := echoInput
    chooseInput := chooseInput
    selectInput := selectInput
    makeRow := makeRow
    echoRow := echoRow
    chooseRow := chooseRow
    selectRow := selectRow
    makePacket := makePacket
    echoPacket := echoPacket
    choosePacket := choosePacket
    selectPacket := selectPacket
    makeHeader := makeHeader
    echoHeader := echoHeader
    chooseHeader := chooseHeader
    selectHeader := selectHeader
    makeEq := makeEq
    echoEq := echoEq
    chooseEq := chooseEq
    selectEq := selectEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [makeEchoInput, makeChooseInput, makeSelectInput, echoChooseInput, echoSelectInput, chooseSelectInput]
    makeDescriptor := makeHeader.descriptor makeStages
    echoDescriptor := echoHeader.descriptor echoStages
    chooseDescriptor := chooseHeader.descriptor chooseStages
    selectDescriptor := selectHeader.descriptor selectStages
  }⟩

end Tests.SourceCoreRecursiveIndex
