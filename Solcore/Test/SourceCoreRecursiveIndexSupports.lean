import Solcore.Test.SourceCoreRecursiveIndexMakeSupport
import Solcore.Test.SourceCoreRecursiveIndexLeafSupport
import Solcore.Test.SourceCoreRecursiveIndexSelectSupport
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

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
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
  terminals : ∀ header, header ∈ headers rows → Terminal header
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
  makeDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named makeHeader.header.named.signature.key)
  echoDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named echoHeader.header.named.signature.key)
  chooseDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseHeader.header.named.signature.key)
  selectDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named selectHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.makeHeader.header, support.echoHeader.header, support.chooseHeader.header, support.selectHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.makeEq, support.echoEq, support.chooseEq, support.selectEq]

private def selectFour {compiled : SourceCoreUnifiedCompilation.Compiled}
    {first second third fourth : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (firstSecond : first.slot ≠ second.slot) (firstThird : first.slot ≠ third.slot)
    (firstFourth : first.slot ≠ fourth.slot) (secondThird : second.slot ≠ third.slot)
    (secondFourth : second.slot ≠ fourth.slot) (thirdFourth : third.slot ≠ fourth.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (firstValue : property first) (secondValue : property second)
    (thirdValue : property third) (fourthValue : property fourth) :
    ∀ header, header ∈ [first, second, third, fourth] → property header := by
  intro header member
  if firstSlot : header.slot = first.slot then
    have same : header = first := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (firstSecond (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstThird (firstSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (firstFourth (firstSlot.symm.trans other))
    exact same.symm ▸ firstValue
  else if secondSlot : header.slot = second.slot then
    have same : header = second := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (secondThird (secondSlot.symm.trans other))
      · have other := congrArg (·.slot) same
        exact False.elim (secondFourth (secondSlot.symm.trans other))
    exact same.symm ▸ secondValue
  else if thirdSlot : header.slot = third.slot then
    have same : header = third := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact same
      · have other := congrArg (·.slot) same
        exact False.elim (thirdFourth (thirdSlot.symm.trans other))
    exact same.symm ▸ thirdValue
  else
    have same : header = fourth := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (firstSlot (congrArg (·.slot) same))
      · exact False.elim (secondSlot (congrArg (·.slot) same))
      · exact False.elim (thirdSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ fourthValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (extra : ObservedMake fixture observed)
    (makeStages : ObservedStages fixture observed.makeRow)
    (echoStages : ObservedStages fixture observed.echoRow)
    (chooseStages : ObservedStages fixture observed.chooseRow)
    (selectStages : ObservedStages fixture observed.selectRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨makeInput, echoInput, chooseInput, selectInput, makeRow, echoRow, chooseRow, selectRow, makePacket, echoPacket, choosePacket, selectPacket, makeHeader, echoHeader, chooseHeader, selectHeader, makeEq, echoEq, chooseEq, selectEq, complete⟩ := observed.inventory
  let rows : Inventory [makeInput, echoInput, chooseInput, selectInput] :=
    .cons makePacket (.cons echoPacket (.cons choosePacket (.cons selectPacket (.nil))))
  have headerList : headers rows = [makeHeader.header, echoHeader.header, chooseHeader.header, selectHeader.header] := by
    simp only [rows, headers, makeEq, echoEq, chooseEq, selectEq]
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
  obtain ⟨makeTerminal, makeDiagnostic, makeExpression, makePoint⟩ := makeHeader.terminal
    observed.makeShape.expression.id observed.makeShape.statement observed.makeShape.roots
    observed.makeShape.statementFound observed.makeShape.returnStatement
  obtain ⟨makeSupport⟩ := makeHeader.make_support extra makeStages (headers rows) complete
    makeTerminal makeDiagnostic makeExpression makePoint (registry := registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  obtain ⟨echoTerminal, _echoExpression, echoSupport⟩ :=
    echoHeader.echo_support observed receiver (actualStagePrepared fixture)
  obtain ⟨echoSupport⟩ := echoSupport
  obtain ⟨chooseTerminal, _chooseExpression, chooseSupport⟩ :=
    chooseHeader.choose_support observed receiver (actualStagePrepared fixture)
  obtain ⟨chooseSupport⟩ := chooseSupport
  obtain ⟨selectTerminal, _selectExpression, selectSupport⟩ :=
    selectHeader.select_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨selectSupport⟩ := selectSupport
  let property := fun header => Σ terminal : Terminal header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let chooseSupport : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectFour makeEcho makeChoose makeSelect echoChoose echoSelect chooseSelect property
      ⟨makeTerminal, makeSupport⟩ ⟨echoTerminal, .recursive echoSupport⟩
      ⟨chooseTerminal, .recursive chooseSupport⟩ ⟨selectTerminal, .canonical selectSupport⟩ header (headerList ▸ member)
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
    terminals := fun header member => (chooseSupport header member).1
    supports := fun header member => (chooseSupport header member).2
    family := fun association => observed.family makeHeader echoHeader chooseHeader selectHeader (actualStagePrepared fixture) receiver association
    makeDescriptor := makeHeader.descriptor makeStages
    echoDescriptor := echoHeader.descriptor echoStages
    chooseDescriptor := chooseHeader.descriptor chooseStages
    selectDescriptor := selectHeader.descriptor selectStages
  }⟩

end Tests.SourceCoreRecursiveIndex
