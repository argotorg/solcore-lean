import Solcore.Test.SourceCoreGenericDirectFamily
import Solcore.Test.SourceCoreGenericDirectRootSupport
import Solcore.Test.SourceCoreGenericDirectLeafSupport
import Solcore.Test.SourceCoreGenericDirectSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)
open CallableIndexedOwnedPreparedStagedNamedBodiesSupport (Support)

theorem actualStagePrepared (fixture : CompiledFixture) :
    RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable :=
  RecursiveNamedPreparedStageContracts.of_compiled fixture.recipe.compiled
    fixture.recipe.compiled.indexed.ancestry.graph.inputs.callableSelected

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (registry : SourceCoreRawMetadata.Registry)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed) where
  wordInput : Input fixture.recipe.compiled
  boolInput : Input fixture.recipe.compiled
  chooseWordInput : Input fixture.recipe.compiled
  chooseBoolInput : Input fixture.recipe.compiled
  wordRow : wordInput.row = observed.wordRow.row
  boolRow : boolInput.row = observed.boolRow.row
  chooseWordRow : chooseWordInput.row = observed.chooseWordRow.row
  chooseBoolRow : chooseBoolInput.row = observed.chooseBoolRow.row
  wordPacket : Issued wordInput
  boolPacket : Issued boolInput
  chooseWordPacket : Issued chooseWordInput
  chooseBoolPacket : Issued chooseBoolInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  boolHeader : ActualHeader fixture observed.boolRow.row
  chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row
  chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row
  wordEq : wordHeader.header = wordPacket.header
  boolEq : boolHeader.header = boolPacket.header
  chooseWordEq : chooseWordHeader.header = chooseWordPacket.header
  chooseBoolEq : chooseBoolHeader.header = chooseBoolPacket.header
  rows : Inventory [wordInput, boolInput, chooseWordInput, chooseBoolInput]
  rowsEq : rows = (.cons wordPacket (.cons boolPacket (.cons chooseWordPacket (.cons chooseBoolPacket  .nil))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([wordInput, boolInput, chooseWordInput, chooseBoolInput].map (fun input => input.prepared.index)).Nodup
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
  wordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named wordHeader.header.named.signature.key)
  boolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named boolHeader.header.named.signature.key)
  chooseWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseWordHeader.header.named.signature.key)
  chooseBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseBoolHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.wordHeader.header, support.boolHeader.header, support.chooseWordHeader.header, support.chooseBoolHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.wordEq, support.boolEq, support.chooseWordEq, support.chooseBoolEq]

private def selectFour {compiled : SourceCoreUnifiedCompilation.Compiled}
    {word bool chooseWord chooseBool : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (wordBool : word.slot ≠ bool.slot)
    (wordChooseWord : word.slot ≠ chooseWord.slot)
    (wordChooseBool : word.slot ≠ chooseBool.slot)
    (boolChooseWord : bool.slot ≠ chooseWord.slot)
    (boolChooseBool : bool.slot ≠ chooseBool.slot)
    (chooseWordChooseBool : chooseWord.slot ≠ chooseBool.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (wordValue : property word)
    (boolValue : property bool)
    (chooseWordValue : property chooseWord)
    (chooseBoolValue : property chooseBool)
    : ∀ header, header ∈ [word, bool, chooseWord, chooseBool] → property header := by
  intro header member
  if wordSlot : header.slot = word.slot then
    have same : header = word := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact same
      · exact False.elim (wordBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseBool (wordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ wordValue
  else if boolSlot : header.slot = bool.slot then
    have same : header = bool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (boolChooseWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseBool (boolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ boolValue
  else if chooseWordSlot : header.slot = chooseWord.slot then
    have same : header = chooseWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (chooseWordChooseBool (chooseWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ chooseWordValue
  else
    have same : header = chooseBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (chooseWordSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ chooseBoolValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨wordInput, boolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, chooseWordEq, chooseBoolEq, complete⟩ := observed.inventory
  let rows : Inventory [wordInput, boolInput, chooseWordInput, chooseBoolInput] := (.cons wordPacket (.cons boolPacket (.cons chooseWordPacket (.cons chooseBoolPacket  .nil))))
  have headerList : headers rows = [wordHeader.header, boolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := by
    simp only [rows, headers, wordEq, boolEq, chooseWordEq, chooseBoolEq]
  have wordIndex : wordHeader.header.slot = observed.wordRow.index :=
    wordHeader.aligned.slot.trans (observed.wordRow.prepared_slot wordHeader.prepared).2
  have wordInputIndex : wordHeader.header.slot = wordInput.prepared.index := by
    rw [wordEq]; exact wordPacket.aligned.slot
  have boolIndex : boolHeader.header.slot = observed.boolRow.index :=
    boolHeader.aligned.slot.trans (observed.boolRow.prepared_slot boolHeader.prepared).2
  have boolInputIndex : boolHeader.header.slot = boolInput.prepared.index := by
    rw [boolEq]; exact boolPacket.aligned.slot
  have chooseWordIndex : chooseWordHeader.header.slot = observed.chooseWordRow.index :=
    chooseWordHeader.aligned.slot.trans (observed.chooseWordRow.prepared_slot chooseWordHeader.prepared).2
  have chooseWordInputIndex : chooseWordHeader.header.slot = chooseWordInput.prepared.index := by
    rw [chooseWordEq]; exact chooseWordPacket.aligned.slot
  have chooseBoolIndex : chooseBoolHeader.header.slot = observed.chooseBoolRow.index :=
    chooseBoolHeader.aligned.slot.trans (observed.chooseBoolRow.prepared_slot chooseBoolHeader.prepared).2
  have chooseBoolInputIndex : chooseBoolHeader.header.slot = chooseBoolInput.prepared.index := by
    rw [chooseBoolEq]; exact chooseBoolPacket.aligned.slot
  have wordBool : wordHeader.header.slot ≠ boolHeader.header.slot := by
    rw [wordIndex, boolIndex]; exact observed.wordBool
  have wordBoolInput : wordInput.prepared.index ≠ boolInput.prepared.index := by
    rw [← wordInputIndex, ← boolInputIndex]; exact wordBool
  have wordChooseWord : wordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [wordIndex, chooseWordIndex]; exact observed.wordChooseWord
  have wordChooseWordInput : wordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← wordInputIndex, ← chooseWordInputIndex]; exact wordChooseWord
  have wordChooseBool : wordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [wordIndex, chooseBoolIndex]; exact observed.wordChooseBool
  have wordChooseBoolInput : wordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← wordInputIndex, ← chooseBoolInputIndex]; exact wordChooseBool
  have boolChooseWord : boolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [boolIndex, chooseWordIndex]; exact observed.boolChooseWord
  have boolChooseWordInput : boolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← boolInputIndex, ← chooseWordInputIndex]; exact boolChooseWord
  have boolChooseBool : boolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [boolIndex, chooseBoolIndex]; exact observed.boolChooseBool
  have boolChooseBoolInput : boolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← boolInputIndex, ← chooseBoolInputIndex]; exact boolChooseBool
  have chooseWordChooseBool : chooseWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [chooseWordIndex, chooseBoolIndex]; exact observed.chooseWordChooseBool
  have chooseWordChooseBoolInput : chooseWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← chooseWordInputIndex, ← chooseBoolInputIndex]; exact chooseWordChooseBool
  obtain ⟨wordTerminal, _wordExpression, ⟨wordSupport⟩⟩ :=
    wordHeader.word_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨boolTerminal, _boolExpression, ⟨boolSupport⟩⟩ :=
    boolHeader.bool_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨chooseWordTerminal, _chooseWordExpression, ⟨chooseWordSupport⟩⟩ :=
    chooseWordHeader.chooseWord_support observed receiver (actualStagePrepared fixture)
  obtain ⟨chooseBoolTerminal, _chooseBoolExpression, ⟨chooseBoolSupport⟩⟩ :=
    chooseBoolHeader.chooseBool_support observed receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectFour wordBool wordChooseWord wordChooseBool boolChooseWord boolChooseBool chooseWordChooseBool property
      ⟨of_terminal wordTerminal, .canonical wordSupport⟩ ⟨of_terminal boolTerminal, .canonical boolSupport⟩ ⟨of_terminal chooseWordTerminal, .recursive chooseWordSupport⟩ ⟨of_terminal chooseBoolTerminal, .recursive chooseBoolSupport⟩ header (headerList ▸ member)
  exact ⟨{
    wordInput := wordInput
    boolInput := boolInput
    chooseWordInput := chooseWordInput
    chooseBoolInput := chooseBoolInput
    wordRow := wordRow
    boolRow := boolRow
    chooseWordRow := chooseWordRow
    chooseBoolRow := chooseBoolRow
    wordPacket := wordPacket
    boolPacket := boolPacket
    chooseWordPacket := chooseWordPacket
    chooseBoolPacket := chooseBoolPacket
    wordHeader := wordHeader
    boolHeader := boolHeader
    chooseWordHeader := chooseWordHeader
    chooseBoolHeader := chooseBoolHeader
    wordEq := wordEq
    boolEq := boolEq
    chooseWordEq := chooseWordEq
    chooseBoolEq := chooseBoolEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [wordBoolInput, wordChooseWordInput, wordChooseBoolInput, boolChooseWordInput, boolChooseBoolInput, chooseWordChooseBoolInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family wordHeader boolHeader chooseWordHeader chooseBoolHeader rows (actualStagePrepared fixture) association
    wordDescriptor := wordStages.descriptor_at wordHeader
    boolDescriptor := boolStages.descriptor_at boolHeader
    chooseWordDescriptor := chooseWordStages.descriptor_at chooseWordHeader
    chooseBoolDescriptor := chooseBoolStages.descriptor_at chooseBoolHeader }⟩

end Tests.SourceCoreGenericDirect
