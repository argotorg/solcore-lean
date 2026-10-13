import Solcore.Test.SourceCoreEvidenceDirectFamily
import Solcore.Test.SourceCoreEvidenceDirectRootSupport
import Solcore.Test.SourceCoreEvidenceDirectLeafSupport
import Solcore.Test.SourceCoreEvidenceDirectSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedBodiesSupport
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreEvidenceDirect
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
  relayWordInput : Input fixture.recipe.compiled
  relayBoolInput : Input fixture.recipe.compiled
  chooseWordInput : Input fixture.recipe.compiled
  chooseBoolInput : Input fixture.recipe.compiled
  wordRow : wordInput.row = observed.wordRow.row
  boolRow : boolInput.row = observed.boolRow.row
  relayWordRow : relayWordInput.row = observed.relayWordRow.row
  relayBoolRow : relayBoolInput.row = observed.relayBoolRow.row
  chooseWordRow : chooseWordInput.row = observed.chooseWordRow.row
  chooseBoolRow : chooseBoolInput.row = observed.chooseBoolRow.row
  wordPacket : Issued wordInput
  boolPacket : Issued boolInput
  relayWordPacket : Issued relayWordInput
  relayBoolPacket : Issued relayBoolInput
  chooseWordPacket : Issued chooseWordInput
  chooseBoolPacket : Issued chooseBoolInput
  wordHeader : ActualHeader fixture observed.wordRow.row
  boolHeader : ActualHeader fixture observed.boolRow.row
  relayWordHeader : ActualHeader fixture observed.relayWordRow.row
  relayBoolHeader : ActualHeader fixture observed.relayBoolRow.row
  chooseWordHeader : ActualHeader fixture observed.chooseWordRow.row
  chooseBoolHeader : ActualHeader fixture observed.chooseBoolRow.row
  wordEq : wordHeader.header = wordPacket.header
  boolEq : boolHeader.header = boolPacket.header
  relayWordEq : relayWordHeader.header = relayWordPacket.header
  relayBoolEq : relayBoolHeader.header = relayBoolPacket.header
  chooseWordEq : chooseWordHeader.header = chooseWordPacket.header
  chooseBoolEq : chooseBoolHeader.header = chooseBoolPacket.header
  rows : Inventory [wordInput, boolInput, relayWordInput, relayBoolInput, chooseWordInput, chooseBoolInput]
  rowsEq : rows = (.cons wordPacket (.cons boolPacket (.cons relayWordPacket (.cons relayBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))
  complete : RecursiveNamedCatalogNativeContexts.Complete
    (values := .initial fixture.recipe.compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed) (headers rows)
  distinct : ([wordInput, boolInput, relayWordInput, relayBoolInput, chooseWordInput, chooseBoolInput].map (fun input => input.prepared.index)).Nodup
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
  relayWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayWordHeader.header.named.signature.key)
  relayBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named relayBoolHeader.header.named.signature.key)
  chooseWordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseWordHeader.header.named.signature.key)
  chooseBoolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named chooseBoolHeader.header.named.signature.key)

theorem StaticSupportPackage.header_list {fixture : CompiledFixture}
    {observed : ObservedProgram fixture} {registry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (support : StaticSupportPackage fixture observed registry completion) :
    headers support.rows = [support.wordHeader.header, support.boolHeader.header, support.relayWordHeader.header, support.relayBoolHeader.header, support.chooseWordHeader.header, support.chooseBoolHeader.header] := by
  rw [support.rowsEq]
  simp only [headers, support.wordEq, support.boolEq, support.relayWordEq, support.relayBoolEq, support.chooseWordEq, support.chooseBoolEq]

private def selectSix {compiled : SourceCoreUnifiedCompilation.Compiled}
    {word bool relayWord relayBool chooseWord chooseBool : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (wordBool : word.slot ≠ bool.slot)
    (wordRelayWord : word.slot ≠ relayWord.slot)
    (wordRelayBool : word.slot ≠ relayBool.slot)
    (wordChooseWord : word.slot ≠ chooseWord.slot)
    (wordChooseBool : word.slot ≠ chooseBool.slot)
    (boolRelayWord : bool.slot ≠ relayWord.slot)
    (boolRelayBool : bool.slot ≠ relayBool.slot)
    (boolChooseWord : bool.slot ≠ chooseWord.slot)
    (boolChooseBool : bool.slot ≠ chooseBool.slot)
    (relayWordRelayBool : relayWord.slot ≠ relayBool.slot)
    (relayWordChooseWord : relayWord.slot ≠ chooseWord.slot)
    (relayWordChooseBool : relayWord.slot ≠ chooseBool.slot)
    (relayBoolChooseWord : relayBool.slot ≠ chooseWord.slot)
    (relayBoolChooseBool : relayBool.slot ≠ chooseBool.slot)
    (chooseWordChooseBool : chooseWord.slot ≠ chooseBool.slot)
    (property : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → Type)
    (wordValue : property word)
    (boolValue : property bool)
    (relayWordValue : property relayWord)
    (relayBoolValue : property relayBool)
    (chooseWordValue : property chooseWord)
    (chooseBoolValue : property chooseBool)
    : ∀ header, header ∈ [word, bool, relayWord, relayBool, chooseWord, chooseBool] → property header := by
  intro header member
  if wordSlot : header.slot = word.slot then
    have same : header = word := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact same
      · exact False.elim (wordBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordRelayWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordRelayBool (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseWord (wordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (wordChooseBool (wordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ wordValue
  else if boolSlot : header.slot = bool.slot then
    have same : header = bool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (boolRelayWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolRelayBool (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseWord (boolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (boolChooseBool (boolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ boolValue
  else if relayWordSlot : header.slot = relayWord.slot then
    have same : header = relayWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (relayWordRelayBool (relayWordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (relayWordChooseWord (relayWordSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (relayWordChooseBool (relayWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ relayWordValue
  else if relayBoolSlot : header.slot = relayBool.slot then
    have same : header = relayBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (relayWordSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (relayBoolChooseWord (relayBoolSlot.symm.trans (congrArg (·.slot) same)))
      · exact False.elim (relayBoolChooseBool (relayBoolSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ relayBoolValue
  else if chooseWordSlot : header.slot = chooseWord.slot then
    have same : header = chooseWord := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (relayWordSlot (congrArg (·.slot) same))
      · exact False.elim (relayBoolSlot (congrArg (·.slot) same))
      · exact same
      · exact False.elim (chooseWordChooseBool (chooseWordSlot.symm.trans (congrArg (·.slot) same)))
    exact same.symm ▸ chooseWordValue
  else
    have same : header = chooseBool := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same | same
      · exact False.elim (wordSlot (congrArg (·.slot) same))
      · exact False.elim (boolSlot (congrArg (·.slot) same))
      · exact False.elim (relayWordSlot (congrArg (·.slot) same))
      · exact False.elim (relayBoolSlot (congrArg (·.slot) same))
      · exact False.elim (chooseWordSlot (congrArg (·.slot) same))
      · exact same
    exact same.symm ▸ chooseBoolValue

theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (relayWordStages : ObservedStages fixture observed.relayWordRow)
    (relayBoolStages : ObservedStages fixture observed.relayBoolRow)
    (chooseWordStages : ObservedStages fixture observed.chooseWordRow)
    (chooseBoolStages : ObservedStages fixture observed.chooseBoolRow)
    (registry : SourceCoreRawMetadata.Registry)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed registry completion) := by
  obtain ⟨wordInput, boolInput, relayWordInput, relayBoolInput, chooseWordInput, chooseBoolInput, wordRow, boolRow, relayWordRow, relayBoolRow, chooseWordRow, chooseBoolRow, wordPacket, boolPacket, relayWordPacket, relayBoolPacket, chooseWordPacket, chooseBoolPacket, wordHeader, boolHeader, relayWordHeader, relayBoolHeader, chooseWordHeader, chooseBoolHeader, wordEq, boolEq, relayWordEq, relayBoolEq, chooseWordEq, chooseBoolEq, complete⟩ := observed.inventory
  let rows : Inventory [wordInput, boolInput, relayWordInput, relayBoolInput, chooseWordInput, chooseBoolInput] := (.cons wordPacket (.cons boolPacket (.cons relayWordPacket (.cons relayBoolPacket (.cons chooseWordPacket (.cons chooseBoolPacket .nil))))))
  have headerList : headers rows = [wordHeader.header, boolHeader.header, relayWordHeader.header, relayBoolHeader.header, chooseWordHeader.header, chooseBoolHeader.header] := by
    simp only [rows, headers, wordEq, boolEq, relayWordEq, relayBoolEq, chooseWordEq, chooseBoolEq]
  have wordIndex : wordHeader.header.slot = observed.wordRow.index :=
    wordHeader.aligned.slot.trans (observed.wordRow.prepared_slot wordHeader.prepared).2
  have wordInputIndex : wordHeader.header.slot = wordInput.prepared.index := by
    rw [wordEq]; exact wordPacket.aligned.slot
  have boolIndex : boolHeader.header.slot = observed.boolRow.index :=
    boolHeader.aligned.slot.trans (observed.boolRow.prepared_slot boolHeader.prepared).2
  have boolInputIndex : boolHeader.header.slot = boolInput.prepared.index := by
    rw [boolEq]; exact boolPacket.aligned.slot
  have relayWordIndex : relayWordHeader.header.slot = observed.relayWordRow.index :=
    relayWordHeader.aligned.slot.trans (observed.relayWordRow.prepared_slot relayWordHeader.prepared).2
  have relayWordInputIndex : relayWordHeader.header.slot = relayWordInput.prepared.index := by
    rw [relayWordEq]; exact relayWordPacket.aligned.slot
  have relayBoolIndex : relayBoolHeader.header.slot = observed.relayBoolRow.index :=
    relayBoolHeader.aligned.slot.trans (observed.relayBoolRow.prepared_slot relayBoolHeader.prepared).2
  have relayBoolInputIndex : relayBoolHeader.header.slot = relayBoolInput.prepared.index := by
    rw [relayBoolEq]; exact relayBoolPacket.aligned.slot
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
  have wordRelayWord : wordHeader.header.slot ≠ relayWordHeader.header.slot := by
    rw [wordIndex, relayWordIndex]; exact observed.wordRelayWord
  have wordRelayWordInput : wordInput.prepared.index ≠ relayWordInput.prepared.index := by
    rw [← wordInputIndex, ← relayWordInputIndex]; exact wordRelayWord
  have wordRelayBool : wordHeader.header.slot ≠ relayBoolHeader.header.slot := by
    rw [wordIndex, relayBoolIndex]; exact observed.wordRelayBool
  have wordRelayBoolInput : wordInput.prepared.index ≠ relayBoolInput.prepared.index := by
    rw [← wordInputIndex, ← relayBoolInputIndex]; exact wordRelayBool
  have wordChooseWord : wordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [wordIndex, chooseWordIndex]; exact observed.wordChooseWord
  have wordChooseWordInput : wordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← wordInputIndex, ← chooseWordInputIndex]; exact wordChooseWord
  have wordChooseBool : wordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [wordIndex, chooseBoolIndex]; exact observed.wordChooseBool
  have wordChooseBoolInput : wordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← wordInputIndex, ← chooseBoolInputIndex]; exact wordChooseBool
  have boolRelayWord : boolHeader.header.slot ≠ relayWordHeader.header.slot := by
    rw [boolIndex, relayWordIndex]; exact observed.boolRelayWord
  have boolRelayWordInput : boolInput.prepared.index ≠ relayWordInput.prepared.index := by
    rw [← boolInputIndex, ← relayWordInputIndex]; exact boolRelayWord
  have boolRelayBool : boolHeader.header.slot ≠ relayBoolHeader.header.slot := by
    rw [boolIndex, relayBoolIndex]; exact observed.boolRelayBool
  have boolRelayBoolInput : boolInput.prepared.index ≠ relayBoolInput.prepared.index := by
    rw [← boolInputIndex, ← relayBoolInputIndex]; exact boolRelayBool
  have boolChooseWord : boolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [boolIndex, chooseWordIndex]; exact observed.boolChooseWord
  have boolChooseWordInput : boolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← boolInputIndex, ← chooseWordInputIndex]; exact boolChooseWord
  have boolChooseBool : boolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [boolIndex, chooseBoolIndex]; exact observed.boolChooseBool
  have boolChooseBoolInput : boolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← boolInputIndex, ← chooseBoolInputIndex]; exact boolChooseBool
  have relayWordRelayBool : relayWordHeader.header.slot ≠ relayBoolHeader.header.slot := by
    rw [relayWordIndex, relayBoolIndex]; exact observed.relayWordRelayBool
  have relayWordRelayBoolInput : relayWordInput.prepared.index ≠ relayBoolInput.prepared.index := by
    rw [← relayWordInputIndex, ← relayBoolInputIndex]; exact relayWordRelayBool
  have relayWordChooseWord : relayWordHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [relayWordIndex, chooseWordIndex]; exact observed.relayWordChooseWord
  have relayWordChooseWordInput : relayWordInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← relayWordInputIndex, ← chooseWordInputIndex]; exact relayWordChooseWord
  have relayWordChooseBool : relayWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [relayWordIndex, chooseBoolIndex]; exact observed.relayWordChooseBool
  have relayWordChooseBoolInput : relayWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← relayWordInputIndex, ← chooseBoolInputIndex]; exact relayWordChooseBool
  have relayBoolChooseWord : relayBoolHeader.header.slot ≠ chooseWordHeader.header.slot := by
    rw [relayBoolIndex, chooseWordIndex]; exact observed.relayBoolChooseWord
  have relayBoolChooseWordInput : relayBoolInput.prepared.index ≠ chooseWordInput.prepared.index := by
    rw [← relayBoolInputIndex, ← chooseWordInputIndex]; exact relayBoolChooseWord
  have relayBoolChooseBool : relayBoolHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [relayBoolIndex, chooseBoolIndex]; exact observed.relayBoolChooseBool
  have relayBoolChooseBoolInput : relayBoolInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← relayBoolInputIndex, ← chooseBoolInputIndex]; exact relayBoolChooseBool
  have chooseWordChooseBool : chooseWordHeader.header.slot ≠ chooseBoolHeader.header.slot := by
    rw [chooseWordIndex, chooseBoolIndex]; exact observed.chooseWordChooseBool
  have chooseWordChooseBoolInput : chooseWordInput.prepared.index ≠ chooseBoolInput.prepared.index := by
    rw [← chooseWordInputIndex, ← chooseBoolInputIndex]; exact chooseWordChooseBool
  obtain ⟨wordTerminal, _wordExpression, ⟨wordSupport⟩⟩ :=
    wordHeader.word_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨boolTerminal, _boolExpression, ⟨boolSupport⟩⟩ :=
    boolHeader.bool_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨relayWordTerminal, _relayWordExpression, ⟨relayWordSupport⟩⟩ :=
    relayWordHeader.relayWord_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨relayBoolTerminal, _relayBoolExpression, ⟨relayBoolSupport⟩⟩ :=
    relayBoolHeader.relayBool_support observed rows complete receiver (actualStagePrepared fixture)
  obtain ⟨chooseWordTerminal, _chooseWordExpression, ⟨chooseWordSupport⟩⟩ :=
    chooseWordHeader.chooseWord_support observed receiver (actualStagePrepared fixture)
  obtain ⟨chooseBoolTerminal, _chooseBoolExpression, ⟨chooseBoolSupport⟩⟩ :=
    chooseBoolHeader.chooseBool_support observed receiver (actualStagePrepared fixture)
  let property := fun header => Σ terminal : Body header,
    Support (headers rows) (CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
      registry header (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture)) terminal
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
  let choose : ∀ header, header ∈ headers rows → property header := fun header member =>
    selectSix wordBool wordRelayWord wordRelayBool wordChooseWord wordChooseBool boolRelayWord boolRelayBool boolChooseWord boolChooseBool relayWordRelayBool relayWordChooseWord relayWordChooseBool relayBoolChooseWord relayBoolChooseBool chooseWordChooseBool property
      ⟨of_terminal wordTerminal, .canonical wordSupport⟩ ⟨of_terminal boolTerminal, .canonical boolSupport⟩ ⟨of_terminal relayWordTerminal, .canonical relayWordSupport⟩ ⟨of_terminal relayBoolTerminal, .canonical relayBoolSupport⟩ ⟨of_terminal chooseWordTerminal, .recursive chooseWordSupport⟩ ⟨of_terminal chooseBoolTerminal, .recursive chooseBoolSupport⟩ header (headerList ▸ member)
  exact ⟨{
    wordInput := wordInput
    boolInput := boolInput
    relayWordInput := relayWordInput
    relayBoolInput := relayBoolInput
    chooseWordInput := chooseWordInput
    chooseBoolInput := chooseBoolInput
    wordRow := wordRow
    boolRow := boolRow
    relayWordRow := relayWordRow
    relayBoolRow := relayBoolRow
    chooseWordRow := chooseWordRow
    chooseBoolRow := chooseBoolRow
    wordPacket := wordPacket
    boolPacket := boolPacket
    relayWordPacket := relayWordPacket
    relayBoolPacket := relayBoolPacket
    chooseWordPacket := chooseWordPacket
    chooseBoolPacket := chooseBoolPacket
    wordHeader := wordHeader
    boolHeader := boolHeader
    relayWordHeader := relayWordHeader
    relayBoolHeader := relayBoolHeader
    chooseWordHeader := chooseWordHeader
    chooseBoolHeader := chooseBoolHeader
    wordEq := wordEq
    boolEq := boolEq
    relayWordEq := relayWordEq
    relayBoolEq := relayBoolEq
    chooseWordEq := chooseWordEq
    chooseBoolEq := chooseBoolEq
    rows := rows
    complete := complete
    rowsEq := rfl
    distinct := by simp [wordBoolInput, wordRelayWordInput, wordRelayBoolInput, wordChooseWordInput, wordChooseBoolInput, boolRelayWordInput, boolRelayBoolInput, boolChooseWordInput, boolChooseBoolInput, relayWordRelayBoolInput, relayWordChooseWordInput, relayWordChooseBoolInput, relayBoolChooseWordInput, relayBoolChooseBoolInput, chooseWordChooseBoolInput]
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    family := fun association => observed.family wordHeader boolHeader relayWordHeader relayBoolHeader chooseWordHeader chooseBoolHeader rows (actualStagePrepared fixture) association
    wordDescriptor := wordStages.descriptor_at wordHeader
    boolDescriptor := boolStages.descriptor_at boolHeader
    relayWordDescriptor := relayWordStages.descriptor_at relayWordHeader
    relayBoolDescriptor := relayBoolStages.descriptor_at relayBoolHeader
    chooseWordDescriptor := chooseWordStages.descriptor_at chooseWordHeader
    chooseBoolDescriptor := chooseBoolStages.descriptor_at chooseBoolHeader
  }⟩

end Tests.SourceCoreEvidenceDirect
