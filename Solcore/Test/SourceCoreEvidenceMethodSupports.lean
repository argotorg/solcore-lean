import Solcore.Test.SourceCoreEvidenceMethodOrdinarySupport
import Solcore.Test.SourceCoreEvidenceMethodSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreEvidenceMethod
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedPhysicalNamedTerminalSupport (Support)

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, viaWordInput, viaBoolInput].map (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers toOrdinaryInventory.rows → Terminal header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    Support (headers := headers toOrdinaryInventory.rows)
      (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (terminals header member)
  wordDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named wordHeader.header.named.signature.key)
  boolDescriptor : SourceCoreCallableContracts.Descriptor fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable.table
    (.named boolHeader.header.named.signature.key)

theorem OrdinaryInventory.indices {fixture observed} (given : OrdinaryInventory fixture observed) :
    given.wordInput.prepared.index = 5 ∧ given.boolInput.prepared.index = 4 ∧
      given.viaWordInput.prepared.index = 3 ∧ given.viaBoolInput.prepared.index = 2 := by
  have word : given.wordHeader.header.slot = given.wordInput.prepared.index := by
    rw [given.wordAligned]; exact given.wordPacket.aligned.slot
  have bool : given.boolHeader.header.slot = given.boolInput.prepared.index := by
    rw [given.boolAligned]; exact given.boolPacket.aligned.slot
  have viaWord : given.viaWordHeader.header.slot = given.viaWordInput.prepared.index := by
    rw [given.viaWordAligned]; exact given.viaWordPacket.aligned.slot
  have viaBool : given.viaBoolHeader.header.slot = given.viaBoolInput.prepared.index := by
    rw [given.viaBoolAligned]; exact given.viaBoolPacket.aligned.slot
  exact ⟨word.symm.trans (given.wordSlot.trans observed.wordIndex),
    bool.symm.trans (given.boolSlot.trans observed.boolIndex),
    viaWord.symm.trans (given.viaWordSlot.trans observed.viaWordIndex),
    viaBool.symm.trans (given.viaBoolSlot.trans observed.viaBoolIndex)⟩

/-- Four ordinary headers are issued at their real physical slots. The two
implementation slots are supplied by the separate method selection support. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (wordStages : ObservedStages fixture observed.wordRow.toObservedRow)
    (boolStages : ObservedStages fixture observed.boolRow.toObservedRow)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨wordTerminal, ⟨wordSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.wordRow.toObservedRow observed.wordShape observed.wordNodes observed.noLocals observed.word_supported
    given.wordHeader (by
      intro index signature target global
      rw [observed.wordInstantiation, observed.viaWordRow.target] at target
      have same := observed.viaWordRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.viaWordHeader.header, given.viaWord_member, given.viaWordSlot.trans same.2.symm,
        given.viaWordSignature.trans same.1.symm⟩)
  obtain ⟨boolTerminal, ⟨boolSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.boolRow.toObservedRow observed.boolShape observed.boolNodes observed.noLocals observed.bool_supported
    given.boolHeader (by
      intro index signature target global
      rw [observed.boolInstantiation, observed.viaBoolRow.target] at target
      have same := observed.viaBoolRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.viaBoolHeader.header, given.viaBool_member, given.viaBoolSlot.trans same.2.symm,
        given.viaBoolSignature.trans same.1.symm⟩)
  obtain ⟨viaWordTerminal, ⟨viaWordSupport⟩⟩ := ActualHeader.operator_support given.rows receiver methods
    observed.viaWordRow observed.viaWordShape observed.viaWordNodes observed.noLocals given.viaWordHeader
  obtain ⟨viaBoolTerminal, ⟨viaBoolSupport⟩⟩ := ActualHeader.operator_support given.rows receiver methods
    observed.viaBoolRow observed.viaBoolShape observed.viaBoolNodes observed.noLocals given.viaBoolHeader
  let property := fun header => Σ terminal : Terminal header,
    Support (headers := headers given.rows)
      (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header terminal
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨⟨wordTerminal, wordSupport⟩⟩
    · exact ⟨⟨boolTerminal, boolSupport⟩⟩
    · exact ⟨⟨viaWordTerminal, viaWordSupport⟩⟩
    · exact ⟨⟨viaBoolTerminal, viaBoolSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by simp only [List.map_cons, List.map_nil, given.indices.1, given.indices.2.1,
      given.indices.2.2.1, given.indices.2.2.2]; decide
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
    wordDescriptor := by rw [given.wordSignature, observed.wordRow.globalKey]; exact wordStages.descriptor
    boolDescriptor := by rw [given.boolSignature, observed.boolRow.globalKey]; exact boolStages.descriptor
  }⟩

end Tests.SourceCoreEvidenceMethod
