import Solcore.Test.SourceCoreMethodOriginEvidenceOrdinarySupport
import Solcore.Test.SourceCoreMethodOriginEvidenceFactorySupport
import Solcore.Test.SourceCoreMethodOriginEvidenceSelection
import Solcore.Test.SourceCoreMethodOriginEvidenceRelaySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodOriginEvidence
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body of_terminal)

abbrev NamedSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (stages : Staging.Recursive.Registry)
    (faults : FunctionCalls.FaultRep)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (body : Body header) :=
  CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
    (headers := catalog) (bodyRegistry := registry) (stages := stages)
    (semanticFaults := faults) header body

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, makeWordInput, makeBoolInput, relayWordInput, relayBoolInput, useWordInput, useBoolInput, identityWordInput, identityBoolInput].map
    (fun input => input.prepared.index)).Nodup
  bodies : ∀ header, header ∈ headers toOrdinaryInventory.rows → Body header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    NamedSupport (headers toOrdinaryInventory.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (bodies header member)

/-- The ten genuine ordinary rows retain their different compiler branches.
Implementation rows remain in the separate physical method inventory. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (factories : ObservedFactories fixture observed)
    (methods : CallableIndexedOwnedPreparedStagedOriginsMethodSelection.Catalog fixture.recipe.compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨wordTerminal, ⟨wordSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.wordRow.toObservedRow observed.wordShape observed.wordNodes observed.noLocals observed.word_supported
    given.wordHeader (by
      intro index signature target global
      rw [observed.wordInstantiation, observed.makeWordRow.target] at target
      have same := observed.makeWordRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.makeWordHeader.header, given.makeWord_member, given.makeWordSlot.trans same.2.symm,
        given.makeWordSignature.trans same.1.symm⟩)
  obtain ⟨boolTerminal, ⟨boolSupport⟩⟩ := ActualHeader.direct_support given.rows receiver methods
    observed.boolRow.toObservedRow observed.boolShape observed.boolNodes observed.noLocals observed.bool_supported
    given.boolHeader (by
      intro index signature target global
      rw [observed.boolInstantiation, observed.makeBoolRow.target] at target
      have same := observed.makeBoolRow.global_slot global (Except.ok.inj target).symm
      exact ⟨given.makeBoolHeader.header, given.makeBool_member, given.makeBoolSlot.trans same.2.symm,
        given.makeBoolSignature.trans same.1.symm⟩)
  obtain ⟨makeWordTerminal, ⟨makeWordSupport⟩⟩ := ActualHeader.factory_support observed
    observed.makeWordRow observed.makeWordShape factories.word given.makeWordHeader
    (registry := completion.result.context.registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
    (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
  obtain ⟨makeBoolTerminal, ⟨makeBoolSupport⟩⟩ := ActualHeader.factory_support observed
    observed.makeBoolRow observed.makeBoolShape factories.bool given.makeBoolHeader
    (registry := completion.result.context.registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
    (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
  obtain ⟨⟨relayWordBody, relayWordSupport⟩⟩ := given.relayWordHeader.relayWord_support
    observed given.rows receiver methods (actualStagePrepared fixture)
  obtain ⟨⟨relayBoolBody, relayBoolSupport⟩⟩ := given.relayBoolHeader.relayBool_support
    observed given.rows receiver methods (actualStagePrepared fixture)
  obtain ⟨useWordTerminal, ⟨useWordSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useWordRow.toObservedRow observed.useWordShape observed.useWordNodes observed.noLocals given.useWordHeader
  obtain ⟨useBoolTerminal, ⟨useBoolSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useBoolRow.toObservedRow observed.useBoolShape observed.useBoolNodes observed.noLocals given.useBoolHeader
  obtain ⟨identityWordTerminal, ⟨identityWordSupport⟩⟩ := ActualHeader.identity_support given.rows receiver methods
    observed.identityWordRow observed.identityWordShape observed.identityWordNodes observed.noLocals given.identityWordHeader
  obtain ⟨identityBoolTerminal, ⟨identityBoolSupport⟩⟩ := ActualHeader.identity_support given.rows receiver methods
    observed.identityBoolRow observed.identityBoolShape observed.identityBoolNodes observed.noLocals given.identityBoolHeader
  let property := fun header => Σ body : Body header,
    NamedSupport (headers given.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header body
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨of_terminal wordTerminal, .terminal wordTerminal wordSupport⟩⟩
    · exact ⟨⟨of_terminal boolTerminal, .terminal boolTerminal boolSupport⟩⟩
    · exact ⟨⟨of_terminal makeWordTerminal, .formation makeWordTerminal makeWordSupport given.makeWordHeader.aligned.globals⟩⟩
    · exact ⟨⟨of_terminal makeBoolTerminal, .formation makeBoolTerminal makeBoolSupport given.makeBoolHeader.aligned.globals⟩⟩
    · exact ⟨⟨relayWordBody, relayWordSupport⟩⟩
    · exact ⟨⟨relayBoolBody, relayBoolSupport⟩⟩
    · exact ⟨⟨of_terminal useWordTerminal, .terminal useWordTerminal useWordSupport⟩⟩
    · exact ⟨⟨of_terminal useBoolTerminal, .terminal useBoolTerminal useBoolSupport⟩⟩
    · exact ⟨⟨of_terminal identityWordTerminal, .terminal identityWordTerminal identityWordSupport⟩⟩
    · exact ⟨⟨of_terminal identityBoolTerminal, .terminal identityBoolTerminal identityBoolSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by rw [given.indices]; exact observed.ordinarySlotsDistinct
    bodies := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
  }⟩

end Tests.SourceCoreMethodOriginEvidence
