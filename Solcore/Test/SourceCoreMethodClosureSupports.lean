import Solcore.Test.SourceCoreMethodClosureOrdinarySupport
import Solcore.Test.SourceCoreMethodClosureFactorySupport
import Solcore.Test.SourceCoreMethodClosureSelection
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreMethodClosure
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedFiniteNamedInventories (headers)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)

abbrev NamedSupport {compiled : SourceCoreUnifiedCompilation.Compiled}
    (catalog : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (stages : Staging.Recursive.Registry)
    (faults : FunctionCalls.FaultRep)
    (header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (terminal : Terminal header) :=
  Sum (CallableIndexedOwnedPreparedStagedPhysicalMixedNamedTerminalSupport.Support
    (headers := catalog) (stages := stages) (semanticFaults := faults) header terminal)
    ({ _support : CallableIndexedOwnedPreparedStagedPhysicalNamedFormationSupport.Support
      (bodyRegistry := registry) (stages := stages) (semanticFaults := faults) header terminal //
      header.globals = compiled.indexed.base.globals.length })

structure StaticSupportPackage (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed)
    extends OrdinaryInventory fixture observed where
  distinct : ([wordInput, boolInput, makeWordInput, makeBoolInput, useWordInput, useBoolInput].map
    (fun input => input.prepared.index)).Nodup
  terminals : ∀ header, header ∈ headers toOrdinaryInventory.rows → Terminal header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    NamedSupport (headers toOrdinaryInventory.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (terminals header member)

/-- The six genuine ordinary rows retain their different compiler branches.
Implementation rows remain in the separate physical method inventory. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (factories : ObservedFactories fixture observed)
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
  obtain ⟨useWordTerminal, ⟨useWordSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useWordRow.toObservedRow observed.useWordShape observed.useWordNodes observed.noLocals given.useWordHeader
  obtain ⟨useBoolTerminal, ⟨useBoolSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useBoolRow.toObservedRow observed.useBoolShape observed.useBoolNodes observed.noLocals given.useBoolHeader
  let property := fun header => Σ terminal : Terminal header,
    NamedSupport (headers given.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header terminal
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨⟨wordTerminal, .inl wordSupport⟩⟩
    · exact ⟨⟨boolTerminal, .inl boolSupport⟩⟩
    · exact ⟨⟨makeWordTerminal, .inr ⟨makeWordSupport, given.makeWordHeader.aligned.globals⟩⟩⟩
    · exact ⟨⟨makeBoolTerminal, .inr ⟨makeBoolSupport, given.makeBoolHeader.aligned.globals⟩⟩⟩
    · exact ⟨⟨useWordTerminal, .inl useWordSupport⟩⟩
    · exact ⟨⟨useBoolTerminal, .inl useBoolSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by rw [given.indices]; exact observed.ordinarySlotsDistinct
    terminals := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
  }⟩

end Tests.SourceCoreMethodClosure
