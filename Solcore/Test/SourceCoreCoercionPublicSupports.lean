import Solcore.Test.SourceCoreCoercionPublicOrdinarySupport
import Solcore.Test.SourceCoreCoercionPublicFactorySupport
import Solcore.Test.SourceCoreCoercionPublicSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreCoercionPublic
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
  distinct : ([makeInput, useInput, keepInput].map
    (fun input => input.prepared.index)).Nodup
  bodies : ∀ header, header ∈ headers toOrdinaryInventory.rows → Body header
  supports : ∀ header, ∀ member : header ∈ headers toOrdinaryInventory.rows,
    NamedSupport (headers toOrdinaryInventory.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header (bodies header member)

/-- The factory, indirect caller and evidence-bearing identity each retain
an authentic ordinary header. The coercion method stays in the physical cache. -/
theorem static_supports (fixture : CompiledFixture) (observed : ObservedProgram fixture)
    (factories : ObservedFactories fixture observed)
    (methods : CallableIndexedOwnedPreparedStagedClosedCoercionSelection.Catalog fixture.recipe.compiled)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics) :
    Nonempty (StaticSupportPackage fixture observed completion) := by
  obtain ⟨given⟩ := ordinary_inventory fixture observed
  obtain ⟨makeTerminal, ⟨makeSupport⟩⟩ := ActualHeader.factory_support observed
    observed.makeRow.toObservedRow observed.makeShape factories.make given.makeHeader
    (registry := completion.result.context.registry)
    (faults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
    (stages := RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
  obtain ⟨useTerminal, ⟨useSupport⟩⟩ := ActualHeader.use_support given.rows receiver methods
    observed.useRow.toObservedRow observed.useShape observed.useNodes observed.noLocals given.useHeader
  obtain ⟨keepTerminal, ⟨keepSupport⟩⟩ := ActualHeader.identity_support given.rows receiver methods
    observed.keepRow observed.keepShape observed.keepNodes observed.noLocals given.keepHeader
  let property := fun header => Σ body : Body header,
    NamedSupport (headers given.rows) completion.result.context.registry
      (RecursiveNamedPreparedStageScopes.registry (actualStagePrepared fixture))
      (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
      header body
  have present : ∀ header, header ∈ headers given.rows → Nonempty (property header) := by
    intro header member
    rw [given.header_list] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact ⟨⟨of_terminal makeTerminal, .formation makeTerminal makeSupport given.makeHeader.aligned.globals⟩⟩
    · exact ⟨⟨of_terminal useTerminal, .terminal useTerminal useSupport⟩⟩
    · exact ⟨⟨of_terminal keepTerminal, .terminal keepTerminal keepSupport⟩⟩
  let choose := fun header member => Classical.choice (present header member)
  exact ⟨{
    toOrdinaryInventory := given
    distinct := by rw [given.indices]; exact observed.ordinarySlotsDistinct
    bodies := fun header member => (choose header member).1
    supports := fun header member => (choose header member).2
  }⟩

end Tests.SourceCoreCoercionPublic
