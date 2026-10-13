import Solcore.Test.SourceCoreGenericDirectMetadata
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport
set_option autoImplicit false
set_option Elab.async false
namespace Tests.SourceCoreGenericDirect
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Ordinary)

/-- The original nonempty instantiation remains attached to the actual
terminal callback and the complete inventory that issued its selected callee. -/
theorem ActualHeader.root_support {fixture : CompiledFixture}
    {signature generic : ProgramFunctionSignature}
    {firstParameter secondParameter : TypeSystem.TypeParameterId}
    {firstType secondType : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : RootShape row.row.function signature generic firstParameter secondParameter firstType secondType)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (ordinary : Ordinary fixture.recipe.compiled.indexed.base.plan shape.call.instantiation)
    (actual : ActualHeader fixture row.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = shape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) := by
  obtain ⟨terminal, diagnostic, expression, point⟩ := actual.terminal shape.call.value.node.id
    shape.statement shape.roots shape.statementFound shape.statementForm
  have same : terminal.prepared.named.specialized = row.row :=
    (congrArg (·.specialized) (terminal.aligned.named.symm.trans actual.aligned.named)).trans actual.prepared.same
  have metadata : CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.NativeMetadataFor
      fixture.recipe.compiled.indexed terminal.prepared.named actual.header.function.source
      (Ordinary fixture.recipe.compiled.indexed.base.plan) := by
    rw [actual.source]
    exact .of_ordinary (shape.metadata nodes terminal.prepared.named noLocals (by rw [same]; exact row.assumptions))
  exact ⟨terminal, expression,
    CallableIndexedOwnedPreparedStagedNamedCanonicalTerminalSupport.of_actual_native_sites
      terminal diagnostic receiver fixture.source_wellFormed (fun _ witness => witness) metadata
      (by rw [expression, actual.source]; exact shape.syntax ordinary)
      rows complete (bootstrap_zero fixture.recipe.compiled) stagePrepared point⟩

theorem ActualHeader.word_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.wordRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.wordShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.wordRow.toObservedRow observed.wordShape observed.wordNodes
    observed.noLocals observed.word_ordinary rows complete receiver stagePrepared

theorem ActualHeader.bool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.boolRow.row)
    {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input fixture.recipe.compiled)}
    (rows : CallableIndexedOwnedPreparedFiniteNamedInventories.Inventory inputs)
    (complete : RecursiveNamedCatalogNativeContexts.Complete
      (values := .initial fixture.recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions fixture.recipe.compiled.indexed)
      (CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows))
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    ∃ terminal : CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch.Terminal actual.header,
      terminal.expression = observed.boolShape.call.value.node.id ∧
      Nonempty (CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.NamedSupport
        (headers := CallableIndexedOwnedPreparedFiniteNamedInventories.headers rows)
        (keys := CallableIndexedOwnedPreparedBootstrapRootState.keys fixture.recipe.compiled)
        (RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header terminal) :=
  actual.root_support observed.boolRow.toObservedRow observed.boolShape observed.boolNodes
    observed.noLocals observed.bool_ordinary rows complete receiver stagePrepared

end Tests.SourceCoreGenericDirect
