import Solcore.Test.SourceCoreMethodNamedScopedRelaySyntax
import Solcore.Test.SourceCoreMethodNamedScopedCatalog
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport

/-! The actual selected relay Header supplies Source typing and the accepted
scoped compiler action. Three trait sites keep their original requirement IDs
and complete caller dictionary after local initialization and loop assignment. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Tests.SourceCoreMethodNamedScoped
open Solcore Frontend SourceInference SourceSemantics CoreLowering
open CallableIndexedOwnedPreparedStagedNamedBranchingReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedPhysicalMixedNamedScopedStaticSupport (Support)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Inventory headers)

/-- The receiver and real cached Header determine all static body children. -/
theorem ActualHeader.scoped_receipt {fixture : CompiledFixture}
    {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (resultType : row.row.function.inferredBodyType = type)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) := by
  have bodyEq : actual.header.function.body = shape.body := by
    rw [actual.aligned.function]
    have accepted := actual.prepared.compilation.roots
    change (actual.prepared.named.specialized.function.typedBody.roots.mapM _) = _ at accepted
    rw [actual.prepared.same, shape.roots] at accepted
    exact (Except.ok.inj accepted).symm
  have resultEq : actual.header.function.resultType = type := by
    rw [actual.header.agreement.result, actual.aligned.named, actual.prepared.same]
    exact resultType
  have syntaxTree : GenericImperativeMatch.Syntax actual.header.function.source
      (fun id => CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates.GeneralSyntax
        actual.header.function.source id (fun _ => False))
      actual.header.context (.statements true actual.header.function.body) actual.header.function.resultType := by
    obtain ⟨facts, finalContext, typed, _roots, _complete⟩ := actual.aligned.bodyTyped
    rw [actual.source, shape.roots, resultEq] at typed
    simp only [List.filterMap_cons, List.filterMap_nil] at typed
    rw [actual.source, bodyEq, resultEq]
    exact shape.body_syntax nodes (actual.source ▸ actual.header.unique) shape.children typed
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedNamedBranchingReceipts.of_accepted
    actual.aligned.accepted (by rw [actual.source, bodyEq]; exact shape.body_shape) actual.aligned.projection
  obtain ⟨loaded, checked⟩ := fixture.loaded
  have checked := CallableMethodBodyCoherence.of_loaded checked
  refine ⟨receipt, ?_⟩
  apply CallableIndexedOwnedPreparedNamedPhysicalMixedScopedCollectors.of_actual actual.prepared actual.aligned
    fixture.recipePrepared actual.diagnostic receiver fixture.source_wellFormed
    (fun _ impossible => False.elim impossible) _ rows
    (fun _ impossible => False.elim impossible) checked _ methods entryMember receipt stagePrepared syntaxTree.prepared
  · rw [actual.source]
    exact shape.metadata nodes actual.prepared.named noLocals
  · rw [fixture.sameProgram]
    exact CallableCoercionSelectionIdentity.Catalog.of_checked fixture.checked

theorem ActualHeader.relayWord_receipt {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayWordRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_receipt observed.relayWordRow observed.relayWordShape observed.relayWordNodes
    observed.relayWordResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.relayBool_receipt {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ receipt : Receipt actual.header,
      Support (headers rows) actual.header (RecursiveNamedPreparedStageScopes.registry stagePrepared) receipt
        (CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)) :=
  actual.scoped_receipt observed.relayBoolRow observed.relayBoolShape observed.relayBoolNodes
    observed.relayBoolResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.scoped_support {fixture : CompiledFixture}
    {signature : ProgramFunctionSignature} {type : TypeSystem.Ty}
    (row : ObservedRow fixture signature)
    (shape : SelectedRelayShape row.row.function type)
    (nodes : row.row.function.typedBody.nodes = shape.nodeList)
    (resultType : row.row.function.inferredBodyType = type)
    (noLocals : fixture.recipe.compiled.indexed.base.locals.bindings = [])
    (actual : ActualHeader fixture row.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {entry : SourceCoreCallableIndexedPrograms.Entry fixture.recipe.compiled.indexed.layouts}
    (entryMember : entry ∈ fixture.recipe.compiled.indexed.entries)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) := by
  obtain ⟨receipt, static⟩ := actual.scoped_receipt row shape nodes resultType noLocals rows entryMember
    receiver methods stagePrepared
  let body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header := {
    row := row.row
    prepared := actual.prepared
    instantiation := CallableNamedCanonicalOrder.retainedInstantiation row.row
    aligned := actual.aligned
    layouts := actual.aligned.layouts
    compilation := .canonicalBranching receipt }
  exact ⟨body, .scoped body receipt rfl static⟩

theorem ActualHeader.relayWord_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayWordRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) :=
  actual.scoped_support observed.relayWordRow observed.relayWordShape observed.relayWordNodes
    observed.relayWordResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared

theorem ActualHeader.relayBool_support {fixture : CompiledFixture}
    (observed : ObservedProgram fixture) (actual : ActualHeader fixture observed.relayBoolRow.row)
    {inputs : List (Input fixture.recipe.compiled)} (rows : Inventory inputs)
    {bodyRegistry : SourceCoreRawMetadata.Registry}
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver fixture.recipe.compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt fixture.recipe.compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (methods : CallableIndexedOwnedPreparedStagedClosedMethodSelection.Catalog fixture.recipe.compiled.sourceProgram)
    (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared fixture.recipe.compiled
      fixture.recipe.compiled.indexed.ancestry.graph.inputs.callable) :
    Nonempty (Σ body : CallableIndexedOwnedPreparedStagedNamedBodies.Body actual.header,
      CallableIndexedOwnedPreparedStagedPhysicalNamedBodySupport.Support
        (headers := headers rows) (bodyRegistry := bodyRegistry)
        (stages := RecursiveNamedPreparedStageScopes.registry stagePrepared)
        (semanticFaults := CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics)
        actual.header body) :=
  actual.scoped_support observed.relayBoolRow observed.relayBoolShape observed.relayBoolNodes
    observed.relayBoolResultType observed.noLocals rows observed.wordRow.entryMember receiver methods stagePrepared


end Tests.SourceCoreMethodNamedScoped
