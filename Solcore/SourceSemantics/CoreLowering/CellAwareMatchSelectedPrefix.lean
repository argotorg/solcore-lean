import Solcore.SourceSemantics.CoreLowering.CellAwareMatchPrefixProtocol
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix

/-! The actual selected match prefix retains every generalized descriptor row.
The existing typed selection proof runs over a protocol whose relation records
its real allocation effects, and returns the same original protected state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix CallableIndexedHistory
universe u v

theorem selected_with_effect
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
    {selection : Dynamic.MatchCaseSelection}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection) :
    ∃ hiddenHeap location finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) ∧
        CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalAgreement, finalTyped, finalReference, finalRead, finalUnmapped,
    canonicalPrefix, continuation, final, related, ⟨returnTo⟩⟩ :=
      CompatibleMatchTypedSelectionPrefix.Stateful.Certificate.selected_prefix_cells_sized_with_literals
        certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid ordinaryCells
        (CellAwareMatchPrefixProtocol.withEffects instances protocol)
        (CellAwareMatchPrefixProtocol.producer instances protocol producer)
        (CellAwareMatchPrefixProtocol.bindings instances protocol stateBindings)
        definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped
        reference read unmapped evaluated initial readyAt selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalAgreement, finalTyped, finalReference, finalRead, finalUnmapped,
    canonicalPrefix, continuation, final, related.1,
    ⟨CellAwareMatchPrefixProtocol.forgetReturn instances protocol returnTo⟩, related.2⟩

theorem success_with_effect
    {compilation : SourceCoreCompatibleDataMatches.Context} {allocationSource : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation allocationSource scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (literals : IntegerLiteralResolution → Prop)
    (signatures : context.signatures = compilation.signatures)
    (numericRequirements : ∀ numeric, literals numeric → RequirementProves context numeric.requirement numeric.predicate)
    (sites : CompatibleMatchDecision.Certificate.LiteralSites literals certificate)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {cells : GenericHeap.CellModel ambient.definitions}
    (instances : GeneralizedLocalDescriptorHeap.InstanceModel ambient.definitions)
    (ordinaryCells : GenericHeap.OrdinaryCells (CompatibleAmbientHeap.payloadModel compilation.checked registry functions) cells)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.CellAllocation.Producer (catalog := CompatibleEquality.storageCatalog compilation.checked.catalog) protocol layouts frame cells)
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : allocationSource.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.CellAllocation.ReadyAt producer contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      GenericHeap.CellHeapRepresents cells finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) ∧
      ∃ final : protocol.State ⟨finalScope, finalMap, finalWorld, finalHeap, finalStore, finalCanonical⟩,
        protocol.Relates initial final ∧ Nonempty (ProtectedStateTransition.ReturnTo protocol scope canonical
          finalScope finalCanonical) ∧
        CellAwareScopeAuthority.Effect instances mapping world heap store finalMap finalWorld finalHeap finalStore := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration, effect⟩ :=
    selected_with_effect certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid instances ordinaryCells protocol producer stateBindings definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration, effect⟩

end Solcore.SourceSemantics.CoreLowering.CellAwareMatchSelectedPrefix
