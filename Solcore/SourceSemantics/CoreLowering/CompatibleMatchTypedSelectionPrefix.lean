import Solcore.SourceSemantics.CoreLowering.CompatibleMatchSourceSelection
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedBranchesPrefix
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedHiddenPrefix

/-! The exact actual marked prefix preserves an independently selected source
arm/default. No global source evaluator determinism or body execution is
required. The enclosing statement Tree supplies scrutinee/body correspondence. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchDecision
open CompatibleMatchSelectionPrefix DataMatchBranchPrefix CallableIndexedHistory
universe u v

theorem Stateful.Certificate.selected_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
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
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
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
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
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
          finalScope finalCanonical) := by
  cases sites with
  | @matchWith statementNode statementType scrutineeNode type scrutinee arms fallback branches _
      readStatement allowed form requirements hiddenOwned hiddenFresh scrutineeOwned scrutineeFound projection
      expressionCertified sameType armCertificates fallbackCertificate branchesCertified hiddenCompiled supported =>
    have nodeEq := Option.some.inj (found.symm.trans scrutineeFound)
    subst scrutineeNode
    have expressionEq := uniqueExpression scrutinee expressionCertified
    subst scrutinee
    have payloadEq : payload = type := Except.ok.inj
      (represented.projection.symm.trans (CompatibleExpressionReads.projectType_of_accepted projection))
    subst payload
    obtain ⟨hiddenOrdinary, ordinaryArms⟩ := ordinary
    have kinds := ordinaryArms type node.type arms armCertificates
    rw [allocator] at hiddenCompiled
    obtain ⟨hiddenHeap, location, hiddenStore, hiddenWorld, hiddenMap, hiddenRef, allocated, hiddenEnvironments,
      hiddenHeaps, hiddenMaps, hiddenWorlds, hiddenFrame, hiddenLayout, hiddenTyped, hiddenAgreement, hiddenState, hiddenRelated, ⟨hiddenReturn⟩⟩ :=
      CompatibleMatchTypedHiddenPrefix.Stateful.success_prefix_sized onError hiddenOrdinary hiddenFresh hiddenCompiled protocol producer stateBindings definitions registered
        (model := CompatibleAmbientHeap.payloadModel compilation.checked registry functions)
        represented environments heaps agrees actualTyped reference read evaluated initial readyAt
    have bound : contextLocation < store.length := (List.getElem?_eq_some_iff.mp read).1
    obtain ⟨stillUnmapped, stillRead⟩ := hiddenFrame contextLocation unmapped bound
    have nextRead := stillRead.trans read
    have nextReference : (hiddenRef :: canonical)[((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals]? =
        some (.cellRef frame.type contextLocation) := by
      have indexEq : ((resolution.hiddenScrutinee, type) :: scope).length + 1 + globals =
          (scope.length + 1 + globals) + 1 := by simp only [List.length_cons]; omega
      rw [indexEq]
      exact reference
    have nextRepresented := represented.extend (.refl _) hiddenMaps hiddenWorlds
    have decision := CompatibleMatchSourceSelection.Arms.selects_with_literals armCertificates fallbackCertificate literals signatures numericRequirements supported
      catalogValid extended nextRepresented selectedSource
    obtain ⟨finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore, finalMap, finalWorld,
      finalEmbedding, finalContext, body, selected, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, selectedRelated, ⟨selectedReturn⟩⟩ :=
      CompatibleMatchTypedBranchesPrefix.Stateful.Decision.prefix_sized protocol producer stateBindings definitions registered allocator decision armCertificates
        branchesCertified kinds nextReference nextRead stillUnmapped hiddenEnvironments hiddenHeaps hiddenLayout hiddenTyped hiddenState readyAt
    exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, decision.source, selected, finalEnvironments, finalHeaps,
      hiddenMaps.trans maps, hiddenWorlds.trans worlds, hiddenFrame.trans preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
      (CanonicalPrefix.cons scope canonical (resolution.hiddenScrutinee, type) hiddenRef).trans spine, hiddenAgreement.trans agreement, finalState, protocol.trans hiddenRelated selectedRelated,
      ⟨ProtectedStateTransition.ReturnTo.then hiddenReturn selectedReturn⟩⟩




theorem Stateful.Certificate.selected_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
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
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
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
          finalScope finalCanonical) := by
  exact Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid protocol producer stateBindings definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selectedSource



theorem Stateful.Certificate.success_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
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
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
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
          finalScope finalCanonical) := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩ :=
    Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid protocol producer stateBindings definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement, finalState, related, restoration⟩


theorem Stateful.Certificate.success_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (producer : ProtectedStateTransition.MarkedAllocation.Producer protocol layouts frame
      (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
    (stateBindings : ProtectedStateTransition.Bindings protocol)
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    (initial : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩)
    (readyAt : ProtectedStateTransition.OrdinaryAllocation.ReadyAt producer.toOrdinary contextLocation native)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
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
          finalScope finalCanonical) := by
  exact Stateful.Certificate.success_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid protocol producer stateBindings definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated initial readyAt




/-- The original API forgets only actual state and future restoration. -/
theorem Certificate.selected_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
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
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
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
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnv,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
    spine, agreement, _final, _related, _return⟩ :=
    Stateful.Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures
      numericRequirements sites catalogValid ProtectedStateTransition.OrdinaryAllocation.unitProtocol
      (ProtectedStateTransition.MarkedAllocation.unitProducer layouts frame
        (CompatibleAmbientHeap.payloadModel compilation.checked registry functions))
      ProtectedStateTransition.MatchPrefix.unitBindings definitions registered extended found uniqueExpression
      represented environments heaps agrees actualTyped reference read unmapped evaluated () (fun _ _ => True.intro) selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnv,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped,
    spine, agreement⟩

theorem Certificate.selected_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
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
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource


/-- Whole Core success can use the independently constructed source decision.
The selected actual body's complete runtime context is derived by the prefix. -/
theorem Certificate.success_prefix_sized_with_literals
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
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
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨selection, selected⟩ := CompatibleMatchDecision.Certificate.source_selects_with_literals certificate literals signatures numericRequirements sites catalogValid extended found represented
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
      finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
      finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement⟩ :=
    Certificate.selected_prefix_sized_with_literals certificate ordinary onError allocator literals signatures numericRequirements sites catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selected
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, sourceSelect, bodySelect, finalEnvironments,
    finalHeaps, maps, worlds, preserved, finalLayout, finalTyped, finalReference, finalRead, finalUnmapped, spine, agreement⟩

theorem Certificate.success_prefix_sized
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      CanonicalPrefix scope canonical finalScope finalCanonical ∧
      ContinuationSize true actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  exact Certificate.success_prefix_sized_with_literals certificate ordinary onError allocator _ valid.signatures (fun _ proof => proof) (CompatibleMatchDecision.Certificate.ordinary_sites certificate valid) catalogValid definitions registered extended found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated


/-- Compatibility erasure of the same measured prefix. -/
theorem Certificate.selected_prefix_typed
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
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
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, _, agreement⟩ :=
    Certificate.selected_prefix_sized certificate ordinary onError allocator valid catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated selectedSource
  exact ⟨hiddenHeap, location, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, agreement.agreement⟩

/-- Compatibility erasure of the same measured prefix. -/
theorem Certificate.success_prefix_typed
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {resultType : Ty} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution resultType internalReason
      expressionCertificate bodyCertificate code) (ordinary : Ordinary certificate)
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {context : SourceSemantics.Context} (valid : CompatiblePatternLeaves.ContextValid compilation context)
    (catalogValid : SignatureCatalogWellFormed compilation.checked.signatures)
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    (definitions : layouts.definitions = ambient.definitions) (registered : frame.Registered ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends compilation.values.registry registry)
    {node : ExpressionNode} (found : source.lookupExpression? resolution.scrutinee = some node)
    {lowered : SourceCoreBasic.LoweredExpr}
    (uniqueExpression : ∀ lowered', expressionCertificate scope resolution.scrutinee lowered' → lowered' = lowered)
    {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
 :
    ∃ hiddenHeap location selection finalScope finalEnvironment finalHeap finalCanonical finalActual finalStore
        finalMap finalWorld finalEmbedding finalContext body,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody selection ∧
      SelectedBody bodyCertificate ((resolution.hiddenScrutinee, payload) :: scope) environment hiddenHeap
        resultType selection finalScope finalEnvironment finalHeap body ∧
      DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog) finalMap finalWorld administrative
        finalScope finalEnvironment finalCanonical ambient.definitions ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions finalMap finalWorld finalHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧
      EnvironmentsAgree finalEmbedding finalCanonical finalActual ∧
      RuntimeEnvironmentHasTypes finalWorld finalActual finalContext ambient.definitions ∧
      finalCanonical[finalScope.length + 1 + globals]? = some (.cellRef frame.type contextLocation) ∧
      finalStore.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native) ∧
      contextLocation ∉ finalMap ∧
      ContinuationAgreement actual before (code.rename ξ) finalActual finalStore (body.rename finalEmbedding) := by
  obtain ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, _, agreement⟩ :=
    Certificate.success_prefix_sized certificate ordinary onError allocator valid catalogValid definitions registered extended
      found uniqueExpression represented environments heaps agrees actualTyped reference read unmapped evaluated
  exact ⟨hiddenHeap, location, selection, finalScope, finalEnvironment, finalHeap, finalCanonical, finalActual, finalStore,
    finalMap, finalWorld, finalEmbedding, finalContext, body, allocated, selected, selectedBody, finalEnv, finalHeaps,
    maps, worlds, frame, layout, typed, finalReference, finalRead, finalUnmapped, agreement.agreement⟩


end Solcore.SourceSemantics.CoreLowering.CompatibleMatchTypedSelectionPrefix
