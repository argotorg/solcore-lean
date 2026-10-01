import Solcore.SourceSemantics.CoreLowering.CompatibleMatchScrutineeReflection
import Solcore.Test.SourceCompilerFeatureSupport

/-! The independently selected compatible arm reaches an actual closure body
with exactly its real captured environment. Both finite directions preserve the
hidden/source binder allocations; no body evaluation is supplied by a caller. -/
set_option autoImplicit false
namespace Tests.SourceCoreCompatibleSelectedMatchPrefixes
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CoreProof CompatiblePayload
open SourceCoreCompatibleDataMatches CompatibleMatchCertificates CompatibleMatchSelectionPrefix CallableIndexedHistory

theorem selected_closure_body
    {compilation : SourceCoreCompatibleDataMatches.Context} {source : TypedSource} {scope : Scope}
    {id : StatementId} {resolution : MatchResolution} {internalReason : Word}
    {expressionCertificate : ExpressionCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution (.function .unit .unit) internalReason
      expressionCertificate (fun _ _ code => code = LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))) code) (ordinary : Ordinary certificate)
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
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
    {heap : Dynamic.Heap} {before store : Store} {sourceValue : Dynamic.Value} {value : Value} {payload : Ty}
    (represented : CompatiblePayload.ValueRep compilation.checked registry functions mapping world node.type sourceValue value payload)
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compilation.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree ξ canonical actual)
    {contextLocation : Location} {native : NativeFrame}
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frame.type contextLocation))
    (read : store.read? contextLocation = some (SourceCoreCallableIndexedFrames.encode frame native))
    (unmapped : contextLocation ∉ mapping)
    (evaluated : Evaluates actual before (lowered.expression.rename ξ) (.inRight .word value) store)
    {statements : List StatementId} {bindings : List (TypedBinder × Dynamic.Value)}
    (selectedSource : Dynamic.MatchCasesSelect context sourceValue resolution.cases resolution.defaultBody (.arm statements bindings)) :
    ∃ hiddenHeap location selectedEnvironment selectedHeap selectedActual selectedStore selectedMap selectedWorld,
      Dynamic.Heap.Allocates heap node.type (some sourceValue) location hiddenHeap ∧
      Dynamic.BindersAllocate environment hiddenHeap (bindings.map Prod.fst) (bindings.map Prod.snd) selectedEnvironment selectedHeap ∧
      CompatibleAmbientHeap.HeapRepresents compilation.checked registry functions selectedMap selectedWorld selectedHeap selectedStore ∧
      AdministrativePreserved mapping store selectedMap selectedStore ∧
      Evaluates actual before (code.rename ξ)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore ∧
      (∀ result finished, Evaluates actual before (code.rename ξ) result finished →
        result = LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual) ∧ finished = selectedStore) := by
  obtain ⟨hiddenHeap, location, finalScope, selectedEnvironment, selectedHeap, selectedCanonical, selectedActual,
      selectedStore, selectedMap, selectedWorld, selectedEmbedding, body,
      allocated, selected, selectedBody, finalEnvironments, finalHeaps, maps, worlds, preserved, finalLayout, agreement⟩ :=
    CompatibleMatchSelectedPrefix.Certificate.selected_prefix certificate ordinary onError allocator valid catalogValid
      definitions registered extended found uniqueExpression represented environments heaps agrees reference read unmapped evaluated selectedSource
  cases selectedBody with
  | arm identities bound certified =>
    subst body
    have child : Evaluates selectedActual selectedStore
        ((LocalLoop.returnValue (.function .unit .unit) (LanguageResult.success (.lambda .unit .unit (.var 0)))).rename selectedEmbedding)
        (LocalLoop.returnedValue (.closure .unit .unit (.var 0) selectedActual)) selectedStore := by
      simp only [LocalLoop.returnValue, LanguageResult.bind, LocalLoop.returned, LanguageResult.success, Expr.rename, Renaming.lift]
      exact .caseRight (.inRight .lambda) (.inRight (.inLeft (.inRight (.var rfl))))
    refine ⟨hiddenHeap, location, selectedEnvironment, selectedHeap, selectedActual, selectedStore, selectedMap, selectedWorld,
      allocated, bound, finalHeaps, preserved, agreement.wrap child, ?_⟩
    intro result finished completed
    exact evaluation_deterministic completed (agreement.wrap child)

end Tests.SourceCoreCompatibleSelectedMatchPrefixes
