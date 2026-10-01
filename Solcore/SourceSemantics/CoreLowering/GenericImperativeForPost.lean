import Solcore.SourceSemantics.CoreLowering.GenericForHeaderPost
import Solcore.SourceSemantics.CoreLowering.TypedImperativeForPost

/-! Concrete post wrappers keep their Bool/Unit/self slots while a generic
header closes its continuation and restores visible source names. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (LoopState Progress postValues postValues_typed postValues_agree post_rename)
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {administrative actualContext : Core.Context}
  {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (meaning : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Preserves (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  (reflection : ∀ context, CompatibleExpressionLiterals.ContextValid solved context evidence →
    TypedGenericExpressionMeaning.Reflects (CompatibleAmbientHeap.payloadModel values.checked registry functions)
      program context evidence source (certificates context) faults)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include definitions registered extension meaning faithful observations in
theorem post_preserves {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after) :
    ∃ finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (LocalLoop.fallthroughValue type) finalStore ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  obtain ⟨tail, maps, worlds, preservation, metadata, evaluated, _, _, _⟩ :=
    tree.preserves_post functions definitions registered extension program evidence meaning faithful observations
      valid state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨tail.store, tail.mapping, tail.world, by simpa only [post_rename] using evaluated,
    tail.heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension meaning faithful observations in
theorem post_fault {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (trace : Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ))
        (.inLeft (LocalLoop.controlType type) (.word token)) finalStore ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, heaps, maps, worlds, preservation, metadata⟩ :=
    tree.preserves_fault functions definitions registered extension program evidence meaning faithful observations
      errors valid state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨token, finalStore, finalMap, finalWorld, by simpa only [post_rename] using evaluated,
    matched, heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension meaning reflection faithful observations in
theorem post_reflects (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : GenericForHeader.Tree layouts owner active frameLayout globals onError values source certificates ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : GenericForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (_unique : NodeOccurrencesUnique source)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (reference : canonical[scope.length + 1 + globals]? = some (.cellRef frameLayout.type contextLocation))
    (state : LoopState values registry functions context scope administrative actualContext frameLayout environment canonical actual
      contextLocation location type conditionCode body (postCode.rename ξ) selfReason mapping world before store)
    (continued : Bool)
    (evaluated : Evaluates (postValues type location continued ++ actual) store (ForLoop.postCode (postCode.rename ξ)) value finalStore) :
    (∃ finalContext finalEnvironment after finalMap finalWorld,
      Dynamic.ForItemsExecute program context evidence source environment before items finalContext finalEnvironment after ∧
      value = LocalLoop.fallthroughValue type ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) ∨
    (∃ finalContext reason token after finalMap finalWorld,
      Dynamic.ForItemsFault program context evidence source environment before items finalContext reason after ∧
      value = .inLeft (LocalLoop.controlType type) (.word token) ∧ faults reason token ∧
      Progress values registry functions before after mapping finalMap world finalWorld store finalStore) := by
  obtain ⟨native, read⟩ := state.contextRead
  obtain ⟨postContext, postTyped⟩ := postValues_typed continued state.selfTyped state.actualTyped
  rcases tree.reflects_post functions definitions registered extension program evidence meaning reflection faithful observations
      functionTypes errors valid state.environments state.heaps state.locals
      (postValues_agree agrees type location continued) postTyped reference read state.contextUnmapped
      (by simpa only [post_rename] using evaluated) with done | fault
  · obtain ⟨finalContext, finalEnvironment, after, tail, trace, same, storeEq, maps, worlds, preservation, metadata, _, _, _⟩ := done
    subst finalStore
    exact .inl ⟨finalContext, finalEnvironment, after, tail.mapping, tail.world, trace, same,
      tail.heaps, maps, worlds, preservation, metadata⟩
  · obtain ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, heaps, maps, worlds, preservation, metadata⟩ := fault
    exact .inr ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched,
      heaps, maps, worlds, preservation, metadata⟩

end Solcore.SourceSemantics.CoreLowering.GenericImperativeFor
