import Solcore.SourceSemantics.CoreLowering.TypedImperativeForState

/-! Concrete post headers run beneath the actual six loop temporaries. Their
success restores the lexical capture used by the next self invocation, while
all post allocations and writes remain in the common compatible heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)

/-- Real envelope values, not merely a count of administrative slots. -/
def postValues (type : Ty) (location : Location) (continued : Bool) : List Value :=
  (if continued then ForLoop.continuingPrefix type else ForLoop.fallthroughPrefix type) ++
    [.unit, .cellRef (OptionalCell.cellType (LocalLoop.functionType type)) location]

theorem postValues_length (type : Ty) (location : Location) (continued : Bool) :
    (postValues type location continued).length = 6 := by cases continued <;> rfl

theorem postValues_typed {definitions : DataEnvironment} {world : StoreTyping}
    {actual : Environment} {actualContext : Core.Context} {type : Ty} {location : Location}
    (continued : Bool) (selfTyped : world[location]? = some (OptionalCell.cellType (LocalLoop.functionType type)))
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    ∃ context, RuntimeEnvironmentHasTypes world (postValues type location continued ++ actual) context definitions := by
  cases continued
  · exact ⟨_, .cons .unit (.cons (.inLeft .unit) (.cons (.inLeft (.inLeft .unit))
      (.cons .bool (.cons .unit (.cons (.cellRef selfTyped) typed)))))⟩
  · exact ⟨_, .cons .unit (.cons (.inRight .unit) (.cons (.inRight (.inRight .unit))
      (.cons .bool (.cons .unit (.cons (.cellRef selfTyped) typed)))))⟩

theorem postValues_agree {canonical actual : Environment} {ξ : Renaming}
    (agrees : EnvironmentsAgree ξ canonical actual) (type : Ty) (location : Location) (continued : Bool) :
    EnvironmentsAgree ((fun index => index + 6).comp ξ) canonical (postValues type location continued ++ actual) := by
  have renamed : DataPlaceChildExpressions.prefixRenaming 6 ξ = ((fun index => index + 6).comp ξ) := by
    funext index
    simp [DataPlaceChildExpressions.prefixRenaming, Renaming.comp, Renaming.insertion]
  rw [← renamed]
  intro index value found
  have actual := DataPlaceChildExpressions.prefix_agrees agrees (postValues type location continued) found
  simpa only [postValues_length] using actual

theorem post_rename (code : Expr) (ξ : Renaming) :
    ForLoop.postCode (code.rename ξ) = code.rename ((fun index => index + 6).comp ξ) := by
  simp only [ForLoop.postCode, Core.LoopExecution.conditionCode, ← Expr.rename_insertion, Expr.rename_comp]
  congr 1

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {readFuel : Nat} {values : ValuesContext} {source : TypedSource} {solved : List SolvedRequirement}
  {reasonAt : ExpressionId → Word} {administrative actualContext : Core.Context}
  {type : Ty} {context : SourceSemantics.Context} {scope : Scope}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  (definitions : layouts.definitions = ambient.definitions) (registered : frameLayout.Registered ambient.definitions)
  {registry : SourceCoreRawMetadata.Registry} (extension : SourceCoreRawMetadata.Extends values.registry registry)
  (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ id location, faults (.uninitializedLocation location) (reasonAt id))
  (missing : ∀ id key value tag, MetadataRep registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((reasonAt id).add tag))
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  {contextLocation location : Location} {conditionCode body postCode : Expr} {selfReason : Word}
  {mapping : LocationMap} {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}

include definitions registered extension uninitialized missing faithful observations in
theorem post_preserves {items : List ForItemForm} {finalContext : SourceSemantics.Context} {finalEnvironment : Dynamic.Environment}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
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
    tree.preserves_post functions definitions registered extension program evidence uninitialized missing faithful observations
      valid unique state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨tail.store, tail.mapping, tail.world, by simpa only [post_rename] using evaluated,
    tail.heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension uninitialized missing faithful observations in
theorem post_fault {items : List ForItemForm} {finalContext : SourceSemantics.Context} {reason : Dynamic.SemanticFault}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : TypedForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
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
    tree.preserves_fault functions definitions registered extension program evidence uninitialized missing faithful observations
      errors valid unique state.environments state.heaps state.locals (postValues_agree agrees type location continued) postTyped
      reference read state.contextUnmapped trace
  exact ⟨token, finalStore, finalMap, finalWorld, by simpa only [post_rename] using evaluated,
    matched, heaps, maps, worlds, preservation, metadata⟩

include definitions registered extension uninitialized missing faithful observations in
theorem post_reflects (functionTypes : FunctionRuntimeViews functions)
    {items : List ForItemForm} {value : Value} {finalStore : Store}
    (tree : TypedForHeader.Tree layouts owner active frameLayout globals onError readFuel values source solved reasonAt ambient.definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items postCode)
    (errors : TypedForHeader.Tree.Errors registry faults tree)
    (valid : CompatibleExpressionLiterals.ContextValid solved context evidence) (unique : NodeOccurrencesUnique source)
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
  rcases tree.reflects_post functions definitions registered extension program evidence uninitialized missing faithful observations
      functionTypes errors valid unique state.environments state.heaps state.locals
      (postValues_agree agrees type location continued) postTyped reference read state.contextUnmapped
      (by simpa only [post_rename] using evaluated) with done | fault
  · obtain ⟨finalContext, finalEnvironment, after, tail, trace, same, storeEq, maps, worlds, preservation, metadata, _, _, _⟩ := done
    subst finalStore
    exact .inl ⟨finalContext, finalEnvironment, after, tail.mapping, tail.world, trace, same,
      tail.heaps, maps, worlds, preservation, metadata⟩
  · obtain ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched, heaps, maps, worlds, preservation, metadata⟩ := fault
    exact .inr ⟨finalContext, reason, token, after, finalMap, finalWorld, trace, same, matched,
      heaps, maps, worlds, preservation, metadata⟩

end Solcore.SourceSemantics.CoreLowering.TypedImperativeFor
