import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.CoreEvaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceExecution
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceWriteback
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceKeys
import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.BasicExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.BareAssignments

/-!
# Compatible profile: renamed places

Places under renaming: native typing, layout, resolution and reflection.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceNative
/-! Renaming the actual compatible assignment syntax. The comparison helpers
are closed by their real preparation receipts, and virtual roots are pure
quoted values. These are syntax equalities, not equality of captured closures
or of stores produced by evaluating code in different environments. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CoreProof

def renamed (code : SourceCoreBasic.LoweredExpr) (ξ : Renaming) : SourceCoreBasic.LoweredExpr :=
  ⟨code.type, code.expression.rename ξ⟩

def renamedCodes (codes : List SourceCoreBasic.LoweredExpr) (ξ : Renaming) : List SourceCoreBasic.LoweredExpr :=
  codes.map (fun code => renamed code ξ)

@[simp] theorem renamedCodes_types (codes : List SourceCoreBasic.LoweredExpr) (ξ : Renaming) :
    (renamedCodes codes ξ).map (·.type) = codes.map (·.type) := by simp [renamedCodes, renamed, List.map_map]

@[simp] theorem packed_renamed_type (codes : List SourceCoreBasic.LoweredExpr) (ξ : Renaming) :
    (SourceCoreCalls.packArguments (renamedCodes codes ξ)).type = (SourceCoreCalls.packArguments codes).type := by
  induction codes with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest => simpa only [renamedCodes, List.map_cons, SourceCoreCalls.packArguments, renamed] using congrArg (Ty.product head.type) ih

@[simp] theorem packed_renamed_expression (codes : List SourceCoreBasic.LoweredExpr) (ξ : Renaming) :
    (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression = (SourceCoreCalls.packArguments codes).expression.rename ξ := by
  induction codes with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest =>
      change LocalSequence.pair head.type (SourceCoreCalls.packArguments (renamedCodes (next :: rest) ξ)).type
        (head.expression.rename ξ) (SourceCoreCalls.packArguments (renamedCodes (next :: rest) ξ)).expression =
        (LocalSequence.pair head.type (SourceCoreCalls.packArguments (next :: rest)).type
          head.expression (SourceCoreCalls.packArguments (next :: rest)).expression).rename ξ
      rw [packed_renamed_type, ih, DataExpressionSequence.pair_rename]

@[simp] theorem renamed_packed (codes : List SourceCoreBasic.LoweredExpr) (ξ : Renaming) :
    renamed (SourceCoreCalls.packArguments codes) ξ = SourceCoreCalls.packArguments (renamedCodes codes ξ) := by
  have ext : ∀ {a b : SourceCoreBasic.LoweredExpr}, a.type = b.type → a.expression = b.expression → a = b := by
    intro a b types expressions
    cases a
    cases b
    cases types
    cases expressions
    rfl
  exact ext (packed_renamed_type codes ξ).symm (packed_renamed_expression codes ξ).symm

private theorem project_rename (types : List Ty) (index : Nat) (value : Expr) (ξ : Renaming) :
    (SourceCoreDataExpressions.projectPacked index types value).rename ξ =
      SourceCoreDataExpressions.projectPacked index types (value.rename ξ) := by
  induction types generalizing index value with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest => cases index <;> simp [SourceCoreDataExpressions.projectPacked, Expr.rename, ih]

private theorem pack_rename (values : List Expr) (ξ : Renaming) :
    (pack values).rename ξ = pack (values.map (·.rename ξ)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => cases tail with
    | nil => rfl
    | cons next rest => simpa only [pack, Expr.rename, List.map_cons] using congrArg (Expr.pair (head.rename ξ)) ih

private theorem replace_rename (index : Nat) (types : List Ty) (payload value : Expr) (ξ : Renaming) :
    (replacePacked index types payload value).rename ξ = replacePacked index types (payload.rename ξ) (value.rename ξ) := by
  simp only [replacePacked, pack_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro entry _
  dsimp only [Function.comp_def]
  split <;> simp [project_rename]

private theorem ordered_lookup_rename (layout : OrderedMapping.Layout) (comparison value key : Expr) (ξ : Renaming) :
    (OrderedMapping.lookup layout comparison value key).rename ξ =
      OrderedMapping.lookup layout (comparison.rename ξ) (value.rename ξ) (key.rename ξ) := by
  simp [OrderedMapping.lookup, OrderedMapping.runHelper, WordMapping.runHelper, OrderedMapping.lookupBody,
    OrderedMapping.invoke, WordMapping.invoke, OptionalCell.allocate, OptionalCell.read,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.rename, Expr.renameList,
    Expr.weakenAt, Renaming.lift]

private theorem ordered_insert_rename (layout : OrderedMapping.Layout) (comparison value key replacement : Expr) (ξ : Renaming) :
    (OrderedMapping.insert layout comparison value key replacement).rename ξ =
      OrderedMapping.insert layout (comparison.rename ξ) (value.rename ξ) (key.rename ξ) (replacement.rename ξ) := by
  simp [OrderedMapping.insert, OrderedMapping.runHelper, WordMapping.runHelper, OrderedMapping.insertBody,
    OrderedMapping.cons, OrderedMapping.empty, OrderedMapping.invoke, WordMapping.invoke,
    OptionalCell.allocate, OptionalCell.read, LanguageResult.bind, LanguageResult.success, LanguageResult.failure,
    Expr.rename, Expr.renameList, Expr.weakenAt, Renaming.lift]

private theorem lookup_rename (layout : OrderedMapping.Layout) (missing : Word) (comparison value key : Expr) (ξ : Renaming) :
    (SourceCoreMappingWithDefault.lookup layout missing comparison value key).rename ξ =
      SourceCoreMappingWithDefault.lookup layout missing (comparison.rename ξ) (value.rename ξ) (key.rename ξ) := by
  simp [SourceCoreMappingWithDefault.lookup, SourceCoreMappingWithDefault.entries, SourceCoreMappingWithDefault.select,
    SourceCoreMappingWithDefault.metadata, SourceCoreMappingWithDefault.defaultValue,
    LanguageResult.bind, LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift,
    ordered_lookup_rename]

private theorem insert_rename (layout : OrderedMapping.Layout) (comparison value key replacement : Expr) (ξ : Renaming) :
    (SourceCoreMappingWithDefault.insert layout comparison value key replacement).rename ξ =
      SourceCoreMappingWithDefault.insert layout (comparison.rename ξ) (value.rename ξ) (key.rename ξ) (replacement.rename ξ) := by
  simp [SourceCoreMappingWithDefault.insert, SourceCoreMappingWithDefault.entries, SourceCoreMappingWithDefault.pack,
    SourceCoreMappingWithDefault.metadata, SourceCoreMappingWithDefault.defaultValue, LanguageResult.bind,
    LanguageResult.success, Expr.rename, Renaming.lift, ordered_insert_rename]

private theorem index_rename {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : CompatibleMapping.Index checked index) (ξ : Renaming) : index.comparison.rename ξ = index.comparison := by
  rw [certificate.expression]
  exact closed_rename certificate.comparison.typed ξ

private theorem selected_rename {checked : SourceCoreCompatibleCatalog.Checked} {index : PreparedIndex}
    (certificate : CompatibleMapping.Index checked index) (prepared : Prepared) (current keys : Expr) (ξ : Renaming) :
    (selectedIndex prepared index current keys).rename ξ = selectedIndex prepared index (current.rename ξ) (keys.rename ξ) := by
  simp [selectedIndex, lookup_rename, project_rename, index_rename certificate]

private theorem branches_rename (branches : List Expr) (ξ : Renaming) :
    Expr.renameList branches ξ = branches.map (·.rename ξ) := by
  induction branches <;> simp_all [Expr.renameList]

private theorem select_rename {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position steps keys leaf)
    (prepared : Prepared) (current selectedKeys : Expr) (ξ : Renaming) :
    (select prepared steps current selectedKeys).rename ξ = select prepared steps (current.rename ξ) (selectedKeys.rename ξ) := by
  induction path generalizing current selectedKeys ξ with
  | nil => rfl
  | member _ _ _ _ ih =>
    simp only [select, Expr.rename, branches_rename, List.map_map]
    congr 1
    apply List.map_congr_left
    intro branch _
    dsimp only [Function.comp_def]
    rw [ih]
    simp [shift, List.range, List.range.loop, List.foldl, project_rename, Expr.rename, Renaming.lift]
  | index _ generated _ ih =>
    simp only [select, LanguageResult.bind, Expr.rename, selected_rename generated]
    rw [ih]
    simp [shift, List.range, List.range.loop, List.foldl, Expr.rename, Renaming.lift]

private theorem update_rename {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position steps keys leaf)
    (prepared : Prepared) (type : Ty) (current selectedKeys replacement : Expr) (ξ : Renaming) :
    (update prepared steps type current selectedKeys replacement).rename ξ =
      update prepared steps type (current.rename ξ) (selectedKeys.rename ξ) (replacement.rename ξ) := by
  induction path generalizing type current selectedKeys replacement ξ with
  | nil => rfl
  | member _ _ _ _ ih =>
    simp only [update, Expr.rename, branches_rename, List.map_map]
    congr 1
    apply List.map_congr_left
    intro branch _
    dsimp only [Function.comp_def]
    simp only [LanguageResult.bind, LanguageResult.success, Expr.rename, ih]
    simp [shift, List.range, List.range.loop, List.foldl, Expr.rename, Renaming.lift,
      project_rename, replace_rename]
  | index _ generated _ ih =>
    simp only [update, LanguageResult.bind, Expr.rename, selected_rename generated, ih]
    simp [insert_rename, index_rename generated, shift, List.range, List.range.loop, List.foldl,
      Expr.rename, Renaming.lift, project_rename]


def VirtualClosed (prepared : Prepared) : Prop :=
  ∀ expression, prepared.route.rootMapping = some expression → ∀ ξ : Renaming, expression.rename ξ = expression

private theorem normalize_rename {prepared : Prepared} (closed : VirtualClosed prepared) (optional : Expr) (ξ : Renaming) :
    (normalizeRoot prepared optional).rename ξ = normalizeRoot prepared (optional.rename ξ) := by
  cases found : prepared.route.rootMapping with
  | none => simp [normalizeRoot, found]
  | some value => simp [normalizeRoot, found, Expr.rename, Renaming.lift, closed value found]

theorem getter_rename {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat} {prepared : Prepared}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position prepared.steps prepared.keys leaf)
    (closed : VirtualClosed prepared) (keyType : Ty) (ξ : Renaming) :
    (getter prepared keyType).rename ξ = getter prepared keyType := by
  unfold getter
  split
  · simp [Expr.rename, LanguageResult.success, normalize_rename closed, Renaming.lift]
  · simp only [Expr.rename, normalize_rename closed, select_rename path]
    simp [LanguageResult.failure, Expr.rename, Renaming.lift]

theorem setter_rename {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat} {prepared : Prepared}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position prepared.steps prepared.keys leaf)
    (closed : VirtualClosed prepared) (keyType : Ty) (ξ : Renaming) :
    (setter prepared keyType).rename ξ = setter prepared keyType := by
  unfold setter
  split
  · simp [Expr.rename, LanguageResult.success, Renaming.lift]
  · simp only [Expr.rename, normalize_rename closed, update_rename path]
    simp [LanguageResult.failure, Expr.rename, Renaming.lift]

private theorem modified_rename (type : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word) (ξ : Renaming) :
    (modified type operator bitNot (.var 1) (.var 0) invalid).rename ξ.lift.lift =
      modified type operator bitNot (.var 1) (.var 0) invalid := by
  cases bitNot <;> cases operator <;> simp [modified, LanguageResult.success, LanguageResult.failure,
    shift, List.range, List.range.loop, List.foldl, Expr.weakenAt, Expr.rename, Renaming.lift]

/-- The entire emitted assignment is renamed together with its children and
continuation. Getter/setter closures will still capture the actual environment
where this syntax runs. -/
theorem execute_rename {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat} {prepared : Prepared}
    (path : CompatibleMixedRoute.PreparedPath checked source site root projections position prepared.steps prepared.keys leaf)
    (closed : VirtualClosed prepared) (reference : Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Expr) (outputType : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (bitNot : Bool) (invalid : Word) (ξ : Renaming) :
    (execute prepared reference keys rhs next outputType operator bitNot invalid).rename ξ =
      execute prepared (reference.rename ξ) (renamed keys ξ) (rhs.rename ξ) (next.rename ξ) outputType operator bitNot invalid := by
  simp [execute, renamed, LanguageResult.bind, shift, List.range, List.range.loop, List.foldl,
    Expr.rename, getter_rename path closed, setter_rename path closed, modified_rename, DataPlaceGuard.rename_lift, Renaming.lift]

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceLayout
/-! The existing actual-layout certificate supplies native helper typing in
an arbitrary related runtime environment. Deep typing and actual slot
agreement determine the native renaming; no source metadata is recovered from
native type equality. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality CompatibleHeap
open SourceCoreCompatibleDataPlaces CompatiblePlaceAssignmentSuccess

/-- Native slot typing, without a source-type injectivity assumption. -/
theorem environment_respects {definitions : DataEnvironment} {world : StoreTyping}
    {canonical actual : Environment} {source target : Core.Context} {ξ : Renaming}
    (canonicalTyped : RuntimeEnvironmentHasTypes world canonical source definitions)
    (actualTyped : RuntimeEnvironmentHasTypes world actual target definitions)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual) : Renaming.Respects ξ source target := by
  intro index type found
  have canonicalTypes := canonicalTyped.type_tags
  have actualTypes := actualTyped.type_tags
  rw [← canonicalTypes, List.getElem?_map] at found
  cases selected : canonical[index]? with
  | none => simp [selected] at found
  | some value =>
    simp only [selected, Option.map_some, Option.some.injEq] at found
    rw [← actualTypes, List.getElem?_map, agrees selected]
    exact congrArg some found

private theorem quote_rename {value : Value} {expression : Expr}
    (quoted : CompatibleMapping.VirtualRoot.Quoted value expression) (ξ : Renaming) :
    expression.rename ξ = expression := by induction quoted <;> simp_all [Expr.rename]

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
  {site : SourceCoreElaboration.ErrorSite} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext : Core.Context} {rhsType : Ty} {definitions : DataEnvironment}
  (layout : Layout compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType definitions)

include layout

/-- Describe only emits a virtual initializer for a retained mapping root;
its successful quote authenticates all of that expression's syntax. -/
theorem virtual_closed
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none) :
    VirtualClosed prepared := by
  classical
  intro expression found ξ
  by_cases mapping : ∃ key value, prepared.route.rootSourceType = .mapping key value
  · obtain ⟨key, value, declared⟩ := mapping
    cases layout.virtual key value declared with
    | encoded accepted unchanged quoted root =>
      have same := Option.some.inj (root.symm.trans found)
      subst expression
      exact quote_rename (CompatibleMapping.VirtualRoot.quoted_of_quote quoted) ξ
  · rw [ordinary (fun key value same => mapping ⟨key, value, same⟩)] at found
    cases found

/-- Typing is transported through the actual context embedding. Closure
values and helper stores are subsequently constructed in the actual context. -/
theorem getter_typed (closed : VirtualClosed prepared) {ξ : Renaming} {actualContext : Core.Context}
    (respects : Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext) :
    HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType :: actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) definitions := by
  have typing := layout.getterTyped.rename ((respects.lift _).lift _)
  simpa only [Expr.rename, getter_rename layout.path closed, Renaming.lift, Nat.zero_add] using typing

theorem setter_typed (closed : VirtualClosed prepared) {ξ : Renaming} {actualContext : Core.Context}
    (respects : Renaming.Respects ξ (SourceCoreLocalCell.coreContext scope ++ administrativeContext) actualContext) :
    HasType (prepared.route.leafType :: rhsType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
      OptionalCell.referenceType prepared.route.rootType :: actualContext)
      (.apply (setter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
      (LanguageResult.resultType prepared.route.rootType) definitions := by
  have typing := layout.setterTyped.rename (((((respects.lift _).lift _).lift _).lift _).lift _)
  simpa only [Expr.rename, setter_rename layout.path closed, Renaming.lift, Nat.zero_add] using typing

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution
/-! Typed child meanings for the actual CompatiblePlaceResolution phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceResolution CompatibleRenamedPlace

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

/-- Successful source resolution constructs the actual key and getter runs.
The universal child theorem covers every intermediate key heap and hidden
reference slot. Independent writable-local typing and environment agreement
recover the exact raw root declaration type. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      TypedDataPlaceKeyOrder.preserves children meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
        (.cons (.cellRef reference.typed) actualTyped) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) (actualTyped.weaken keyWorlds))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := keyMap) keyHeaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := by simpa only [packed_renamed_type] using evaluated
              keysRelated := by simpa only [renamedCodes_types] using keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, agrees coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceRhs
/-! The saved snapshot, packed keys and captured root reference are the actual
three RHS slots. Their typing is derived from resolution receipts and the
actual environment typing, rather than supplied as a child execution.
The result and latest-root relations are shared with unrestricted RHS meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open CompatibleRenamedPlace
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhs

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Every hidden slot uses the post-getter world. Existing administrative
captures are transported by the exact world extension from resolution. -/
theorem snapshot_runtimeTyped {actualContext : Core.Context}
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions) :
    RuntimeEnvironmentHasTypes resolution.world
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      (OptionalCell.cellType prepared.route.leafType :: (SourceCoreCalls.packArguments (renamedCodes codes ξ)).type ::
        OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions :=
  .cons (.inRight resolution.snapshotRelated.runtime_hasType)
    (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
      (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem preserves
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped trace
  refine ⟨value, store, mapping, world, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem reflects
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped
      (by simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, mapping, world, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceRhs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceSuccess
/-! Typed successful assignment prefixes expose their seven real temporary
values. Getter/setter typing and represented payloads type those slots in the
post-write world; no arbitrary slot list is assumed to be safe for captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceSuccess
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: prepared.route.leafType ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/-- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  cases trace with
  | @intro _ _ _ _ _ _ targetHeap rhsHeap _ _ sourceTarget _ right _ resolve evaluate written =>
    obtain ⟨resolution, coreLookup⟩ := CompatibleRenamedPlaceResolution.preserves layout.path layout.views layout.children layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped meaning faithful observations
      environments heaps locals agrees actualTyped slot rootTyped resolve
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult⟩ :=
      CompatibleRenamedPlaceRhs.preserves resolution meaning rhsGenerated found environments agrees actualTyped locals (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      have snapshotRep := rhsResult.saved_snapshot
      have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
        simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
      have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
      have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ found => by simpa only [Nat.zero_add] using found)
      obtain ⟨latest⟩ := rhsResult.latest
      cases written with
      | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
        have cellEq := sourceRead.functional latest.read
        have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
        obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
        rw [resolution.selectedEq] at applies
        have passes := CompatiblePlaceModifier.passes_of_applies observations operatorProfile rightRep applies
          (prepared.route.leafType = .integer)
        obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
          CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
        have present : ∃ sourceRoot, initial = some sourceRoot := by
          cases initial with
          | some value => exact ⟨value, rfl⟩
          | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
        obtain ⟨sourceRoot, rfl⟩ := present
        have rootExists : ∃ optional rootValue,
            RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
              cell optional sourceRoot rootValue := by
          cases initialValue with
          | initialized =>
            obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
            exact ⟨_, value, root⟩
          | emptyMapping key value =>
            obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
              (layout.virtual key value cellType.symm) registryExtension
            exact ⟨_, native, root⟩
        obtain ⟨optional, rootValue, root⟩ := rootExists
        have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
        have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
            (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
            (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
              OptionalCell.referenceType prepared.route.rootType :: actualContext)
            ambient.definitions :=
          .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
            (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
              (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
        have currentPath : PreparedPath compilation.checked source site cell.type place.projections
            0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
        have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
            currentPath sourceTarget.projections := by simpa only [cellType] using arguments
        obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
          helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
          CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
            faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
        refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
          by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
          (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
          (resolution.metadata.trans rhsResult.metadata).trans metadata,
          [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
            packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_⟩
        · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
        · intro next outputType
          rw [execute_rename layout.path closed]
          simp only [renamed_packed, Expr.rename]
          unfold execute
          simp only [packed_renamed_type]
          have snapshotEvaluated := resolution.snapshotEvaluated
          simp only [packed_renamed_type] at snapshotEvaluated
          exact (ContinuationAgreement.letE (.var coreLookup)).trans
            ((ContinuationAgreement.bind resolution.keysEvaluated).trans
              ((ContinuationAgreement.bind snapshotEvaluated).trans
                ((ContinuationAgreement.bind rhsResult.evaluated).trans
                  ((ContinuationAgreement.bind modifiedEvaluated).trans
                    ((ContinuationAgreement.bind setterEvaluated).trans
                      ((DataPlaceGuard.agreement passes).trans
                        (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten))))))))

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceSuccess
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTargetKeys
/-! Typed child meanings for the actual CompatiblePlaceTargetKeys phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTargetKeys CompatibleRenamedPlace

/-- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index)) := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped) trace
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
      packed_renamed_expression, List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    by simpa only [renamedCodes_types] using related, keyHeaps, maps, worlds, frame, metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceTargetKeys
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceKeyReflection
/-! Typed child meanings for the actual CompatiblePlaceKeyReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceKeyReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceKeyReflection CompatibleRenamedPlace

/-- Completed emitted code supplies the key runs to the universal reflection
IH. No source projection trace or child runtime execution is an input. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) :
    Result checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place environment
      coreEnvironment before store mapping world (ξ index) rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) keyValue keyStore) =>
    TypedDataPlaceKeyOrder.reflects children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (.cons (.cellRef reference.typed) actualTyped)
      (by simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var (agrees selected))
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | @values sources values related =>
        cases sourceTrace with
        | @values _ resolved _ shaped sourceTrace =>
          obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional staticLookupRuntime
          subst staticLocation
          have cellEq := initialRead.functional staticRead
          subst staticCell
          obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
          exact .keys lookup sourceTrace
            ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
              type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
              keysEvaluated, by simpa only [renamedCodes_types] using related, finalHeaps, maps, worlds, frame, metadata⟩ tail

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceKeyReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePrefixReflection
/-! Typed child meanings for the actual CompatiblePlacePrefixReflection phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePrefixReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlacePrefixReflection CompatibleRenamedPlace

/-- The diagnostic premises are static interpretations of emitted tokens.
They do not supply any source or native execution. All target source traces
are reconstructed from a completed emitted assignment and universal child IH. -/
theorem reflects {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming} {rhsType : Core.Ty}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext rhsType)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    (functionTypes : FunctionRuntimeViews functions)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    [FunctionCalls.FaultTokens faults] (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before : Dynamic.Heap} {store finalStore : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {rhs next : Expr} {outputType : Ty} {operator : Option Frontend.SourceCoreDataPlaces.Modifier} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType operator bitNot invalid) result finalStore) :
    Result compilation.checked registry functions program context evidence source faults prepared (renamedCodes codes ξ) sourceTypes place leaf environment
      coreEnvironment before store mapping world rhs next outputType operator bitNot invalid result finalStore := by
  have closed := virtual_closed layout ordinary
  have getterTyped := getter_typed layout closed (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨location, initialCell, lookup, initialRead, _, _⟩ := locals.lookup staticLookup
  have keyPhase := CompatibleRenamedPlaceKeyReflection.reflects layout.children meaning environments heaps locals agrees actualTyped slot rootTyped lookup initialRead completed
  cases keyPhase with
  | fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata =>
    exact .fault sourceFault resultEq tokenRep finalHeaps maps worlds frame metadata
  | @keys sourceLocation resolved after keyLookup sourceTrace keys continuation =>
    have locationEq := lookup.functional keyLookup
    subst sourceLocation
    have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
      simpa only [renamedCodes_types] using keys.related
    have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have currentPath : PreparedPath compilation.checked source site keys.cell.type place.projections 0 prepared.steps prepared.keys leaf := keys.type ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values currentPath resolved := by
      simpa only [keys.type] using arguments
    have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
        (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (CompatiblePlaceResolution.values_typed keyRelated)
        (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
    have reflectGetter := fun {value : Value} {afterStore : Store}
        (evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment) keys.keyStore
          (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0))) value afterStore) =>
      CompatiblePlaceGetterReflection.reflects currentArguments layout.leafProjected
        (fun k v same => layout.virtual k v (keys.type.symm.trans same))
        (fun nonmapping => ordinary (fun k v same => nonmapping k v (keys.type.trans same)))
        registryExtension layout.nonempty functionTypes faithful observations (layout.keyTypes ▸ keyRelated.length.2)
        keys.heaps keys.reference keys.read typedEnvironment getterTyped (.var rfl) (.var rfl) evaluated
    unfold CompatiblePlaceKeyReflection.remainder at continuation
    simp only [packed_renamed_type] at continuation
    cases continuation with
    | caseLeft getterEvaluated failed =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | missing initial fault receipt =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.projectionRead lookup initialRead sourceTrace keys.read initial fault) rfl
              (missingTokens receipt) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
      | uninitialized empty notMapping nonempty =>
        cases failed with
        | inLeft valueEvaluated =>
          cases valueEvaluated with
          | var found =>
            simp only [List.getElem?_cons_zero, Option.some.injEq] at found
            subst_vars
            exact .fault (.uninitialized lookup initialRead sourceTrace keys.read empty notMapping nonempty) rfl
              (invalidTokens _) finalHeaps keys.maps (keys.worlds.trans extension) (keys.frame.trans frame) keys.metadata
    | caseRight getterEvaluated remaining =>
      obtain ⟨futureWorld, _, resultRep, finalHeaps, extension, frame, _⟩ := reflectGetter getterEvaluated
      cases resultRep with
      | @read sourceRoot selected snapshot initial read represented =>
        exact .resolved (.intro lookup initialRead sourceTrace keys.read initial read)
          { target := keys.target
            sources := keys.sources
            values := keys.values
            selected := selected
            snapshot := snapshot
            keyStore := keys.keyStore
            store := _
            mapping := keys.keyMap
            world := futureWorld
            selectedEq := rfl
            currentCell := keys.cell
            currentRead := keys.read
            currentType := keys.type
            reference := keys.reference.extend (.refl _) extension
            shaped := keys.shaped
            keysEvaluated := keys.evaluated
            snapshotEvaluated := by simpa only [packed_renamed_type] using getterEvaluated
            keysRelated := keys.related.extend (.refl _) extension
            snapshotRelated := represented
            heaps := finalHeaps
            maps := keys.maps
            worlds := keys.worlds.trans extension
            frame := keys.frame.trans frame
            metadata := keys.metadata } (by simpa only [CompatiblePlacePrefixReflection.remainder, packed_renamed_type, snapshotEnvironment] using remaining)

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlacePrefixReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNotNative
/-! Exact syntax transport of the absent-RHS bare assignment. Its helper
closures are created in the actual environment; no existing captured closure
or stored value is replaced by a weakened evaluation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
open Core Frontend SourceInference GeneralHeap CoreProof
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatibleBareBitNotCertificates

private theorem getter_rename (prepared : Prepared) (layout : Layout prepared) (ξ : Renaming) :
    (getter prepared .unit).rename ξ = getter prepared .unit := by
  simp [getter, layout.steps, normalizeRoot, layout.ordinary, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem setter_rename (prepared : Prepared) (layout : Layout prepared) (ξ : Renaming) :
    (setter prepared .unit).rename ξ = setter prepared .unit := by
  simp [setter, layout.steps, LanguageResult.success, Expr.rename, Renaming.lift]

private theorem modified_rename (type : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) (ξ : Renaming) :
    (modified type operator true (.var 1) (.var 0) invalid).rename ξ.lift.lift =
      modified type operator true (.var 1) (.var 0) invalid := by
  simp [modified, LanguageResult.success, LanguageResult.failure, Expr.rename, Renaming.lift]

/-- Only the free lexical reference and continuation move. The Unit RHS stays
an administrative slot and is never represented as a source expression. -/
theorem execute_rename {prepared : Prepared} (layout : Layout prepared) (index : Nat)
    (next : Expr) (output : Ty) (operator : Option Frontend.SourceCoreDataPlaces.Modifier) (invalid : Word) (ξ : Renaming) :
    (execute prepared (.var index) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
      next output operator true invalid).rename ξ =
    execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments []) (LanguageResult.success .unit)
      (next.rename ξ) output operator true invalid := by
  simp [execute, SourceCoreCalls.packArguments, LanguageResult.bind, LanguageResult.success,
    shift, List.range, List.range.loop, List.foldl, Expr.rename, Expr.weakenAt,
    getter_rename _ layout, setter_rename _ layout, modified_rename, DataPlaceGuard.rename_lift, Renaming.lift]

def writtenContext (prepared : Prepared) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.rootType :: .unit ::
    OptionalCell.cellType prepared.route.rootType :: .unit :: OptionalCell.referenceType prepared.route.rootType :: context
end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedBareBitNot
end
