import Solcore.SourceSemantics.CoreLowering.CompatiblePreparedPath
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingVirtualRoot
import Solcore.SourceSemantics.CoreLowering.CoreClosedRenaming
import Solcore.SourceSemantics.CoreLowering.LoopRenaming
import Solcore.SourceSemantics.CoreLowering.DataPlaceChildExpressions
import Solcore.SourceSemantics.CoreLowering.DataExpressionSequence

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

private theorem modified_rename (type : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) (ξ : Renaming) :
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
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) (ξ : Renaming) :
    (execute prepared reference keys rhs next outputType operator bitNot invalid).rename ξ =
      execute prepared (reference.rename ξ) (renamed keys ξ) (rhs.rename ξ) (next.rename ξ) outputType operator bitNot invalid := by
  simp [execute, renamed, LanguageResult.bind, shift, List.range, List.range.loop, List.foldl,
    Expr.rename, getter_rename path closed, setter_rename path closed, modified_rename, Renaming.lift]

end Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlace
