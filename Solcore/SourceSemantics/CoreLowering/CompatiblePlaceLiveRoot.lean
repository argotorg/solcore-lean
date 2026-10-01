import Solcore.SourceSemantics.CoreLowering.CompatiblePathFaults
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingMixedRuns

/-! A local live-root receipt for compatible places. It refers to the existing
location map and source heap read, without introducing a competing heap model.
The payload is authenticated independently of native typing. Generated virtual
mapping values leave the actual optional root cell uninitialized. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

structure RootRead (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    (functions : FunctionModel checked.catalog) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (heap : Dynamic.Heap) (store : Store) (location : Dynamic.Location) (target : Location)
    (cell : Dynamic.Cell) (optional : Value) (source : Dynamic.Value) (value : Value) : Prop where
  sourceRead : Dynamic.Heap.Reads heap location cell
  reference : ReferenceRepresents mapping world location target prepared.route.rootType
  nativeRead : store.read? target = some optional
  input : RootInput prepared cell optional source value
  payload : ValueRep checked registry functions mapping world cell.type source value prepared.route.rootType

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}

theorem RootRead.initialized {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, some source, none⟩)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (native : store.read? target = some (.inRight .unit value))
    (represented : ValueRep checked registry functions mapping world sourceType source value prepared.route.rootType) :
    RootRead checked registry functions mapping world prepared heap store location target
      ⟨sourceType, some source, none⟩ (.inRight .unit value) source value :=
  ⟨read, reference, native, .initialized, represented⟩

/-- Actual describe's encoded literal supplies the virtual value and its full
raw-header/default representation; the source and native cells stay absent. -/
theorem RootRead.virtual {context : SourceCoreCompatibleDataPlaces.Context}
    {functions : FunctionModel context.checked.catalog} {key valueType : TypeSystem.Ty}
    (generated : VirtualRoot.Generated context prepared.route key valueType)
    (extension : SourceCoreRawMetadata.Extends context.registry registry)
    (projected : context.checked.catalog.project (.mapping key valueType) = .ok prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location ⟨.mapping key valueType, none, none⟩)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (native : store.read? target = some (.inLeft prepared.route.rootType .unit)) :
    ∃ value, RootRead context.checked registry functions mapping world prepared heap store location target
      ⟨.mapping key valueType, none, none⟩ (.inLeft prepared.route.rootType .unit) (.mapping key valueType []) value := by
  obtain ⟨header, layout, fallback, fields, input⟩ := generated_root generated functions mapping world extension
  have represented := fields.represents
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  exact ⟨_, read, reference, native, input, same ▸ represented⟩

/-- The helper can append administrative closures, but cannot overwrite the
live root. The finite Core world is recovered from the actual checker proof. -/
theorem RootRead.after_append {cell : Dynamic.Cell} {optional value : Value} {source : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional source value)
    {futureWorld : StoreTyping} {suffix : Store}
    (extension : WorldExtends world futureWorld) :
    RootRead checked registry functions mapping futureWorld prepared heap (store ++ suffix) location target cell optional source value := by
  have bound : target < store.length := (List.getElem?_eq_some_iff.mp root.nativeRead).1
  exact ⟨root.sourceRead, root.reference.extend (.refl _) extension,
    by simpa [Store.read?, List.getElem?_append_left bound] using root.nativeRead,
    root.input, root.payload.extend (.refl _) (.refl _) extension⟩

/-- An actual getter whose input loads the live cell. Its structural recursion
is supplied by the independently constructed tree, never an assumed execution. -/
theorem readTree_at {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot selected : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {leaf : TypeSystem.Ty} {leafCore : Ty} {resolved : List Dynamic.EvaluatedProjection} {count : Nat}
    (tree : ReadTree checked registry functions mapping world prepared keys leaf leafCore cell.type sourceRoot rootValue
      prepared.steps resolved selected count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native finalStore administrative,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected) ∧
      ValueRep checked registry functions mapping world leaf selected native leafCore ∧
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word (.inRight .unit native)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨native, finalStore, administrative, meaning, represented, evaluated, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (rootValue :: input :: environment) store (.var 0) (.second (.var 1)) (.var rfl) (.second (.var rfl))
  refine ⟨native, finalStore, administrative, root.input.initial, meaning, represented, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead) (keysSelected.evaluates store))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- Exact missing-default diagnostics from an actual live load, including the
raw metadata word of the inner mapping where selection stopped. -/
theorem faultTree_at {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {resolved : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys sourceRoot rootValue prepared.route.rootType
      prepared.steps resolved reason token count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧ Dynamic.ProjectionsFaults (some sourceRoot) resolved reason ∧
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (packValues keys)
  obtain ⟨finalStore, administrative, meaning, evaluated, _, appended, counted⟩ := tree.preserves faithful functionLeaves keyLength
    (rootValue :: input :: environment) store (.var 0) (.second (.var 1)) (.var 0) (.var rfl) (.second (.var rfl))
  refine ⟨finalStore, administrative, root.input.initial, meaning, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead) (keysSelected.evaluates store))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- An absent ordinary root fails before any projection or helper allocation.
The source observation is root absence, not an invented mapping/default fault. -/
theorem ordinary_absent_at {sourceType : TypeSystem.Ty}
    (ordinary : ∀ key value, sourceType ≠ .mapping key value)
    (read : Dynamic.Heap.Reads heap location ⟨sourceType, none, none⟩)
    (native : store.read? target = some (.inLeft prepared.route.rootType .unit))
    (noVirtual : prepared.route.rootMapping = none) (nonempty : prepared.steps ≠ [])
    {keys : Value} (environment : Environment) (keyType : Ty) (referenceExpression keyExpression : Expr)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression keys) :
    Dynamic.Heap.Reads heap location ⟨sourceType, none, none⟩ ∧
      Dynamic.RootInitialValue ⟨sourceType, none, none⟩ none ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
  refine ⟨read, .uninitialized ?_, .of_evaluates ?_⟩
  · rintro ⟨key, value, same⟩
    exact ordinary key value same
  · apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (keysSelected.evaluates store))
    cases steps : prepared.steps with
    | nil => exact (nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
