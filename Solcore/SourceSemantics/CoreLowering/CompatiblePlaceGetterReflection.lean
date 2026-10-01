import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceReadTotality
import Solcore.SourceSemantics.CoreLowering.CompatibleHeap

/-! Every actual completed live compatible getter has an independent source
read, exact raw missing-default fault, or absent-root fault. The source outcome
is constructed from static path/authentication receipts and the common heap;
no source projection trace or helper execution is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open CompatibleMapping CompatibleMapping.MixedPaths SourceCoreCompatibleDataPlaces

inductive ResultRep (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (cell : Dynamic.Cell) (resolved : List Dynamic.EvaluatedProjection)
    (leaf : TypeSystem.Ty) : Value → Prop where
  | read {sourceRoot selected : Dynamic.Value} {native : Value}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (selection : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
      (represented : ValueRep checked registry functions mapping world leaf selected native prepared.route.leafType) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inRight .word (.inRight .unit native))
  | missing {sourceRoot : Dynamic.Value} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
      (initial : Dynamic.RootInitialValue cell (some sourceRoot))
      (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
      (receipt : FaultToken checked registry sourceRoot prepared.steps resolved reason token count) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inLeft prepared.optionalLeaf (.word token))
  | uninitialized
      (empty : cell.value = none)
      (ordinary : ¬ ∃ key value, cell.type = .mapping key value)
      (nonempty : resolved ≠ []) :
      ResultRep checked registry functions mapping world prepared cell resolved leaf (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection))

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell}
  {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)} {leaf : TypeSystem.Ty}
  {path : PreparedPath compilation.checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}
  {identities : Dynamic.Value → Word → Prop}

private theorem present_evaluates
    {optional rootValue : Value} {sourceRoot : Dynamic.Value}
    (root : RootRead compilation.checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  rcases CompatiblePlaceReadTotality.read_or_fault arguments functionTypes root.payload leafProjected with
      ⟨selected, _, read, _⟩ | ⟨reason, fault⟩
  · have tree := arguments.readTree root.payload leafProjected read prepared
    obtain ⟨native, after, administrative, initial, _, represented, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated,
      .read initial read (represented.extend (.refl _) (.refl _) extension),
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩
  · obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
    obtain ⟨after, administrative, initial, _, evaluated, appended, _⟩ :=
      faultTree_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
    obtain ⟨futureWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := mapping) heaps.runtime_hasTypes environmentTyped helperTyped evaluated appended
    exact ⟨_, after, futureWorld, administrative, evaluated, .missing initial fault receipt,
      CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame, appended⟩

private theorem resolved_nonempty
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (nonempty : prepared.steps ≠ []) : resolved ≠ [] := by
  have general : ∀ {root leaf projections position steps sites}
      {path : PreparedPath compilation.checked source site root projections position steps sites leaf} {resolved},
      Arguments compilation.checked registry functions mapping world source site keys path resolved → steps.length = resolved.length := by
    intro root leaf projections position steps sites path resolved arguments
    induction arguments with
    | nil => rfl
    | member _ ih | index _ _ _ ih => exact congrArg Nat.succ ih
  have length := general arguments
  intro empty
  rw [empty, List.length_nil] at length
  exact nonempty (List.eq_nil_of_length_eq_zero length)

/-- Construct finite execution of the real live getter, including its source
classification and any administrative suffix, from authenticated live inputs. -/
theorem evaluates
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys)) :
    ∃ result after futureWorld administrative,
      Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after ∧
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  cases represented with
  | initialized related =>
    exact present_evaluates (.initialized read reference native related) arguments leafProjected nonempty functionTypes
      faithful observations keyLength heaps environmentTyped helperTyped referenceSelected keysSelected
  | @uninitialized sourceType payload projected =>
    by_cases mappingRoot : ∃ key value, sourceType = .mapping key value
    · obtain ⟨key, value, rfl⟩ := mappingRoot
      obtain ⟨rootValue, root⟩ := RootRead.virtual (virtual key value rfl) registryExtension projected read reference native
      exact present_evaluates root arguments leafProjected nonempty functionTypes faithful observations keyLength
        heaps environmentTyped helperTyped referenceSelected keysSelected
    · have noVirtual := ordinary (fun key value same => mappingRoot ⟨key, value, same⟩)
      have evaluated : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
          (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) store := by
        apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) native) (keysSelected.evaluates store))
        cases steps : prepared.steps with
        | nil => exact (nonempty steps).elim
        | cons head tail =>
          simp only [normalizeRoot, noVirtual, LanguageResult.failure]
          exact .caseLeft (.first (.var rfl)) (.inLeft .word)
      exact ⟨_, store, world, [], evaluated, .uninitialized rfl mappingRoot (resolved_nonempty arguments nonempty),
        heaps, .refl _, .refl _ _, by simp⟩

/-- Actual completed native execution determines an independent source
outcome without a prior source trace or a helper-execution certificate. -/
theorem reflects
    (arguments : Arguments compilation.checked registry functions mapping world source site keys path resolved)
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, cell.type = .mapping key value → VirtualRoot.Generated compilation prepared.route key value)
    (ordinary : (∀ key value, cell.type ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ []) (functionTypes : FunctionRuntimeViews functions)
    (faithful : DataEquality.IdentityFaithful identities) (observations : FunctionObservations compilation.checked.catalog functions identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    (heaps : HeapRepresents compilation.checked registry functions mapping world heap store)
    (reference : ReferenceRepresents mapping world location target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap location cell)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    {result : Value} {after : Store}
    (completed : Evaluates environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression)) result after) :
    ∃ futureWorld administrative,
      ResultRep compilation.checked registry functions mapping futureWorld prepared cell resolved leaf result ∧
      HeapRepresents compilation.checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative := by
  obtain ⟨actual, actualStore, futureWorld, administrative, evaluated, resultRep, heaps, worlds, frame, appended⟩ :=
    evaluates arguments leafProjected virtual ordinary registryExtension nonempty functionTypes faithful observations keyLength
      heaps reference read environmentTyped helperTyped referenceSelected keysSelected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed evaluated
  exact ⟨futureWorld, administrative, resultRep, heaps, worlds, frame, appended⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceGetterReflection
