import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot

/-! Live snapshot observations from real static path receipts and independent
source reads/faults. Only pure reference/key selections are premises; native
load, recursive helpers, sufficient fuel and completed-run reflection are
constructed here. A final checker receipt gives the extended finite world.
This is the local snapshot phase, not an alternate whole-heap relation or a
proof of source key/RHS expression lowering. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality DataEquality DataPatternValues
open SourceCoreCompatibleDataPlaces CompatibleMapping CompatibleMapping.MixedPaths CompatibleMixedRoute

/-- Finite Core preservation accounts for the real helper allocations. Every
old cell, including the live root and prior administrative cells, is unchanged. -/
theorem evaluation_frame {definitions : DataEnvironment} {mapping : LocationMap} {world : StoreTyping}
    {environment : Environment} {context : Core.Context} {store after : Store} {expression : Expr} {value : Value} {type : Ty}
    (storeTyped : RuntimeStoreHasTypes world store definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context definitions)
    (expressionTyped : HasType context expression type definitions)
    (evaluated : Evaluates environment store expression value after)
    {suffix : Store} (appended : after = store ++ suffix) :
    ∃ futureWorld, WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after definitions ∧
      RuntimeValueHasType futureWorld value type definitions ∧ AdministrativePreserved mapping store mapping after := by
  obtain ⟨futureWorld, extension, storeTyped, valueTyped⟩ :=
    evaluation_preserves_type evaluated expressionTyped environmentTyped storeTyped
  refine ⟨futureWorld, extension, storeTyped, valueTyped, ?_⟩
  subst after
  intro index absent bound
  exact ⟨absent, by simp [Store.read?, List.getElem?_append_left bound]⟩

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
  {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {prepared : Prepared}
  {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}
  {leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
  {path : PreparedPath checked source site cell.type projections position prepared.steps keySites leaf}
  {keys : List Value} {resolved : List Dynamic.EvaluatedProjection}
  {identities : Dynamic.Value → Word → Prop}
  {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression : Expr}

/-- Successful independent path reads produce actual live-root Core snapshots;
the final root receipt certifies that virtual defaults did not initialize it. -/
theorem read_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    (leafProjected : checked.catalog.project leaf = .ok prepared.route.leafType)
    {selected : Dynamic.Value} (read : Dynamic.ProjectionsRead (some sourceRoot) resolved (some selected))
    (nonempty : prepared.steps ≠ []) (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ native after administrative futureWorld,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      ValueRep checked registry functions mapping futureWorld leaf selected native prepared.route.leafType ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inRight .word (.inRight .unit native)) after ∧
      WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after checked.catalog.definitions ∧
      RuntimeValueHasType futureWorld (.inRight .word (.inRight .unit native))
        (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      AdministrativePreserved mapping store mapping after ∧
      after = store ++ administrative ∧ administrative.length = readCost checked prepared.steps := by
  have tree := arguments.readTree root.payload leafProjected read prepared
  obtain ⟨native, after, administrative, initial, _, represented, evaluated, appended, counted⟩ :=
    readTree_at root tree nonempty faithful functionLeaves keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
  obtain ⟨futureWorld, extension, typedStore, typedValue, frame⟩ :=
    evaluation_frame (mapping := mapping) storeTyped environmentTyped helperTyped evaluated appended
  refine ⟨native, after, administrative, futureWorld, initial,
    represented.extend (.refl _) (.refl _) extension, .of_evaluates evaluated,
    extension, typedStore, typedValue, ?_, frame, appended, counted⟩
  rw [appended]
  exact root.after_append extension

/-- Source structural faults determine the exact raw metadata token and every
completed live getter result. The actual source and native root cells survive. -/
theorem fault_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (arguments : Arguments checked registry functions mapping world source site keys path resolved)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) resolved reason)
    (nonempty : prepared.steps ≠ []) (faithful : IdentityFaithful identities)
    (functionLeaves : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (storeTyped : RuntimeStoreHasTypes world store checked.catalog.definitions)
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
      (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ token count after administrative futureWorld,
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken checked registry sourceRoot prepared.steps resolved reason token count ∧
      FiniteRun environment store (.apply (getter prepared keyType) (.pair (.loadCell referenceExpression) keyExpression))
        (.inLeft prepared.optionalLeaf (.word token)) after ∧
      WorldExtends world futureWorld ∧ RuntimeStoreHasTypes futureWorld after checked.catalog.definitions ∧
      RuntimeValueHasType futureWorld (.inLeft prepared.optionalLeaf (.word token))
        (LanguageResult.resultType prepared.optionalLeaf) checked.catalog.definitions ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      AdministrativePreserved mapping store mapping after ∧ after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, initial, _, evaluated, appended, counted⟩ :=
    faultTree_at root tree nonempty faithful functionLeaves keyLength environment keyType referenceExpression keyExpression referenceSelected keysSelected
  obtain ⟨futureWorld, extension, typedStore, typedValue, frame⟩ :=
    evaluation_frame (mapping := mapping) storeTyped environmentTyped helperTyped evaluated appended
  refine ⟨token, count, after, administrative, futureWorld, initial, receipt, .of_evaluates evaluated,
    extension, typedStore, typedValue, ?_, frame, appended, counted⟩
  rw [appended]
  exact root.after_append extension

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceLiveRoot
