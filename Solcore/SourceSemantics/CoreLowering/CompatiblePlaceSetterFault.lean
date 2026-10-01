import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback

/-! A structural source fault in the latest root derives a failed actual setter
load. The raw key guard and missing-default metadata come from the independent
fault trace. Administrative comparisons may allocate; no source cell is written.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- Actual load plus the generated structural recursion. Replacement is only
an already evaluated value; a fault never executes an insertion or root write. -/
theorem setter_at
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection} {reason : Dynamic.SemanticFault} {token : Word} {count : Nat}
    (tree : FaultTree checked registry functions mapping world prepared keys sourceRoot rootValue prepared.route.rootType
      prepared.steps projections reason token count)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    (environment : Environment) (keyType : Ty) (referenceExpression keyExpression replacementExpression : Expr) (replacement : Value)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ after administrative,
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      after = store ++ administrative ∧ administrative.length = count := by
  let input := Value.pair optional (.pair (packValues keys) replacement)
  obtain ⟨after, administrative, _, _, evaluated, appended, counted⟩ := tree.preserves faithful observations keyLength
    (rootValue :: input :: environment) store (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
    (.var rfl) (.first (.second (.var rfl)))
  refine ⟨after, administrative, ?_, appended, counted⟩
  apply Evaluates.apply .lambda (.pair (.loadCell (referenceSelected.evaluates store) root.nativeRead)
    (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store)))
  cases steps : prepared.steps with
  | nil => exact (nonempty steps).elim
  | cons head tail =>
    simp only [steps] at evaluated ⊢
    exact .caseRight (root.input.normalize _ store (.first (.var 0)) (.first (.var rfl))) evaluated

/-- The source fault automatically supplies the exact token and fault tree.
Finite Core preservation and the real administrative suffix transport the
common heap; the latest source and native root remain unchanged. -/
theorem preserves
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {reason : Dynamic.SemanticFault} (fault : Dynamic.ProjectionsFaults (some sourceRoot) projections reason)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {replacement : Value}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ token count after administrative futureWorld,
      FaultToken checked registry sourceRoot prepared.steps projections reason token count ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      HeapRepresents checked registry functions mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, evaluated, appended, counted⟩ :=
    setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression replacement
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, typedStore, _, frame⟩ := evaluation_frame heaps.runtime_hasTypes environmentTyped setterTyped evaluated appended
  exact ⟨token, count, after, administrative, futureWorld, receipt, evaluated,
    CompatibleHeap.HeapRepresents.after_snapshot heaps extension typedStore appended, extension, frame,
    by rw [appended]; exact root.after_append extension, appended, counted⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
