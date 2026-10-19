import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceSetterFault
import Solcore.SourceSemantics.CoreLowering.CellMappingHeap

/-! A structural source fault in the latest root derives a failed actual setter
load. The raw key guard and missing-default metadata come from the independent
fault trace. Administrative comparisons may allocate; no source cell is written.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterFault
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces CompatibleMapping.MixedPaths

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {prepared : Prepared} {heap : Dynamic.Heap} {store : Store} {location : Dynamic.Location} {target : Location}
  {cell : Dynamic.Cell} {optional rootValue : Value} {sourceRoot : Dynamic.Value}

/-- The source fault automatically supplies the exact token and fault tree.
Finite Core preservation and the real administrative suffix transport the
common heap; the latest source and native root remain unchanged. -/
theorem preserves {cells : GenericHeap.CellModel ambient.definitions}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : GenericHeap.CellHeapRepresents cells mapping world heap store)
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
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context ambient.definitions)
    (setterTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement) :
    ∃ token count after administrative futureWorld,
      FaultToken checked registry sourceRoot prepared.steps projections reason token count ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inLeft prepared.route.rootType (.word token)) after ∧
      GenericHeap.CellHeapRepresents cells mapping futureWorld heap after ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping after ∧
      RootRead checked registry functions mapping futureWorld prepared heap after location target cell optional sourceRoot rootValue ∧
      after = store ++ administrative ∧ administrative.length = count := by
  obtain ⟨token, count, receipt, tree⟩ := arguments.faultTree root.payload fault prepared
  obtain ⟨after, administrative, evaluated, appended, counted⟩ :=
    CompatiblePlaceSetterFault.setter_at root tree nonempty faithful observations keyLength environment keyType referenceExpression keyExpression replacementExpression replacement
      referenceSelected keysSelected replacementSelected
  obtain ⟨futureWorld, extension, finalHeaps, _, frame⟩ := CellMappingHeap.evaluation_preserves_frame heaps environmentTyped setterTyped evaluated appended
  exact ⟨token, count, after, administrative, futureWorld, receipt, evaluated,
    finalHeaps, extension, frame,
    by rw [appended]; exact root.after_append extension, appended, counted⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleCellPlaceSetterFault
