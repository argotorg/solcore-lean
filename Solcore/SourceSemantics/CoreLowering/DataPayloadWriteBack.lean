import Solcore.SourceSemantics.CoreLowering.DataPayloadUpdatePaths
import Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack

/-! Strong payload reconstruction and writeback through the common mapped
heap. Setter arguments may read the live root through actual Core evaluation;
they are not restricted to the pure `Selects` fragment. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
open Core Frontend Frontend.SourceInference GeneralHeap GenericHeap DataPatternValues DataEquality
open SourceCoreDataPlaces DataPayload DataPayloadReadPaths

/-- Invoke the actual closed setter after evaluating its argument. The caller
supplies the root observed by that argument and the static/source path facts;
all recursive helper evaluations are derived from the complete payload. -/
theorem setter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {rootType leaf : TypeSystem.Ty} {leafType : Ty} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys rootType prepared.route.rootType prepared.steps projections leaf leafType count)
    {cell : Dynamic.Cell} {optional value replacement : Value} {source updatedSource replacementSource : Dynamic.Value}
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (represented : DataPayload.ValueRep checked.catalog signatures functions mapping world rootType source value prepared.route.rootType)
    (replacementRep : DataPayload.ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    {environment : Environment} {before store : Store} (keyType : Ty) {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (.pair (packValues keys) replacement)) store) :
    ∃ updatedValue finalStore administrative,
      DataPayload.ValueRep checked.catalog signatures functions mapping world rootType updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment before (.apply (setter prepared keyType) argument) (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  obtain ⟨output, finalStore, admin, resultRep, evaluated, extended, counted⟩ :=
    path.update_preserves observations faithful layouts prepared keyLength represented replacementRep changed
      (value :: .pair optional (.pair (packValues keys) replacement) :: environment) store
      (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1)))
      (.var rfl) (.first (.second (.var rfl))) (.second (.second (.var rfl)))
  cases stepsEq : prepared.steps with
  | nil =>
    have emptyEval : Evaluates (value :: .pair optional (.pair (packValues keys) replacement) :: environment) store
        (update prepared prepared.steps prepared.route.rootType (.var 0) (.first (.second (.var 1))) (.second (.second (.var 1))))
        (.inRight .word replacement) store := by
      rw [stepsEq]
      exact .inRight (.second (.second (.var rfl)))
    have same := evaluation_deterministic evaluated emptyEval
    have valueSame := (Value.inRight.inj same.1).2
    subst output
    have storeSame := same.2
    rw [storeSame] at extended
    exact ⟨replacement, store, admin, resultRep,
      .apply .lambda argumentEvaluated (by simp only [stepsEq]; exact .inRight (.second (.second (.var rfl)))),
      extended, counted⟩
  | cons step steps =>
    refine ⟨output, finalStore, admin, resultRep, .apply .lambda argumentEvaluated ?_, extended, counted⟩
    simp only [stepsEq]
    exact .caseRight (root.normalizes (.first (.var rfl)) store) (by simpa only [stepsEq] using evaluated)

private theorem source_write {heap : Dynamic.Heap} {location : Dynamic.Location} {cell : Dynamic.Cell}
    (read : Dynamic.Heap.Reads heap location cell) (value : Dynamic.Value) :
    Dynamic.Heap.Writes heap location (some value) ⟨heap.cells.set location.index {cell with value := some value}⟩ := by
  have replace : ∀ {cells : List Dynamic.Cell} {index : Nat} {old : Dynamic.Cell},
      Dynamic.Heap.CellAt cells index old →
      Dynamic.Heap.CellsWrite cells index {old with value := some value} (cells.set index {old with value := some value}) := by
    intro cells index old selected
    induction selected with
    | head => exact .head
    | tail selected ih => exact .tail ih
  cases read with
  | intro selected => exact .intro (.intro selected) (replace selected)

/-- The completed reconstruction is written once into the mapped latest root.
The complete key/value payload survives; source aliases and all preexisting
administrative cells are preserved by the common GenericHeap laws. -/
theorem commit_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {leaf : TypeSystem.Ty} {leafType : Ty} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    {heap : Dynamic.Heap} {store : Store} {cell : Dynamic.Cell} {sourceLocation : Dynamic.Location} {target : Location}
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType prepared.steps projections leaf leafType count)
    (heapRelated : HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (sourceRead : Dynamic.Heap.Reads heap sourceLocation cell) {optional value replacement : Value}
    {source updatedSource replacementSource : Dynamic.Value} (coreRead : store.read? target = some optional)
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (represented : DataPayload.ValueRep checked.catalog signatures functions mapping world cell.type source value prepared.route.rootType)
    (replacementRep : DataPayload.ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ new => new = replacementSource) (some source) projections updatedSource)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression argument : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) argument)
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (argumentEvaluated : Evaluates environment store argument (.pair optional (.pair (packValues keys) replacement)) store)
    (snapshot : Option Dynamic.Value) :
    ∃ updatedValue finalHeap finalStore futureWorld,
      Dynamic.ResolvedPlaceWrites (fun _ value => value = replacementSource) heap
        ⟨sourceLocation, cell.type, leaf, projections, snapshot⟩ updatedSource finalHeap ∧
      Evaluates environment store (DataPlaceWriteBack.commit prepared keyType referenceExpression argument) (.inRight .word .unit) finalStore ∧
      WorldExtends world futureWorld ∧
      HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld finalHeap finalStore ∧
      DataPayload.ValueRep checked.catalog signatures functions mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      finalStore.read? target = some (.inRight .unit updatedValue) ∧
      AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨updatedValue, helperStore, admin, represented, evaluated, extended, counted⟩ :=
    setter_evaluates observations faithful layouts prepared keyLength path root represented replacementRep changed keyType argumentEvaluated
  obtain ⟨futureWorld, extension, helperHeap, _, administrativeFrame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heapRelated environmentTyped helperTyped evaluated extended
  have represented := represented.extend (.refl _) extension
  have sourceWritten := source_write sourceRead updatedSource
  obtain ⟨finalStore, written, finalHeap, writeFrame⟩ :=
    helperHeap.write_initialized (reference.extend (.refl _) extension) sourceRead represented sourceWritten
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heapRelated.target_lt reference.mapped)] using coreRead
  refine ⟨updatedValue, _, finalStore, futureWorld,
    .intro sourceRead rfl root.initial changed sourceWritten, ?_, extension, finalHeap, represented,
    Store.write?_reads_written written, administrativeFrame.trans writeFrame⟩
  exact LanguageResult.bind_success _ evaluated
    (.inRight (.storeCell ((referenceSelected.weaken updatedValue).evaluates helperStore)
      helperRead (.inRight (.var rfl)) written))

end Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
