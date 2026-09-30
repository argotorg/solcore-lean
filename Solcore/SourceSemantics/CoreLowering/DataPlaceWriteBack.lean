import Solcore.SourceSemantics.CoreLowering.DataPlacePathHelpers

/-! Commit an authenticated latest-root reconstruction through the common
GenericHeap relation. Helper initialization extends only the Core world; the
single subsequent source-cell write preserves aliases and old admin cells. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
open Core Frontend SourceInference SourceCoreDataPlaces DataEquality DataPatternValues GeneralHeap GenericHeap

def commit (prepared : Prepared) (keyType : Ty) (reference argument : Expr) : Expr :=
  LanguageResult.bind .unit (.apply (setter prepared keyType) argument)
    (LanguageResult.success (.storeCell (reference.weakenAt 0) (.inRight .unit (.var 0))))

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

/-- The returned root is independently represented at the source declaration's
exact type. Core typing alone is not used to authenticate the new source value.
The path tree derives the setter execution, including every comparator and
default, before the mapped cell is written once. -/
theorem commit_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {model : PayloadModel checked.catalog}
    {prepared : Prepared} {keys : List Value} {mapping : LocationMap} {world : StoreTyping}
    {heap : Dynamic.Heap} {store : Store} {cell : Dynamic.Cell} {sourceLocation : Dynamic.Location} {target : Location}
    {source updatedSource replacementSource : Dynamic.Value} {optional value replacement : Value}
    {steps : List PreparedStep} {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (heapRelated : HeapRepresents model mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (sourceRead : Dynamic.Heap.Reads heap sourceLocation cell)
    (coreRead : store.read? target = some optional)
    (root : DataPlacePathHelpers.Root prepared cell optional source value)
    (tree : DataPlaceUpdateTree.Tree checked signatures identities prepared keys replacementSource replacement
      (fun source value => model.Represents mapping world cell.type source value prepared.route.rootType)
      source value steps projections updatedSource count)
    (sameSteps : prepared.steps = steps) (faithful : IdentityFaithful identities)
    (keyLength : prepared.keyTypes.length = keys.length)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression argument : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context (.apply (setter prepared keyType) argument)
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (argumentSelected : Selects environment argument (.pair optional (.pair (packValues keys) replacement)))
    (leafSourceType : TypeSystem.Ty) (snapshot : Option Dynamic.Value) :
    ∃ updatedValue finalHeap finalStore futureWorld,
      Dynamic.ResolvedPlaceWrites (fun _ value => value = replacementSource) heap
        ⟨sourceLocation, cell.type, leafSourceType, projections, snapshot⟩ updatedSource finalHeap ∧
      Evaluates environment store (commit prepared keyType referenceExpression argument) (.inRight .word .unit) finalStore ∧
      WorldExtends world futureWorld ∧ HeapRepresents model mapping futureWorld finalHeap finalStore ∧
      model.Represents mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      finalStore.read? target = some (.inRight .unit updatedValue) ∧
      AdministrativePreserved mapping store mapping finalStore := by
  obtain ⟨updatedValue, helperStore, administrative, initial, changed, represented, evaluated, extended, counted⟩ :=
    DataPlacePathHelpers.setter_preserves root tree sameSteps faithful keyLength environment store keyType argument argumentSelected
  obtain ⟨futureWorld, extension, helperHeap, _, administrativeFrame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heapRelated environmentTyped helperTyped evaluated extended
  have represented : model.Represents mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType :=
    model.extend represented (.refl _) extension
  have sourceWritten := source_write sourceRead updatedSource
  obtain ⟨finalStore, written, finalHeap, writeFrame⟩ :=
    helperHeap.write_initialized (reference.extend (.refl _) extension) sourceRead represented sourceWritten
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heapRelated.target_lt reference.mapped)] using coreRead
  refine ⟨updatedValue, _, finalStore, futureWorld,
    .intro sourceRead rfl initial changed sourceWritten, ?_, extension, finalHeap, represented,
    Store.write?_reads_written written, administrativeFrame.trans writeFrame⟩
  · exact LanguageResult.bind_success _ evaluated
      (.inRight (.storeCell ((referenceSelected.weaken updatedValue).evaluates helperStore)
        helperRead (.inRight (.var rfl)) written))

end Solcore.SourceSemantics.CoreLowering.DataPlaceWriteBack
