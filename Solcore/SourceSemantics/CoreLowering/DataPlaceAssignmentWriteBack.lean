import Solcore.SourceSemantics.CoreLowering.DataPayloadWriteBack
import Solcore.SourceSemantics.CoreLowering.DataPlaceSnapshot

/-! The assignment writeback phase consumes the independent latest-root
update. It derives the setter, administrative extension and single mapped
write, including plain initialization of an absent bare root.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPayloadReadPaths

/-- A source update with a snapshot-dependent modifier installs one fixed
replacement at the final leaf. This extraction preserves all intermediate
mapping lookups, defaults, insertions and constructor reconstruction. -/
theorem replacement_of_update {Modify : Dynamic.Value → Prop} {initial : Option Dynamic.Value}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate (fun _ value => Modify value) initial projections updated) :
    ∃ replacement, Modify replacement ∧
      Dynamic.ProjectionsUpdate (fun _ value => value = replacement) initial projections updated := by
  induction changed with
  | leaf modified => exact ⟨_, modified, .leaf rfl⟩
  | indexFound found _ inserted ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .indexFound found changed inserted⟩
  | indexDefault absent defaulted _ inserted ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .indexDefault absent defaulted changed inserted⟩
  | member selected _ replaced ih =>
    obtain ⟨replacement, modified, changed⟩ := ih
    exact ⟨replacement, modified, .member selected changed replaced⟩

private theorem empty_represents {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {keys : List Value} {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps [] leaf leafType count)
    {source : Dynamic.Value} {value : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world leaf source value leafType) :
    ValueRep checked.catalog signatures functions mapping world root source value type := by
  generalize projectionsEq : ([] : List Dynamic.EvaluatedProjection) = projections at path
  induction path with
  | nil => exact represented
  | member => cases projectionsEq
  | index => cases projectionsEq
  | comptime _ ih => exact .comptime (ih represented projectionsEq)

theorem setter_evaluates {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {cell : Dynamic.Cell} {optional replacement : Value} {initial : Option Dynamic.Value}
    {updatedSource replacementSource : Dynamic.Value} {leaf : TypeSystem.Ty}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type)
    (cellRep : GenericHeap.CellRepresents (payloadModel checked.catalog signatures functions) mapping world
      cell optional prepared.route.rootType)
    (root : Dynamic.RootInitialValue cell initial)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) initial projections updatedSource)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {environment : Environment} {before store : Store} {keyType : Ty} {argument : Expr}
    (argumentEvaluated : Evaluates environment before argument (.pair optional (.pair (packValues keys) replacement)) store) :
    ∃ updatedValue finalStore administrative,
      ValueRep checked.catalog signatures functions mapping world cell.type updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment before (.apply (setter prepared keyType) argument) (.inRight .word updatedValue) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length = 2 * count := by
  cases initial with
  | some source =>
    obtain ⟨value, normalized, represented⟩ := DataPlaceSnapshot.root_present rootLayout cellRep root
    exact DataPayloadWriteBack.setter_evaluates observations faithful layouts prepared keyLength path
      normalized represented replacementRep changed keyType argumentEvaluated
  | none =>
    cases changed with
    | leaf same =>
      subst updatedSource
      obtain ⟨empty, _, rfl⟩ := DataPlaceSnapshot.path_empty path
      exact ⟨replacement, store, [], empty_represents path replacementRep,
        .apply .lambda argumentEvaluated (by simp only [empty]; exact .inRight (.second (.second (.var rfl)))),
        by simp, rfl⟩

/-- No modifier, getter or setter runtime behavior is assumed. The actual
setter argument loads the current mapped root, and the source's own write
determines the final heap. The returned evaluation/write witnesses compose
directly with execute_success. -/
theorem preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : DataEquality.IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {heap after : Dynamic.Heap} {store : Store} {sourceLocation : Dynamic.Location} {target : Location}
    {cell : Dynamic.Cell} {replacement : Value} {initial : Option Dynamic.Value}
    {updatedSource replacementSource : Dynamic.Value} {leaf : TypeSystem.Ty}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (heaps : GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping world heap store)
    (reference : ReferenceRepresents mapping world sourceLocation target prepared.route.rootType)
    (read : Dynamic.Heap.Reads heap sourceLocation cell)
    (rootLayout : DataPlaceSnapshot.RootLayout checked.catalog prepared cell.type)
    (root : Dynamic.RootInitialValue cell initial)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) initial projections updatedSource)
    (written : Dynamic.Heap.Writes heap sourceLocation (some updatedSource) after)
    (path : Path checked signatures functions mapping world keys cell.type prepared.route.rootType
      prepared.steps projections leaf prepared.route.leafType count)
    (replacementRep : ValueRep checked.catalog signatures functions mapping world leaf replacementSource replacement prepared.route.leafType)
    {environment : Environment} {context : Core.Context} {keyType : Ty} {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment context checked.catalog.definitions)
    (helperTyped : HasType context
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) checked.catalog.definitions)
    (referenceSelected : DataEquality.Selects environment referenceExpression
      (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : DataEquality.Selects environment keyExpression (packValues keys))
    (replacementSelected : DataEquality.Selects environment replacementExpression replacement) :
    ∃ updatedValue helperStore finalStore futureWorld old,
      ValueRep checked.catalog signatures functions mapping futureWorld cell.type updatedSource updatedValue prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word updatedValue) helperStore ∧
      helperStore.read? target = some old ∧ helperStore.write? target (.inRight .unit updatedValue) = some finalStore ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (payloadModel checked.catalog signatures functions) mapping futureWorld after finalStore ∧
      AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after := by
  obtain ⟨optional, coreRead, cellRep⟩ := DataPlaceSnapshot.read_at heaps reference read
  have argument : Evaluates environment store (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression))
      (.pair optional (.pair (packValues keys) replacement)) store :=
    .pair (.loadCell (referenceSelected.evaluates store) coreRead)
      (.pair (keysSelected.evaluates store) (replacementSelected.evaluates store))
  obtain ⟨updatedValue, helperStore, administrative, represented, evaluated, extended, _⟩ :=
    setter_evaluates observations faithful layouts prepared keyLength rootLayout cellRep root changed path replacementRep argument
  obtain ⟨futureWorld, extension, helperHeaps, _, frame⟩ :=
    DataMappingHeap.evaluation_preserves_frame heaps environmentTyped helperTyped evaluated extended
  have futureRep := represented.extend (.refl _) extension
  obtain ⟨finalStore, coreWritten, finalHeaps, writeFrame⟩ :=
    helperHeaps.write_initialized (reference.extend (.refl _) extension) read futureRep written
  have helperRead : helperStore.read? target = some optional := by
    rw [extended]
    simpa [Store.read?, List.getElem?_append_left (heaps.target_lt reference.mapped)] using coreRead
  exact ⟨updatedValue, helperStore, finalStore, futureWorld, optional, futureRep, evaluated,
    helperRead, coreWritten, extension, finalHeaps, frame.trans writeFrame, .of_write written⟩

end Solcore.SourceSemantics.CoreLowering.DataPlaceAssignmentWriteBack
