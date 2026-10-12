import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEntries

/-! Observed function leaves inside products are extracted from the actual
successful output encoding and its independent Source representation. Each
leaf keeps its original raw Source type and the actual recursive codec fuel. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedPublicFunctionHistory (Entry)

/-- Structural selection of public output leaves; it contains no execution or
representation premise. Unselected subtrees may contain arbitrary data. -/
inductive Selection : TypeSystem.Ty → SourceCorePublicValues.Value → Type where
  | skip {type value} : Selection type value
  | function {type handle} : Selection type (.function handle)
  | product {a b left right}
      (leftSelected : Selection a left) (rightSelected : Selection b right) :
      Selection (.product a b) (.product left right)

def Selection.handles {sourceType publicValue} : Selection sourceType publicValue → List SourceCorePublicValues.Handle
  | .skip => []
  | @Selection.function _ handle => [handle]
  | .product left right => left.handles ++ right.handles

theorem Selection.handles_cast {sourceType first second} (same : first = second)
    (selection : Selection sourceType first) :
    (same ▸ selection : Selection sourceType second).handles = selection.handles := by
  cases same
  rfl

/-- The selected entries retain only the shapes of this output, including
its actual recursive fuel. Their meaning is derived separately from execution. -/
inductive Selected : {sourceType : TypeSystem.Ty} → {publicValue : SourceCorePublicValues.Value} →
    Selection sourceType publicValue →
    Dynamic.Value → Core.Value → Core.Ty → Nat → List Entry → Prop where
  | skip {sourceType publicValue source native type fuel} :
      Selected (Selection.skip (type := sourceType) (value := publicValue)) source native type fuel []
  | function {sourceType handle source native type fuel} :
      Selected (Selection.function (type := sourceType) (handle := handle)) source native type fuel
        [⟨sourceType, source, handle, native, type, fuel⟩]
  | product {a b left right}
      {leftSelection : Selection a left} {rightSelection : Selection b right}
      {x y p q pType qType remaining leftEntries rightEntries}
      (leftSelected : Selected leftSelection x p pType remaining leftEntries)
      (rightSelected : Selected rightSelection y q qType remaining rightEntries) :
      Selected (.product leftSelection rightSelection) (.product x y) (.pair p q)
        (.product pType qType) (remaining + 1) (leftEntries ++ rightEntries)

theorem Selected.unique {sourceType publicValue}
    {selection : Selection sourceType publicValue} {source native type fuel first second}
    (left : Selected selection source native type fuel first)
    (right : Selected selection source native type fuel second) : first = second := by
  induction left generalizing second with
  | skip => cases right; rfl
  | function => cases right; rfl
  | product leftSelected rightSelected ihLeft ihRight =>
      cases right with
      | product nextLeft nextRight => rw [ihLeft nextLeft, ihRight nextRight]

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

private theorem product_rep {expected a b : TypeSystem.Ty} {source : Dynamic.Value}
    {left right : Core.Value} {type : Core.Ty}
    (related : ValueRep checked receiving functions mapping world expected source (.pair left right) type)
    (view : SourceCoreRawMetadata.runtimeType expected =
      .product (SourceCoreRawMetadata.runtimeType a) (SourceCoreRawMetadata.runtimeType b)) :
    ∃ x y first second, source = .product x y ∧ type = .product first second ∧
      ValueRep checked receiving functions mapping world a x left first ∧
      ValueRep checked receiving functions mapping world b y right second := by
  generalize nativeEq : Core.Value.pair left right = native at related
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | unit => cases nativeEq
  | bool value => cases nativeEq
  | word value => cases nativeEq
  | integer value => cases nativeEq
  | product first second _ _ =>
      cases nativeEq
      have types := TypeSystem.Ty.product.inj view
      exact ⟨_, _, _, _, rfl, rfl, .compatible types.1.symm first, .compatible types.2.symm second⟩
  | function represented => cases view
  | proxy metadata identity registered => cases nativeEq
  | constructed metadata owner selected projected registered payloads _ => cases nativeEq
  | mappingValue metadata identity keyProjection valueProjection registered stored fallback _ _ => cases view
  | compatible same related ih => exact ih (same.symm.trans view) nativeEq
  | nil => trivial
  | cons _ _ _ _ => trivial
  | empty => trivial
  | entry _ _ _ _ _ _ => trivial
  | absent => trivial
  | present _ _ _ => trivial

/-- Every selected output function is represented in the exact returned heap
and reimports on the returned session, including functions below products. -/
theorem Selection.collect {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact}
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    (selection : Selection sourceType publicValue)
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked receiving functions mapping world sourceType source native type)
    (typed : Dynamic.ValueHasType context heap source sourceType)
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected publicValue encoded)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (payload : encoded.value = native) :
    ∃ entries : List Entry, Selected selection source native type fuel entries ∧
      entries.map Entry.handle = selection.handles ∧
      ∀ entry ∈ entries,
        session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
        ValueRep checked receiving functions mapping world entry.sourceType entry.source entry.native entry.nativeType ∧
        Dynamic.ValueHasType context heap entry.source entry.sourceType := by
  induction selection generalizing source native type fuel registry expected with
  | skip => exact ⟨[], .skip, rfl, by intro entry member; cases member⟩
  | @function rawType handle =>
      refine ⟨[⟨rawType, source, handle, native, type, fuel⟩], .function, rfl, ?_⟩
      intro entry member
      cases List.mem_singleton.mp member
      exact ⟨payload ▸ accepted.reimports_function compatible, represented, typed⟩
  | @product a b left right leftSelection rightSelection ihLeft ihRight =>
      obtain ⟨remaining, fuelEq, leftEncoded, rightEncoded, leftAccepted, rightAccepted, encodedEq⟩ :=
        accepted.product compatible.symm
      cases encodedEq
      cases payload
      obtain ⟨x, y, leftType, rightType, sourceEq, typeEq, leftRep, rightRep⟩ :=
        product_rep represented rfl
      cases sourceEq
      cases typeEq
      cases fuelEq
      have childTyped := typed.product_inv
      obtain ⟨leftEntries, leftSelected, leftHandles, leftValues⟩ := ihLeft leftRep childTyped.1 leftAccepted
        (SourceCoreRawMetadata.runtimeType_idempotent a).symm rfl
      obtain ⟨rightEntries, rightSelected, rightHandles, rightValues⟩ := ihRight rightRep childTyped.2 rightAccepted
        (SourceCoreRawMetadata.runtimeType_idempotent b).symm rfl
      refine ⟨leftEntries ++ rightEntries, .product leftSelected rightSelected, ?_, ?_⟩
      · simp only [List.map_append, leftHandles, rightHandles, Selection.handles]
      · intro entry member
        rcases List.mem_append.mp member with member | member
        · exact leftValues entry member
        · exact rightValues entry member

theorem Selected.current {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact}
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value}
    (selection : Selection sourceType publicValue)
    {source : Dynamic.Value} {native : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked receiving functions mapping world sourceType source native type)
    (typed : Dynamic.ValueHasType context heap source sourceType)
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected publicValue encoded)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (payload : encoded.value = native)
    {entries : List Entry} (receipt : Selected selection source native type fuel entries) :
    ∀ entry ∈ entries,
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
      ValueRep checked receiving functions mapping world entry.sourceType entry.source entry.native entry.nativeType ∧
      Dynamic.ValueHasType context heap entry.source entry.sourceType := by
  obtain ⟨actual, selected, _handles, meanings⟩ := selection.collect represented typed accepted compatible payload
  have same := receipt.unique selected
  cases same
  exact meanings

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
