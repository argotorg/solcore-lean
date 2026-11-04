import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicArgumentReceipts
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.ExpressionIndices
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicInputRegistries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.Selected.NamedAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicPhysicalApplications
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.PublicRoots
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.HeadersAndPrograms
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.RuntimeProfileFactories

/-!
# Recursive named public results: nested inputs and outputs

Encoding of nested and returned inputs, history entries, output selections and collection, and the runtime factory meaning that consumes them.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEntries
/-! One prior function export keeps its original handle, raw Source type,
independent Source value and exact native payload. Its validation budget is
the budget of that export, independent of later input-validation budgets. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
open Core Frontend SourceInference

structure Entry where
  sourceType : TypeSystem.Ty
  source : Dynamic.Value
  handle : SourceCorePublicValues.Handle
  native : Core.Value
  nativeType : Core.Ty
  fuel : Nat

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
/-! Ordered structural selection of exported functions in products, constructor
payloads and mapping rows. The selected receipt keeps codec authentication and
static projections; Source meaning is recovered from the independent result. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedPublicFunctionHistory (Entry)

mutual
inductive Selection : TypeSystem.Ty → SourceCorePublicValues.Value → Type where
  | skip {type value} : Selection type value
  | function {type handle} : Selection type (.function handle)
  | product {a b left right} (first : Selection a left) (second : Selection b right) :
      Selection (.product a b) (.product left right)
  | constructed {type metadata values} (children : PayloadSelection metadata.payloadTypes values) :
      Selection type (.constructed metadata values)
  | mapping {key value rows} (children : EntrySelection key value rows) :
      Selection (.mapping key value) (.mapping key value rows)
inductive PayloadSelection : List TypeSystem.Ty → List SourceCorePublicValues.Value → Type where
  | nil : PayloadSelection [] []
  | cons {type types value values} (head : Selection type value)
      (tail : PayloadSelection types values) : PayloadSelection (type :: types) (value :: values)
inductive EntrySelection : (key value : TypeSystem.Ty) →
    List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) → Type where
  | empty {key value} : EntrySelection key value []
  | entry {key value a b rows} (first : Selection key a) (second : Selection value b)
      (tail : EntrySelection key value rows) : EntrySelection key value ((a,b) :: rows)
end
mutual
def Selection.handles {type value} : Selection type value → List SourceCorePublicValues.Handle
  | .skip => []
  | @Selection.function _ handle => [handle]
  | .product first second => first.handles ++ second.handles
  | .constructed children => children.handles
  | .mapping children => children.handles
def PayloadSelection.handles {types values} : PayloadSelection types values → List SourceCorePublicValues.Handle
  | .nil => []
  | .cons head tail => head.handles ++ tail.handles
def EntrySelection.handles {key value rows} : EntrySelection key value rows → List SourceCorePublicValues.Handle
  | .empty => []
  | .entry first second tail => first.handles ++ second.handles ++ tail.handles
end

theorem Selection.handles_cast {type first second} (same : first = second) (selection : Selection type first) :
    (same ▸ selection : Selection type second).handles = selection.handles := by cases same; rfl

mutual
inductive Selected (checked : SourceCoreCompatibleCatalog.Checked)
    {artifact : SourceCoreIndexedSession.Artifact} (session : SourceCoreIndexedSession.Session artifact) :
    {sourceType : TypeSystem.Ty} → {publicValue : SourceCorePublicValues.Value} →
    Selection sourceType publicValue → Dynamic.Value → Core.Value → Core.Ty → Nat → List Entry → Prop where
  | skip {sourceType publicValue source native type fuel} :
      Selected checked session (Selection.skip (type := sourceType) (value := publicValue)) source native type fuel []
  | function {sourceType handle source native type fuel}
      (imported : session.EncodesAt fuel sourceType (.function handle) native) :
      Selected checked session (Selection.function (type := sourceType) (handle := handle)) source native type fuel
        [⟨sourceType, source, handle, native, type, fuel⟩]
  | product {a b left right} {first : Selection a left} {second : Selection b right}
      {x y p q pType qType remaining firstEntries secondEntries}
      (firstSelected : Selected checked session first x p pType remaining firstEntries)
      (secondSelected : Selected checked session second y q qType remaining secondEntries) :
      Selected checked session (.product first second) (.product x y) (.pair p q)
        (.product pType qType) (remaining + 1) (firstEntries ++ secondEntries)
  | constructed {sourceType metadata publicValues}
      {selection : PayloadSelection metadata.payloadTypes publicValues}
      {sources values types tag id remaining entries}
      (projection : metadata.payloadTypes.mapM checked.catalog.project = .ok types)
      (children : PayloadSelected checked session selection sources values types remaining entries) :
      Selected checked session (Selection.constructed (type := sourceType) selection)
        (.constructed metadata sources) (.constructed tag (.pair (.word id) (DataPatternValues.packValues values)))
        (.namedData tag.owner) (remaining + 1) entries
  | mapping {key value publicRows} {selection : EntrySelection key value publicRows}
      {sources rows layout id fallback remaining entries}
      (registered : layout.Registered checked.catalog.definitions)
      (children : EntriesSelected checked session selection sources rows layout.keyType layout.valueType remaining entries) :
      Selected checked session (.mapping selection) (.mapping key value sources)
        (SourceCoreMappingWithDefault.value id fallback layout rows)
        (SourceCoreMappingWithDefault.type layout) (remaining + 1) entries
inductive PayloadSelected (checked : SourceCoreCompatibleCatalog.Checked)
    {artifact : SourceCoreIndexedSession.Artifact} (session : SourceCoreIndexedSession.Session artifact) :
    {types : List TypeSystem.Ty} → {publicValues : List SourceCorePublicValues.Value} →
    PayloadSelection types publicValues → List Dynamic.Value → List Core.Value → List Core.Ty → Nat → List Entry → Prop where
  | none {fuel} : PayloadSelected checked session .nil [] [] [] fuel []
  | one {sourceType publicValue} {selection : Selection sourceType publicValue}
      {source native type remaining entries}
      (head : Selected checked session selection source native type remaining entries) :
      PayloadSelected checked session (.cons selection .nil) [source] [native] [type] (remaining + 1) entries
  | more {sourceType nextType sourceTypes publicValue nextValue publicValues}
      {selection : Selection sourceType publicValue}
      {tail : PayloadSelection (nextType :: sourceTypes) (nextValue :: publicValues)}
      {source sources native natives type types remaining entries rest}
      (head : Selected checked session selection source native type remaining entries)
      (children : PayloadSelected checked session tail sources natives types remaining rest) :
      PayloadSelected checked session (.cons selection tail) (source :: sources) (native :: natives) (type :: types)
        (remaining + 1) (entries ++ rest)
inductive EntriesSelected (checked : SourceCoreCompatibleCatalog.Checked)
    {artifact : SourceCoreIndexedSession.Artifact} (session : SourceCoreIndexedSession.Session artifact)
    : {key value : TypeSystem.Ty} → {publicRows : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)} →
    EntrySelection key value publicRows → List (Dynamic.Value × Dynamic.Value) → OrderedMapping.Entries →
    Core.Ty → Core.Ty → Nat → List Entry → Prop where
  | empty {key value keyType valueType fuel} : EntriesSelected checked session (EntrySelection.empty (key := key) (value := value)) [] [] keyType valueType fuel []
  | entry {key value a b publicRows} {first : Selection key a} {second : Selection value b}
      {tail : EntrySelection key value publicRows}
      {sourceKey sourceValue sources nativeKey nativeValue natives keyType valueType remaining keys values rest}
      (firstSelected : Selected checked session first sourceKey nativeKey keyType remaining keys)
      (secondSelected : Selected checked session second sourceValue nativeValue valueType remaining values)
      (children : EntriesSelected checked session tail sources natives keyType valueType remaining rest) :
      EntriesSelected checked session (.entry first second tail) ((sourceKey,sourceValue) :: sources)
        ((nativeKey,nativeValue) :: natives) keyType valueType (remaining + 1) (keys ++ values ++ rest)
end

private theorem pack_injective {left right : List Core.Value} (length : left.length = right.length)
    (same : DataPatternValues.packValues left = DataPatternValues.packValues right) : left = right := by
  induction left generalizing right with
  | nil => cases right <;> simp_all
  | cons head tail ih =>
      cases right with
      | nil => simp at length
      | cons next rest =>
          cases tail with
          | nil => cases rest <;> simp_all [DataPatternValues.packValues]
          | cons item items =>
              cases rest with
              | nil => simp at length
              | cons last lasts =>
                  have parts := Core.Value.pair.inj same
                  exact congr (congrArg List.cons parts.1) (ih (by simpa using length) parts.2)

private theorem mapping_encode_injective (layout : OrderedMapping.Layout) {left right : OrderedMapping.Entries}
    (same : OrderedMapping.encode layout left = OrderedMapping.encode layout right) : left = right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons head tail => cases head; cases same
  | cons head tail ih =>
      cases right with
      | nil => cases head; cases same
      | cons next rest =>
          cases head; cases next
          simp only [OrderedMapping.encode, Core.Value.constructed.injEq, Core.Value.pair.injEq, true_and] at same
          exact congr (congrArg List.cons (Prod.ext same.1.1 same.1.2)) (ih same.2)

private theorem values_length {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {types sources values coreTypes} (represented : ValuesRep checked registry functions mapping world types sources values coreTypes) :
    sources.length = values.length := represented.length.1.symm.trans represented.length.2.1

private theorem selected_payload_length {checked : SourceCoreCompatibleCatalog.Checked}
    {artifact : SourceCoreIndexedSession.Artifact} {session : SourceCoreIndexedSession.Session artifact}
    {types publicValues} {selection : PayloadSelection types publicValues} {sources values coreTypes fuel entries}
    (selected : PayloadSelected checked session selection sources values coreTypes fuel entries) :
    sources.length = values.length := by
  induction selected using PayloadSelected.rec
    (motive_1 := fun {_ _} _ _ _ _ _ _ _ => True)
    (motive_3 := fun {_ _ _} _ _ _ _ _ _ _ _ => True) with
  | none => rfl
  | one => rfl
  | more _ _ _ ih => simpa using ih
  | skip | function | product | constructed | mapping | empty | entry => trivial


variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

theorem product_rep {expected a b : TypeSystem.Ty} {source : Dynamic.Value}
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
  | nil | cons | empty | entry | absent | present => trivial

private theorem constructor_typed {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {metadata : DataConstructorInstantiation} {sources : List Dynamic.Value} {type : TypeSystem.Ty}
    (typed : Dynamic.ValueHasType context heap (.constructed metadata sources) type) :
    Dynamic.ValuesHaveTypes context heap sources metadata.payloadTypes := by
  cases typed with
  | constructed _ typed => exact typed
  | comptime inner => exact constructor_typed inner
termination_by sizeOf type

private theorem constructed_rep {sourceType metadata sources values types tag id}
    (projection : metadata.payloadTypes.mapM checked.catalog.project = .ok types)
    (length : sources.length = values.length)
    (represented : ValueRep checked receiving functions mapping world sourceType (.constructed metadata sources)
      (.constructed tag (.pair (.word id) (DataPatternValues.packValues values))) (.namedData tag.owner)) :
    ValuesRep checked receiving functions mapping world metadata.payloadTypes sources values types := by
  obtain ⟨actualTag, actualId, actualValues, actualTypes, nativeEq, _, fields⟩ := constructor_fields represented rfl
  have typesEq := Except.ok.inj (fields.payloads.projection.symm.trans projection)
  cases typesEq
  have same := Core.Value.constructed.inj nativeEq
  have packed := (Core.Value.pair.inj same.2).2
  have valuesEq := pack_injective (length.symm.trans (values_length fields.payloads)) packed
  cases valuesEq
  exact fields.payloads

private theorem mapping_rep {key value sources rows layout id fallback}
    (registered : layout.Registered checked.catalog.definitions)
    (represented : ValueRep checked receiving functions mapping world (.mapping key value) (.mapping key value sources)
      (SourceCoreMappingWithDefault.value id fallback layout rows) (SourceCoreMappingWithDefault.type layout)) :
    EntriesRep checked receiving functions mapping world key value sources rows layout.keyType layout.valueType := by
  obtain ⟨actualId, actualLayout, actualRows, actualFallback, nativeEq, typeEq, _, fields⟩ :=
    CompatibleMapping.mapping_fields represented rfl
  have layoutEq := CompatibleMapping.registered_layout_eq fields.registered registered typeEq.symm
  cases layoutEq
  have encoded : OrderedMapping.encode layout rows = OrderedMapping.encode layout actualRows :=
    (Core.Value.pair.inj (Core.Value.pair.inj nativeEq).2).2
  have rowsEq := mapping_encode_injective layout encoded
  cases rowsEq
  exact fields.stored

private def EntriesCurrent {artifact : SourceCoreIndexedSession.Artifact}
    (session : SourceCoreIndexedSession.Session artifact) (context : SourceSemantics.Context) (heap : Dynamic.Heap)
    (entries : List Entry) : Prop :=
  ∀ entry ∈ entries,
    session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
    ValueRep checked receiving functions mapping world entry.sourceType entry.source entry.native entry.nativeType ∧
    Dynamic.ValueHasType context heap entry.source entry.sourceType

private theorem EntriesCurrent.append {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {first second : List Entry}
    (a : EntriesCurrent (functions := functions) (receiving := receiving) (mapping := mapping) (world := world) session context heap first)
    (b : EntriesCurrent (functions := functions) (receiving := receiving) (mapping := mapping) (world := world) session context heap second) :
    EntriesCurrent (functions := functions) (receiving := receiving) (mapping := mapping) (world := world) session context heap (first ++ second) := by
  intro entry member
  rcases List.mem_append.mp member with member | member
  · exact a entry member
  · exact b entry member

/-- A selected receipt contains no Source representation or typing premise.
Both properties are recovered from the independently represented whole result. -/
theorem Selected.current {artifact : SourceCoreIndexedSession.Artifact}
    {session : SourceCoreIndexedSession.Session artifact}
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {sourceType publicValue} {selection : Selection sourceType publicValue}
    {source native type fuel entries}
    (selected : Selected checked session selection source native type fuel entries)
    (represented : ValueRep checked receiving functions mapping world sourceType source native type)
    (typed : Dynamic.ValueHasType context heap source sourceType) :
    ∀ entry ∈ entries,
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
      ValueRep checked receiving functions mapping world entry.sourceType entry.source entry.native entry.nativeType ∧
      Dynamic.ValueHasType context heap entry.source entry.sourceType := by
  induction selected using Selected.rec
    (motive_2 := fun {types _} _ sources values coreTypes _ entries _ =>
      ValuesRep checked receiving functions mapping world types sources values coreTypes →
      Dynamic.ValuesHaveTypes context heap sources types →
      EntriesCurrent (functions := functions) (receiving := receiving) (mapping := mapping) (world := world) session context heap entries)
    (motive_3 := fun {key value _} _ sources values keyType valueType _ entries _ =>
      EntriesRep checked receiving functions mapping world key value sources values keyType valueType →
      Dynamic.MappingEntriesHaveTypes context heap sources key value →
      EntriesCurrent (functions := functions) (receiving := receiving) (mapping := mapping) (world := world) session context heap entries) with
  | skip => intro entry member; cases member
  | function imported =>
      intro entry member
      cases List.mem_singleton.mp member
      exact ⟨imported, represented, typed⟩
  | product first second firstIH secondIH =>
      obtain ⟨_, _, _, _, sourceEq, typeEq, firstRep, secondRep⟩ := product_rep represented rfl
      cases sourceEq; cases typeEq
      exact EntriesCurrent.append (firstIH firstRep typed.product_inv.1) (secondIH secondRep typed.product_inv.2)
  | constructed projection children ih =>
      exact ih (constructed_rep projection (selected_payload_length children) represented) (constructor_typed typed)
  | mapping registered children ih =>
      exact ih (mapping_rep registered represented) typed.mapping_exact_inv
  | none => intro entry member; cases member
  | one _ ih =>
      rename_i related typed
      cases related with
      | cons head tail => cases typed with
        | cons first rest => exact ih head first
  | more head children firstIH restIH =>
      rename_i related typed
      cases related with
      | cons first rest => cases typed with
        | cons firstTyped restTyped => exact EntriesCurrent.append (firstIH first firstTyped) (restIH rest restTyped)
  | empty => intro entry member; cases member
  | entry first second children firstIH secondIH restIH =>
      rename_i related typed
      cases related with
      | entry firstRep secondRep restRep => cases typed with
        | cons firstTyped secondTyped restTyped =>
            exact EntriesCurrent.append (EntriesCurrent.append (firstIH firstRep firstTyped) (secondIH secondRep secondTyped))
              (restIH restRep restTyped)

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputCollection
/-! Recover structural function selections from the real recursive output
encoder. Registry extension is used in its forward direction to authenticate
exact constructor and mapping metadata. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedPublicFunctionHistory (Entry)
open SourceCoreIndexedSession

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

private theorem source_constructor {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Core.Value} {type : Core.Ty}
    (related : ValueRep checked receiving functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

private theorem constructed_children {sourceType expected : TypeSystem.Ty} {source : Dynamic.Value}
    {registry : SourceCoreRawMetadata.Registry} {metadata : DataConstructorInstantiation}
    (inserted : SourceCoreRawMetadata.Inserted registry expected (.constructor metadata))
    {tag : ConstructorId} {payload : Core.Value} {type : Core.Ty}
    (represented : ValueRep checked receiving functions mapping world sourceType source
      (.constructed tag (.pair (.word inserted.id) payload)) type)
    (view : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ sources values types, source = .constructed metadata sources ∧ type = .namedData tag.owner ∧
      payload = DataPatternValues.packValues values ∧
      ValuesRep checked receiving functions mapping world metadata.payloadTypes sources values types := by
  obtain ⟨signature, constructor, arguments, _, _, _, _, _, resultType⟩ :=
    CompatibleConstructorMetadata.facts inserted.authenticated
  have nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) =
      some (signature.id, arguments.map SourceCoreRawMetadata.runtimeType) := by
    rw [view, inserted.runtime_compatible]
    change SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType metadata.resultType) = _
    rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal]
  obtain ⟨actual, sources, sourceEq⟩ := source_constructor represented nominal
  cases sourceEq
  obtain ⟨actualTag, actualId, values, types, nativeEq, typeEq, fields⟩ := constructor_fields represented rfl
  have parts := Core.Value.constructed.inj nativeEq
  have children := Core.Value.pair.inj parts.2
  have idEq := Core.Value.word.inj children.1
  have original := (prior.trans inserted.preserves).lookup fields.metadataRep.lookup
  rw [← idEq] at original
  have metadataEq := SourceCoreRawMetadata.Metadata.constructor.inj (Option.some.inj (original.symm.trans inserted.reconstruct))
  cases metadataEq
  cases parts.1
  exact ⟨sources, values, types, rfl, typeEq, children.2, fields.payloads⟩

private theorem mapping_children {key value : TypeSystem.Ty} {source : Dynamic.Value}
    {expected : TypeSystem.Ty} {registry : SourceCoreRawMetadata.Registry}
    (inserted : SourceCoreRawMetadata.Inserted registry expected (.mapping key value))
    {layout : OrderedMapping.Layout} {rows fallback : Core.Value}
    (represented : ValueRep checked receiving functions mapping world (.mapping key value) source
      (.pair (.word inserted.id) (.pair fallback rows)) (SourceCoreMappingWithDefault.type layout))
    (registered : layout.Registered checked.catalog.definitions)
    (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ sources values default, source = .mapping key value sources ∧
      rows = OrderedMapping.encode layout values ∧ fallback = OrderedMapping.optionValue layout.valueType default ∧
      EntriesRep checked receiving functions mapping world key value sources values layout.keyType layout.valueType := by
  obtain ⟨actualKey, actualValue, sources, sourceEq⟩ := CompatibleExpressionIndices.source_mapping represented rfl
  cases sourceEq
  obtain ⟨actualId, actualLayout, values, default, nativeEq, typeEq, _, fields⟩ :=
    CompatibleMapping.mapping_fields represented rfl
  have layoutEq := CompatibleMapping.registered_layout_eq fields.registered registered typeEq.symm
  cases layoutEq
  have parts := Core.Value.pair.inj nativeEq
  have idEq := Core.Value.word.inj parts.1
  have original := (prior.trans inserted.preserves).lookup fields.metadata.lookup
  rw [← idEq] at original
  have metadataEq := SourceCoreRawMetadata.Metadata.mapping.inj (Option.some.inj (original.symm.trans inserted.reconstruct))
  cases metadataEq.1
  cases metadataEq.2
  exact ⟨sources, values, default, rfl, (Core.Value.pair.inj parts.2).2,
    (Core.Value.pair.inj parts.2).1, fields.stored⟩

variable {artifact : Artifact} {session : Session artifact}

private def Collects (sourceType : TypeSystem.Ty) (publicValue : SourceCorePublicValues.Value)
    (selection : Selection sourceType publicValue) : Prop :=
  ∀ {source native type},
    ValueRep checked receiving functions mapping world sourceType source native type →
    ∀ {fuel registry expected} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.RawEncodedAt fuel registry expected publicValue encoded →
      SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected →
      encoded.value = native → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, Selected checked session selection source native type fuel entries ∧
        entries.map Entry.handle = selection.handles

private def CollectsPayloads (sourceTypes : List TypeSystem.Ty) (publicValues : List SourceCorePublicValues.Value)
    (selection : PayloadSelection sourceTypes publicValues) : Prop :=
  ∀ {sources values types},
    ValuesRep checked receiving functions mapping world sourceTypes sources values types →
    ∀ {fuel registry} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.PayloadsEncodedAt fuel registry sourceTypes publicValues encoded →
      encoded.value = DataPatternValues.packValues values → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, PayloadSelected checked session selection sources values types fuel entries ∧
        entries.map Entry.handle = selection.handles

private def CollectsEntries (key value : TypeSystem.Ty) (publicRows : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value))
    (selection : EntrySelection key value publicRows) : Prop :=
  ∀ {sources values keyType valueType},
    EntriesRep checked receiving functions mapping world key value sources values keyType valueType →
    ∀ {fuel registry} {layout : OrderedMapping.Layout} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
      session.EntriesEncodedAt fuel registry key value layout publicRows encoded →
      encoded.value = OrderedMapping.encode layout values → SourceCoreRawMetadata.Extends receiving registry →
      ∃ entries, EntriesSelected checked session selection sources values keyType valueType fuel entries ∧
        entries.map Entry.handle = selection.handles

/-- Exact current output encoding determines all selected leaves, preserving
constructor packing, mapping duplicates and each leaf's original raw type and
recursive validation fuel. -/
theorem Selection.collect {sourceType publicValue} (selection : Selection sourceType publicValue)
    {recipe : Recipe} (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (checkedAt : checked = recipe.compiled.compatible.checked)
    {source native type}
    (represented : ValueRep checked receiving functions mapping world sourceType source native type)
    {fuel registry expected} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected publicValue encoded)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType expected)
    (payload : encoded.value = native) (prior : SourceCoreRawMetadata.Extends receiving registry) :
    ∃ entries, Selected checked session selection source native type fuel entries ∧
      entries.map Entry.handle = selection.handles := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst recipe
  have all : Collects (functions := functions) (receiving := receiving) (mapping := mapping) (world := world)
      (session := session) sourceType publicValue selection := by
    clear represented accepted compatible payload prior
    refine Selection.rec
      (motive_1 := fun type value selection => Collects (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) type value selection)
      (motive_2 := fun types values selection => CollectsPayloads (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) types values selection)
      (motive_3 := fun key value rows selection => CollectsEntries (functions := functions) (receiving := receiving)
        (mapping := mapping) (world := world) (session := session) key value rows selection)
      ?skip ?function ?product ?constructed ?mapping ?nil ?cons ?empty ?entry selection
    case skip => intro _ _ _ _ _ _ _ _ _ _ _ _ _ _; exact ⟨[], .skip, rfl⟩
    case function =>
        intro rawType handle
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        exact ⟨[⟨_, source, _, native, type, fuel⟩], .function (payload ▸ accepted.reimports_function compatible), rfl⟩
    case product =>
        intro a b left right first second firstIH secondIH
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, firstEncoded, secondEncoded, firstAt, secondAt, encodedEq⟩ := accepted.product compatible.symm
        cases encodedEq; cases payload; cases fuelEq
        obtain ⟨x, y, firstType, secondType, sourceEq, typeEq, firstRep, secondRep⟩ := product_rep represented rfl
        cases sourceEq; cases typeEq
        obtain ⟨firstEntries, firstSelected, firstHandles⟩ := firstIH firstRep firstAt
          (SourceCoreRawMetadata.runtimeType_idempotent a).symm rfl prior
        obtain ⟨secondEntries, secondSelected, secondHandles⟩ := secondIH secondRep secondAt
          (SourceCoreRawMetadata.runtimeType_idempotent b).symm rfl (prior.trans firstEncoded.preserves)
        exact ⟨_, .product firstSelected secondSelected, by simp only [List.map_append, firstHandles, secondHandles, handles]⟩
    case constructed =>
        intro rawType metadata publicValues children ih
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, inserted, tag, fields, _, _, fieldsAt, encodedEq⟩ := accepted.constructed
        cases encodedEq; cases payload; cases fuelEq
        obtain ⟨sources, values, types, sourceEq, typeEq, packed, related⟩ :=
          constructed_children inserted represented compatible prior
        cases sourceEq; cases typeEq
        obtain ⟨entries, selected, handles⟩ := ih related fieldsAt packed (prior.trans inserted.preserves)
        exact ⟨entries, packed ▸ .constructed related.projection selected, handles⟩
    case mapping =>
        intro key value rows children ih
        intro source native type represented fuel registry expected encoded accepted compatible payload prior
        obtain ⟨remaining, fuelEq, inserted, layout, rows, fallback, _, layoutAt, rowsAt, _, encodedEq⟩ := accepted.mapping compatible.symm
        cases encodedEq; cases payload; cases fuelEq
        rw [← checkedAt] at layoutAt
        obtain ⟨identity, keyProjection, valueProjection, registered⟩ := CompatibleEncoding.mappingLayout_facts layoutAt
        have projected : checked.catalog.project (.mapping key value) = .ok (SourceCoreMappingWithDefault.type layout) := by
          rw [← checked.catalog.project_runtimeType]
          exact CompatibleEncoding.mapping_project identity keyProjection valueProjection
        have typeEq := Except.ok.inj (represented.projection.symm.trans projected)
        cases typeEq
        obtain ⟨sources, values, default, sourceEq, rowsEq, defaultEq, related⟩ := mapping_children inserted represented registered prior
        cases sourceEq
        obtain ⟨entries, selected, handles⟩ := ih related rowsAt rowsEq (prior.trans inserted.preserves)
        exact ⟨entries, by rw [rowsEq, defaultEq]; exact .mapping registered selected, handles⟩
    case nil =>
        intro sources values types represented fuel registry encoded accepted payload prior
        cases represented
        exact ⟨[], .none, rfl⟩
    case cons =>
        intro sourceType types publicValue publicValues head tail firstIH tailIH
        intro sources values coreTypes represented fuel registry encoded accepted payload prior
        cases represented with
        | cons first rest =>
          cases tail with
          | nil =>
              cases rest
              obtain ⟨remaining, fuelEq, firstAt⟩ := accepted.singleton
              cases fuelEq
              obtain ⟨entries, selected, handles⟩ := firstIH first firstAt rfl payload prior
              exact ⟨entries, .one selected, by simpa [PayloadSelection.handles] using handles⟩
          | cons next remaining =>
              cases rest with
              | cons nextRep remainingRep =>
                obtain ⟨budget, fuelEq, firstEncoded, tailEncoded, firstAt, tailAt, encodedEq⟩ := accepted.cons (by simp)
                cases encodedEq; cases fuelEq
                have parts := Core.Value.pair.inj payload
                obtain ⟨firstEntries, firstSelected, firstHandles⟩ := firstIH first firstAt rfl parts.1 prior
                obtain ⟨restEntries, restSelected, restHandles⟩ := tailIH (.cons nextRep remainingRep) tailAt parts.2 (prior.trans firstEncoded.preserves)
                exact ⟨_, .more firstSelected restSelected, by simp only [List.map_append, firstHandles, restHandles, PayloadSelection.handles]⟩
    case empty =>
        intro key value
        intro sources values keyType valueType represented fuel registry layout encoded accepted payload prior
        have actual := accepted.nil
        cases actual
        cases represented with
        | empty => exact ⟨[], .empty, rfl⟩
        | entry => cases payload
    case entry =>
        intro key value a b rows first second tail firstIH secondIH tailIH
        intro sources values keyType valueType represented fuel registry layout encoded accepted payload prior
        obtain ⟨remaining, fuelEq, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, encodedEq⟩ := accepted.cons
        cases encodedEq; cases fuelEq
        cases represented with
        | empty => cases payload
        | entry keyRep valueRep restRep =>
          have rowEq := (Core.Value.constructed.inj payload).2
          have parts := Core.Value.pair.inj rowEq
          have items := Core.Value.pair.inj parts.1
          obtain ⟨keys, keysSelected, keysHandles⟩ := firstIH keyRep keyAt rfl items.1 prior
          obtain ⟨values, valuesSelected, valuesHandles⟩ := secondIH valueRep valueAt rfl items.2 (prior.trans keyEncoded.preserves)
          obtain ⟨rest, restSelected, restHandles⟩ := tailIH restRep tailAt parts.2 (prior.trans (keyEncoded.preserves.trans valueEncoded.preserves))
          exact ⟨_, .entry keysSelected valuesSelected restSelected,
            by simp only [List.map_append, keysHandles, valuesHandles, restHandles, EntrySelection.handles]⟩
  exact all represented accepted compatible payload prior

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedOutputSelections
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicIssuedHistoryEntries
/-! Newly issued functions join an existing history through actual issuance
and encoding observations. Their Source meaning is derived from the current
owned caller and physical store, rather than supplied as a certificate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Input Issued Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)

inductive IssuedEntry {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact} :
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))) →
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))) →
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) →
    SourceCoreRawMetadata.Registry → Header compiled (Program.ofChecked compiled.sourceProgram) →
    Session artifact → Session artifact → Entry → Prop where
  | named {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | builtin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩
  | physicalNamed {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | physicalNamedSelected {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | physicalBuiltin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩

  | preparedPhysicalNamedSelected {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (inputs : List (Input compiled)) (rows : Inventory inputs)
      {input : Input compiled} (packet : Issued input) (member : Inventory.HasRow packet rows)
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {fuel : Nat}
      (issuance : before.NamedIssuedAt packet.header.named.signature.key fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel packet.header.named.specialized.function.type (.function handle) native)
      (certified : SelectedCompilationNamedArgumentRows.CertifiedAt (header := packet.header) (function := CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available))) :
      IssuedEntry (headers rows) (keys compiled)
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions (headers rows) (keys compiled) bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨packet.header.named.specialized.function.type,
          .global (CallableNamedReversal.global (CallableNamedMetadata.global packet.header.named.specialized input.prepared.available)),
          handle, native, CallableContract.functionType packet.header.named.signature.parameterType packet.header.named.signature.resultType, fuel⟩
  | preparedPhysicalBuiltin {recipe : Recipe} (prepared : Recipe.prepare compiled = .ok recipe)
      (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
      (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
      (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
      (profile : compiled.compatible.checked.catalog.callableContracts = true)
      (anchor : Header compiled (Program.ofChecked compiled.sourceProgram))
      {before : Session artifact} {issued : Completion artifact} {function : BuiltinFunctionId} {fuel : Nat}
      (issuance : before.BuiltinIssuedAt function fuel issued)
      (atRecipe : ArtifactRecipe artifact recipe)
      {handle : Handle} (handleValue : issued.value = .function handle) {native : Core.Value}
      (encoded : issued.session.EncodesAt fuel function.type (.function handle) native) :
      IssuedEntry headers keys (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry faults profile)
        registry anchor before issued.session
        ⟨function.type, .builtin ⟨function⟩, handle, native,
          CallableContract.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), fuel⟩

/-- Retaining a newly issued entry preserves all earlier registry slots. -/
theorem IssuedEntry.chain
    {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry) :
    before.IssuanceChain after := by
  cases receipt with
  | named _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | builtin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue
  | physicalNamed _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | physicalNamedSelected _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | preparedPhysicalNamedSelected _ _ _ _ _ _ _ _ _ _ issuance _ handleValue _ _ => exact .named (.refl _) issuance handleValue
  | physicalBuiltin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue
  | preparedPhysicalBuiltin _ _ _ _ _ _ _ _ issuance _ handleValue _ => exact .builtin (.refl _) issuance handleValue

/-- Current store checks identify every fresh named capture. Builtins retain
their compiler-owned closed code. Both cases use the real issued handle. -/
theorem IssuedEntry.current
    {compiled : SourceCoreUnifiedCompilation.Compiled} {artifact : Artifact}
    {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
    {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {anchor : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {before after : Session artifact} {entry : Entry}
    (receipt : IssuedEntry headers keys functions registry anchor before after entry)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (caller : State headers keys ⟨[], mapping, world, heap, store,
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (atNative : before.NativeAt world store) :
    before.SameRuntime after ∧
      after.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native ∧
      ValueRep compiled.compatible.checked registry functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType ∧
      Dynamic.ValueHasType anchor.function.context heap entry.source entry.sourceType := by
  cases receipt with
  | named prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      obtain ⟨native, imported, represented, typed⟩ :=
        RecursiveNamedPublicCurrentFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue wellFormed
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | builtin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicBuiltinArgumentReceipts.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented, typed⟩
  | physicalNamed prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded wellFormed =>
      obtain ⟨native, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue wellFormed
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | physicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      obtain ⟨native, imported, represented, typed⟩ :=
        SelectedCompilationPublicFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue certified
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented, typed⟩
  | physicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented, typed⟩

  | preparedPhysicalNamedSelected prepared inputs rows packet member bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded certified =>
      obtain ⟨native, imported, represented, typed⟩ :=
        SelectedCompilationPublicFactoryValues.Session.named_value_represents_current
          prepared inputs rows packet member bodyRegistry registry faults profile caller anchor
          issuance atNative (.refl _) atRecipe handleValue certified
      have same := imported.unique encoded
      cases same
      exact ⟨issuance.same_runtime, encoded, represented.map_functions
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.includes_physical profile), typed⟩
  | preparedPhysicalBuiltin prepared headers keys bodyRegistry registry faults profile anchor issuance atRecipe handleValue encoded =>
      obtain ⟨native, sameRuntime, _type, imported, represented, typed⟩ :=
        RecursiveNamedPublicPhysicalFactoryValues.Session.builtin_value_represents_after
          prepared headers keys bodyRegistry registry faults profile mapping anchor.function.context heap
          issuance (.refl _) atRecipe handleValue (world := world)
      have same := imported.unique encoded
      cases same
      exact ⟨sameRuntime, encoded, represented.map_functions
        (CallableIndexedOwnedPreparedPhysicalCellOrigins.includes_physical profile), typed⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistory
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryInputs
/-! Public input descriptions retain literal members of a finite function
history. Distinct handles and repeated aliases can occur beside data at any
finite depth. Raw constructor and mapping metadata, counts and entry order
are preserved without assuming native representation or execution. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession
open RecursiveNamedPublicFunctionHistory (Entry)

mutual
  inductive Input (history : List Entry) (context : SourceSemantics.Context) :
      TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
    | retained (entry : Entry) (member : entry ∈ history) :
        Input history context entry.sourceType (.function entry.handle) entry.source
    | data {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (typed : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value type)
        (meaning : RecursiveNamedPublicDataInputs.Means value source) :
        Input history context type value source
    | product {leftType rightType : TypeSystem.Ty}
        {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
        (leftInput : Input history context leftType left first)
        (rightInput : Input history context rightType right second) :
        Input history context (.product leftType rightType) (.product left right) (.product first second)
    | constructed {metadata : DataConstructorInstantiation}
        {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (payloads : Inputs history context metadata.payloadTypes values sources) :
        Input history context metadata.resultType (.constructed metadata values) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (stored : Entries history context key value entries sources) :
        Input history context (.mapping key value) (.mapping key value entries) (.mapping key value sources)
    | comptime {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (input : Input history context type value source) :
        Input history context (.comptime type) value source

  inductive Inputs (history : List Entry) (context : SourceSemantics.Context) :
      List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
    | nil : Inputs history context [] [] []
    | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
        {source : Dynamic.Value} {sources : List Dynamic.Value}
        (head : Input history context type value source)
        (tail : Inputs history context types values sources) :
        Inputs history context (type :: types) (value :: values) (source :: sources)

  inductive Entries (history : List Entry) (context : SourceSemantics.Context) : TypeSystem.Ty → TypeSystem.Ty →
      List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) →
      List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : Entries history context key value [] []
    | entry {key value : TypeSystem.Ty}
        {first second : SourceCorePublicValues.Value} {left right : Dynamic.Value}
        {rest : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (keyInput : Input history context key first left)
        (valueInput : Input history context value second right)
        (remaining : Entries history context key value rest sources) :
        Entries history context key value ((first, second) :: rest) ((left, right) :: sources)
end

variable {history : List Entry} {context : SourceSemantics.Context}

theorem Input.source_hasType {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input history context type value source)
    {heap : Dynamic.Heap}
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType context heap entry.source entry.sourceType) :
    Dynamic.ValueHasType context heap source type := by
  induction receipt using Input.rec
    (motive_2 := fun types _ sources _ => Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value _ sources _ => Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | retained entry member => exact retainedTyped entry member
  | data typed meaning => exact RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType typed meaning
  | product _ _ left right => exact .product left right
  | constructed valid _ payloads => exact .constructed valid payloads
  | mapping _ entries => exact .mapping entries
  | comptime _ typed => exact .comptime typed
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty key value => exact .nil key value
  | entry _ _ _ key value rest => exact .cons key value rest

theorem Inputs.source_hasTypes {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources)
    {heap : Dynamic.Heap}
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType context heap entry.source entry.sourceType) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction types generalizing values sources with
  | nil => cases receipts; exact .nil
  | cons type types ih => cases receipts with
    | cons head tail => exact .cons (head.source_hasType retainedTyped) (ih tail)

theorem Inputs.source_length {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources) : sources.length = types.length := by
  induction types generalizing values sources with
  | nil => cases receipts; rfl
  | cons type types ih => cases receipts with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

theorem Inputs.lookup {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs history context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input history context type value source := by
  induction types generalizing values sources index with
  | nil => simp at found
  | cons type types ih => cases receipts with
    | cons head tail =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih tail found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
/-! Independent public input descriptions retain raw types and the Source
value at every nested position. Function leaves use genuine issuance and
inventory receipts. Containers preserve payload and mapping entry order;
none of these constructors assumes a native representation or execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory)

mutual
  inductive Input {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) :
      TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
    | leaf {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (receipt : RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source) :
        Input rows session context type value source
    | product {leftType rightType : TypeSystem.Ty}
        {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
        (leftInput : Input rows session context leftType left first)
        (rightInput : Input rows session context rightType right second) :
        Input rows session context (.product leftType rightType) (.product left right) (.product first second)
    | constructed {metadata : DataConstructorInstantiation}
        {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (payloads : Inputs rows session context metadata.payloadTypes values sources) :
        Input rows session context metadata.resultType (.constructed metadata values) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (stored : Entries rows session context key value entries sources) :
        Input rows session context (.mapping key value) (.mapping key value entries) (.mapping key value sources)
    | comptime {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (input : Input rows session context type value source) :
        Input rows session context (.comptime type) value source

  inductive Inputs {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) :
      List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
    | nil : Inputs rows session context [] [] []
    | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
        {source : Dynamic.Value} {sources : List Dynamic.Value}
        (head : Input rows session context type value source)
        (tail : Inputs rows session context types values sources) :
        Inputs rows session context (type :: types) (value :: values) (source :: sources)

  inductive Entries {compiled : SourceCoreUnifiedCompilation.Compiled}
      {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
      (rows : Inventory inputs) {artifact : Artifact} (session : Session artifact)
      (context : SourceSemantics.Context) : TypeSystem.Ty → TypeSystem.Ty →
      List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) →
      List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : Entries rows session context key value [] []
    | entry {key value : TypeSystem.Ty}
        {first second : SourceCorePublicValues.Value} {left right : Dynamic.Value}
        {rest : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (keyInput : Input rows session context key first left)
        (valueInput : Input rows session context value second right)
        (remaining : Entries rows session context key value rest sources) :
        Entries rows session context key value ((first, second) :: rest) ((left, right) :: sources)
end

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
  {context : SourceSemantics.Context}

theorem Input.source_hasType {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input rows session context type value source)
    {heap : Dynamic.Heap}
    (leaves : ∀ {type value source},
      RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source →
      Dynamic.ValueHasType context heap source type) : Dynamic.ValueHasType context heap source type := by
  induction receipt using Input.rec
    (motive_2 := fun types _ sources _ => Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value _ sources _ => Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | leaf receipt => exact leaves receipt
  | product _ _ left right => exact .product left right
  | constructed valid _ payloads => exact .constructed valid payloads
  | mapping _ entries => exact .mapping entries
  | comptime _ typed => exact .comptime typed
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty key value => exact .nil key value
  | entry _ _ _ key value rest => exact .cons key value rest

theorem Inputs.source_length {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources) : sources.length = types.length := by
  induction types generalizing values sources with
  | nil => cases receipts; rfl
  | cons type types ih => cases receipts with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

theorem Inputs.lookup {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs rows session context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input rows session context type value source := by
  induction types generalizing values sources index with
  | nil => simp at found
  | cons type types ih => cases receipts with
    | cons head tail =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih tail found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext
/-! Induction statements for the original public codec. Each conclusion uses
one fixed receiving registry. Child receipts retain their own actual metadata
and extend forward into that registry. These statements are discharged by the
structural fold and real function issuance below. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession

variable {artifact : Artifact} (session : Session artifact)
  {checked : SourceCoreCompatibleCatalog.Checked}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  (functions : FunctionModel checked.catalog ambient)
  (receiving : SourceCoreRawMetadata.Registry) (mapping : LocationMap) (world : StoreTyping)

def RawMeaning (sourceType : TypeSystem.Ty) (value : SourceCorePublicValues.Value)
    (source : Dynamic.Value) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value} {type : Ty},
    registry.signatures = checked.signatures →
    SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType sourceType →
    session.RawEncodedAt fuel registry expected value encoded →
    checked.catalog.project expected = .ok type →
    RuntimeValueHasType world encoded.value type ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ValueRep checked receiving functions mapping world
      sourceType source encoded.value type

def PayloadMeaning (types : List TypeSystem.Ty) (values : List SourceCorePublicValues.Value)
    (sources : List Dynamic.Value) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value} {coreTypes : List Ty},
    registry.signatures = checked.signatures →
    session.PayloadsEncodedAt fuel registry types values encoded →
    types.mapM checked.catalog.project = .ok coreTypes →
    RuntimeValueHasType world encoded.value (SourceCoreCompatibleCatalog.packTypes coreTypes) ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ∃ native, ValuesRep checked receiving functions mapping world
      types sources native coreTypes ∧ encoded.value = packValues native

def EntriesMeaning (key value : TypeSystem.Ty)
    (entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value))
    (sources : List (Dynamic.Value × Dynamic.Value)) : Prop :=
  ∀ {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {layout : OrderedMapping.Layout}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value},
    registry.signatures = checked.signatures →
    session.EntriesEncodedAt fuel registry key value layout entries encoded →
    checked.catalog.project key = .ok layout.keyType →
    checked.catalog.project value = .ok layout.valueType →
    layout.Registered checked.catalog.definitions →
    RuntimeValueHasType world encoded.value layout.type ambient.definitions →
    SourceCoreRawMetadata.Extends encoded.registry receiving →
    ∃ native, EntriesRep checked receiving functions mapping world
      key value sources native layout.keyType layout.valueType ∧ encoded.value = OrderedMapping.encode layout native

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContext
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContainers
/-! Nested constructor and mapping receipts use the original public encoder.
Payloads and entries are interpreted in their actual order, in the ambient
definitions that also type issued closures. Mapping defaults are generated by
the existing data codec and then represented in the same receiving model. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContainers
open Core Frontend SourceInference GeneralHeap CompatiblePayload ReadOnly
open SourceCoreIndexedSession RecursiveNamedPublicNestedEncodingContext

private theorem default_represents {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient}
    {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    (owner : registry.signatures = checked.signatures)
    {sourceType : TypeSystem.Ty} {type : Core.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : SourceCoreCompatibleValues.encodeDefaultRaw fuel checked registry sourceType type = .ok encoded)
    (projected : checked.catalog.project sourceType = .ok type)
    (wellFormed : type.WellFormed checked.catalog.definitions)
    (typed : RuntimeValueHasType world encoded.value (.sum .unit type) ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends encoded.registry receiving) :
    ∃ fallback, encoded.value = OrderedMapping.optionValue type fallback ∧
      DefaultRep checked receiving functions mapping world sourceType fallback type := by
  cases found : SourceCoreCompatibleValues.defaultValue? (sourceType.size + 1) sourceType with
  | none =>
      simp only [SourceCoreCompatibleValues.encodeDefaultRaw, found, pure, Except.pure] at accepted
      cases accepted
      exact ⟨none, rfl, .absent ((CompatiblePayload.defaultValue?_absent_iff (by omega)).mp
        ((SourceCoreCompatibleValues.defaultValue?_absent_iff _ _).mp found)) projected wellFormed⟩
  | some carrier =>
      simp only [SourceCoreCompatibleValues.encodeDefaultRaw, found] at accepted
      obtain ⟨inner, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
      cases accepted
      cases typed with
      | inRight typed =>
          have input : EncodedDataInput checked receiving sourceType (DataInput.publicValue carrier) inner.value :=
            ⟨carrier, fuel, registry, inner, rfl, owner, generated, rfl, extended⟩
          obtain ⟨source, means, related⟩ := RecursiveNamedPublicDataInputs.EncodedDataInput.represents
            functions mapping world input projected ambient.basePrefix typed
          obtain ⟨actual, meaning, actualMeans⟩ := CompatibleEncoding.default_meaning found
          have same := RecursiveNamedPublicRuntimeMeaning.means_functional means ⟨carrier, rfl, actualMeans⟩
          subst actual
          exact ⟨some inner.value, rfl, .present meaning related⟩

variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

theorem constructed (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {metadata : DataConstructorInstantiation}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (children : PayloadMeaning session functions receiving mapping world metadata.payloadTypes values sources)
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {expected : TypeSystem.Ty} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    {type : Core.Ty}
    (owner : registry.signatures = recipe.compiled.compatible.checked.signatures)
    (accepted : session.RawEncodedAt fuel registry expected (.constructed metadata values) encoded)
    (projected : recipe.compiled.compatible.checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends encoded.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      expected (.constructed metadata sources) encoded.value type := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst recipe
  obtain ⟨remaining, _, inserted, tag, payloads, _, resolved, payloadsAccepted, same⟩ := accepted.constructed
  cases same
  obtain ⟨selected, types, projections, registered⟩ := CompatibleEncoding.resolveConstructor_facts resolved
  cases typed with
  | constructed lookup payloadTyped =>
      have same := Option.some.inj (lookup.symm.trans (ambient.basePrefix.constructor_lookup registered))
      subst_vars
      cases payloadTyped with
      | pair headerTyped fieldsTyped =>
          obtain ⟨native, related, packed⟩ := children
            (inserted.preserves.signatures.trans owner) payloadsAccepted projections fieldsTyped extended
          have resultProjection : actualRecipe.compiled.compatible.checked.catalog.project metadata.resultType =
              .ok (.namedData tag.owner) :=
            (CompatibleEncoding.project_compatible inserted.runtime_compatible).symm.trans projected
          refine .compatible inserted.runtime_compatible ?_
          rw [packed]
          exact .constructed ⟨extended.lookup (payloads.preserves.lookup inserted.reconstruct)⟩
            (extended.signatures.trans (payloads.preserves.signatures.trans (inserted.preserves.signatures.trans owner)))
            selected resultProjection registered related

theorem mapping_value (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {actualKey actualValue : TypeSystem.Ty}
    {values : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
    {sources : List (Dynamic.Value × Dynamic.Value)}
    (children : EntriesMeaning session functions receiving mapping world actualKey actualValue values sources)
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {expected keyType valueType : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value} {type : Core.Ty}
    (owner : registry.signatures = recipe.compiled.compatible.checked.signatures)
    (erased : SourceCoreRawMetadata.runtimeType expected = .mapping keyType valueType)
    (accepted : session.RawEncodedAt fuel registry expected (.mapping actualKey actualValue values) encoded)
    (projected : recipe.compiled.compatible.checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType world encoded.value type ambient.definitions)
    (extended : SourceCoreRawMetadata.Extends encoded.registry receiving) :
    ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      expected (.mapping actualKey actualValue sources) encoded.value type := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst recipe
  obtain ⟨remaining, _, inserted, layout, entries, fallback, _, layoutAccepted,
    entriesAccepted, fallbackAccepted, same⟩ := accepted.mapping erased
  cases same
  obtain ⟨selected, first, second, registered⟩ := CompatibleEncoding.mappingLayout_facts layoutAccepted
  have expectedProjection : actualRecipe.compiled.compatible.checked.catalog.project expected =
      .ok (SourceCoreMappingWithDefault.type layout) := by
    rw [← actualRecipe.compiled.compatible.checked.catalog.project_runtimeType expected, erased]
    exact CompatibleEncoding.mapping_project selected first second
  have typeEq := Except.ok.inj (projected.symm.trans expectedProjection)
  subst type
  have headerCompatible := inserted.runtime_compatible
  have components : keyType = SourceCoreRawMetadata.runtimeType actualKey ∧
      valueType = SourceCoreRawMetadata.runtimeType actualValue := by
    rw [erased] at headerCompatible
    exact TypeSystem.Ty.mapping.inj headerCompatible
  have actualFirst : actualRecipe.compiled.compatible.checked.catalog.project actualKey = .ok layout.keyType := by
    rw [← actualRecipe.compiled.compatible.checked.catalog.project_runtimeType actualKey, ← components.1]
    exact first
  have actualSecond : actualRecipe.compiled.compatible.checked.catalog.project actualValue = .ok layout.valueType := by
    rw [← actualRecipe.compiled.compatible.checked.catalog.project_runtimeType actualValue, ← components.2]
    exact second
  have actualSelected : actualRecipe.compiled.compatible.checked.catalog.identity? (.mapping actualKey actualValue) =
      some layout.dataType :=
    (CompatibleEncoding.identity_compatible ((CompatibleEncoding.runtime_view erased).symm.trans
      inserted.runtime_compatible)).symm.trans selected
  cases typed with
  | pair headerTyped restTyped => cases restTyped with
    | pair fallbackTyped entriesTyped =>
        obtain ⟨native, stored, storedEq⟩ := children
          (inserted.preserves.signatures.trans owner) entriesAccepted actualFirst actualSecond registered
          entriesTyped (fallback.preserves.trans extended)
        obtain ⟨default, defaultEq, defaultRep⟩ := default_represents
          (entries.preserves.signatures.trans (inserted.preserves.signatures.trans owner))
          fallbackAccepted actualSecond registered.valueWellFormed fallbackTyped extended
        refine .compatible inserted.runtime_compatible ?_
        rw [storedEq, defaultEq]
        exact .mappingValue
          ⟨extended.lookup (fallback.preserves.lookup (entries.preserves.lookup inserted.reconstruct))⟩
          actualSelected actualFirst actualSecond registered stored defaultRep

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncodingContainers
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEncoding
/-! Each retained function leaf uses its actual current-session encoding and
semantic representation at the current map and world. Containers follow the
original codec in order, preserving distinct handles and repeated aliases in
one fixed receiving metadata registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEncoding
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession RecursiveNamedPublicFunctionHistoryInputs RecursiveNamedPublicNestedEncodingContext
open RecursiveNamedPublicFunctionHistory (Entry)

variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
  {context : SourceSemantics.Context}

private theorem data_meaning
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (inputTyped : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value sourceType)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  intro fuel before expected encoded type owner compatible accepted projected typed metadata
  obtain ⟨carrier, image, _typed⟩ := inputTyped
  have encodedAt := accepted.data owner ⟨carrier, image⟩
  obtain ⟨interpreted, interpretedAt, represented⟩ :=
    RecursiveNamedPublicDataInputs.EncodedDataInput.represents functions mapping world
      encodedAt projected ambient.basePrefix typed
  have same := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
  subst interpreted
  exact .compatible compatible.symm (represented.extend metadata (.refl _) (.refl _))

variable {history : List Entry}

private theorem represents
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input history context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : ∀ entry, entry ∈ history →
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native)
    (represented : ∀ entry, entry ∈ history →
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  induction receipt using Input.rec
    (motive_2 := fun types values sources _ => PayloadMeaning session functions receiving mapping world types values sources)
    (motive_3 := fun key value entries sources _ => EntriesMeaning session functions receiving mapping world key value entries sources) with
  | retained entry member =>
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      have sameValue := accepted.function_eq (imported entry member)
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have actualRepresentation := represented entry member
      have sameType := Except.ok.inj (actualRepresentation.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ actualRepresentation
  | data inputTyped meaning => exact data_meaning atRecipe inputTyped meaning
  | product _ _ first second =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      have view := compatible
      simp only [SourceCoreRawMetadata.runtimeType] at view
      obtain ⟨remaining, _fuel, left, right, leftAt, rightAt, shape⟩ := accepted.product view
      cases shape
      obtain ⟨a, b, leftProjected, rightProjected, rfl⟩ := CompatibleEncoding.product_projection view projected
      cases typed with
      | pair leftTyped rightTyped =>
          exact .product
            (first owner (SourceCoreRawMetadata.runtimeType_idempotent _) leftAt leftProjected leftTyped
              (right.preserves.trans metadata))
            (second (left.preserves.signatures.trans owner)
              (SourceCoreRawMetadata.runtimeType_idempotent _) rightAt rightProjected rightTyped metadata)
  | constructed _ _ payloads =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.constructed atRecipe payloads owner accepted projected typed metadata)
  | mapping _ entries =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.mapping_value atRecipe entries owner compatible accepted projected typed metadata)
  | @comptime sourceType _ _ _ child =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible (actual := sourceType) rfl (child owner compatible accepted projected typed metadata)
  | nil =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      have shape := accepted.nil
      cases shape
      cases projected
      exact ⟨[], .nil, rfl⟩
  | @cons type types value values source sources head tail first rest =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ :=
        CompatibleEncoding.project_cons projected
      cases types with
      | nil =>
          cases tail
          cases remainingProjection
          obtain ⟨remaining, _fuel, actual⟩ := accepted.singleton
          exact ⟨[encoded.value], .cons (first owner rfl actual firstProjection typed metadata) .nil, rfl⟩
      | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ :=
            CompatibleEncoding.project_cons remainingProjection
          obtain ⟨remaining, _fuel, headEncoded, tailEncoded, headAt, tailAt, shape⟩ :=
            accepted.cons (by simp)
          cases shape
          cases typed with
          | pair headTyped tailTyped =>
              obtain ⟨native, related, packing⟩ := rest (headEncoded.preserves.signatures.trans owner)
                tailAt remainingProjection tailTyped metadata
              cases native with
              | nil => cases related
              | cons next native =>
                  exact ⟨headEncoded.value :: next :: native,
                    .cons (first owner rfl headAt firstProjection headTyped
                      (tailEncoded.preserves.trans metadata)) related,
                    by simp only [packValues]; rw [packing]⟩
  | empty key value =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      have shape := accepted.nil
      cases shape
      exact ⟨[], .empty _ _ _ _, rfl⟩
  | entry _ _ _ key value rest =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      obtain ⟨remaining, _fuel, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, shape⟩ :=
        accepted.cons
      cases shape
      cases typed with
      | constructed lookup payloadTyped =>
          have same := Option.some.inj (lookup.symm.trans (ambient.basePrefix.constructor_lookup registered.consLookup))
          cases same
          cases payloadTyped with
          | pair pairTyped restTyped => cases pairTyped with
            | pair keyTyped valueTyped =>
                obtain ⟨native, represented, packing⟩ := rest
                  (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
                  tailAt keyProjection valueProjection registered restTyped metadata
                exact ⟨(keyEncoded.value, valueEncoded.value) :: native,
                  .entry
                    (key owner rfl keyAt keyProjection keyTyped
                      (valueEncoded.preserves.trans (tailEncoded.preserves.trans metadata)))
                    (value (keyEncoded.preserves.signatures.trans owner) rfl valueAt valueProjection valueTyped
                      (tailEncoded.preserves.trans metadata)) represented,
                  by simp only [OrderedMapping.encode]; rw [packing]⟩

/-- Current history evidence supplies each literal retained function leaf.
Independent data receipts and actual encoding supply all other positions,
while each container preserves its complete ordered native payload. -/
theorem Input.meaning
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input history context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : ∀ entry, entry ∈ history →
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native)
    (represented : ∀ entry, entry ∈ history →
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType)
    {heap : Dynamic.Heap}
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType context heap entry.source entry.sourceType) :
    RawMeaning session functions receiving mapping world sourceType value source ∧
      Dynamic.ValueHasType context heap source sourceType :=
  ⟨represents receipt atRecipe imported represented, receipt.source_hasType retainedTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
/-! Exact raw input receipts from the original public startup. The selected
payload, native projection and metadata extension retain the same argument
position and the actual checkpoint; this module adds no semantic premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- The actual selected input keeps its own starting registry and the genuine
extension through all later inputs into the startup's final registry. -/
theorem StartAt.raw_input
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {arguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments fuel checkpoint recipe root world store native encodedValues)
    {index : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    (rawType : root.inputs[index]? = some expected)
    (found : arguments[index]? = some value) :
    ∃ (before : SourceCoreRawMetadata.Registry)
      (encoded : SourceCoreCompatibleValues.Extended before Core.Value) (type : Core.Ty),
      native[index]? = some encoded.value ∧ root.types[index]? = some type ∧
      recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
      before.signatures = recipe.compiled.compatible.checked.signatures ∧
      session.RawEncodedAt fuel before expected value encoded ∧
      SourceCoreRawMetadata.Extends encoded.registry encodedValues.registry := by
  have receipt := started.original.raw_input found
  cases artifact
  rename_i authority actualRecipe
  have sameRecipe : actualRecipe = recipe := started.recipe_eq
  subst recipe
  obtain ⟨actualRoot, encodedPrefix, selected, atIndex, initial⟩ := receipt
  have sameRoot := Option.some.inj (started.selected.symm.trans selected)
  subst actualRoot
  obtain ⟨before, encoded, type, payloadAt, typeAt, projected, owner, encodedAt, extended⟩ :=
    atIndex expected rawType
  have original := started.initial
  have actualValues := started.values
  cases checkpoint
  rename_i origin request checkpointWorld state stored typed extension registry values valueOwner
  change values = encodedValues at actualValues
  change SourceCoreRawMetadata.Extends encoded.registry values.registry at extended
  rw [actualValues] at extended
  change state = Core.State.initial root.body
    (native.reverse ++ SourceCoreCallableIndexedTemplates.globalEnvironment actualRecipe.compiled.indexed) store at original
  have sameState := initial.symm.trans original
  have sameControl := congrArg Core.State.control sameState
  have sameEnvironment := (Core.Control.eval.inj sameControl).2
  have samePrefix : encodedPrefix = native := by
    have reversed := congrArg List.reverse (List.append_inj_left' sameEnvironment rfl)
    simpa only [List.reverse_reverse] using reversed
  subst encodedPrefix
  exact ⟨before, encoded, type, payloadAt, typeAt, projected, owner, encodedAt, extended⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedRawInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
/-! Arbitrary ordered arguments can contain distinct retained functions and
repeated aliases inside data containers. Current function-history evidence
supplies meaning and typing; actual startup fixes every native payload and
intermediate registry. Both lists retain the actual map, world and heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicFunctionHistoryInputs (Inputs)
open RecursiveNamedPublicFunctionHistory (Entry)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedParameterCertificates (Binding)

private theorem projected_at {checked : SourceCoreCompatibleCatalog.Checked}
    {bindings : List Binding} {index : Nat} {binding : Binding}
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (found : bindings[index]? = some binding) :
    checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  induction bindings generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.map_cons] at projected
      obtain ⟨type, types, headProjected, tailProjected, shape⟩ := CompatibleEncoding.project_cons projected
      have parts := List.cons.inj shape
      have headActual : checked.catalog.project head.1.scheme.body = .ok head.2 := by
        simpa only [← parts.1] using headProjected
      have tailActual : (tail.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
          .ok (tail.map Prod.snd) := by
        simpa only [← parts.2] using tailProjected
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact headActual
      | succ index => exact ih tailActual found

/-- Reconstruct both complete lists from their original positions. Exact
lengths exclude silently discarded native or Source suffixes. -/
private theorem arguments_of_positions
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (sourceLength : sources.length = bindings.length) (nativeLength : native.length = bindings.length)
    (positions : ∀ {index : Nat} {binding : Binding}, bindings[index]? = some binding →
      ∃ source value, sources[index]? = some source ∧ native[index]? = some value ∧
        ValueRep checked registry functions mapping world binding.1.scheme.body source value binding.2 ∧
        Dynamic.ValueHasType context heap source binding.1.scheme.body) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources native ∧
      Dynamic.ValuesHaveTypes context heap sources (bindings.map (fun binding => binding.1.scheme.body)) := by
  induction bindings generalizing sources native with
  | nil =>
      have sourceNil := List.eq_nil_of_length_eq_zero sourceLength
      have nativeNil := List.eq_nil_of_length_eq_zero nativeLength
      subst sources
      subst native
      exact ⟨.nil, .nil⟩
  | cons binding bindings ih =>
      cases sources with
      | nil => simp at sourceLength
      | cons source sources =>
          cases native with
          | nil => simp at nativeLength
          | cons value native =>
              obtain ⟨actualSource, actualValue, sourceAt, valueAt, represented, typed⟩ :=
                positions (index := 0) rfl
              have sameSource : source = actualSource := Option.some.inj sourceAt
              have sameValue : value = actualValue := Option.some.inj valueAt
              subst actualSource
              subst actualValue
              simp only [List.length_cons] at sourceLength nativeLength
              have remaining := ih (Nat.succ.inj sourceLength) (Nat.succ.inj nativeLength) (by
                intro index next found
                exact positions (index := index + 1) found)
              exact ⟨.cons represented remaining.1, .cons typed remaining.2⟩

/-- Actual retained history and original input encoding produce complete
current arguments. Each selected native position is preserved, with no extra
Source or native suffix and no supplied body execution law. -/
theorem StartAt.history_arguments_receiving
    {artifact : Artifact} {session : Session artifact} {key : Key}
    {publicArguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments inputFuel checkpoint recipe root world store native encodedValues)
    (functions : FunctionModel recipe.compiled.compatible.checked.catalog
      (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed))
    {headers : List (Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram))}
    {header : Header recipe.compiled (Program.ofChecked recipe.compiled.sourceProgram)}
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial recipe.compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed)
      (program := Program.ofChecked recipe.compiled.sourceProgram) headers root header)
    (history : List Entry)
    (imported : ∀ entry, entry ∈ history →
      session.EncodesAt entry.fuel entry.sourceType (.function entry.handle) entry.native)
    {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {heap : Dynamic.Heap}
    (retained : ∀ entry, entry ∈ history →
      ValueRep recipe.compiled.compatible.checked receiving functions mapping world
        entry.sourceType entry.source entry.native entry.nativeType)
    (retainedTyped : ∀ entry, entry ∈ history →
      Dynamic.ValueHasType header.function.context heap entry.source entry.sourceType)
    {sources : List Dynamic.Value}
    (receipts : Inputs history header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments sources)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry receiving)
    (wellFormed : ProgramWellFormed (Program.ofChecked recipe.compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel recipe.compiled.compatible.checked receiving functions)
      mapping world header.bindings sources native ∧
    Dynamic.ValuesHaveTypes header.function.context heap sources header.types := by
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : sources.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have assembled := arguments_of_positions (functions := functions) (registry := receiving)
      (mapping := mapping) (world := world) (context := header.function.context) (heap := heap)
      sourceCount nativeCount (by
        intro index binding bindingAt
        have rawAt : (header.bindings.map (fun binding => binding.1.scheme.body))[index]? =
            some binding.1.scheme.body := by
          simp only [List.getElem?_map, bindingAt, Option.map_some]
        obtain ⟨publicValue, source, publicAt, sourceAt, receipt⟩ := receipts.lookup rawAt
        have bindingProjected := projected_at projected bindingAt
        have rawRoot : root.inputs[index]? = some binding.1.scheme.body := by
          rw [rawInputs]
          exact rawAt
        obtain ⟨before, encoded, type, valueAt, typeAt, projection, owner, accepted, extended⟩ :=
          RecursiveNamedPublicNestedRawInputs.StartAt.raw_input started rawRoot publicAt
        obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
        have sameValue : actual = encoded.value := Option.some.inj (actualAt.symm.trans valueAt)
        subst actual
        obtain ⟨meaning, sourceTyped⟩ := RecursiveNamedPublicFunctionHistoryEncoding.Input.meaning
          receipt started.recipe_eq imported retained retainedTyped
        have represented := meaning owner rfl accepted projection typed (extended.trans metadata)
        have typeEq := Except.ok.inj (projection.symm.trans bindingProjected)
        exact ⟨source, encoded.value, sourceAt, valueAt, typeEq ▸ represented, sourceTyped⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicFunctionHistoryArgumentsReceiving
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
/-! Structural induction connects nested public inputs to their original
encoded bytes. Every function leaf is discharged by the issued callable
producer. Payload packing, metadata extension and mapping order follow the
actual encoder receipts; no child representation is supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession RecursiveNamedPublicNestedInputs RecursiveNamedPublicNestedEncodingContext
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled)}
  {rows : Inventory inputs} {artifact : Artifact} {session : Session artifact}
  {context : SourceSemantics.Context}
  {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}

theorem Input.represents {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input rows session context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (leaves : ∀ {type value source},
      RecursiveNamedPublicMixedArgumentReceipts.Input rows session context type value source →
      RawMeaning session functions receiving mapping world type value source) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  induction receipt using Input.rec
    (motive_2 := fun types values sources _ => PayloadMeaning session functions receiving mapping world types values sources)
    (motive_3 := fun key value entries sources _ => EntriesMeaning session functions receiving mapping world key value entries sources) with
  | leaf receipt => exact leaves receipt
  | product _ _ first second =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      have view := compatible
      simp only [SourceCoreRawMetadata.runtimeType] at view
      obtain ⟨remaining, _fuel, left, right, leftAt, rightAt, shape⟩ := accepted.product view
      cases shape
      obtain ⟨a, b, leftProjected, rightProjected, rfl⟩ := CompatibleEncoding.product_projection view projected
      cases typed with
      | pair leftTyped rightTyped =>
          exact .product
            (first owner (SourceCoreRawMetadata.runtimeType_idempotent _) leftAt leftProjected leftTyped
              (right.preserves.trans metadata))
            (second (left.preserves.signatures.trans owner)
              (SourceCoreRawMetadata.runtimeType_idempotent _) rightAt rightProjected rightTyped metadata)
  | constructed _ _ payloads =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.constructed atRecipe payloads owner accepted projected typed metadata)
  | mapping _ entries =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.mapping_value atRecipe entries owner compatible accepted projected typed metadata)
  | @comptime sourceType _ _ _ child =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible (actual := sourceType) rfl (child owner compatible accepted projected typed metadata)
  | nil =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      have shape := accepted.nil
      cases shape
      cases projected
      exact ⟨[], .nil, rfl⟩
  | @cons type types value values source sources head tail first rest =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ :=
        CompatibleEncoding.project_cons projected
      cases types with
      | nil =>
          cases tail
          cases remainingProjection
          obtain ⟨remaining, _fuel, actual⟩ := accepted.singleton
          exact ⟨[encoded.value], .cons (first owner rfl actual firstProjection typed metadata) .nil, rfl⟩
      | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ :=
            CompatibleEncoding.project_cons remainingProjection
          obtain ⟨remaining, _fuel, headEncoded, tailEncoded, headAt, tailAt, shape⟩ :=
            accepted.cons (by simp)
          cases shape
          cases typed with
          | pair headTyped tailTyped =>
              obtain ⟨native, related, packing⟩ := rest (headEncoded.preserves.signatures.trans owner)
                tailAt remainingProjection tailTyped metadata
              cases native with
              | nil => cases related
              | cons next native =>
                  exact ⟨headEncoded.value :: next :: native,
                    .cons (first owner rfl headAt firstProjection headTyped
                      (tailEncoded.preserves.trans metadata)) related,
                    by simp only [packValues]; rw [packing]⟩
  | empty key value =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      have shape := accepted.nil
      cases shape
      exact ⟨[], .empty _ _ _ _, rfl⟩
  | entry _ _ _ key value rest =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      obtain ⟨remaining, _fuel, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, shape⟩ :=
        accepted.cons
      cases shape
      cases typed with
      | constructed lookup payloadTyped =>
          have same := Option.some.inj (lookup.symm.trans (ambient.basePrefix.constructor_lookup registered.consLookup))
          cases same
          cases payloadTyped with
          | pair pairTyped restTyped => cases pairTyped with
            | pair keyTyped valueTyped =>
                obtain ⟨native, represented, packing⟩ := rest
                  (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
                  tailAt keyProjection valueProjection registered restTyped metadata
                exact ⟨(keyEncoded.value, valueEncoded.value) :: native,
                  .entry
                    (key owner rfl keyAt keyProjection keyTyped
                      (valueEncoded.preserves.trans (tailEncoded.preserves.trans metadata)))
                    (value (keyEncoded.preserves.signatures.trans owner) rfl valueAt valueProjection valueTyped
                      (tailEncoded.preserves.trans metadata)) represented,
                  by simp only [OrderedMapping.encode]; rw [packing]⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
/-! Function leaves obtain their meaning from actual issued factories and the
initialized owned caller. Nested encoding selects the same authenticated
callable independently of its validation fuel or intermediate metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning RecursiveNamedPublicNestedEncodingContext
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedOwnedFunctionValues (Header)

theorem leaf_meaning {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    {artifact : Artifact} {session : Session artifact}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    (atRecipe : ArtifactRecipe artifact recipe)
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : RecursiveNamedPublicMixedArgumentReceipts.Input rows session callerHeader.function.context
      sourceType publicValue source)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    RawMeaning session
      (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
        bodyRegistry faults profile) registry []
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      sourceType publicValue source ∧
    Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩ source sourceType := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  cases receipt with
  | data inputTyped meaning =>
      refine ⟨?_, RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType inputTyped meaning⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      obtain ⟨carrier, image, _typed⟩ := inputTyped
      have encodedAt := accepted.data owner ⟨carrier, image⟩
      obtain ⟨interpreted, interpretedAt, represented⟩ :=
        RecursiveNamedPublicDataInputs.EncodedDataInput.represents
          (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
            bodyRegistry faults profile) []
          ((RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
          encodedAt projected (CallableIndexedAmbient.ambientDefinitions recipe.compiled.indexed).basePrefix typed
      have same := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
      subst interpreted
      exact .compatible compatible.symm (represented.extend metadata (.refl _) (.refl _))
  | named packet member issuance continued handleValue =>
      obtain ⟨callable, imported, represented, sourceTyped⟩ :=
        RecursiveNamedPublicNamedArgumentReceipts.Session.named_value_represents_after
          prepared inputs rows packet member bodyRegistry registry faults profile caller callerHeader
          issuance continued rfl handleValue wellFormed
      refine ⟨?_, sourceTyped⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have sameValue := accepted.function_eq imported
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented
  | builtin issuance continued handleValue =>
      obtain ⟨callable, _same, _sourceType, imported, represented, sourceTyped⟩ :=
        RecursiveNamedPublicBuiltinArgumentReceipts.Session.builtin_value_represents_after
          prepared (headers rows) (keys recipe.compiled) bodyRegistry registry faults profile
          [] callerHeader.function.context ⟨[]⟩ issuance continued rfl handleValue
          (world := (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      refine ⟨?_, sourceTyped⟩
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have sameValue := accepted.function_eq imported
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedLeafMeaning
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
/-! One actual startup input may contain issued functions at arbitrary finite
depth. The original codec and genuine leaf issuance construct its complete
receiving representation and independent Source typing. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedOwnedFunctionValues (Header)

theorem StartAt.nested_argument_represents
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    (callerHeader : Header compiled (Program.ofChecked compiled.sourceProgram))
    {artifact : Artifact} {session : Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root recipe.compiled}
    {native : Environment} {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments fuel checkpoint recipe root
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    {sourceType : TypeSystem.Ty} {publicValue : SourceCorePublicValues.Value} {source : Dynamic.Value} {index : Nat}
    (rawType : root.inputs[index]? = some sourceType)
    (found : publicArguments[index]? = some publicValue)
    (receipt : RecursiveNamedPublicNestedInputs.Input rows session callerHeader.function.context
      sourceType publicValue source)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    ∃ value type, native[index]? = some value ∧ compiled.compatible.checked.catalog.project sourceType = .ok type ∧
      ValueRep compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
          bodyRegistry faults profile)
        [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
        sourceType source value type ∧
      Dynamic.ValueHasType callerHeader.function.context ⟨[]⟩ source sourceType := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  obtain ⟨before, encoded, type, valueAt, typeAt, projected, owner, accepted, extended⟩ :=
    RecursiveNamedPublicNestedRawInputs.StartAt.raw_input started rawType found
  obtain ⟨actual, actualAt, typed⟩ := started.typed.lookup typeAt
  have sameValue : actual = encoded.value := Option.some.inj (actualAt.symm.trans valueAt)
  subst actual
  have leaves := fun {type value source}
      (leaf : RecursiveNamedPublicMixedArgumentReceipts.Input rows session callerHeader.function.context type value source) =>
    RecursiveNamedPublicNestedLeafMeaning.leaf_meaning prepared inputs rows bodyRegistry registry faults profile
      caller callerHeader started.recipe_eq leaf wellFormed
  have represented := RecursiveNamedPublicNestedEncoding.Input.represents receipt started.recipe_eq
    (fun leaf => (leaves leaf).1) owner rfl accepted projected typed (extended.trans metadata)
  exact ⟨encoded.value, type, valueAt, projected, represented,
    RecursiveNamedPublicNestedInputs.Input.source_hasType receipt (fun leaf => (leaves leaf).2)⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
/-! Nested public inputs are assembled in their original argument positions.
The per-position producer follows actual encoding through products,
constructor payloads and ordered mapping entries. Exact list lengths retain
all Source and native arguments, including repeated handles. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning
open RecursiveNamedPublicNestedInputs (Inputs)
open CallableIndexedOwnedFunctionValues (Header)
open CallableIndexedOwnedPreparedFiniteNamedInventories (Inventory headers)
open CallableIndexedOwnedPreparedBootstrapRootState (keys)
open CallableIndexedOwnedFunctionState (State)
open CallableIndexedParameterCertificates (Binding)

private theorem projected_at {checked : SourceCoreCompatibleCatalog.Checked}
    {bindings : List Binding} {index : Nat} {binding : Binding}
    (projected : (bindings.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
      .ok (bindings.map Prod.snd))
    (found : bindings[index]? = some binding) :
    checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  induction bindings generalizing index with
  | nil => simp at found
  | cons head tail ih =>
      simp only [List.map_cons] at projected
      obtain ⟨type, types, headProjected, tailProjected, shape⟩ := CompatibleEncoding.project_cons projected
      have parts := List.cons.inj shape
      have headActual : checked.catalog.project head.1.scheme.body = .ok head.2 := by
        simpa only [← parts.1] using headProjected
      have tailActual : (tail.map (fun binding => binding.1.scheme.body)).mapM checked.catalog.project =
          .ok (tail.map Prod.snd) := by
        simpa only [← parts.2] using tailProjected
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact headActual
      | succ index => exact ih tailActual found

/-- Reconstruct both complete lists from their original positions. Exact
lengths exclude silently discarded native or Source suffixes. -/
private theorem arguments_of_positions
    {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {registry : SourceCoreRawMetadata.Registry}
    {mapping : LocationMap} {world : StoreTyping} {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {bindings : List Binding} {sources : List Dynamic.Value} {native : Environment}
    (sourceLength : sources.length = bindings.length) (nativeLength : native.length = bindings.length)
    (positions : ∀ {index : Nat} {binding : Binding}, bindings[index]? = some binding →
      ∃ source value, sources[index]? = some source ∧ native[index]? = some value ∧
        ValueRep checked registry functions mapping world binding.1.scheme.body source value binding.2 ∧
        Dynamic.ValueHasType context heap source binding.1.scheme.body) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel checked registry functions) mapping world bindings sources native ∧
      Dynamic.ValuesHaveTypes context heap sources (bindings.map (fun binding => binding.1.scheme.body)) := by
  induction bindings generalizing sources native with
  | nil =>
      have sourceNil := List.eq_nil_of_length_eq_zero sourceLength
      have nativeNil := List.eq_nil_of_length_eq_zero nativeLength
      subst sources
      subst native
      exact ⟨.nil, .nil⟩
  | cons binding bindings ih =>
      cases sources with
      | nil => simp at sourceLength
      | cons source sources =>
          cases native with
          | nil => simp at nativeLength
          | cons value native =>
              obtain ⟨actualSource, actualValue, sourceAt, valueAt, represented, typed⟩ :=
                positions (index := 0) rfl
              have sameSource : source = actualSource := Option.some.inj sourceAt
              have sameValue : value = actualValue := Option.some.inj valueAt
              subst actualSource
              subst actualValue
              simp only [List.length_cons] at sourceLength nativeLength
              have remaining := ih (Nat.succ.inj sourceLength) (Nat.succ.inj nativeLength) (by
                intro index next found
                exact positions (index := index + 1) found)
              exact ⟨.cons represented remaining.1, .cons typed remaining.2⟩

/-- Actual nested startup constructs all argument representations and Source
value typing at the body's receiving registry. Structural input receipts
preserve raw types, container order and the actual issuance histories. -/
theorem StartAt.nested_arguments_receiving
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    (inputs : List (CallableIndexedOwnedPreparedFiniteNamedInventories.Input compiled))
    (rows : Inventory inputs)
    (bodyRegistry registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (caller : State (headers rows) (keys compiled)
      ⟨[], [], (RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type,
        ⟨[]⟩, RecursiveNamedCatalogPreparedInitialization.store compiled,
        SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed⟩)
    {artifact : Artifact} {session : Session artifact}
    {key : SourceCoreIndexedSession.Key} {publicArguments : List SourceCorePublicValues.Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} {root : Root compiled}
    {header : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {native : Environment} {arguments : List Dynamic.Value}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key publicArguments fuel checkpoint recipe
      ((Recipe.prepare_compiled prepared).symm ▸ root)
      ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      (RecursiveNamedCatalogPreparedInitialization.store compiled) native encodedValues)
    (selected : RecursiveNamedPublicRootMeaning.RootSelection
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) (headers rows) root header)
    (receipts : Inputs rows session header.function.context
      (header.bindings.map (fun binding => binding.1.scheme.body)) publicArguments arguments)
    (metadata : SourceCoreRawMetadata.Extends encodedValues.registry registry)
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram)) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys compiled)
          bodyRegistry faults profile))
      [] ((RecursiveNamedCatalogPreparedInitialization.store compiled).map Core.Value.type)
      header.bindings arguments native ∧
    Dynamic.ValuesHaveTypes header.function.context ⟨[]⟩ arguments header.types := by
  have sameCompiled := Recipe.prepare_compiled prepared
  cases sameCompiled
  have arity := congrArg List.length (header.parameters.symm.trans header.agreement.parameters)
  simp only [List.length_map] at arity
  have nativeLength := congrArg List.length started.typed.type_tags
  rw [selected.shape.1] at nativeLength
  simp only [List.length_map] at nativeLength
  have nativeCount : native.length = header.bindings.length := nativeLength.trans arity.symm
  have sourceCount : arguments.length = header.bindings.length := by
    simpa only [List.length_map] using receipts.source_length
  have record := CallableIndexedActualNamedSourceReceipts.header_record recipe.compiled header
  have projected := RecursiveNamedHeaderParameterProjections.projections_of_record
    header rfl wellFormed record
  have rawInputs := (RecursiveNamedPublicRootSourceSignature.inputs_and_result selected).1
  have assembled := arguments_of_positions (functions :=
      CallableIndexedOwnedContextualCellOrigins.functions (headers rows) (keys recipe.compiled)
        bodyRegistry faults profile) (registry := registry) (mapping := [])
      (world := (RecursiveNamedCatalogPreparedInitialization.store recipe.compiled).map Core.Value.type)
      (context := header.function.context) (heap := ⟨[]⟩)
      sourceCount nativeCount (by
        intro index binding bindingAt
        have rawAt : (header.bindings.map (fun binding => binding.1.scheme.body))[index]? =
            some binding.1.scheme.body := by
          simp only [List.getElem?_map, bindingAt, Option.map_some]
        obtain ⟨publicValue, source, publicAt, sourceAt, receipt⟩ := receipts.lookup rawAt
        have bindingProjected := projected_at projected bindingAt
        have rawRoot : root.inputs[index]? = some binding.1.scheme.body := by
          rw [rawInputs]
          exact rawAt
        obtain ⟨value, type, valueAt, projection, represented, typed⟩ :=
          RecursiveNamedPublicNestedArgumentReceipts.StartAt.nested_argument_represents
            prepared inputs rows bodyRegistry registry faults profile caller header
            started rawRoot publicAt receipt metadata wellFormed
        have typeEq := Except.ok.inj (projection.symm.trans bindingProjected)
        exact ⟨source, value, sourceAt, valueAt, typeEq ▸ represented, typed⟩)
  have typesEq : header.bindings.map (fun binding => binding.1.scheme.body) = header.types := by
    simpa only [header.parameters, List.map_map, Function.comp_def] using header.extended.bodyTypes_eq
  exact ⟨assembled.1, typesEq ▸ assembled.2⟩


end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicNestedArgumentsReceiving
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
/-! A following public start uses the native state of the actual preceding
successful completion. Optional named/builtin issuance preserves that state;
Source closure and heap meaning remain the returned semantic proof's job. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession RecursiveNamedPublicStartMeaning

/-- Reconcile the next real startup with the previous returned world and
store, including a finite sequence of actual state-preserving issuances. -/
theorem StartAt.after_succeeded
    {artifact : Artifact} {previous : Checkpoint artifact}
    {executionFuel outputFuel : Nat} {generation : SourceCorePublicValues.ExportGeneration}
    {result : Core.Value} {returnedStore : Store} {completion : Completion artifact}
    (returned : previous.SucceededResultAt executionFuel outputFuel generation result returnedStore completion)
    {session : Session artifact} (continued : completion.session.IssuanceChain session)
    {key : Key} {arguments : List SourceCorePublicValues.Value} {inputFuel : Nat}
    {checkpoint : Checkpoint artifact} {recipe : Recipe} {root : Root recipe.compiled}
    {world : StoreTyping} {store : Store} {native : Environment}
    {encodedValues : SourceCoreCompatibleValues.Context}
    (started : StartAt session key arguments inputFuel checkpoint recipe root world store native encodedValues) :
    world = returnedStore.map Core.Value.type ∧ store = returnedStore := by
  have nativeAt := continued.same_runtime.native_at returned.native_at.2
  have current := started.state
  cases session
  rename_i authority actualWorld actualStore stored environmentTyped registry values owner sourcePrefix
  change actualWorld = returnedStore.map Core.Value.type ∧ actualStore = returnedStore at nativeAt
  change actualWorld = world ∧ actualStore = store at current
  exact ⟨current.1.symm.trans nativeAt.1, current.2.symm.trans nativeAt.2⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedSessionInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputs
/-! Input descriptions may reuse one actual returned callable at any finite
number of positions, alongside independently typed data. Constructor payloads
and mapping entries keep their original raw metadata, count and order. The
certificate itself contains no native representation or execution premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputs
open Core Frontend SourceInference
open SourceCoreIndexedSession

mutual
  inductive Input (returnedType : TypeSystem.Ty) (returnedValue : SourceCorePublicValues.Value)
      (returnedSource : Dynamic.Value) (context : SourceSemantics.Context) :
      TypeSystem.Ty → SourceCorePublicValues.Value → Dynamic.Value → Prop where
    | returned : Input returnedType returnedValue returnedSource context returnedType returnedValue returnedSource
    | data {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (typed : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value type)
        (meaning : RecursiveNamedPublicDataInputs.Means value source) :
        Input returnedType returnedValue returnedSource context type value source
    | product {leftType rightType : TypeSystem.Ty}
        {left right : SourceCorePublicValues.Value} {first second : Dynamic.Value}
        (leftInput : Input returnedType returnedValue returnedSource context leftType left first)
        (rightInput : Input returnedType returnedValue returnedSource context rightType right second) :
        Input returnedType returnedValue returnedSource context (.product leftType rightType) (.product left right) (.product first second)
    | constructed {metadata : DataConstructorInstantiation}
        {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
        (valid : DataConstructorInstantiation.Valid context metadata)
        (payloads : Inputs returnedType returnedValue returnedSource context metadata.payloadTypes values sources) :
        Input returnedType returnedValue returnedSource context metadata.resultType (.constructed metadata values) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty}
        {entries : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (stored : Entries returnedType returnedValue returnedSource context key value entries sources) :
        Input returnedType returnedValue returnedSource context (.mapping key value) (.mapping key value entries) (.mapping key value sources)
    | comptime {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
        (input : Input returnedType returnedValue returnedSource context type value source) :
        Input returnedType returnedValue returnedSource context (.comptime type) value source

  inductive Inputs (returnedType : TypeSystem.Ty) (returnedValue : SourceCorePublicValues.Value)
      (returnedSource : Dynamic.Value) (context : SourceSemantics.Context) :
      List TypeSystem.Ty → List SourceCorePublicValues.Value → List Dynamic.Value → Prop where
    | nil : Inputs returnedType returnedValue returnedSource context [] [] []
    | cons {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
        {value : SourceCorePublicValues.Value} {values : List SourceCorePublicValues.Value}
        {source : Dynamic.Value} {sources : List Dynamic.Value}
        (head : Input returnedType returnedValue returnedSource context type value source)
        (tail : Inputs returnedType returnedValue returnedSource context types values sources) :
        Inputs returnedType returnedValue returnedSource context (type :: types) (value :: values) (source :: sources)

  inductive Entries (returnedType : TypeSystem.Ty) (returnedValue : SourceCorePublicValues.Value)
      (returnedSource : Dynamic.Value) (context : SourceSemantics.Context) : TypeSystem.Ty → TypeSystem.Ty →
      List (SourceCorePublicValues.Value × SourceCorePublicValues.Value) →
      List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty (key value : TypeSystem.Ty) : Entries returnedType returnedValue returnedSource context key value [] []
    | entry {key value : TypeSystem.Ty}
        {first second : SourceCorePublicValues.Value} {left right : Dynamic.Value}
        {rest : List (SourceCorePublicValues.Value × SourceCorePublicValues.Value)}
        {sources : List (Dynamic.Value × Dynamic.Value)}
        (keyInput : Input returnedType returnedValue returnedSource context key first left)
        (valueInput : Input returnedType returnedValue returnedSource context value second right)
        (remaining : Entries returnedType returnedValue returnedSource context key value rest sources) :
        Entries returnedType returnedValue returnedSource context key value ((first, second) :: rest) ((left, right) :: sources)
end

variable {returnedType : TypeSystem.Ty} {returnedValue : SourceCorePublicValues.Value}
  {returnedSource : Dynamic.Value} {context : SourceSemantics.Context}

theorem Input.source_hasType {type : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {source : Dynamic.Value} (receipt : Input returnedType returnedValue returnedSource context type value source)
    {heap : Dynamic.Heap}
    (returnedTyped : Dynamic.ValueHasType context heap returnedSource returnedType) :
    Dynamic.ValueHasType context heap source type := by
  induction receipt using Input.rec
    (motive_2 := fun types _ sources _ => Dynamic.ValuesHaveTypes context heap sources types)
    (motive_3 := fun key value _ sources _ => Dynamic.MappingEntriesHaveTypes context heap sources key value) with
  | returned => exact returnedTyped
  | data typed meaning => exact RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped.source_hasType typed meaning
  | product _ _ left right => exact .product left right
  | constructed valid _ payloads => exact .constructed valid payloads
  | mapping _ entries => exact .mapping entries
  | comptime _ typed => exact .comptime typed
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty key value => exact .nil key value
  | entry _ _ _ key value rest => exact .cons key value rest

theorem Inputs.source_hasTypes {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs returnedType returnedValue returnedSource context types values sources)
    {heap : Dynamic.Heap}
    (returnedTyped : Dynamic.ValueHasType context heap returnedSource returnedType) :
    Dynamic.ValuesHaveTypes context heap sources types := by
  induction types generalizing values sources with
  | nil => cases receipts; exact .nil
  | cons type types ih => cases receipts with
    | cons head tail => exact .cons (head.source_hasType returnedTyped) (ih tail)

theorem Inputs.source_length {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs returnedType returnedValue returnedSource context types values sources) : sources.length = types.length := by
  induction types generalizing values sources with
  | nil => cases receipts; rfl
  | cons type types ih => cases receipts with
    | cons _ tail => exact congrArg Nat.succ (ih tail)

theorem Inputs.lookup {types : List TypeSystem.Ty}
    {values : List SourceCorePublicValues.Value} {sources : List Dynamic.Value}
    (receipts : Inputs returnedType returnedValue returnedSource context types values sources)
    {index : Nat} {type : TypeSystem.Ty} (found : types[index]? = some type) :
    ∃ value source, values[index]? = some value ∧ sources[index]? = some source ∧
      Input returnedType returnedValue returnedSource context type value source := by
  induction types generalizing values sources index with
  | nil => simp at found
  | cons type types ih => cases receipts with
    | cons head tail =>
      cases index with
      | zero =>
          have same := Option.some.inj found
          cases same
          exact ⟨_, _, rfl, rfl, head⟩
      | succ index =>
          obtain ⟨value, source, valueAt, sourceAt, receipt⟩ := ih tail found
          exact ⟨value, source, valueAt, sourceAt, receipt⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedInputs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedEncoding
/-! A returned callable can occur repeatedly inside subsequent public inputs.
Its original value representation supplies each function occurrence; the real
codec selects exactly that payload. Data and all containers use their actual
encoding receipts in one fixed receiving metadata registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedEncoding
open Core Frontend SourceInference GeneralHeap CompatiblePayload DataPatternValues
open SourceCoreIndexedSession RecursiveNamedPublicReturnedInputs RecursiveNamedPublicNestedEncodingContext

variable {artifact : Artifact} {session : Session artifact} {recipe : Recipe}
  {ambient : AmbientDefinitions recipe.compiled.compatible.checked.catalog.definitions}
  {functions : FunctionModel recipe.compiled.compatible.checked.catalog ambient}
  {receiving : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
  {context : SourceSemantics.Context}

private theorem data_meaning
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (inputTyped : RecursiveNamedPublicDataArgumentReceipts.PublicDataTyped context value sourceType)
    (meaning : RecursiveNamedPublicDataInputs.Means value source) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  cases artifact
  rename_i authority actualRecipe
  change actualRecipe = recipe at atRecipe
  subst actualRecipe
  intro fuel before expected encoded type owner compatible accepted projected typed metadata
  obtain ⟨carrier, image, _typed⟩ := inputTyped
  have encodedAt := accepted.data owner ⟨carrier, image⟩
  obtain ⟨interpreted, interpretedAt, represented⟩ :=
    RecursiveNamedPublicDataInputs.EncodedDataInput.represents functions mapping world
      encodedAt projected ambient.basePrefix typed
  have same := RecursiveNamedPublicRuntimeMeaning.means_functional interpretedAt meaning
  subst interpreted
  exact .compatible compatible.symm (represented.extend metadata (.refl _) (.refl _))

variable {returnedType : TypeSystem.Ty} {returnedValue : SourceCorePublicValues.Value}
  {returnedSource : Dynamic.Value} {returnedNative : Core.Value} {returnedNativeType : Core.Ty}
  {returnedFuel : Nat} {handle : SourceCorePublicValues.Handle}

private theorem represents
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input returnedType returnedValue returnedSource context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : session.EncodesAt returnedFuel returnedType returnedValue returnedNative)
    (handleValue : returnedValue = .function handle)
    (represented : ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      returnedType returnedSource returnedNative returnedNativeType) :
    RawMeaning session functions receiving mapping world sourceType value source := by
  induction receipt using Input.rec
    (motive_2 := fun types values sources _ => PayloadMeaning session functions receiving mapping world types values sources)
    (motive_3 := fun key value entries sources _ => EntriesMeaning session functions receiving mapping world key value entries sources) with
  | returned =>
      intro fuel before expected encoded type owner compatible accepted projected typed metadata
      rw [handleValue] at accepted
      have actualImport := imported
      rw [handleValue] at actualImport
      have sameValue := accepted.function_eq actualImport
      have actualProjection := (CompatibleEncoding.project_compatible compatible).symm.trans projected
      have sameType := Except.ok.inj (represented.projection.symm.trans actualProjection)
      rw [sameValue]
      exact sameType ▸ represented
  | data inputTyped meaning => exact data_meaning atRecipe inputTyped meaning
  | product _ _ first second =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      have view := compatible
      simp only [SourceCoreRawMetadata.runtimeType] at view
      obtain ⟨remaining, _fuel, left, right, leftAt, rightAt, shape⟩ := accepted.product view
      cases shape
      obtain ⟨a, b, leftProjected, rightProjected, rfl⟩ := CompatibleEncoding.product_projection view projected
      cases typed with
      | pair leftTyped rightTyped =>
          exact .product
            (first owner (SourceCoreRawMetadata.runtimeType_idempotent _) leftAt leftProjected leftTyped
              (right.preserves.trans metadata))
            (second (left.preserves.signatures.trans owner)
              (SourceCoreRawMetadata.runtimeType_idempotent _) rightAt rightProjected rightTyped metadata)
  | constructed _ _ payloads =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.constructed atRecipe payloads owner accepted projected typed metadata)
  | mapping _ entries =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible compatible.symm
        (RecursiveNamedPublicNestedEncodingContainers.mapping_value atRecipe entries owner compatible accepted projected typed metadata)
  | @comptime sourceType _ _ _ child =>
      intro fuel registry expected encoded type owner compatible accepted projected typed metadata
      exact .compatible (actual := sourceType) rfl (child owner compatible accepted projected typed metadata)
  | nil =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      have shape := accepted.nil
      cases shape
      cases projected
      exact ⟨[], .nil, rfl⟩
  | @cons type types value values source sources head tail first rest =>
      intro fuel registry encoded coreTypes owner accepted projected typed metadata
      obtain ⟨coreType, remainingTypes, firstProjection, remainingProjection, rfl⟩ :=
        CompatibleEncoding.project_cons projected
      cases types with
      | nil =>
          cases tail
          cases remainingProjection
          obtain ⟨remaining, _fuel, actual⟩ := accepted.singleton
          exact ⟨[encoded.value], .cons (first owner rfl actual firstProjection typed metadata) .nil, rfl⟩
      | cons next types =>
          obtain ⟨nextType, restTypes, nextProjection, restProjection, rfl⟩ :=
            CompatibleEncoding.project_cons remainingProjection
          obtain ⟨remaining, _fuel, headEncoded, tailEncoded, headAt, tailAt, shape⟩ :=
            accepted.cons (by simp)
          cases shape
          cases typed with
          | pair headTyped tailTyped =>
              obtain ⟨native, related, packing⟩ := rest (headEncoded.preserves.signatures.trans owner)
                tailAt remainingProjection tailTyped metadata
              cases native with
              | nil => cases related
              | cons next native =>
                  exact ⟨headEncoded.value :: next :: native,
                    .cons (first owner rfl headAt firstProjection headTyped
                      (tailEncoded.preserves.trans metadata)) related,
                    by simp only [packValues]; rw [packing]⟩
  | empty key value =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      have shape := accepted.nil
      cases shape
      exact ⟨[], .empty _ _ _ _, rfl⟩
  | entry _ _ _ key value rest =>
      intro fuel registry layout encoded owner accepted keyProjection valueProjection registered typed metadata
      obtain ⟨remaining, _fuel, keyEncoded, valueEncoded, tailEncoded, keyAt, valueAt, tailAt, shape⟩ :=
        accepted.cons
      cases shape
      cases typed with
      | constructed lookup payloadTyped =>
          have same := Option.some.inj (lookup.symm.trans (ambient.basePrefix.constructor_lookup registered.consLookup))
          cases same
          cases payloadTyped with
          | pair pairTyped restTyped => cases pairTyped with
            | pair keyTyped valueTyped =>
                obtain ⟨native, represented, packing⟩ := rest
                  (valueEncoded.preserves.signatures.trans (keyEncoded.preserves.signatures.trans owner))
                  tailAt keyProjection valueProjection registered restTyped metadata
                exact ⟨(keyEncoded.value, valueEncoded.value) :: native,
                  .entry
                    (key owner rfl keyAt keyProjection keyTyped
                      (valueEncoded.preserves.trans (tailEncoded.preserves.trans metadata)))
                    (value (keyEncoded.preserves.signatures.trans owner) rfl valueAt valueProjection valueTyped
                      (tailEncoded.preserves.trans metadata)) represented,
                  by simp only [OrderedMapping.encode]; rw [packing]⟩

/-- The single preceding result supplies the only function leaf. All other
positions are discharged from independent data input certificates, and every
container preserves its full ordered native payload. -/
theorem Input.meaning
    {sourceType : TypeSystem.Ty} {value : SourceCorePublicValues.Value} {source : Dynamic.Value}
    (receipt : Input returnedType returnedValue returnedSource context sourceType value source)
    (atRecipe : RecursiveNamedPublicStartMeaning.ArtifactRecipe artifact recipe)
    (imported : session.EncodesAt returnedFuel returnedType returnedValue returnedNative)
    (handleValue : returnedValue = .function handle)
    (represented : ValueRep recipe.compiled.compatible.checked receiving functions mapping world
      returnedType returnedSource returnedNative returnedNativeType)
    {heap : Dynamic.Heap}
    (returnedTyped : Dynamic.ValueHasType context heap returnedSource returnedType) :
    RawMeaning session functions receiving mapping world sourceType value source ∧
      Dynamic.ValueHasType context heap source sourceType :=
  ⟨represents receipt atRecipe imported handleValue represented, receipt.source_hasType returnedTyped⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicReturnedEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
/-! Static body extraction connects to actual public execution through an
existential receipt whose own diagnostics are interpreted. A receipt is selected
only after this interpretation is supplied. All source input typing, staging,
heap and Entry conditions remain independent. Capture prefixes are zero; general
lambda/indirect/builtin closure assembly and Header inventory construction are
separate boundaries. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open SourceCoreIndexedSession RecursiveNamedCatalog RecursiveNamedCatalogNativeContexts
open RecursiveNamedCatalogInvocationBounds
open CallableAncestryPairedLookup

section Static
variable {checked : SourceCoreCompatibleCatalog.Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {header : Header prepared values ambient.definitions program}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {administrative : Core.Context} {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

variable {authenticated : Bool}

/-- Static compiler inputs and an extraction receipt with its own interpreted
diagnostics. This proposition neither quantifies over all receipts nor chooses
an arbitrary receipt before asking whether its diagnostics hold. The shared
indices fix the Header, compiler, read fuel, administrative context and emitted
body. The equalities below expose the same accepted lowering, projection and
source signatures; the result itself keeps the generated flow and its Tree. -/
def InputsWith (authenticated tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  ∃ (actual : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative),
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative,
      result.accepted = actual.accepted ∧ result.projection = actual.projection ∧
      result.signatures = actual.sourceSignatures ∧ result.extracted.diagnostics registry faults

/-- Package exactly this static extraction and this interpretation. Its accepted
body, generated flow, Tree and complete ledger remain in the receipt. -/
theorem InputsWith.of_receipt
    (actual : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
    (result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax administrative)
    (interpreted : result.extracted.diagnostics registry faults) :
    InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  ⟨actual, result, Subsingleton.elim _ _, Subsingleton.elim _ _, Subsingleton.elim _ _, interpreted⟩

/-- A good receipt is eliminated only inside a proposition. No data getter or
runtime law is added to the input package. -/
theorem InputsWith.profile
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (inputs : InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults) :
    Nonempty (RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      administrative registry faults) := by
  obtain ⟨_, result, _, _, _, interpreted⟩ := inputs
  exact ⟨result.profile catalog interpreted⟩

abbrev Inputs (tracked : Bool) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (headers : Inventory prepared values ambient.definitions program)
    (header : Header prepared values ambient.definitions program)
    (compilation : SourceCoreFunctions.Context) (expressionSyntax : ExpressionId → Prop)
    (administrative : Core.Context) (registry : SourceCoreRawMetadata.Registry)
    (faults : FunctionCalls.FaultRep) : Prop :=
  InputsWith false tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults

/-- Package exactly this static extraction and this interpretation. Its accepted
body, generated flow, Tree and complete ledger remain in the receipt. -/
theorem Inputs.of_receipt
    (actual : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative)
    (result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax administrative)
    (interpreted : result.extracted.diagnostics registry faults) :
    Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults :=
  InputsWith.of_receipt actual result interpreted

/-- A good receipt is eliminated only inside a proposition. No data getter or
runtime law is added to the input package. -/
theorem Inputs.profile
    (catalog : SignatureCatalogWellFormed values.checked.signatures)
    (inputs : Inputs tracked diagnosticPolicy headers header compilation expressionSyntax administrative registry faults) :
    Nonempty (RuntimeMatchProfileFor diagnosticPolicy headers header compilation header.readFuel expressionSyntax
      administrative registry faults) := by
  exact InputsWith.profile catalog inputs
end Static

section ActualCache
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
  (accepted : Recipe.prepare compiled = .ok recipe)
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory compiled.indexed.ancestry values ambient.definitions program}
  {header rootHeader : Header compiled.indexed.ancestry values ambient.definitions program}
  {root : Root compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root rootHeader)
  (definitions : ambient.definitions = compiled.indexed.layouts.definitions)
  (sameCache : header.compiled.closures = compiled.indexed.secondPass.closures)

include accepted selected definitions sameCache in
/-- The real selected root supplies an indexed native entry. Its accepted
assembly types the same cached lambda; actual preparation supplies its support.
Neither fact supplies source typing or catalog authority. -/
theorem cached_facts :
    ∃ suffix : Core.Context,
      HasType (compiled.indexed.base.globals.map (·.referenceType) ++
        .cell compiled.indexed.ancestry.layout.frame.type :: suffix)
        (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
        header.named.signature.functionType ambient.definitions ∧
      NativeExpressionContextSupport.supported
        (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code)
        (compiled.indexed.base.globals.length + 1) = true := by
  obtain ⟨_, nativeEntry, member, _, _⟩ := selected
  have cached := header.cached
  rw [sameCache] at cached
  have typed := CallableIndexedCachedNativeTyping.prepared_native_closure compiled.indexedPrepared member cached
    (CallableIndexedPreparedInventories.cached_global_at compiled header.selected)
  exact ⟨_, by simpa only [← definitions] using typed,
    RecursiveNamedCatalogPreparedInitialization.supported_cached accepted cached⟩

section EvidenceExtraction
variable (authenticated : Bool)
variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem extract_source_with_evidence :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.ReceiptWith authenticated diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        InputsWith authenticated tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  obtain ⟨suffix, typed, support⟩ := cached_facts accepted selected definitions sameCache
  obtain ⟨result⟩ := RecursiveNamedCatalogRuntimeProfileFactory.extract_source_with actualInputs typed support complete globals entry
  exact ⟨result, fun _ interpreted => InputsWith.of_receipt actualInputs result interpreted⟩
end EvidenceExtraction

variable {locations : Locations} {functions : FunctionModel values.checked.catalog ambient}
  {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {before : Dynamic.Heap}
  {initialStore : Store} {initialMap : LocationMap} {initialWorld : StoreTyping}
  {administrative actualContext : Core.Context} {actual : Environment} {ξ : Renaming} {frameLocation : Location}
  {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame}
  {compilation : SourceCoreFunctions.Context} {expressionSyntax : ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {tracked : Bool}
  (actualInputs : RecursiveNamedCatalogRuntimeProfileFactory.Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
    (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative))
  (complete : Complete headers) (globals : header.globals = compiled.indexed.base.globals.length)
  (entry : BodyState headers locations 0 functions registry header arguments before initialStore initialMap initialWorld
    administrative actualContext actual ξ frameLocation current ghost)

include accepted selected definitions sameCache actualInputs complete globals entry in
/-- The existing single extractor returns a receipt before its diagnostic
obligation is interpreted. Only that result is packaged; no arbitrary choice of
a Nonempty Receipt and no universal diagnostic premise is used. -/
theorem extract_source :
    ∃ result : RecursiveNamedCatalogRuntimeProfileFactory.Receipt diagnosticPolicy headers header compilation expressionSyntax
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative),
      ∀ faults : FunctionCalls.FaultRep, result.extracted.diagnostics registry faults →
        Inputs tracked diagnosticPolicy headers header compilation expressionSyntax
          (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) registry faults := by
  exact extract_source_with_evidence (authenticated := false) accepted selected definitions sameCache actualInputs complete globals entry
end ActualCache

section EvidenceMeaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable (authenticated : Bool) {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      InputsWith authenticated (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel_evidence
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  classical
  let profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults := by
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
    have good := Classical.choose_spec (inputs header member entry)
    let result := Classical.choose good
    exact result.profile catalog (Classical.choose_spec good).2.2.2
  exact RecursiveNamedPublicRuntimeMeaning.has_sufficient_fuel_evidence authenticated functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program_evidence
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  classical
  let profiles : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      RuntimeMatchProfileForWith authenticated diagnosticPolicy headers header (compilation header) header.readFuel (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults := by
    intro header member arguments before initialStore initialMap initialWorld administrative actualContext actual ξ frameLocation current ghost entry
    have good := Classical.choose_spec (inputs header member entry)
    let result := Classical.choose good
    exact result.profile catalog (Classical.choose_spec good).2.2.2
  exact RecursiveNamedPublicRuntimeMeaning.completed_reflects_program_evidence authenticated functions extension faithful observations runtimeViews
    uninitialized missing escaped prefixMatches profiles caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end EvidenceMeaning

section Meaning
open GeneralHeap ReadOnly CompatiblePayload CoreProof
open RecursiveNamedCatalog RecursiveNamedPublicStartMeaning RecursiveNamedPublicDataInputs
open RecursiveNamedCatalogInvocationBounds
variable {artifact : Artifact} {session : Session artifact} {key : Key}
  {publicArguments : List SourceCorePublicValues.Value} {boundaryFuel : Nat}
  {checkpoint : Checkpoint artifact} {recipe : Recipe}
  {encodedValues : SourceCoreCompatibleValues.Context}
  {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory recipe.compiled.indexed.ancestry values ambient.definitions program} {locations : Locations}
  {compilation : Header recipe.compiled.indexed.ancestry values ambient.definitions program → SourceCoreFunctions.Context}
  {expressionSyntax : Header recipe.compiled.indexed.ancestry values ambient.definitions program → ExpressionId → Prop}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  (functions : FunctionModel values.checked.catalog ambient)
  (extension : SourceCoreRawMetadata.Extends values.registry encodedValues.registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations values.checked.catalog functions identities)
  (runtimeViews : FunctionRuntimeViews functions)
  {faults : FunctionCalls.FaultRep}
  (uninitialized : ∀ header ∈ headers, ∀ id location, faults (.uninitializedLocation location) (header.reasonAt id))
  (missing : ∀ header ∈ headers, ∀ id key value tag, MetadataRep encodedValues.registry (.mapping key value) tag →
    faults (.missingMappingDefault value) ((header.reasonAt id).add tag))
  (escaped : ∀ header ∈ headers, faults .controlEscapedFunction header.escaped)
  (prefixMatches : ∀ header ∈ headers, (compilation header).administrativePrefix = 1)
  {tracked : Header recipe.compiled.indexed.ancestry values ambient.definitions program → Bool}
  (catalog : SignatureCatalogWellFormed values.checked.signatures)
  (inputs : ∀ header, header ∈ headers →
    ∀ {arguments : List Dynamic.Value} {before : Dynamic.Heap} {initialStore : Store}
      {initialMap : LocationMap} {initialWorld : StoreTyping} {administrative actualContext : Core.Context}
      {actual : Environment} {ξ : Renaming} {frameLocation : Location}
      {current : CallableIndexedHistory.NativeFrame} {ghost : CallableIndexedHistory.GhostFrame},
      BodyState headers locations 0 functions encodedValues.registry header arguments before initialStore initialMap initialWorld
        administrative actualContext actual ξ frameLocation current ghost →
      Inputs (tracked header) diagnosticPolicy headers header (compilation header) (expressionSyntax header)
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: administrative) encodedValues.registry faults)

variable {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  (caller : Entry headers locations 0 0 [] mapping world before store
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed))
  {header : Header recipe.compiled.indexed.ancestry values ambient.definitions program}
  {root : SourceCoreIndexedSession.Root recipe.compiled} (selected : RecursiveNamedPublicRootMeaning.RootSelection headers root header)
  {arguments : List Dynamic.Value} {payloads : List Core.Value}
  (started : StartAt session key publicArguments boundaryFuel checkpoint recipe root world store payloads encodedValues)
  (data : ∀ argument ∈ publicArguments, DataPublic argument)
  (sameChecked : values.checked = recipe.compiled.compatible.checked)
  (programTyped : ProgramWellFormed program)
  (record : SourceCompilationPlan.exactSpecialization recipe.compiled.indexed.base.plan header.named.signature.key =
    .ok header.named.specialized)
  (meanings : RecursiveNamedPublicDataInputs.Meanings publicArguments arguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions mapping world before store)


include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Source execution is preserved by the actual checkpoint initial state.
The exact encoded prefix and full store are transported by equality only. -/
theorem has_sufficient_fuel
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (executed : Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after) :
    ∃ value finalStore finalMap finalWorld required,
      (∀ fuel, required ≤ fuel → checkpoint.NativeDone fuel value finalStore) ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact has_sufficient_fuel_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps executed

include extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps in
/-- Original checkpoint completion reflects through the same initial state.
Source representation, staging and heap conditions remain independent. -/
theorem completed_reflects_program
    (admitted : Staging.ProgramHasStages program)
    (heapTyped : Dynamic.HeapWellTyped header.function.context before)
    (argumentsTyped : Dynamic.ValuesHaveTypes header.function.context before arguments header.types)
    {fuel : Nat} {value : Core.Value} {finalStore : Core.Store}
    (completed : checkpoint.NativeDone fuel value finalStore) :
    ∃ outcome after finalMap finalWorld,
      Dynamic.ProgramOutcome program (RecursiveNamedProgramEntrySource.entry header arguments) before outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel values.checked encodedValues.registry functions)
        finalMap finalWorld header.function.resultType header.output faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents values.checked encodedValues.registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Nonempty (Entry headers locations 0 0 [] finalMap finalWorld after finalStore
        (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed)) := by
  exact completed_reflects_program_evidence false functions extension faithful observations runtimeViews uninitialized missing escaped prefixMatches catalog inputs caller selected started data sameChecked programTyped record meanings heaps admitted heapTyped argumentsTyped completed

end Meaning

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicRuntimeFactoryMeaning
end
