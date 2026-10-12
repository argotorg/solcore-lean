import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicOutputSelections
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers
import Solcore.SourceSemantics.CoreLowering.CompatibleMappingEncoding

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
