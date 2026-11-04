import Solcore.SourceSemantics.CoreLowering.GenericHeapPayload
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.CoreLowering.OrderedMapping
import Solcore.SourceSemantics.CoreLowering.Internal.Data.HeapsAndBindings
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.CoreLowering.Internal.Statements.GenericMatches
import Solcore.SourceSemantics.CoreLowering.ContractedFunctionValues

/-!
# Data: payloads

The data payload, with defaults, encoding, equality, mappings, fields and the read and fault paths through it.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayload
/-! Compositional data payloads for the existing mapped heap model. Nominal
metadata, ordered mapping entries, and proxy identities are retained. Function
leaves come from a separate authenticated model; typing does not establish
closure code semantics or source capture validity. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues

mutual
  inductive ValueRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
      (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping) :
      TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
    | unit : ValueRep catalog signatures functions mapping world .unit .unit .unit .unit
    | bool (value : Bool) : ValueRep catalog signatures functions mapping world .bool (.bool value) (.bool value) .bool
    | word (value : Word) : ValueRep catalog signatures functions mapping world .word (.word value) (.word value) .word
    | integer (value : Int) : ValueRep catalog signatures functions mapping world .integer (.integer value) (.integer value) .integer
    | product {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value} {aType bType : Ty}
        (first : ValueRep catalog signatures functions mapping world leftType left a aType)
        (second : ValueRep catalog signatures functions mapping world rightType right b bType) :
        ValueRep catalog signatures functions mapping world (.product leftType rightType)
          (.product left right) (.pair a b) (.product aType bType)
    | function {parameter result : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (represented : functions.Represents mapping world (.function parameter result) source value type) :
        ValueRep catalog signatures functions mapping world (.function parameter result) source value type
    | proxy {inner : TypeSystem.Ty} {id : DataTypeId}
        (identity : catalog.identity? (.proxy inner) = some id)
        (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, 0⟩ = some .unit) :
        ValueRep catalog signatures functions mapping world (.proxy inner) (.proxy inner)
          (.constructed ⟨id, 0⟩ .unit) (.namedData id)
    | mapping {key value : TypeSystem.Ty} {layout : Core.OrderedMapping.Layout}
        {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
        (identity : catalog.identity? (.mapping key value) = some layout.dataType)
        (keyProjected : catalog.project key = .ok layout.keyType)
        (valueProjected : catalog.project value = .ok layout.valueType)
        (registered : layout.Registered catalog.definitions)
        (contents : EntriesRep catalog signatures functions mapping world key value layout.keyType layout.valueType sources entries) :
        ValueRep catalog signatures functions mapping world (.mapping key value) (.mapping key value sources)
          (Core.OrderedMapping.encode layout entries) layout.type
    | constructed {type : TypeSystem.Ty} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
        {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
        {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
        (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
        (result : metadata.resultType = type)
        (authenticated : catalog.resolveConstructor signatures metadata = .ok tag)
        (projection : catalog.project type = .ok (.namedData tag.owner))
        (registered : catalog.definitions.lookupConstructorPayloadType? tag = some (SourceCoreDataMatches.bundleType types))
        (payloads : ValuesRep catalog signatures functions mapping world metadata.payloadTypes sources values types) :
        ValueRep catalog signatures functions mapping world type (.constructed metadata sources)
          (.constructed tag (packValues values)) (.namedData tag.owner)
    | comptime {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (represented : ValueRep catalog signatures functions mapping world inner source value type) :
        ValueRep catalog signatures functions mapping world (.comptime inner) source value type
  inductive ValuesRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
      (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping) :
      List TypeSystem.Ty → List Dynamic.Value → List Value → List Ty → Prop where
    | nil : ValuesRep catalog signatures functions mapping world [] [] [] []
    | cons {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
        (head : ValueRep catalog signatures functions mapping world sourceType source value type)
        (tail : ValuesRep catalog signatures functions mapping world sourceTypes sources values types) :
        ValuesRep catalog signatures functions mapping world (sourceType :: sourceTypes) (source :: sources) (value :: values) (type :: types)
  inductive EntriesRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
      (functions : GenericHeap.PayloadModel catalog) (mapping : LocationMap) (world : StoreTyping) :
      TypeSystem.Ty → TypeSystem.Ty → Ty → Ty → List (Dynamic.Value × Dynamic.Value) → Core.OrderedMapping.Entries → Prop where
    | empty (key value : TypeSystem.Ty) (keyType valueType : Ty) :
        EntriesRep catalog signatures functions mapping world key value keyType valueType [] []
    | prepend {key value : TypeSystem.Ty} {keyType valueType : Ty}
        {sourceKey sourceValue : Dynamic.Value} {coreKey coreValue : Value}
        {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
        (keyRelated : ValueRep catalog signatures functions mapping world key sourceKey coreKey keyType)
        (valueRelated : ValueRep catalog signatures functions mapping world value sourceValue coreValue valueType)
        (tail : EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries) :
        EntriesRep catalog signatures functions mapping world key value keyType valueType
          ((sourceKey, sourceValue) :: sources) ((coreKey, coreValue) :: entries)
end

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
  {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}

theorem ValueRep.projection {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    catalog.project sourceType = .ok type := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit | bool | word | integer => rfl
  | product _ _ first second => simp [SourceCoreDataCatalog.Catalog.project, first, second, bind, Except.bind, pure, Except.pure]
  | function represented => exact functions.projection represented
  | proxy identity _ => simp [SourceCoreDataCatalog.Catalog.project, identity, pure, Except.pure]
  | mapping identity _ _ _ _ _ => simp [SourceCoreDataCatalog.Catalog.project, identity, Core.OrderedMapping.Layout.type, pure, Except.pure]
  | constructed _ _ _ projection _ _ _ => exact projection
  | comptime _ ih => exact ih
  | nil | cons => trivial
  | empty | prepend => trivial

private theorem pack_typed {definitions : DataEnvironment} {types : List Ty} {values : List Value}
    (typed : ListRel (fun value type => RuntimeValueHasType world value type definitions) values types) :
    RuntimeValueHasType world (packValues values) (SourceCoreDataMatches.bundleType types) definitions := by
  induction typed with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => exact head
    | cons => exact .pair head ih

theorem ValueRep.runtime_hasType {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    RuntimeValueHasType world value type catalog.definitions := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ values types _ => ListRel (fun value type => RuntimeValueHasType world value type catalog.definitions) values types)
    (motive_3 := fun _ _ keyType valueType _ entries _ => ∀ key value, (key, value) ∈ entries →
      RuntimeValueHasType world key keyType catalog.definitions ∧ RuntimeValueHasType world value valueType catalog.definitions) with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .pair first second
  | function represented => exact functions.runtime_hasType represented
  | proxy _ registered => exact .constructed registered .unit
  | mapping _ _ _ registered _ ih => exact Core.OrderedMapping.encode_hasType registered _ ih
  | constructed _ _ _ _ registered _ ih => exact .constructed registered (pack_typed ih)
  | comptime _ ih => exact ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => rename_i a b member; cases member
  | prepend _ _ _ key value rest =>
    rename_i a b member
    rcases List.mem_cons.mp member with same | member
    · cases same; exact ⟨key, value⟩
    · exact rest a b member

theorem ValueRep.extend {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    ValueRep catalog signatures functions futureMapping futureWorld sourceType source value type := by
  induction represented using ValueRep.rec
    (motive_2 := fun types sources values coreTypes _ => ValuesRep catalog signatures functions futureMapping futureWorld types sources values coreTypes)
    (motive_3 := fun key value keyType valueType sources entries _ => EntriesRep catalog signatures functions futureMapping futureWorld key value keyType valueType sources entries) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | function represented => exact .function (functions.extend represented maps worlds)
  | proxy identity registered => exact .proxy identity registered
  | mapping identity key value registered _ ih => exact .mapping identity key value registered ih
  | constructed nominal result authenticated projection registered _ ih => exact .constructed nominal result authenticated projection registered ih
  | comptime _ ih => exact .comptime ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => exact .empty _ _ _ _
  | prepend _ _ _ key value rest => exact .prepend key value rest

/-- Reuse the mapped heap and its administrative-frame laws without defining
another heap relation. The supplied function model remains the only function
leaf authority. -/
def payloadModel (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) : GenericHeap.PayloadModel catalog where
  Represents := ValueRep catalog signatures functions
  projection := ValueRep.projection
  runtime_hasType := ValueRep.runtime_hasType
  extend := ValueRep.extend

theorem ValuesRep.length {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes) :
    types.length = sources.length ∧ types.length = values.length ∧ types.length = coreTypes.length := by
  induction types generalizing sources values coreTypes with
  | nil => cases represented; exact ⟨rfl, rfl, rfl⟩
  | cons type types ih => cases represented with
    | cons head tail =>
      have rest := ih tail
      exact ⟨congrArg Nat.succ rest.1, congrArg Nat.succ rest.2.1, congrArg Nat.succ rest.2.2⟩

theorem ValuesRep.projection {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes) :
    types.mapM catalog.project = .ok coreTypes := by
  induction types generalizing sources values coreTypes with
  | nil => cases represented; rfl
  | cons type types ih => cases represented with
    | cons head tail => simp [List.mapM_cons, head.projection, ih tail, bind, Except.bind, pure, Except.pure]

theorem EntriesRep.ordered {key value : TypeSystem.Ty} {keyType valueType : Ty}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (represented : EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries) :
    OrderedMapping.EntriesRel
      (fun source core => ValueRep catalog signatures functions mapping world key source core keyType)
      (fun source core => ValueRep catalog signatures functions mapping world value source core valueType) sources entries := by
  induction sources generalizing entries with
  | nil => cases represented; exact .nil
  | cons source sources ih => cases represented with
    | prepend key value tail => exact .cons key value (ih tail)

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadDefaults
/-! Static catalog layout receipts used by complete payload representations.
A `Checked` catalog only proves Core definition well-formedness. It does not
by itself prove the source mapping/proxy layout equations below. These are
compile-time data-layout facts, not premises about executing helper code. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues

structure CatalogLayouts (catalog : SourceCoreDataCatalog.Catalog) : Prop where
  proxy : ∀ {inner id}, catalog.identity? (.proxy inner) = some id →
    catalog.definitions.lookupConstructorPayloadType? ⟨id, 0⟩ = some .unit
  mapping : ∀ {key value id}, catalog.identity? (.mapping key value) = some id →
    ∃ keyType valueType,
      catalog.project key = .ok keyType ∧ catalog.project value = .ok valueType ∧
      (Core.OrderedMapping.Layout.mk keyType valueType id).Registered catalog.definitions

/-- Actual default-generation certificates produce complete payloads. The
empty mapping still authenticates its declared key/value layout, even though
there are no entries whose values could expose a malformed declaration. -/
theorem default_represents {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    (layouts : CatalogLayouts catalog) {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {value : Value} {expression : Expr} (tree : DataDefaults.Tree catalog sourceType source value expression) :
    ∃ type, ValueRep catalog signatures functions mapping world sourceType source value type := by
  induction tree with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool _⟩
  | word => exact ⟨_, .word _⟩
  | integer => exact ⟨_, .integer _⟩
  | product _ _ left right =>
    obtain ⟨a, first⟩ := left
    obtain ⟨b, second⟩ := right
    exact ⟨_, .product first second⟩
  | proxy inner id identity => exact ⟨_, .proxy identity (layouts.proxy identity)⟩
  | mapping key value id identity =>
    obtain ⟨keyType, valueType, keyProjection, valueProjection, registered⟩ := layouts.mapping identity
    exact ⟨_, .mapping identity keyProjection valueProjection registered (.empty _ _ _ _)⟩
  | comptime _ ih => obtain ⟨type, represented⟩ := ih; exact ⟨_, .comptime represented⟩

theorem default_represents_at {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    (layouts : CatalogLayouts catalog) {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {value : Value} {expression : Expr} {type : Ty}
    (projected : catalog.project sourceType = .ok type)
    (tree : DataDefaults.Tree catalog sourceType source value expression) :
    ValueRep catalog signatures functions mapping world sourceType source value type := by
  obtain ⟨actual, represented⟩ := default_represents (signatures := signatures) (functions := functions) (mapping := mapping) (world := world) layouts tree
  have same := Except.ok.inj (represented.projection.symm.trans projected)
  exact same ▸ represented

/-- Existing finite constructor proofs embed without losing metadata. This
also keeps all earlier finite-heap clients compatible with the full model. -/
theorem finite_represents {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, ValueRep catalog signatures functions mapping world sourceType source value type := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types sources values _ => ∃ coreTypes,
      ValuesRep catalog signatures functions mapping world types sources values coreTypes) with
  | unit => exact ⟨_, .unit⟩
  | bool value => exact ⟨_, .bool value⟩
  | word value => exact ⟨_, .word value⟩
  | integer value => exact ⟨_, .integer value⟩
  | product _ _ first second =>
    obtain ⟨a, first⟩ := first
    obtain ⟨b, second⟩ := second
    exact ⟨_, .product first second⟩
  | @constructed sourceType metadata tag declaration arguments sources values nominal result authenticated original ih =>
    obtain ⟨types, payloads⟩ := ih
    obtain ⟨registered, projected, payload⟩ := DataValueTyping.resolveConstructor_payload authenticated
    have same := Except.ok.inj (payloads.projection.symm.trans projected)
    subst registered
    obtain ⟨coreType, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed
      (.constructed nominal result authenticated original)
    have typeEq : coreType = .namedData tag.owner := by cases typed []; rfl
    subst coreType
    exact ⟨_, .constructed nominal result authenticated projection payload payloads⟩
  | nil => exact ⟨[], .nil⟩
  | cons _ _ head tail =>
    obtain ⟨type, head⟩ := head
    obtain ⟨types, tail⟩ := tail
    exact ⟨_, .cons head tail⟩

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
/-! The public data encoder supplies independent source values and complete
payload representations, including ordered mappings and raw proxy identities.
Catalog layout authentication is static and explicit. No executable source
runtime value or source evaluator is imported at this boundary. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
abbrev PublicValue := SourceCoreDataValues.Value
abbrev EncodingContext := SourceCoreDataValues.Context

mutual
  inductive Means : PublicValue → Dynamic.Value → Prop where
    | unit : Means .unit .unit
    | bool (value : Bool) : Means (.bool value) (.bool value)
    | word (value : Word) : Means (.word value) (.word value)
    | integer (value : Int) : Means (.integer value) (.integer value)
    | product {left right : PublicValue} {a b : Dynamic.Value} :
        Means left a → Means right b → Means (.product left right) (.product a b)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {sources : List Dynamic.Value} :
        Meanings payloads sources → Means (.constructed metadata payloads) (.constructed metadata sources)
    | mapping {key value : TypeSystem.Ty} {entries : List (PublicValue × PublicValue)} {sources : List (Dynamic.Value × Dynamic.Value)} :
        EntryMeanings entries sources → Means (.mapping key value entries) (.mapping key value sources)
    | proxy (inner : TypeSystem.Ty) : Means (.proxy inner) (.proxy inner)
  inductive Meanings : List PublicValue → List Dynamic.Value → Prop where
    | nil : Meanings [] []
    | cons {head : PublicValue} {tail : List PublicValue} {source : Dynamic.Value} {sources : List Dynamic.Value} :
        Means head source → Meanings tail sources → Meanings (head :: tail) (source :: sources)
  inductive EntryMeanings : List (PublicValue × PublicValue) → List (Dynamic.Value × Dynamic.Value) → Prop where
    | empty : EntryMeanings [] []
    | prepend {key value : PublicValue} {sourceKey sourceValue : Dynamic.Value}
        {entries : List (PublicValue × PublicValue)} {sources : List (Dynamic.Value × Dynamic.Value)} :
        Means key sourceKey → Means value sourceValue → EntryMeanings entries sources →
        EntryMeanings ((key, value) :: entries) ((sourceKey, sourceValue) :: sources)
end

theorem Means.functional {value : PublicValue} {left right : Dynamic.Value}
    (first : Means value left) (second : Means value right) : left = right := by
  induction first using Means.rec
    (motive_2 := fun values sources _ => ∀ other, Meanings values other → sources = other)
    (motive_3 := fun values sources _ => ∀ other, EntryMeanings values other → sources = other) generalizing right with
  | unit => cases second; rfl
  | bool => cases second; rfl
  | word => cases second; rfl
  | integer => cases second; rfl
  | proxy => cases second; rfl
  | product _ _ left right => cases second with
    | product a b => rw [left a, right b]
  | constructed _ ih => cases second with
    | constructed rest => rw [ih _ rest]
  | mapping _ ih => cases second with
    | mapping rest => rw [ih _ rest]
  | nil => rename_i other related; cases related; rfl
  | cons _ _ head tail =>
    rename_i other related
    cases related with
    | cons first rest => rw [head first, tail _ rest]
  | empty => rename_i other related; cases related; rfl
  | prepend _ _ _ key value rest =>
    rename_i other related
    cases related with
    | prepend a b tail => rw [key a, value b, rest _ tail]

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]
private theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

private theorem namedIdentity_project {context : EncodingContext} {sourceType : TypeSystem.Ty} {id : DataTypeId}
    (accepted : SourceCoreDataValues.namedIdentity context sourceType = .ok id) :
    context.checked.catalog.project sourceType = .ok (.namedData id) := by
  unfold SourceCoreDataValues.namedIdentity at accepted
  obtain ⟨type, projected, accepted⟩ := bind_ok accepted
  have projected := mapError_ok projected
  cases type <;> cases accepted
  exact projected

private theorem namedIdentity_mapping {context : EncodingContext} {key value : TypeSystem.Ty} {id : DataTypeId}
    (accepted : SourceCoreDataValues.namedIdentity context (.mapping key value) = .ok id) :
    context.checked.catalog.identity? (.mapping key value) = some id := by
  have projected := namedIdentity_project accepted
  cases selected : context.checked.catalog.identity? (.mapping key value) with
  | none => simp [SourceCoreDataCatalog.Catalog.project, selected] at projected
  | some actual => simpa [SourceCoreDataCatalog.Catalog.project, selected, pure, Except.pure] using projected

private theorem namedIdentity_proxy {context : EncodingContext} {inner : TypeSystem.Ty} {id : DataTypeId}
    (accepted : SourceCoreDataValues.namedIdentity context (.proxy inner) = .ok id) :
    context.checked.catalog.identity? (.proxy inner) = some id := by
  have projected := namedIdentity_project accepted
  cases selected : context.checked.catalog.identity? (.proxy inner) with
  | none => simp [SourceCoreDataCatalog.Catalog.project, selected] at projected
  | some actual => simpa [SourceCoreDataCatalog.Catalog.project, selected, pure, Except.pure] using projected

private theorem project_nominal {catalog : SourceCoreDataCatalog.Catalog}
    {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (selected : catalog.identity? type = some identity) : catalog.project type = .ok (.namedData identity) := by
  cases type with
  | constructor constructor => cases constructor with
    | declaration => simp [SourceCoreDataCatalog.Catalog.project, selected]
    | builtin builtin => cases builtin <;> simp [SourceCoreDataCatalog.nominalParts] at nominal
  | application => simp [SourceCoreDataCatalog.Catalog.project, selected]
  | _ => simp [SourceCoreDataCatalog.nominalParts] at nominal

private def EncodingSound (fuel : Nat) (context : EncodingContext)
    (functions : GenericHeap.PayloadModel context.checked.catalog) (mapping : LocationMap) (world : StoreTyping) : Prop :=
  ∀ type value core, SourceCoreDataValues.encodeRaw fuel context type value = .ok core →
    ∃ source coreType, Means value source ∧ ValueRep context.checked.catalog context.signatures functions mapping world type source core coreType
private def PayloadSound (fuel : Nat) (context : EncodingContext)
    (functions : GenericHeap.PayloadModel context.checked.catalog) (mapping : LocationMap) (world : StoreTyping) : Prop :=
  ∀ types values index core, SourceCoreDataValues.encodePayloadsRaw fuel context types values index = .ok core →
    ∃ sources cores coreTypes, Meanings values sources ∧
      ValuesRep context.checked.catalog context.signatures functions mapping world types sources cores coreTypes ∧ core = packValues cores
private def EntriesSound (fuel : Nat) (context : EncodingContext)
    (functions : GenericHeap.PayloadModel context.checked.catalog) (mapping : LocationMap) (world : StoreTyping) : Prop :=
  ∀ key value (layout : Core.OrderedMapping.Layout) values index core,
    context.checked.catalog.project key = .ok layout.keyType → context.checked.catalog.project value = .ok layout.valueType →
    SourceCoreDataValues.encodeEntriesRaw fuel context key value layout.dataType values index = .ok core →
    ∃ sources entries, EntryMeanings values sources ∧
      EntriesRep context.checked.catalog context.signatures functions mapping world key value layout.keyType layout.valueType sources entries ∧
      core = Core.OrderedMapping.encode layout entries

private theorem constructed_sound {fuel : Nat} {context : EncodingContext}
    {functions : GenericHeap.PayloadModel context.checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    (induction : PayloadSound fuel context functions mapping world)
    {type : TypeSystem.Ty} {metadata : DataConstructorInstantiation} {payloads : List PublicValue}
    {tag : ConstructorId} {payload : Value} (same : metadata.resultType = type)
    (authenticated : context.checked.catalog.resolveConstructor context.signatures metadata = .ok tag)
    (encoded : SourceCoreDataValues.encodePayloadsRaw fuel context metadata.payloadTypes payloads 0 = .ok payload) :
    ∃ source coreType, Means (.constructed metadata payloads) source ∧
      ValueRep context.checked.catalog context.signatures functions mapping world type source (.constructed tag payload) coreType := by
  obtain ⟨sources, cores, coreTypes, meanings, represented, packing⟩ := induction _ _ _ _ encoded
  obtain ⟨signature, constructor, selected, ctor, parameters, result, types⟩ := DataPatternAuthenticity.metadataFacts authenticated
  have nominal := DataPatternAuthenticity.nominalParts_nominal signature.id (metadata.parameterSubstitution.map Prod.snd)
  rw [← result, same] at nominal
  have identity := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
  rw [same] at identity
  obtain ⟨registered, projected, payloadType⟩ := DataValueTyping.resolveConstructor_payload authenticated
  have eqTypes := Except.ok.inj (represented.projection.symm.trans projected)
  subst registered
  subst payload
  exact ⟨_, _, .constructed meanings, .constructed nominal same authenticated (project_nominal nominal identity) payloadType represented⟩

private theorem raw_sound (fuel : Nat) (context : EncodingContext)
    (functions : GenericHeap.PayloadModel context.checked.catalog) (mapping : LocationMap) (world : StoreTyping)
    (layouts : CatalogLayouts context.checked.catalog) :
    EncodingSound fuel context functions mapping world ∧ PayloadSound fuel context functions mapping world ∧
      EntriesSound fuel context functions mapping world := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro type value core accepted; cases accepted
    · intro types values index core accepted
      cases types with
      | nil => cases values with
        | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], [], .nil, .nil, rfl⟩
        | cons => simp [SourceCoreDataValues.encodePayloadsRaw, bind, Except.bind, throw] at accepted
      | cons => simp only [SourceCoreDataValues.encodePayloadsRaw] at accepted; split at accepted <;> cases accepted
    · intro key value layout values index core keyProjected valueProjected accepted
      cases values with
      | nil => cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
      | cons => cases accepted
  | succ fuel ih =>
    refine ⟨?_, ?_, ?_⟩
    · intro type value core accepted
      cases type with
      | comptime inner =>
        obtain ⟨source, coreType, meaning, represented⟩ := ih.1 _ _ _ accepted
        exact ⟨_, _, meaning, .comptime represented⟩
      | function => cases accepted
      | constructor constructor =>
        cases constructor with
        | builtin builtin =>
          cases builtin <;> cases value <;> try (solve | cases accepted)
          all_goals try (solve | cases accepted; exact ⟨_, _, .unit, .unit⟩)
          all_goals try (solve | cases accepted; exact ⟨_, _, .bool _, .bool _⟩)
          all_goals try (solve | cases accepted; exact ⟨_, _, .word _, .word _⟩)
          all_goals try (solve | cases accepted; exact ⟨_, _, .integer _, .integer _⟩)
          all_goals
            simp only [SourceCoreDataValues.encodeRaw] at accepted
            split at accepted
            · rename_i same
              obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
              obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
              cases accepted
              exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
            · cases accepted
        | declaration =>
          cases value <;> try (solve | cases accepted)
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
            obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
            cases accepted
            exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
          · cases accepted
      | product leftType rightType =>
        cases value <;> try (solve | cases accepted)
        case product left right =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          obtain ⟨a, encodedA, accepted⟩ := bind_ok accepted
          obtain ⟨b, encodedB, accepted⟩ := bind_ok accepted
          cases accepted
          obtain ⟨sourceA, typeA, meaningA, representedA⟩ := ih.1 _ _ _ (mapError_ok encodedA)
          obtain ⟨sourceB, typeB, meaningB, representedB⟩ := ih.1 _ _ _ (mapError_ok encodedB)
          exact ⟨_, _, .product meaningA meaningB, .product representedA representedB⟩
        case constructed metadata payloads =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
            obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
            cases accepted
            exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
          · cases accepted
      | mapping keyType valueType =>
        cases value <;> try (solve | cases accepted)
        case mapping actualKey actualValue entries =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨rfl, rfl⟩ := same
            obtain ⟨id, identity, encoded⟩ := bind_ok accepted
            have identity := namedIdentity_mapping identity
            obtain ⟨key, value, keyProjected, valueProjected, registered⟩ := layouts.mapping identity
            obtain ⟨sources, cores, meanings, represented, packing⟩ := ih.2.2 _ _ ⟨key, value, id⟩ _ _ _ keyProjected valueProjected encoded
            subst core
            exact ⟨_, _, .mapping meanings, .mapping identity keyProjected valueProjected registered represented⟩
          · cases accepted
        case constructed metadata payloads =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
            obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
            cases accepted
            exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
          · cases accepted
      | proxy inner =>
        cases value <;> try (solve | cases accepted)
        case proxy actual =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            subst actual
            obtain ⟨id, identity, accepted⟩ := bind_ok accepted
            cases accepted
            have identity := namedIdentity_proxy identity
            exact ⟨_, _, .proxy inner, .proxy identity (layouts.proxy identity)⟩
          · cases accepted
        case constructed metadata payloads =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
            obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
            cases accepted
            exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
          · cases accepted
      | «variable» | parameter | application | error =>
        cases value <;> try (solve | cases accepted)
        all_goals
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          split at accepted
          · rename_i same
            obtain ⟨tag, authenticated, accepted⟩ := bind_ok accepted
            obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
            cases accepted
            exact constructed_sound ih.2.1 same (mapError_ok authenticated) encoded
          · cases accepted
    · intro types values index core accepted
      by_cases length : types.length = values.length
      · cases types with
        | nil => cases values with
          | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], [], .nil, .nil, rfl⟩
          | cons => simp at length
        | cons type types => cases values with
          | nil => simp at length
          | cons value values =>
            cases types with
            | nil =>
              have empty : values = [] := by simpa using length.symm
              subst values
              simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
              obtain ⟨source, type, meaning, represented⟩ := ih.1 _ _ _ (mapError_ok accepted)
              exact ⟨[source], [core], [type], .cons meaning .nil, .cons represented .nil, rfl⟩
            | cons next types =>
              simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
              obtain ⟨a, encodedA, accepted⟩ := bind_ok accepted
              obtain ⟨b, encodedB, accepted⟩ := bind_ok accepted
              cases accepted
              obtain ⟨source, type, meaning, represented⟩ := ih.1 _ _ _ (mapError_ok encodedA)
              obtain ⟨sources, cores, types, meanings, representations, packed⟩ := ih.2.1 _ _ _ _ encodedB
              cases cores with
              | nil => cases representations
              | cons first cores =>
                refine ⟨source :: sources, a :: first :: cores, type :: types, .cons meaning meanings, .cons represented representations, ?_⟩
                simp only [packValues]; rw [packed]
      · unfold SourceCoreDataValues.encodePayloadsRaw at accepted
        simp [length, bind, Except.bind, throw] at accepted
    · intro key value layout values index core keyProjected valueProjected accepted
      cases values with
      | nil => cases accepted; exact ⟨[], [], .empty, .empty _ _ _ _, rfl⟩
      | cons entry entries =>
        obtain ⟨publicKey, publicValue⟩ := entry
        simp only [SourceCoreDataValues.encodeEntriesRaw] at accepted
        obtain ⟨a, encodedA, accepted⟩ := bind_ok accepted
        obtain ⟨b, encodedB, accepted⟩ := bind_ok accepted
        obtain ⟨rest, encodedRest, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨sourceKey, aType, meaningKey, representedKey⟩ := ih.1 _ _ _ (mapError_ok encodedA)
        obtain ⟨sourceValue, bType, meaningValue, representedValue⟩ := ih.1 _ _ _ (mapError_ok encodedB)
        have aEq := Except.ok.inj (representedKey.projection.symm.trans keyProjected)
        have bEq := Except.ok.inj (representedValue.projection.symm.trans valueProjected)
        subst aType; subst bType
        obtain ⟨sources, cores, meanings, represented, packed⟩ := ih.2.2 _ _ layout _ _ _ keyProjected valueProjected encodedRest
        subst rest
        exact ⟨_, _, .prepend meaningKey meaningValue meanings, .prepend representedKey representedValue represented, rfl⟩

/-- No source-value profile is assumed: every successful public data encoding
is covered, subject to the stated catalog layout receipts. Function handles
are rejected by this encoder and belong to the separate session boundary. -/
theorem encodes_represents {fuel : Nat} {context : EncodingContext}
    {functions : GenericHeap.PayloadModel context.checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {publicValue : PublicValue} {core : Value}
    (layouts : CatalogLayouts context.checked.catalog)
    (encoded : SourceCoreDataValues.Encodes fuel context type publicValue core) :
    ∃ source coreType, Means publicValue source ∧
      ValueRep context.checked.catalog context.signatures functions mapping world type source core coreType :=
  (raw_sound fuel context functions mapping world layouts).1 type publicValue core encoded.generated

theorem encodes_represents_at {fuel : Nat} {context : EncodingContext}
    {functions : GenericHeap.PayloadModel context.checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {publicValue : PublicValue} {source : Dynamic.Value} {core : Value} {coreType : Ty}
    (layouts : CatalogLayouts context.checked.catalog)
    (meaning : Means publicValue source) (projection : context.checked.catalog.project type = .ok coreType)
    (encoded : SourceCoreDataValues.Encodes fuel context type publicValue core) :
    ValueRep context.checked.catalog context.signatures functions mapping world type source core coreType := by
  obtain ⟨actual, actualType, actualMeaning, represented⟩ := encodes_represents
    (functions := functions) (mapping := mapping) (world := world) layouts encoded
  have sameSource := actualMeaning.functional meaning
  have sameType := Except.ok.inj (represented.projection.symm.trans projection)
  subst actual; subst actualType
  exact represented

theorem encode_represents {fuel : Nat} {context : EncodingContext}
    {functions : GenericHeap.PayloadModel context.checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {publicValue : PublicValue} {core : Value}
    (layouts : CatalogLayouts context.checked.catalog)
    (encoded : SourceCoreDataValues.encode fuel context type publicValue = .ok core) :
    ∃ source coreType, Means publicValue source ∧
      ValueRep context.checked.catalog context.signatures functions mapping world type source core coreType :=
  encodes_represents layouts (SourceCoreDataValues.encodes_of_encode encoded)

theorem decode_represents {fuel : Nat} {context : EncodingContext}
    {functions : GenericHeap.PayloadModel context.checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {type : TypeSystem.Ty} {publicValue : PublicValue} {core : Value}
    (layouts : CatalogLayouts context.checked.catalog)
    (decoded : SourceCoreDataValues.decode fuel context type core = .ok publicValue) :
    ∃ source coreType, Means publicValue source ∧
      ValueRep context.checked.catalog context.signatures functions mapping world type source core coreType :=
  encodes_represents layouts (SourceCoreDataValues.encodes_of_decode decoded)

end Solcore.SourceSemantics.CoreLowering.DataPayloadEncoding
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadEquality
/-! Equality observations extracted from the complete data payload relation.
Function identity authentication remains a separate law of the function model;
there is no generic equality of function code or captured heaps. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataEqualityValues

/-- Additional observation law needed only by source equality. Future function
carriers may establish this law through their own authenticated adapter. -/
def FunctionObservations (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel catalog) (identities : Dynamic.Value → Word → Prop) : Prop :=
  ∀ {mapping world parameter result source value type},
    functions.Represents mapping world (.function parameter result) source value type →
    Observation catalog signatures identities type source value

theorem ValueRep.observation {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {identities : Dynamic.Value → Word → Prop}
    (functionObservations : FunctionObservations catalog signatures functions identities)
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    Observation catalog signatures identities type source value := by
  induction represented using ValueRep.rec
    (motive_2 := fun _ sources values types _ => ∃ packed, Dynamic.ValuesPack sources packed ∧
      Observation catalog signatures identities (SourceCoreDataMatches.bundleType types) packed (packValues values))
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => exact .unit
  | bool value => exact .bool value
  | word value => exact .word value
  | integer value => exact .integer value
  | product _ _ first second => exact .product first second
  | function represented => exact functionObservations represented
  | proxy identity _ => exact .proxy_of_identity identity
  | mapping identity _ _ _ _ _ => exact .mapping_of_identity identity _ _
  | @constructed sourceType metadata tag declaration arguments sources values types nominal result authenticated projection registered payloads ih =>
    obtain ⟨packed, packing, observed⟩ := ih
    have identity := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    obtain ⟨entry, selected, sourceTypeEq⟩ := identity_entry identity
    have nominalResult : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
      rw [result]; exact nominal
    rw [erase_nominal nominalResult] at sourceTypeEq
    exact .constructed selected sourceTypeEq nominalResult authenticated registered
      payloads.length.1.symm packing observed
  | comptime _ ih => exact ih
  | nil => exact ⟨.unit, .nil, .unit⟩
  | cons head tail first rest =>
    obtain ⟨packed, packing, observed⟩ := rest
    cases tail with
    | nil => exact ⟨_, .singleton _, first⟩
    | cons => exact ⟨_, .cons packing, .product first observed⟩
  | empty | prepend => trivial

/-- Every stored key receives its authentic source equality observation from
its full representation. Entry order and duplicate keys are preserved. -/
theorem EntriesRep.observed {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {identities : Dynamic.Value → Word → Prop}
    (functionObservations : FunctionObservations catalog signatures functions identities)
    {mapping : LocationMap} {world : StoreTyping} {key value : TypeSystem.Ty} {keyType valueType : Ty}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (represented : EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries) :
    OrderedMapping.EntriesRel (Observation catalog signatures identities keyType)
      (fun source core => ValueRep catalog signatures functions mapping world value source core valueType) sources entries := by
  induction sources generalizing entries with
  | nil => cases represented; exact .nil
  | cons source sources ih => cases represented with
    | prepend key value rest => exact .cons (key.observation functionObservations) value (ih rest)

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadMapping
/-! Actual mapping insertion retains the complete representations of both keys
and values. The comparator only needs equality observations, but that weaker
observation must not replace the stored key's code/data authentication. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataEquality

variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
  {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}

theorem EntriesRep.of_ordered {key value : TypeSystem.Ty} {keyType valueType : Ty}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (represented : OrderedMapping.EntriesRel
      (fun source core => ValueRep catalog signatures functions mapping world key source core keyType)
      (fun source core => ValueRep catalog signatures functions mapping world value source core valueType) sources entries) :
    EntriesRep catalog signatures functions mapping world key value keyType valueType sources entries := by
  induction represented with
  | nil => exact .empty _ _ _ _
  | cons key value _ ih => exact .prepend key value ih

/-- The exact generated insertion uses full keys for representation, and only
for comparison projects those keys to their source equality observations. The
output relation never authenticates a closure from equality observations. -/
theorem insert_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (prepared : SourceCoreDataEquality.Prepared checked)
    (layout : Core.OrderedMapping.Layout) (comparisonType : layout.keyType = prepared.type)
    {keyType valueType : TypeSystem.Ty}
    (identity : checked.catalog.identity? (.mapping keyType valueType) = some layout.dataType)
    (keyProjection : checked.catalog.project keyType = .ok layout.keyType)
    (valueProjection : checked.catalog.project valueType = .ok layout.valueType)
    (registered : layout.Registered checked.catalog.definitions)
    {sourceKey sourceValue : Dynamic.Value} {key value : Value}
    {sources updated : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key layout.keyType)
    (valueRep : ValueRep checked.catalog signatures functions mapping world valueType sourceValue value layout.valueType)
    (related : EntriesRep checked.catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries)
    (inserted : Dynamic.MappingInsert sourceKey sourceValue sources updated)
    (environment : Environment) (store : Store) (current keyExpression valueExpression : Expr)
    (currentSelected : Selects environment current (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) (valueSelected : Selects environment valueExpression value) :
    ∃ output,
      ValueRep checked.catalog signatures functions mapping world (.mapping keyType valueType)
        (.mapping keyType valueType updated) output layout.type ∧
      Evaluates environment store (Core.OrderedMapping.insert layout prepared.expression current keyExpression valueExpression)
        (.inRight .word output) (DataMappingComparison.insertStore prepared layout environment store entries key value) := by
  have keyObserved : DataMappingComparison.KeyRep prepared signatures identities sourceKey key := by
    unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact keyRep.observation observations
  have entriesObserved : OrderedMapping.EntriesRel (DataMappingComparison.KeyRep prepared signatures identities)
      (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core layout.valueType) sources entries := by
    unfold DataMappingComparison.KeyRep
    rw [← comparisonType]
    exact related.observed observations
  obtain ⟨equal, correct⟩ := DataMappingComparison.exists_predicate_correct prepared signatures faithful
  have fullCorrect : OrderedMapping.KeyEqualityCorrect
      (fun source core => ValueRep checked.catalog signatures functions mapping world keyType source core layout.keyType) equal := by
    constructor
    intro sourceKey sourceStored key stored first second
    apply correct.equivalent
    · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact first.observation observations
    · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact second.observation observations
  have resultRelated := OrderedMapping.insert_related fullCorrect keyRep valueRep related.ordered inserted
  exact ⟨_, .mapping identity keyProjection valueProjection registered (EntriesRep.of_ordered resultRelated),
    DataMappingComparison.insert_evaluates prepared layout comparisonType faithful equal correct keyObserved entriesObserved
      environment store current keyExpression valueExpression currentSelected keySelected valueSelected⟩

/-- Found lookup also retains the complete selected value. Comparison projects
stored keys to observations without modifying their stronger relation. -/
theorem lookup_found {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop}
    (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (prepared : SourceCoreDataEquality.Prepared checked)
    (layout : Core.OrderedMapping.Layout) (comparisonType : layout.keyType = prepared.type)
    {keyType valueType : TypeSystem.Ty} {sourceKey sourceValue : Dynamic.Value} {key : Value}
    {sources : List (Dynamic.Value × Dynamic.Value)} {entries : Core.OrderedMapping.Entries}
    (keyRep : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key layout.keyType)
    (related : EntriesRep checked.catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries)
    (found : Dynamic.MappingLookup sourceKey sources sourceValue)
    (environment : Environment) (store : Store) (current keyExpression : Expr)
    (currentSelected : Selects environment current (Core.OrderedMapping.encode layout entries))
    (keySelected : Selects environment keyExpression key) :
    ∃ output, ValueRep checked.catalog signatures functions mapping world valueType sourceValue output layout.valueType ∧
      Evaluates environment store (Core.OrderedMapping.lookup layout prepared.expression current keyExpression)
        (.inRight .word (.inRight .unit output)) (DataMappingComparison.lookupStore prepared layout environment store entries key) := by
  apply DataMappingComparison.lookup_found (signatures := signatures) prepared layout comparisonType faithful (valueRel :=
    fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core layout.valueType)
    ?_ ?_ found environment store current keyExpression currentSelected keySelected
  · unfold DataMappingComparison.KeyRep; rw [← comparisonType]; exact keyRep.observation observations
  · unfold DataMappingComparison.KeyRep
    rw [← comparisonType]
    exact related.observed observations

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadFields
/-! Structural field and ordered-entry facts for complete payloads. These
lemmas retain siblings and captured code while selecting/replacing one field;
no runtime expression evaluation appears in the assumptions. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues
variable {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
  {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}

theorem ValuesRep.at {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} (lookup : types[index]? = some type) :
    ∃ source value coreType, Dynamic.ValueAt sources index source ∧ values[index]? = some value ∧
      coreTypes[index]? = some coreType ∧ ValueRep catalog signatures functions mapping world type source value coreType := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; exact ⟨_, _, _, .head, rfl, rfl, first⟩
      | succ index =>
        obtain ⟨source, value, type, selected, found, typed, represented⟩ := ih rest lookup
        exact ⟨source, value, type, .tail selected, found, typed, represented⟩

theorem ValuesRep.replace {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (represented : ValuesRep catalog signatures functions mapping world types sources values coreTypes)
    {index : Nat} {type : TypeSystem.Ty} {coreType : Ty} (lookup : types[index]? = some type)
    (coreLookup : coreTypes[index]? = some coreType)
    {source : Dynamic.Value} {value : Value}
    (replacement : ValueRep catalog signatures functions mapping world type source value coreType) :
    ValuesRep catalog signatures functions mapping world types (sources.set index source) (values.set index value) coreTypes := by
  induction types generalizing sources values coreTypes index with
  | nil => simp at lookup
  | cons head tail ih => cases represented with
    | cons first rest => cases index with
      | zero => cases lookup; cases coreLookup; exact .cons replacement rest
      | succ index => exact .cons first (ih rest lookup coreLookup)

theorem ValueRep.nominal_parts {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts sourceType = some (declaration, arguments))
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type) :
    ∃ metadata tag sources values types,
      source = .constructed metadata sources ∧ value = .constructed tag (packValues values) ∧ type = .namedData tag.owner ∧
      metadata.resultType = sourceType ∧ catalog.resolveConstructor signatures metadata = .ok tag ∧
      catalog.definitions.lookupConstructorPayloadType? tag = some (SourceCoreDataMatches.bundleType types) ∧
      ValuesRep catalog signatures functions mapping world metadata.payloadTypes sources values types := by
  cases represented with
  | constructed nominal result authenticated projection registered payloads => exact ⟨_, _, _, _, _, rfl, rfl, rfl, result, authenticated, registered, payloads⟩
  | _ => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at nominal

theorem ValueRep.mapping_parts {keyType valueType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (layout : Core.OrderedMapping.Layout)
    (keyProjected : catalog.project keyType = .ok layout.keyType)
    (valueProjected : catalog.project valueType = .ok layout.valueType)
    (represented : ValueRep catalog signatures functions mapping world (.mapping keyType valueType) source value layout.type) :
    ∃ sources entries, source = .mapping keyType valueType sources ∧ value = Core.OrderedMapping.encode layout entries ∧
      catalog.identity? (.mapping keyType valueType) = some layout.dataType ∧ layout.Registered catalog.definitions ∧
      EntriesRep catalog signatures functions mapping world keyType valueType layout.keyType layout.valueType sources entries := by
  generalize typeEq : layout.type = type at represented
  cases represented with
  | @mapping sourceKeyType sourceValueType actual sources entries identity keyProjection valueProjection registered contents =>
    have sameKey := Except.ok.inj (keyProjection.symm.trans keyProjected)
    have sameValue := Except.ok.inj (valueProjection.symm.trans valueProjected)
    have sameLayout : actual = layout := by
      cases actual; cases layout
      simp_all [Core.OrderedMapping.Layout.type]
    subst actual
    exact ⟨_, _, rfl, rfl, identity, registered, contents⟩
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
/-! Read trees are derived from complete payloads, static path layout/key
receipts, and the independent source read. No child Core evaluations or
representation-promotion callbacks are assumptions of the extraction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers

inductive Path (checked : SourceCoreDataCatalog.Checked) (signatures : ProgramSignatures)
    (functions : GenericHeap.PayloadModel checked.catalog) (mapping : LocationMap) (world : StoreTyping)
    (keys : List Value) : TypeSystem.Ty → Ty → List PreparedStep → List Dynamic.EvaluatedProjection →
      TypeSystem.Ty → Ty → Nat → Prop where
  | nil {sourceType : TypeSystem.Ty} {type : Ty} (projected : checked.catalog.project sourceType = .ok type) :
      Path checked signatures functions mapping world keys sourceType type [] [] sourceType type 0
  | member {root field leaf : TypeSystem.Ty} {dataType : DataTypeId} {index : Nat} {branches : List MemberBranch}
      {fieldType leafType : Ty} {name : String} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (layout : MemberLayout checked signatures root field dataType index branches)
      (fieldProjected : checked.catalog.project field = .ok fieldType)
      (tail : Path checked signatures functions mapping world keys field fieldType steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys root (.namedData dataType)
        (.member dataType index branches fieldType :: steps) (.member name index :: projections) leaf leafType count
  | index {keyType valueType leaf : TypeSystem.Ty} {index : PreparedIndex} {leafType : Ty}
      {sourceKey : Dynamic.Value} {key : Value} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (certificate : Index checked valueType index)
      (keyProjected : checked.catalog.project keyType = .ok index.layout.keyType)
      (valueProjected : checked.catalog.project valueType = .ok index.layout.valueType)
      (keyRelated : ValueRep checked.catalog signatures functions mapping world keyType sourceKey key index.layout.keyType)
      (keyAt : keys[index.keyPosition]? = some key)
      (tail : Path checked signatures functions mapping world keys valueType index.layout.valueType steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys (.mapping keyType valueType) index.layout.type
        (.index index :: steps) (.index sourceKey :: projections) leaf leafType (checked.catalog.entries.length + 1 + count)
  | comptime {inner leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
      {projections : List Dynamic.EvaluatedProjection} {count : Nat}
      (tail : Path checked signatures functions mapping world keys inner type steps projections leaf leafType count) :
      Path checked signatures functions mapping world keys (.comptime inner) type steps projections leaf leafType count

private theorem comptime_parts {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep catalog signatures functions mapping world (.comptime inner) source value type) :
    ValueRep catalog signatures functions mapping world inner source value type := by
  cases represented with
  | comptime inner => exact inner
  | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal

theorem Path.read_tree {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (layouts : CatalogLayouts checked.catalog) (prepared : Prepared) {keys : List Value}
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source sourceLeaf : Dynamic.Value} {value : Value}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (read : Dynamic.ProjectionsRead (some source) projections (some sourceLeaf)) :
    DataPlaceReadTree.Tree checked signatures identities prepared keys
      (fun source core => ValueRep checked.catalog signatures functions mapping world leaf source core leafType)
      source value steps projections sourceLeaf count := by
  induction path generalizing source value sourceLeaf with
  | nil projected => cases read; exact .leaf represented
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases read with
    | member selected read =>
      have same := sourceAt.functional selected
      subst sourceChild
      exact .member authenticated owner branchAt constructor payloads.length.1
        (arity.trans payloads.length.2.1) sourceAt coreAt (ih childRep read)
  | @index keyType valueType leaf index leafType sourceKey key steps projections count certificate keyProjected valueProjected keyRelated keyAt tail ih =>
    obtain ⟨sources, entries, sourceEq, valueEq, identity, registered, contents⟩ :=
      represented.mapping_parts index.layout keyProjected valueProjected
    subst source; subst value
    have keyObserved : KeyRep certificate signatures identities sourceKey key := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact keyRelated.observation observations
    have entriesObserved : OrderedMapping.EntriesRel (KeyRep certificate signatures identities)
        (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core index.layout.valueType)
        sources entries := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact contents.observed observations
    cases read with
    | indexFound found read =>
      apply DataPlaceReadTree.Tree.mapping (count := count) certificate keyObserved keyAt entriesObserved (.found found)
      intro child childRep
      rcases childRep with childRep | ⟨expression, defaulted⟩
      · exact ih childRep read
      · exact ih (default_represents_at layouts valueProjected defaulted) read
    | indexDefault absent defaulted read =>
      apply DataPlaceReadTree.Tree.mapping (count := count) certificate keyObserved keyAt entriesObserved (.default absent defaulted)
      intro child childRep
      rcases childRep with childRep | ⟨expression, defaulted⟩
      · exact ih childRep read
      · exact ih (default_represents_at layouts valueProjected defaulted) read
  | comptime tail ih => exact ih (comptime_parts represented) read

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
/-! Views of finite independent match execution. They retain the actual source
scrutinee and body derivations, hidden-cell allocation and lexical scope. The
view is proved from the existing judgments; it is not an executable evaluator. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
open Frontend Frontend.SourceInference

inductive Trace (program : Program) (context : Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (resolution : MatchResolution) : Dynamic.ControlOutcome → Dynamic.Heap → Prop where
  | scrutineeFault {reason after}
      (fault : Dynamic.ExpressionFaults program context evidence source environment before resolution.scrutinee reason after) :
      Trace program context evidence source environment before resolution (.fault reason) after
  | patternFault {node value middle hidden location}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (allocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (fault : Dynamic.MatchCasesPatternFault context value resolution.cases) :
      Trace program context evidence source environment before resolution (.fault .invalidPattern) hidden
  | arm {node value middle hidden location statements bindings armContext armEnvironment bound finalContext outcome after}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.arm statements bindings))
      (extended : BindersExtend source.owner context (bindings.map Prod.fst) armContext)
      (allocated : Dynamic.BindersAllocate environment hidden (bindings.map Prod.fst) (bindings.map Prod.snd) armEnvironment bound)
      (body : Dynamic.StatementsExecuteOutcome program armContext evidence source armEnvironment bound statements finalContext outcome after) :
      Trace program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | default {node value middle hidden location statements finalContext outcome after}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody (.default statements))
      (body : Dynamic.StatementsExecuteOutcome program context evidence source environment hidden statements finalContext outcome after) :
      Trace program context evidence source environment before resolution (Dynamic.restoreControl environment outcome) after
  | noBranch {node value middle hidden location}
      (contains : ContainsExpression source resolution.scrutinee node)
      (evaluated : Dynamic.ExpressionEvaluates program context evidence source environment before resolution.scrutinee value middle)
      (hiddenAllocated : Dynamic.Heap.Allocates middle node.type (some value) location hidden)
      (selected : Dynamic.MatchCasesSelect context value resolution.cases resolution.defaultBody .noBranch) :
      Trace program context evidence source environment before resolution (.fallthrough environment) hidden

private theorem shape {source : TypedSource} {id : StatementId} {node : StatementNode}
    {form : StatementForm} (unique : NodeOccurrencesUnique source)
    (contains : ContainsStatement source id node) (sameForm : node.form = form) :
    ∀ other, ContainsStatement source id other → other.form = form := by
  intro other otherContains
  have same : other = node := Option.some.inj
    ((lookupStatement?_complete unique otherContains).symm.trans (lookupStatement?_complete unique contains))
  exact same ▸ sameForm

theorem of_outcome {program : Program} {context finalContext : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .matchWith resolution)
    (executed : Dynamic.StatementExecutesOutcome program context evidence source environment before id finalContext outcome after) :
    finalContext = context ∧ Trace program context evidence source environment before resolution outcome after := by
  have formShape := shape unique contains form
  have present : ¬ Dynamic.StatementMissing source id := fun absent => Dynamic.StatementAbsentIn.excludes_contains absent contains
  clear contains form
  cases executed with
  | control executed =>
    cases executed <;> have actualForm := formShape _ (by assumption) <;> simp_all
    · exact .arm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (.control (by assumption))
    · exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.control (by assumption))
    · exact .noBranch (by assumption) (by assumption) (by assumption) (by assumption)
  | fault fault =>
    refine ⟨rfl, ?_⟩
    cases fault
    all_goals first
      | exact False.elim (present (by assumption))
      | have actualForm := formShape _ (by assumption); simp_all
    · exact .scrutineeFault (by assumption)
    · exact .patternFault (by assumption) (by assumption) (by assumption) (by assumption)
    · exact .arm (by assumption) (by assumption) (by assumption) (by assumption)
        (by assumption) (by assumption) (.fault (by assumption))
    · exact .default (by assumption) (by assumption) (by assumption) (by assumption) (.fault (by assumption))

theorem Trace.statement {program : Program} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
    {id : StatementId} {node : StatementNode} {resolution : MatchResolution} {outcome : Dynamic.ControlOutcome}
    (contains : ContainsStatement source id node) (form : node.form = .matchWith resolution)
    (trace : Trace program context evidence source environment before resolution outcome after) :
    Dynamic.StatementExecutesOutcome program context evidence source environment before id context outcome after := by
  cases trace with
  | scrutineeFault fault => exact .fault (.matchScrutinee contains form fault)
  | patternFault found evaluated allocated fault => exact .fault (.matchPattern contains form found evaluated allocated fault)
  | arm found evaluated hidden selected extended allocated body =>
    cases body with
    | control executed => exact .control (.matchArm contains form found evaluated hidden selected rfl rfl extended allocated executed)
    | fault fault => exact .fault (.matchArmBody contains form found evaluated hidden selected rfl rfl extended allocated fault)
  | default found evaluated hidden selected body =>
    cases body with
    | control executed => exact .control (.matchDefault contains form found evaluated hidden selected executed)
    | fault fault => exact .fault (.matchDefaultBody contains form found evaluated hidden selected fault)
  | noBranch found evaluated hidden selected => exact .control (.matchNoBranch contains form found evaluated hidden selected)

end Solcore.SourceSemantics.CoreLowering.DataMatchSourceTrace
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadRuntimeTypes
/-! Source shallow runtime types are a separate authenticity law for abstract
function leaves. Core typing alone cannot provide this information. Concrete
ordinary and descriptor-bearing closures retain their exact source metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayload
open Core Frontend Frontend.SourceInference GeneralHeap

/-- The key-type premise used by independent source mapping projections. It
observes retained function metadata, without inspecting captured heap cells. -/
def FunctionRuntimeTypes {catalog : SourceCoreDataCatalog.Catalog}
    (functions : GenericHeap.PayloadModel catalog) : Prop :=
  ∀ {mapping world parameter result source value type},
    functions.Represents mapping world (.function parameter result) source value type →
      Dynamic.ValueRuntimeType source (.function parameter result)

theorem ordinary_function_runtimeTypes (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (policy : SourceCoreFunctions.Policy) :
    FunctionRuntimeTypes (FunctionValues.model catalog program bodyCertificate policy) := by
  intro mapping world parameter result source value type related
  cases related with
  | closure layout code => exact .closure _

theorem contracted_function_runtimeTypes (catalog : SourceCoreDataCatalog.Catalog) (program : Program)
    (bodyCertificate : FunctionCode.BodyCertificate) (table : SourceCoreStageCodebook.Table) :
    FunctionRuntimeTypes (ContractedFunctionValues.model catalog program bodyCertificate table) := by
  intro mapping world parameter result source value type related
  cases related with
  | closure layout code => exact .closure _

private theorem erase_ne_comptime (type inner : TypeSystem.Ty) :
    SourceCoreDataCatalog.erase type ≠ .comptime inner := by
  induction type <;> simp_all [SourceCoreDataCatalog.erase]

/-- Canonical retained data types determine the mathematical source value's
shallow runtime type, including functions nested in products. Nominal and
proxy arguments are retained exactly, not erased by this conclusion. -/
theorem ValueRep.source_runtimeType {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel catalog} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (functionTypes : FunctionRuntimeTypes functions)
    (represented : ValueRep catalog signatures functions mapping world sourceType source value type)
    (canonical : SourceCoreDataCatalog.erase sourceType = sourceType) :
    Dynamic.ValueRuntimeType source sourceType := by
  revert canonical
  induction represented using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) with
  | unit => intro _; exact .unit
  | bool value => intro _; exact .bool value
  | word value => intro _; exact .word value
  | integer value => intro _; exact .integer value
  | product _ _ first second =>
    intro canonical
    obtain ⟨left, right⟩ := TypeSystem.Ty.product.inj canonical
    exact .product (first left) (second right)
  | function related => intro _; exact functionTypes related
  | proxy => intro _; exact .proxy _
  | mapping => intro _; exact .mapping _ _ _
  | constructed nominal result => intro _; rw [← result]; exact .constructed _ _
  | comptime => intro impossible; exact False.elim (erase_ne_comptime _ _ impossible)
  | nil | cons | empty | prepend => trivial

end Solcore.SourceSemantics.CoreLowering.DataPayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.DataPayloadFaultPaths
/-! Independent source missing-default faults determine the actual generated
read/update failures. Child evaluations are derived from complete payloads and
static helper receipts; no replacement expression is evaluated on this path. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues DataPayload
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMembers DataEquality

theorem Path.fault_preserves {checked : SourceCoreDataCatalog.Checked} {signatures : ProgramSignatures}
    {functions : GenericHeap.PayloadModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}
    {identities : Dynamic.Value → Word → Prop} (observations : FunctionObservations checked.catalog signatures functions identities)
    (faithful : IdentityFaithful identities) (layouts : CatalogLayouts checked.catalog)
    (prepared : Prepared) {keys : List Value} (keyLength : prepared.keyTypes.length = keys.length)
    {root leaf : TypeSystem.Ty} {type leafType : Ty} {steps : List PreparedStep}
    {projections : List Dynamic.EvaluatedProjection} {count : Nat}
    (path : Path checked signatures functions mapping world keys root type steps projections leaf leafType count)
    {source : Dynamic.Value} {value : Value} {reason : Dynamic.SemanticFault}
    (represented : ValueRep checked.catalog signatures functions mapping world root source value type)
    (fault : Dynamic.ProjectionsFaults (some source) projections reason)
    (environment : Environment) (store : Store) (current keyExpression replacementExpression : Expr)
    (selected : Selects environment current value) (keysSelected : Selects environment keyExpression (packValues keys)) :
    ∃ token finalStore administrative,
      Evaluates environment store (select prepared steps current keyExpression)
        (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
      Evaluates environment store (update prepared steps type current keyExpression replacementExpression)
        (.inLeft type (.word token)) finalStore ∧
      finalStore = store ++ administrative ∧ administrative.length ≤ count := by
  induction path generalizing source value environment store current keyExpression replacementExpression with
  | nil projected => cases fault
  | @member root field leaf dataType index branches fieldType leafType name steps projections count layout fieldProjected tail ih =>
    obtain ⟨declaration, arguments, nominal⟩ := layout.nominal
    obtain ⟨metadata, tag, sources, values, types, sourceEq, valueEq, typeEq, result, authenticated, registered, payloads⟩ :=
      represented.nominal_parts nominal
    subst source; subst value
    obtain ⟨owner, branch, branchAt, constructor, fieldAt, arity⟩ := layout.constructors metadata tag result authenticated
    obtain ⟨sourceChild, valueChild, childType, sourceAt, coreAt, coreTypeAt, childRep⟩ := payloads.at fieldAt
    have childTypeEq := Except.ok.inj (childRep.projection.symm.trans fieldProjected)
    subst childType
    cases fault with
    | member selectedAt fault =>
      have same := sourceAt.functional selectedAt
      subst sourceChild
      obtain ⟨token, finalStore, admin, readEval, updateEval, extended, counted⟩ :=
        ih childRep fault (packValues values :: environment) store _ (shift 1 keyExpression) (shift 1 replacementExpression)
          (projectPacked_selects (Selects.var (index := 0) rfl) (arity.trans payloads.length.2.1) index coreAt)
          (by simpa [shift] using keysSelected.weaken (packValues values))
      refine ⟨token, finalStore, admin, ?_, ?_, extended, counted⟩
      · exact .matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl) readEval
      · exact .matchData (selected.evaluates store) owner
          (by simp only [List.getElem?_map, branchAt, Option.map_some] <;> rfl)
          (LanguageResult.bind_failure _ updateEval)
  | @index keyType valueType leaf index leafType sourceKey key steps projections count certificate keyProjected valueProjected keyRelated keyAt tail ih =>
    obtain ⟨sources, entries, sourceEq, valueEq, identity, registered, contents⟩ :=
      represented.mapping_parts index.layout keyProjected valueProjected
    subst source; subst value
    have keyObserved : KeyRep certificate signatures identities sourceKey key := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact keyRelated.observation observations
    have entriesObserved : OrderedMapping.EntriesRel (KeyRep certificate signatures identities)
        (fun source core => ValueRep checked.catalog signatures functions mapping world valueType source core index.layout.valueType)
        sources entries := by
      unfold KeyRep DataMappingComparison.KeyRep
      rw [← certificate.keyType]
      exact contents.observed observations
    have keySelected := projectPacked_selects keysSelected keyLength index.keyPosition keyAt
    have finish {sourceChild : Dynamic.Value} (read : Reads sourceKey sources valueType sourceChild)
        (fault : Dynamic.ProjectionsFaults (some sourceChild) projections reason) :
        ∃ token finalStore administrative,
          Evaluates environment store (select prepared (.index index :: steps) current keyExpression)
            (.inLeft prepared.optionalLeaf (.word token)) finalStore ∧
          Evaluates environment store (update prepared (.index index :: steps) index.layout.type current keyExpression replacementExpression)
            (.inLeft index.layout.type (.word token)) finalStore ∧
          finalStore = store ++ administrative ∧ administrative.length ≤ checked.catalog.entries.length + 1 + count := by
      obtain ⟨child, childRep, childEvaluated⟩ := selectedIndex_preserves certificate prepared faithful keyObserved entriesObserved read
        environment store current keyExpression selected keySelected
      have completeChild : ValueRep checked.catalog signatures functions mapping world valueType sourceChild child index.layout.valueType := by
        rcases childRep with childRep | ⟨expression, defaulted⟩
        · exact childRep
        · exact default_represents_at layouts valueProjected defaulted
      obtain ⟨token, finalStore, after, readEval, updateEval, extended, counted⟩ :=
        ih completeChild fault (child :: environment) _ (.var 0) (shift 1 keyExpression) (shift 1 replacementExpression)
          (.var rfl) (by simpa [shift] using keysSelected.weaken child)
      obtain ⟨before, beforeExtended, beforeCounted⟩ := selectedStore_extension certificate environment store entries key
      refine ⟨token, finalStore, before ++ after, LanguageResult.bind_success _ childEvaluated readEval,
        LanguageResult.bind_success _ childEvaluated (LanguageResult.bind_failure _ updateEval), ?_, ?_⟩
      · rw [extended, beforeExtended, List.append_assoc]
      · simp only [List.length_append, beforeCounted]; omega
    cases fault with
    | indexDefaultUnavailable keyType absent unavailable =>
      have evaluated := selectedIndex_missing certificate prepared faithful keyObserved entriesObserved absent unavailable
        environment store current keyExpression selected keySelected
      obtain ⟨admin, extended, counted⟩ := selectedStore_extension certificate environment store entries key
      exact ⟨index.missing, _, admin, LanguageResult.bind_failure _ evaluated,
        LanguageResult.bind_failure _ evaluated, extended, by rw [counted]; omega⟩
    | indexFound keyType found fault => exact finish (.found found) fault
    | indexDefault keyType absent defaulted fault => exact finish (.default absent defaulted) fault
  | comptime tail ih =>
    exact ih (comptime_parts represented) fault environment store current keyExpression replacementExpression selected keysSelected

end Solcore.SourceSemantics.CoreLowering.DataPayloadReadPaths
end
