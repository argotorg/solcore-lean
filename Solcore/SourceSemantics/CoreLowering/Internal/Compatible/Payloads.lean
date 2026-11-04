import Solcore.SourceSemantics.CoreLowering.Internal.Foundations.Heaps
import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.SourceSemantics.CoreLowering.Internal.Data.Patterns
import Solcore.SourceSemantics.Dynamic.Default
import Solcore.Frontend.SourceRuntimeValues
import Solcore.Core.DefinitionExtension

/-!
# Compatible profile: payloads

`CompatiblePayload`, the independent data representation, with defaults, mappings, the ambient payload and the catalog registration prefix.

This file stays below the compiler's encoder, because this relation is stated independently of it, and the tests of these modules assert that the encoder is out of reach. The theorems that relate the two are in `Compatible/Encoding`.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePayload
/-! Independent data representation for the source-compatible native profile.
Raw proxy and constructor metadata is retained through authenticated registry
words even when native types erase comptime distinctions. This is not an
encode/decode graph and imports no source runtime value codec or evaluator.

Function leaves have the same projection, finite-world typing and extension
obligations as GenericHeap.PayloadModel, with an additional registry index.
The compatible catalog has a different projection, so this module does not
reinterpret it as a strict catalog or introduce another heap relation.
Ordered mappings preserve every entry in source order, including duplicates.
Their transported optional default is justified by the original raw source
type and the independent DefaultValue relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues

/-- Shape authentication only; code, evidence and capture validity remain the
responsibility of the supplied function model. -/
inductive IsFunction : Dynamic.Value → Prop where
  | closure (function : Dynamic.Closure) : IsFunction (.closure function)
  | global (function : Dynamic.GlobalFunction) : IsFunction (.global function)
  | builtin (function : Dynamic.BuiltinFunction) : IsFunction (.builtin function)

structure FunctionModel (catalog : SourceCoreCompatibleCatalog.Catalog)
    (ambient : AmbientDefinitions catalog.definitions := .original catalog.definitions) where
  Represents : SourceCoreRawMetadata.Registry → LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop
  projection : ∀ {registry mapping world sourceType source value type},
    Represents registry mapping world sourceType source value type → catalog.project sourceType = .ok type
  runtime_hasType : ∀ {registry mapping world sourceType source value type},
    Represents registry mapping world sourceType source value type → RuntimeValueHasType world value type ambient.definitions
  source_function : ∀ {registry mapping world sourceType source value type},
    Represents registry mapping world sourceType source value type → IsFunction source
  extend : ∀ {registry futureRegistry mapping futureMapping world futureWorld sourceType source value type},
    Represents registry mapping world sourceType source value type → SourceCoreRawMetadata.Extends registry futureRegistry →
    LocationMap.Extends mapping futureMapping → WorldExtends world futureWorld →
    Represents futureRegistry futureMapping futureWorld sourceType source value type

/-- One nonwrapping ID in its owning registry, with its original metadata. -/
structure MetadataRep (registry : SourceCoreRawMetadata.Registry) (metadata : SourceCoreRawMetadata.Metadata) (id : Word) : Prop where
  lookup : registry.lookup id = some metadata

theorem MetadataRep.authenticated {registry : SourceCoreRawMetadata.Registry} {metadata : SourceCoreRawMetadata.Metadata} {id : Word}
    (related : MetadataRep registry metadata id) : metadata.authentic registry.signatures = true :=
  SourceCoreRawMetadata.Registry.lookup_authenticated related.lookup

theorem MetadataRep.extend {registry future : SourceCoreRawMetadata.Registry} {metadata : SourceCoreRawMetadata.Metadata} {id : Word}
    (related : MetadataRep registry metadata id) (extension : SourceCoreRawMetadata.Extends registry future) :
    MetadataRep future metadata id := ⟨extension.lookup related.lookup⟩

theorem MetadataRep.nonzero {registry : SourceCoreRawMetadata.Registry} {metadata : SourceCoreRawMetadata.Metadata} {id : Word}
    (related : MetadataRep registry metadata id) : id ≠ Word.zero := by
  intro zero
  have found := related.lookup
  rw [zero, SourceCoreRawMetadata.Registry.lookup_zero] at found
  contradiction

/-- Native word equality observes exact original metadata, independently of
native type compatibility. -/
theorem MetadataRep.ids_equal_iff {registry : SourceCoreRawMetadata.Registry} {left right : SourceCoreRawMetadata.Metadata} {a b : Word}
    (first : MetadataRep registry left a) (second : MetadataRep registry right b) :
    a = b ↔ left = right := SourceCoreRawMetadata.Registry.ids_equal_iff first.lookup second.lookup

theorem MetadataRep.word_equality_iff {registry : SourceCoreRawMetadata.Registry} {left right : SourceCoreRawMetadata.Metadata} {a b : Word}
    (first : MetadataRep registry left a) (second : MetadataRep registry right b) :
    (a == b) = decide (left = right) := SourceCoreRawMetadata.Registry.word_equality_iff first.lookup second.lookup

mutual
  inductive ValueRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
      {ambient : AmbientDefinitions checked.catalog.definitions}
      (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping) :
      TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
    | unit : ValueRep checked registry functions mapping world .unit .unit .unit .unit
    | bool (value : Bool) : ValueRep checked registry functions mapping world .bool (.bool value) (.bool value) .bool
    | word (value : Word) : ValueRep checked registry functions mapping world .word (.word value) (.word value) .word
    | integer (value : Int) : ValueRep checked registry functions mapping world .integer (.integer value) (.integer value) .integer
    | product {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value} {aType bType : Ty}
        (first : ValueRep checked registry functions mapping world leftType left a aType)
        (second : ValueRep checked registry functions mapping world rightType right b bType) :
        ValueRep checked registry functions mapping world (.product leftType rightType)
          (.product left right) (.pair a b) (.product aType bType)
    | function {parameter result : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (related : functions.Represents registry mapping world (.function parameter result) source value type) :
        ValueRep checked registry functions mapping world (.function parameter result) source value type
    | proxy {inner : TypeSystem.Ty} {owner : DataTypeId} {id : Word}
        (metadata : MetadataRep registry (.proxy inner) id)
        (identity : checked.catalog.identity? (.proxy inner) = some owner)
        (registered : checked.catalog.definitions.lookupConstructorPayloadType? ⟨owner, 0⟩ = some .word) :
        ValueRep checked registry functions mapping world (.proxy inner) (.proxy inner)
          (.constructed ⟨owner, 0⟩ (.word id)) (.namedData owner)
    | constructed {metadata : DataConstructorInstantiation} {id : Word} {tag : ConstructorId}
        {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
        (metadataRep : MetadataRep registry (.constructor metadata) id)
        (registryOwner : registry.signatures = checked.signatures)
        (selected : checked.catalog.constructor? metadata = some tag)
        (projected : checked.catalog.project metadata.resultType = .ok (.namedData tag.owner))
        (registered : checked.catalog.definitions.lookupConstructorPayloadType? tag =
          some (.product .word (SourceCoreCompatibleCatalog.packTypes types)))
        (payloads : ValuesRep checked registry functions mapping world metadata.payloadTypes sources values types) :
        ValueRep checked registry functions mapping world metadata.resultType (.constructed metadata sources)
          (.constructed tag (.pair (.word id) (packValues values))) (.namedData tag.owner)
    | mappingValue {keyType valueType : TypeSystem.Ty} {id : Word} {layout : OrderedMapping.Layout}
        {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries} {fallback : Option Value}
        (metadata : MetadataRep registry (.mapping keyType valueType) id)
        (identity : checked.catalog.identity? (.mapping keyType valueType) = some layout.dataType)
        (keyProjection : checked.catalog.project keyType = .ok layout.keyType)
        (valueProjection : checked.catalog.project valueType = .ok layout.valueType)
        (registered : layout.Registered checked.catalog.definitions)
        (stored : EntriesRep checked registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType)
        (defaultValue : DefaultRep checked registry functions mapping world valueType fallback layout.valueType) :
        ValueRep checked registry functions mapping world (.mapping keyType valueType)
          (.mapping keyType valueType sources) (SourceCoreMappingWithDefault.value id fallback layout entries)
          (SourceCoreMappingWithDefault.type layout)
    | compatible {expected actual : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
        (related : ValueRep checked registry functions mapping world actual source value type) :
        ValueRep checked registry functions mapping world expected source value type
  inductive ValuesRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
      {ambient : AmbientDefinitions checked.catalog.definitions}
      (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping) :
      List TypeSystem.Ty → List Dynamic.Value → List Value → List Ty → Prop where
    | nil : ValuesRep checked registry functions mapping world [] [] [] []
    | cons {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
        (head : ValueRep checked registry functions mapping world sourceType source value type)
        (tail : ValuesRep checked registry functions mapping world sourceTypes sources values types) :
        ValuesRep checked registry functions mapping world (sourceType :: sourceTypes) (source :: sources) (value :: values) (type :: types)
  inductive EntriesRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
      {ambient : AmbientDefinitions checked.catalog.definitions}
      (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping) :
      TypeSystem.Ty → TypeSystem.Ty → List (Dynamic.Value × Dynamic.Value) → OrderedMapping.Entries → Ty → Ty → Prop where
    | empty (keyType valueType : TypeSystem.Ty) (key value : Ty) :
        EntriesRep checked registry functions mapping world keyType valueType [] [] key value
    | entry {keyType valueType : TypeSystem.Ty} {key value : Dynamic.Value} {a b : Value} {aType bType : Ty}
        {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries}
        (keyRep : ValueRep checked registry functions mapping world keyType key a aType)
        (valueRep : ValueRep checked registry functions mapping world valueType value b bType)
        (tail : EntriesRep checked registry functions mapping world keyType valueType sources entries aType bType) :
        EntriesRep checked registry functions mapping world keyType valueType ((key, value) :: sources) ((a, b) :: entries) aType bType
  inductive DefaultRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
      {ambient : AmbientDefinitions checked.catalog.definitions}
      (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping) :
      TypeSystem.Ty → Option Value → Ty → Prop where
    | absent {sourceType : TypeSystem.Ty} {type : Ty}
        (missing : ¬ Dynamic.Defaultable sourceType)
        (projected : checked.catalog.project sourceType = .ok type)
        (wellFormed : type.WellFormed checked.catalog.definitions) :
        DefaultRep checked registry functions mapping world sourceType none type
    | present {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (meaning : Dynamic.DefaultValue sourceType source)
        (related : ValueRep checked registry functions mapping world sourceType source value type) :
        DefaultRep checked registry functions mapping world sourceType (some value) type

end

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

theorem ValueRep.projection {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    checked.catalog.project sourceType = .ok type := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer => rfl
  | product _ _ first second => simp [SourceCoreCompatibleCatalog.Catalog.project, first, second, bind, Except.bind, pure, Except.pure]
  | function related => exact functions.projection related
  | proxy _ identity _ => simp [SourceCoreCompatibleCatalog.Catalog.project, identity]
  | constructed _ _ _ projected => exact projected
  | compatible same _ ih =>
    rw [← checked.catalog.project_runtimeType, same, checked.catalog.project_runtimeType]
    exact ih
  | mappingValue _ identity key value _ _ _ _ _ =>
    simp [SourceCoreCompatibleCatalog.Catalog.project, identity, key, value, bind, Except.bind, pure, Except.pure]
  | nil | cons | empty | entry | absent | present => trivial

private theorem pack_typed {definitions : DataEnvironment} {types : List Ty} {values : List Value}
    (typed : ListRel (fun value type => RuntimeValueHasType world value type definitions) values types) :
    RuntimeValueHasType world (packValues values) (SourceCoreCompatibleCatalog.packTypes types) definitions := by
  induction typed with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => exact head
    | cons => exact .pair head ih

theorem ValueRep.runtime_hasType {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    RuntimeValueHasType world value type ambient.definitions := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ values types _ => ListRel (fun value type => RuntimeValueHasType world value type ambient.definitions) values types)
    (motive_3 := fun _ _ _ entries aType bType _ => ∀ a b, (a, b) ∈ entries →
      RuntimeValueHasType world a aType ambient.definitions ∧ RuntimeValueHasType world b bType ambient.definitions)
    (motive_4 := fun _ fallback type _ => RuntimeValueHasType world (OrderedMapping.optionValue type fallback) (.sum .unit type) ambient.definitions) with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .pair first second
  | function related => exact functions.runtime_hasType related
  | proxy _ _ registered => exact .constructed (ambient.basePrefix.constructor_lookup registered) .word
  | constructed _ _ _ _ registered _ ih => exact .constructed (ambient.basePrefix.constructor_lookup registered) (.pair .word (pack_typed ih))
  | compatible _ _ ih => exact ih
  | mappingValue _ _ _ _ registered _ _ entries fallback =>
    exact .pair .word (.pair fallback (OrderedMapping.encode_hasType (registered.extend_definitions ambient.basePrefix) _ entries))
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => simp_all
  | entry _ _ _ key value tail =>
    rename_i a b member
    rcases List.mem_cons.mp member with head | rest
    · cases head; exact ⟨key, value⟩
    · exact tail a b rest
  | absent => exact .inLeft .unit
  | present _ _ typed => exact .inRight typed

/-- Static IDs and all raw metadata survive input-registry extension. The
finite location map/world extension is delegated only at function leaves. -/
theorem ValueRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    ValueRep checked futureRegistry functions futureMapping futureWorld sourceType source value type := by
  induction related using ValueRep.rec
    (motive_2 := fun types sources values coreTypes _ => ValuesRep checked futureRegistry functions futureMapping futureWorld types sources values coreTypes)
    (motive_3 := fun key value sources entries aType bType _ => EntriesRep checked futureRegistry functions futureMapping futureWorld key value sources entries aType bType)
    (motive_4 := fun type fallback coreType _ => DefaultRep checked futureRegistry functions futureMapping futureWorld type fallback coreType) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | function related => exact .function (functions.extend related metadata maps worlds)
  | proxy header identity registered => exact .proxy (header.extend metadata) identity registered
  | constructed header owner selected projected registered _ ih =>
    exact .constructed (header.extend metadata) (metadata.signatures.trans owner) selected projected registered ih
  | compatible same _ ih => exact .compatible same ih
  | mappingValue header identity key value registered _ _ entries fallback =>
    exact .mappingValue (header.extend metadata) identity key value registered entries fallback
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => exact .empty _ _ _ _
  | entry _ _ _ key value tail => exact .entry key value tail
  | absent missing projected wf => exact .absent missing projected wf
  | present meaning _ ih => exact .present meaning ih

theorem ValuesRep.length {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {coreTypes : List Ty}
    (related : ValuesRep checked registry functions mapping world types sources values coreTypes) :
    types.length = sources.length ∧ types.length = values.length ∧ types.length = coreTypes.length := by
  induction types generalizing sources values coreTypes with
  | nil => cases related; exact ⟨rfl, rfl, rfl⟩
  | cons head tail ih =>
    cases related with
    | cons first rest =>
      have same := ih rest
      exact ⟨congrArg Nat.succ same.1, congrArg Nat.succ same.2.1, congrArg Nat.succ same.2.2⟩

/-- Registry ownership authenticates the exact original substitution, payload
types and nominal result, independently of their runtime-compatible projection. -/
theorem constructor_authenticated {metadata : DataConstructorInstantiation} {id : Word}
    (related : MetadataRep registry (.constructor metadata) id)
    (owner : registry.signatures = checked.signatures) :
    SourceCoreRawMetadata.constructorAuthentic checked.signatures metadata = true := by
  simpa only [SourceCoreRawMetadata.Metadata.authentic, owner] using related.authenticated

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleDefaults
/-! The pure runtime default constructor agrees with the independent source
semantics. Its original source types are retained: runtime type erasure is
never used to choose a default. The carrier relation below is structural and
has no evaluator, codec, or generated-expression premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap

/-- The data shapes that the pure default constructor can produce. Raw proxy
and empty-mapping metadata is equal on both sides. -/
inductive DefaultData : SourceTypedRuntime.Value → Dynamic.Value → Prop where
  | unit : DefaultData .unit .unit
  | bool (value : Bool) : DefaultData (.bool value) (.bool value)
  | word (value : Word) : DefaultData (.word value) (.word value)
  | integer (value : Int) : DefaultData (.integer value) (.integer value)
  | product {a b : SourceTypedRuntime.Value} {left right : Dynamic.Value}
      (first : DefaultData a left) (second : DefaultData b right) :
      DefaultData (.product a b) (.product left right)
  | proxy (inner : TypeSystem.Ty) : DefaultData (.proxy inner) (.proxy inner)
  | mapping (key value : TypeSystem.Ty) :
      DefaultData (.mapping key value []) (.mapping key value [])

theorem DefaultData.functional {raw : SourceTypedRuntime.Value} {a b : Dynamic.Value}
    (first : DefaultData raw a) (second : DefaultData raw b) : a = b := by
  induction first generalizing b with
  | product _ _ first second =>
    cases ‹DefaultData _ b› with
    | product a b => rw [first a, second b]
  | unit | bool | word | integer | proxy | mapping => cases second; rfl

/-- Every successful pure constructor has an independent default meaning,
including the exact un-erased metadata of proxy and mapping leaves. -/
theorem defaultValue?_sound {fuel : Nat} {type : TypeSystem.Ty} {raw : SourceTypedRuntime.Value}
    (found : SourceTypedRuntime.defaultValue? fuel type = some raw) :
    ∃ source, Dynamic.DefaultValue type source ∧ DefaultData raw source := by
  induction fuel generalizing type raw with
  | zero => simp [SourceTypedRuntime.defaultValue?] at found
  | succ fuel ih =>
    cases type with
    | constructor id =>
      cases id with
      | builtin builtin =>
        cases builtin <;> simp [SourceTypedRuntime.defaultValue?] at found <;> subst raw
        · exact ⟨_, .unit, .unit⟩
        · exact ⟨_, .bool, .bool _⟩
        · exact ⟨_, .word, .word _⟩
        · exact ⟨_, .integer, .integer _⟩
      | declaration => simp [SourceTypedRuntime.defaultValue?] at found
    | product left right =>
      cases first : SourceTypedRuntime.defaultValue? fuel left with
      | none => simp [SourceTypedRuntime.defaultValue?, first] at found
      | some a =>
        cases second : SourceTypedRuntime.defaultValue? fuel right with
        | none => simp [SourceTypedRuntime.defaultValue?, first, second] at found
        | some b =>
          simp [SourceTypedRuntime.defaultValue?, first, second] at found
          subst raw
          obtain ⟨aSource, aMeaning, aRep⟩ := ih first
          obtain ⟨bSource, bMeaning, bRep⟩ := ih second
          exact ⟨_, .product aMeaning bMeaning, .product aRep bRep⟩
    | proxy inner =>
      simp [SourceTypedRuntime.defaultValue?] at found
      subst raw
      exact ⟨_, .proxy _, .proxy _⟩
    | mapping key value =>
      simp [SourceTypedRuntime.defaultValue?] at found
      subst raw
      exact ⟨_, .mapping _ _, .mapping _ _⟩
    | comptime inner =>
      obtain ⟨source, meaning, represented⟩ := ih found
      exact ⟨source, .comptime meaning, represented⟩
    | «variable» | parameter | application | function | error => simp [SourceTypedRuntime.defaultValue?] at found

/-- A structural source-size bound suffices; this is compile-time constructor
fuel and has no relationship to Core execution fuel. -/
theorem defaultValue?_complete {type : TypeSystem.Ty} {source : Dynamic.Value}
    (meaning : Dynamic.DefaultValue type source) :
    ∀ fuel, type.size < fuel → ∃ raw,
      SourceTypedRuntime.defaultValue? fuel type = some raw ∧ DefaultData raw source := by
  induction meaning with
  | unit | bool | word | integer | proxy | mapping =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel => exact ⟨_, rfl, by constructor⟩
  | @product leftType rightType left right _ _ first second =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [TypeSystem.Ty.size] at bound
      obtain ⟨a, aFound, aRep⟩ := first fuel (by omega)
      obtain ⟨b, bFound, bRep⟩ := second fuel (by omega)
      exact ⟨_, by simp [SourceTypedRuntime.defaultValue?, aFound, bFound], .product aRep bRep⟩
  | @comptime inner source _ ih =>
    intro fuel bound
    cases fuel with
    | zero => omega
    | succ fuel =>
      simp only [TypeSystem.Ty.size] at bound
      exact ih fuel (by omega)

theorem defaultValue?_absent_iff {fuel : Nat} {type : TypeSystem.Ty} (enough : type.size < fuel) :
    SourceTypedRuntime.defaultValue? fuel type = none ↔ ¬ Dynamic.Defaultable type := by
  constructor
  · intro absent existsDefault
    obtain ⟨source, meaning⟩ := existsDefault.exists_default
    obtain ⟨raw, found, _⟩ := defaultValue?_complete meaning fuel enough
    rw [absent] at found
    contradiction
  · intro missing
    cases found : SourceTypedRuntime.defaultValue? fuel type with
    | none => rfl
    | some raw =>
      obtain ⟨source, meaning, _⟩ := defaultValue?_sound found
      exact False.elim (missing meaning.defaultable)

theorem defaultValue?_canonical {type : TypeSystem.Ty} {source : Dynamic.Value}
    (meaning : Dynamic.DefaultValue type source) :
    ∃ raw, SourceTypedRuntime.defaultValue? (type.size + 1) type = some raw ∧ DefaultData raw source :=
  defaultValue?_complete meaning _ (by omega)

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {functions : FunctionModel checked.catalog} {mapping : LocationMap} {world : StoreTyping}

/-- A transported default is present exactly when the original raw source
type has a default. Its native carrier may recursively contain mappings and
raw proxy metadata. -/
theorem DefaultRep.isSome_iff {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType) :
    fallback.isSome = true ↔ Dynamic.Defaultable type := by
  cases represented with
  | absent missing => simp [missing]
  | present meaning => simp [meaning.defaultable]

theorem DefaultRep.absent_iff {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType) :
    fallback = none ↔ ¬ Dynamic.Defaultable type := by
  cases represented with
  | absent missing => simp [missing]
  | present meaning => simp [meaning.defaultable]

/-- This bridge connects the actual pure default computation to an already
authenticated native payload. It does not assume a codec is semantics. -/
theorem DefaultRep.of_computed {fuel : Nat} {type : TypeSystem.Ty} {raw : SourceTypedRuntime.Value}
    {source : Dynamic.Value} {value : Value} {coreType : Ty}
    (found : SourceTypedRuntime.defaultValue? fuel type = some raw)
    (data : DefaultData raw source)
    (represented : ValueRep checked registry functions mapping world type source value coreType) :
    DefaultRep checked registry functions mapping world type (some value) coreType := by
  obtain ⟨actual, meaning, related⟩ := defaultValue?_sound found
  have same := related.functional data
  subst actual
  exact .present meaning represented

theorem DefaultRep.of_absent {fuel : Nat} {type : TypeSystem.Ty} {coreType : Ty}
    (enough : type.size < fuel) (missing : SourceTypedRuntime.defaultValue? fuel type = none)
    (projected : checked.catalog.project type = .ok coreType)
    (wf : coreType.WellFormed checked.catalog.definitions) :
    DefaultRep checked registry functions mapping world type none coreType :=
  .absent ((defaultValue?_absent_iff enough).mp missing) projected wf

/-- Conversely, an independent transported default determines the observable
pure-constructor result. Absence cannot be attributed to exhausted fuel. -/
theorem DefaultRep.computed {fuel : Nat} {type : TypeSystem.Ty} {fallback : Option Value} {coreType : Ty}
    (represented : DefaultRep checked registry functions mapping world type fallback coreType)
    (enough : type.size < fuel) :
    match fallback with
    | none => SourceTypedRuntime.defaultValue? fuel type = none
    | some value => ∃ raw source,
        SourceTypedRuntime.defaultValue? fuel type = some raw ∧ DefaultData raw source ∧
        Dynamic.DefaultValue type source ∧ ValueRep checked registry functions mapping world type source value coreType := by
  cases represented with
  | absent missing => exact (defaultValue?_absent_iff enough).mpr missing
  | present meaning related =>
    obtain ⟨raw, found, data⟩ := defaultValue?_complete meaning fuel enough
    exact ⟨raw, _, found, data, meaning, related⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleMappings
/-! Ordered-entry and transported-default laws for the compatible payload
relation. Entries remain an ordered list: there is no deduplication, key
comparison, or normalization in this representation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}

theorem DefaultRep.projection {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type) :
    checked.catalog.project sourceType = .ok type := by
  cases related with
  | absent _ projected => exact projected
  | present _ related => exact related.projection

theorem DefaultRep.runtime_hasType {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type) :
    RuntimeValueHasType world (OrderedMapping.optionValue type fallback) (.sum .unit type) ambient.definitions := by
  cases related with
  | absent => exact .inLeft .unit
  | present _ related => exact .inRight related.runtime_hasType

theorem DefaultRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {fallback : Option Value} {type : Ty}
    (related : DefaultRep checked registry functions mapping world sourceType fallback type)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    DefaultRep checked futureRegistry functions futureMapping futureWorld sourceType fallback type := by
  cases related with
  | absent missing projected wf => exact .absent missing projected wf
  | present meaning related => exact .present meaning (related.extend metadata maps worlds)

theorem EntriesRep.length {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value) :
    sources.length = entries.length := by
  induction sources generalizing entries with
  | nil => cases related; rfl
  | cons source sources ih => cases related with
    | entry _ _ tail => exact congrArg Nat.succ (ih tail)

/-- Every source entry has its corresponding native entry at the same index.
In particular, repeated source keys keep all their positions. -/
theorem EntriesRep.get {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value)
    {index : Nat} {sourceKey sourceValue : Dynamic.Value} (found : sources[index]? = some (sourceKey, sourceValue)) :
    ∃ a b, entries[index]? = some (a, b) ∧
      ValueRep checked registry functions mapping world keyType sourceKey a key ∧
      ValueRep checked registry functions mapping world valueType sourceValue b value := by
  induction index generalizing sources entries with
  | zero => cases related with
    | empty => simp at found
    | entry keyRep valueRep tail =>
      simp only [List.getElem?_cons_zero, Option.some.injEq, Prod.mk.injEq] at found
      rcases found with ⟨rfl, rfl⟩
      exact ⟨_, _, rfl, keyRep, valueRep⟩
  | succ index ih => cases related with
    | empty => simp at found
    | entry _ _ tail => exact ih tail found

theorem EntriesRep.runtime_hasType {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)}
    {entries : OrderedMapping.Entries} {layout : OrderedMapping.Layout}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType)
    (registered : layout.Registered checked.catalog.definitions) :
    RuntimeValueHasType world (OrderedMapping.encode layout entries) layout.type ambient.definitions := by
  have nativeRegistered : layout.Registered ambient.definitions :=
    ⟨registered.keyWellFormed.extend_definitions ambient.basePrefix,
      registered.valueWellFormed.extend_definitions ambient.basePrefix,
      ambient.basePrefix.lookup registered.lookup⟩
  apply OrderedMapping.encode_hasType nativeRegistered
  induction sources generalizing entries with
  | nil => cases related; simp
  | cons source sources ih =>
    cases related with
    | entry keyRep valueRep tail =>
      intro a b member
      rcases List.mem_cons.mp member with head | rest
      · cases head; exact ⟨keyRep.runtime_hasType, valueRep.runtime_hasType⟩
      · exact ih tail a b rest

theorem EntriesRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {keyType valueType : TypeSystem.Ty} {sources : List (Dynamic.Value × Dynamic.Value)} {entries : OrderedMapping.Entries} {key value : Ty}
    (related : EntriesRep checked registry functions mapping world keyType valueType sources entries key value)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    EntriesRep checked futureRegistry functions futureMapping futureWorld keyType valueType sources entries key value := by
  induction sources generalizing entries with
  | nil => cases related; exact .empty _ _ _ _
  | cons source sources ih => cases related with
    | entry first second tail => exact .entry (first.extend metadata maps worlds) (second.extend metadata maps worlds) (ih tail)

/-- Extract the authenticated raw header and exact ordered/default carriers
from any mapping payload, even behind a runtime-compatible type view. -/
theorem ValueRep.mapping_shape {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {keyType valueType sources}, source = .mapping keyType valueType sources →
      ∃ id layout entries fallback,
        value = SourceCoreMappingWithDefault.value id fallback layout entries ∧
        type = SourceCoreMappingWithDefault.type layout ∧
        MetadataRep registry (.mapping keyType valueType) id ∧
        layout.Registered checked.catalog.definitions ∧
        EntriesRep checked registry functions mapping world keyType valueType sources entries layout.keyType layout.valueType ∧
        DefaultRep checked registry functions mapping world valueType fallback layout.valueType := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed => intro _ _ _ impossible; cases impossible
  | function related =>
    intro _ _ _ impossible
    have shape := functions.source_function related
    cases shape <;> cases impossible
  | mappingValue header _ _ _ registered stored fallback _ _ =>
    intro _ _ _ same
    cases same
    exact ⟨_, _, _, _, rfl, rfl, header, registered, stored, fallback⟩
  | compatible _ _ ih => exact ih
  | nil | cons | empty | entry | absent | present => trivial

/-- Equal native mapping header words mean equal original key/value metadata,
including all nested staging wrappers. -/
theorem mapping_headers_equal_iff {a b : Word} {leftKey leftValue rightKey rightValue : TypeSystem.Ty}
    (left : MetadataRep registry (.mapping leftKey leftValue) a)
    (right : MetadataRep registry (.mapping rightKey rightValue) b) :
    a = b ↔ leftKey = rightKey ∧ leftValue = rightValue := by
  simpa only [SourceCoreRawMetadata.Metadata.mapping.injEq] using left.ids_equal_iff right

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleAmbientPayload
/-! Changing only the ambient Core definition environment preserves the raw
source metadata relation. Function interpretations are transferred explicitly;
a fresh interpretation may authenticate new administrative closure code, while
simple extension transports only the old interpreted values. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend GeneralHeap

/-- Existing function code and values retain their exact representation when
the definition table grows. This does not add new functions to the relation. -/
def FunctionModel.extend_definitions {catalog : SourceCoreCompatibleCatalog.Catalog}
    {before after : AmbientDefinitions catalog.definitions}
    (functions : FunctionModel catalog before) (extension : before.definitions.Extends after.definitions) :
    FunctionModel catalog after where
  Represents := functions.Represents
  projection := functions.projection
  runtime_hasType := fun represented => (functions.runtime_hasType represented).extend_definitions extension
  source_function := functions.source_function
  extend := functions.extend

/-- A function model may grow to include newly emitted code. Its full typing,
source authenticity and semantic laws remain the new model's responsibility. -/
def FunctionModel.Includes {catalog : SourceCoreCompatibleCatalog.Catalog}
    {before after : AmbientDefinitions catalog.definitions}
    (initial : FunctionModel catalog before) (future : FunctionModel catalog after) : Prop :=
  ∀ {registry mapping world sourceType source value type},
    initial.Represents registry mapping world sourceType source value type →
      future.Represents registry mapping world sourceType source value type

theorem ValueRep.map_functions {checked : SourceCoreCompatibleCatalog.Checked}
    {before after : AmbientDefinitions checked.catalog.definitions}
    {initial : FunctionModel checked.catalog before} {future : FunctionModel checked.catalog after}
    (includes : initial.Includes future)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry initial mapping world sourceType source value type) :
    ValueRep checked registry future mapping world sourceType source value type := by
  induction related using ValueRep.rec
    (motive_2 := fun types sources values coreTypes _ => ValuesRep checked registry future mapping world types sources values coreTypes)
    (motive_3 := fun key value sources entries aType bType _ => EntriesRep checked registry future mapping world key value sources entries aType bType)
    (motive_4 := fun type fallback coreType _ => DefaultRep checked registry future mapping world type fallback coreType) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | function related => exact .function (includes related)
  | proxy header identity registered => exact .proxy header identity registered
  | constructed header owner selected projected registered _ ih => exact .constructed header owner selected projected registered ih
  | compatible same _ ih => exact .compatible same ih
  | mappingValue header identity key value registered _ _ entries fallback =>
    exact .mappingValue header identity key value registered entries fallback
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail
  | empty => exact .empty _ _ _ _
  | entry _ _ _ key value tail => exact .entry key value tail
  | absent missing projected wf => exact .absent missing projected wf
  | present meaning _ ih => exact .present meaning ih

theorem ValueRep.extend_definitions {checked : SourceCoreCompatibleCatalog.Checked}
    {before after : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog before)
    (extension : before.definitions.Extends after.definitions)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ValueRep checked registry (functions.extend_definitions extension) mapping world sourceType source value type :=
  ValueRep.map_functions (initial := functions) (future := functions.extend_definitions extension) (fun represented => represented) related

end Solcore.SourceSemantics.CoreLowering.CompatiblePayload
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix
/-! Successful compatible type registration preserves every existing entry.
The exact fuel induction follows the production reserve/register/install calls,
including recursive nominal payloads. This yields native definition extensions;
complete constructor coverage still requires a separate factory invariant. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix
open Core Frontend SourceInference SourceCoreCompatibleCatalog

def EntriesExtend (before after : Catalog) : Prop :=
  ∃ suffix, after.entries = before.entries ++ suffix

theorem EntriesExtend.refl (catalog : Catalog) : EntriesExtend catalog catalog := ⟨[], by simp⟩

theorem EntriesExtend.trans {before middle after : Catalog}
    (first : EntriesExtend before middle) (last : EntriesExtend middle after) : EntriesExtend before after := by
  obtain ⟨left, first⟩ := first
  obtain ⟨right, last⟩ := last
  exact ⟨left ++ right, by rw [last, first, List.append_assoc]⟩

private theorem modify_suffix {α : Type} (front rest : List α) (index : Nat) (update : α → α) :
    (front ++ rest).modify (front.length + index) update = front ++ rest.modify index update := by
  induction front with
  | nil => simp
  | cons head tail ih => simpa [List.modify, Nat.succ_add] using congrArg (List.cons head) ih

private theorem install_suffix {before middle : Catalog} {entry : Entry} (update : Entry → Entry)
    (extension : EntriesExtend {before with entries := before.entries ++ [entry]} middle) :
    ∃ suffix, middle.entries.modify before.entries.length update = before.entries ++ suffix := by
  obtain ⟨suffix, extended⟩ := extension
  refine ⟨([entry] ++ suffix).modify 0 update, ?_⟩
  rw [extended, List.append_assoc]
  exact modify_suffix before.entries ([entry] ++ suffix) 0 update

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- Only registered Source types are used to justify concrete preparation. -/
def ClosedSources (catalog : Catalog) : Prop :=
  ∀ entry, entry ∈ catalog.entries → SourceCoreDataCatalog.closed entry.sourceType = true

/-- The same registration fold retains its source closure invariant beside
its original append-only entry prefix. -/
structure Registered (before after : Catalog) : Prop where
  entries : EntriesExtend before after
  closed : ClosedSources before → ClosedSources after

theorem Registered.refl (catalog : Catalog) : Registered catalog catalog :=
  ⟨EntriesExtend.refl catalog, fun closed => closed⟩

theorem Registered.trans {before middle after : Catalog}
    (first : Registered before middle) (last : Registered middle after) : Registered before after :=
  ⟨first.entries.trans last.entries, fun closed => last.closed (first.closed closed)⟩

private theorem closed_modify (entries : List Entry) (index : Nat) (update : Entry → Entry)
    (same : ∀ entry, (update entry).sourceType = entry.sourceType)
    (closed : ∀ entry, entry ∈ entries → SourceCoreDataCatalog.closed entry.sourceType = true) :
    ∀ entry, entry ∈ entries.modify index update → SourceCoreDataCatalog.closed entry.sourceType = true := by
  induction entries generalizing index with
  | nil => intro entry member; simp only [List.modify_nil, List.not_mem_nil] at member
  | cons head tail ih =>
    cases index with
    | zero =>
      intro entry member
      simp only [List.modify_zero_cons, List.mem_cons] at member
      rcases member with rfl | member
      · rw [same]; exact closed head List.mem_cons_self
      · exact closed entry (List.mem_cons_of_mem _ member)
    | succ index =>
      intro entry member
      simp only [List.modify_succ_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact closed _ List.mem_cons_self
      · exact ih index (fun entry member => closed entry (List.mem_cons_of_mem _ member)) entry member

private theorem installed {before middle : Catalog} {entry : Entry} (update : Entry → Entry)
    (same : ∀ item, (update item).sourceType = item.sourceType)
    (entryClosed : SourceCoreDataCatalog.closed entry.sourceType = true)
    (extension : Registered {before with entries := before.entries ++ [entry]} middle) :
    Registered before {middle with entries := middle.entries.modify before.entries.length update} := by
  refine ⟨install_suffix update extension.entries, ?_⟩
  intro beforeClosed
  apply closed_modify _ _ _ same
  apply extension.closed
  intro item member
  rcases List.mem_append.mp member with old | fresh
  · exact beforeClosed item old
  · exact List.mem_singleton.mp fresh ▸ entryClosed

theorem registered_prefix_with_closed (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, registerType signatures fuel before original = .ok (after, type) → Registered before after) ∧
    (∀ before originals after types, registerTypes signatures fuel before originals = .ok (after, types) → Registered before after) := by
  induction fuel with
  | zero =>
    constructor
    · intro before original after type accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · rename_i closed
        split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact .refl _
        · cases accepted
      · cases accepted
    · intro before originals after types accepted
      cases originals with
      | nil => cases accepted; exact .refl _
      | cons => cases accepted
  | succ fuel ih =>
    constructor
    · intro before original after type accepted
      unfold registerType at accepted
      simp only [bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at accepted
      split at accepted
      · rename_i closed
        split at accepted
        · obtain ⟨native, _, accepted⟩ := bind_ok accepted
          cases accepted
          exact .refl _
        · split at accepted
          · obtain ⟨native, _, accepted⟩ := bind_ok accepted
            cases accepted
            exact .refl _
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            exact (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
          · obtain ⟨registered, child, accepted⟩ := bind_ok accepted
            cases accepted
            have extension := ih.1 _ _ _ _ child
            exact installed _ (fun _ => rfl) closed extension
          · obtain ⟨first, initial, remaining⟩ := bind_ok accepted
            obtain ⟨last, final, accepted⟩ := bind_ok remaining
            cases accepted
            have extension := (ih.1 _ _ _ _ initial).trans (ih.1 _ _ _ _ final)
            exact installed _ (fun _ => rfl) closed extension
          · split at accepted
            · obtain ⟨signature, selected, accepted⟩ := bind_ok accepted
              split at accepted
              · split at accepted
                · obtain ⟨_, _, accepted⟩ := bind_ok accepted
                  obtain ⟨registered, child, accepted⟩ := bind_ok accepted
                  cases accepted
                  exact installed _ (fun _ => rfl) closed (ih.2 _ _ _ _ child)
                · cases accepted
              · cases accepted
            · cases accepted
      · cases accepted
    · intro before originals after types accepted
      cases originals with
      | nil => cases accepted; exact .refl _
      | cons original rest =>
        obtain ⟨first, initial, remaining⟩ := bind_ok accepted
        obtain ⟨tail, final, accepted⟩ := bind_ok remaining
        cases accepted
        exact (ih.1 _ _ _ _ initial).trans (ih.2 _ _ _ _ final)

/-- The original registration interface forgets only the closed-source invariant. -/
theorem registered_prefix (signatures : ProgramSignatures) (fuel : Nat) :
    (∀ before original after type, registerType signatures fuel before original = .ok (after, type) → EntriesExtend before after) ∧
    (∀ before originals after types, registerTypes signatures fuel before originals = .ok (after, types) → EntriesExtend before after) := by
  exact ⟨fun _ _ _ _ accepted => ((registered_prefix_with_closed signatures fuel).1 _ _ _ _ accepted).entries,
    fun _ _ _ _ accepted => ((registered_prefix_with_closed signatures fuel).2 _ _ _ _ accepted).entries⟩

theorem EntriesExtend.definitions {before after : Catalog} (extension : EntriesExtend before after) :
    before.definitions.Extends after.definitions := by
  obtain ⟨suffix, extended⟩ := extension
  refine ⟨suffix.map (fun entry => entry.definition.getD ⟨[]⟩), ?_⟩
  simp only [Catalog.definitions, extended, List.map_append]

theorem EntriesExtend.lookup {before after : Catalog} (extension : EntriesExtend before after)
    {index : Nat} {entry : Entry} (found : before.entries[index]? = some entry) :
    after.entries[index]? = some entry := by
  obtain ⟨suffix, extended⟩ := extension
  rw [extended, List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

theorem EntriesExtend.identity {before after : Catalog} (extension : EntriesExtend before after)
    {original : TypeSystem.Ty} {identity : DataTypeId}
    (found : before.identity? original = some identity) : after.identity? original = some identity := by
  obtain ⟨suffix, extended⟩ := extension
  unfold Catalog.identity? at found ⊢
  rw [extended, List.zipIdx_append, List.find?_append]
  cases selected : before.entries.zipIdx.find? (fun item =>
      decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType original)) with
  | none => simp [selected] at found
  | some entry => simpa [selected, Option.or] using found

theorem registerType_entries {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (accepted : registerType signatures fuel before original = .ok (after, type)) :
    EntriesExtend before after := (registered_prefix signatures fuel).1 _ _ _ _ accepted

theorem registerTypes_entries {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    EntriesExtend before after := (registered_prefix signatures fuel).2 _ _ _ _ accepted

theorem registerType_definitions {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {original : TypeSystem.Ty} {type : Ty}
    (accepted : registerType signatures fuel before original = .ok (after, type)) :
    before.definitions.Extends after.definitions := (registerType_entries accepted).definitions

theorem registerTypes_definitions {signatures : ProgramSignatures} {fuel : Nat}
    {before after : Catalog} {originals : List TypeSystem.Ty} {types : List Ty}
    (accepted : registerTypes signatures fuel before originals = .ok (after, types)) :
    before.definitions.Extends after.definitions := (registerTypes_entries accepted).definitions

end Solcore.SourceSemantics.CoreLowering.CompatibleCatalogRegistrationPrefix
end
