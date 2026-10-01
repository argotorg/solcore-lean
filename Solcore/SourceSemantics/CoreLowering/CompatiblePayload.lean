import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.SourceSemantics.CoreLowering.GeneralHeap
import Solcore.SourceSemantics.CoreLowering.DataPatternValues

/-! Independent data representation for the source-compatible native profile.
Raw proxy and constructor metadata is retained through authenticated registry
words even when native types erase comptime distinctions. This is not an
encode/decode graph and imports no source runtime value codec or evaluator.

Function leaves have the same projection, finite-world typing and extension
obligations as GenericHeap.PayloadModel, with an additional registry index.
The compatible catalog has a different projection, so this module does not
reinterpret it as a strict catalog or introduce another heap relation.
Ordered mappings and transported raw defaults are a separate next layer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePayload
open Core Frontend Frontend.SourceInference GeneralHeap DataPatternValues

/-- Shape authentication only; code, evidence and capture validity remain the
responsibility of the supplied function model. -/
inductive IsFunction : Dynamic.Value → Prop where
  | closure (function : Dynamic.Closure) : IsFunction (.closure function)
  | global (function : Dynamic.GlobalFunction) : IsFunction (.global function)
  | builtin (function : Dynamic.BuiltinFunction) : IsFunction (.builtin function)

structure FunctionModel (catalog : SourceCoreCompatibleCatalog.Catalog) where
  Represents : SourceCoreRawMetadata.Registry → LocationMap → StoreTyping → TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop
  projection : ∀ {registry mapping world sourceType source value type},
    Represents registry mapping world sourceType source value type → catalog.project sourceType = .ok type
  runtime_hasType : ∀ {registry mapping world sourceType source value type},
    Represents registry mapping world sourceType source value type → RuntimeValueHasType world value type catalog.definitions
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
      (functions : FunctionModel checked.catalog) (mapping : LocationMap) (world : StoreTyping) :
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
    | compatible {expected actual : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual)
        (related : ValueRep checked registry functions mapping world actual source value type) :
        ValueRep checked registry functions mapping world expected source value type
  inductive ValuesRep (checked : SourceCoreCompatibleCatalog.Checked) (registry : SourceCoreRawMetadata.Registry)
      (functions : FunctionModel checked.catalog) (mapping : LocationMap) (world : StoreTyping) :
      List TypeSystem.Ty → List Dynamic.Value → List Value → List Ty → Prop where
    | nil : ValuesRep checked registry functions mapping world [] [] [] []
    | cons {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
        {sourceTypes : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value} {types : List Ty}
        (head : ValueRep checked registry functions mapping world sourceType source value type)
        (tail : ValuesRep checked registry functions mapping world sourceTypes sources values types) :
        ValuesRep checked registry functions mapping world (sourceType :: sourceTypes) (source :: sources) (value :: values) (type :: types)
end

variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel checked.catalog}
  {mapping : LocationMap} {world : StoreTyping}

theorem ValueRep.projection {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    checked.catalog.project sourceType = .ok type := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True) with
  | unit | bool | word | integer => rfl
  | product _ _ first second => simp [SourceCoreCompatibleCatalog.Catalog.project, first, second, bind, Except.bind, pure, Except.pure]
  | function related => exact functions.projection related
  | proxy _ identity _ => simp [SourceCoreCompatibleCatalog.Catalog.project, identity]
  | constructed _ _ _ projected => exact projected
  | compatible same _ ih =>
    rw [← checked.catalog.project_runtimeType, same, checked.catalog.project_runtimeType]
    exact ih
  | nil | cons => trivial

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
    RuntimeValueHasType world value type checked.catalog.definitions := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ values types _ => ListRel (fun value type => RuntimeValueHasType world value type checked.catalog.definitions) values types) with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .pair first second
  | function related => exact functions.runtime_hasType related
  | proxy _ _ registered => exact .constructed registered .word
  | constructed _ _ _ _ registered _ ih => exact .constructed registered (.pair .word (pack_typed ih))
  | compatible _ _ ih => exact ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

/-- Static IDs and all raw metadata survive input-registry extension. The
finite location map/world extension is delegated only at function leaves. -/
theorem ValueRep.extend {futureRegistry : SourceCoreRawMetadata.Registry} {futureMapping : LocationMap} {futureWorld : StoreTyping}
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type)
    (metadata : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMapping)
    (worlds : WorldExtends world futureWorld) :
    ValueRep checked futureRegistry functions futureMapping futureWorld sourceType source value type := by
  induction related using ValueRep.rec
    (motive_2 := fun types sources values coreTypes _ => ValuesRep checked futureRegistry functions futureMapping futureWorld types sources values coreTypes) with
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
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

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
