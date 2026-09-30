import Solcore.SourceSemantics.CoreLowering.GenericHeapPayload
import Solcore.SourceSemantics.CoreLowering.DataEqualityValues
import Solcore.SourceSemantics.CoreLowering.OrderedMapping

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
