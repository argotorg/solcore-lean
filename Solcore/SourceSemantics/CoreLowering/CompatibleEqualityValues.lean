import Solcore.SourceSemantics.CoreLowering.CompatiblePayload
import Solcore.SourceSemantics.CoreLowering.DataEqualityValues
import Solcore.Frontend.SourceCoreCompatibleDataEquality

/-! Finite equality observations retain raw metadata authentication. Mapping
entries/defaults are opaque to equality; their full representation remains in
CompatiblePayload. Callable identities are explicit semantic receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleEquality
open Core Frontend SourceInference DataEquality CompatiblePayload
abbrev Catalog := SourceCoreCompatibleCatalog.Catalog
abbrev Registry := SourceCoreRawMetadata.Registry

inductive DataMeaning (registry : Registry) (catalog : Catalog) : ConstructorId → Dynamic.Value → Dynamic.Value → Prop where
  | proxy {inner : TypeSystem.Ty} {id : DataTypeId} {word : Word}
      (metadata : MetadataRep registry (.proxy inner) word)
      (selected : catalog.identity? (.proxy inner) = some id) :
      DataMeaning registry catalog ⟨id, 0⟩ (.proxy inner) (.word word)
  | constructed {metadata : DataConstructorInstantiation} {id : Word} {tag : ConstructorId}
      {sources : List Dynamic.Value} {packed : Dynamic.Value}
      (authenticated : MetadataRep registry (.constructor metadata) id)
      (selected : catalog.constructor? metadata = some tag)
      (arity : sources.length = metadata.payloadTypes.length)
      (packing : Dynamic.ValuesPack sources packed) :
      DataMeaning registry catalog tag (.constructed metadata sources) (.product (.word id) packed)

theorem DataMeaning.tags_equal {registry : Registry} {catalog : Catalog}
    {leftTag rightTag : ConstructorId} {source left right : Dynamic.Value}
    (a : DataMeaning registry catalog leftTag source left) (b : DataMeaning registry catalog rightTag source right) : leftTag = rightTag := by
  cases a with
  | proxy leftAuth leftSelected =>
    cases b with
    | proxy rightAuth rightSelected =>
      exact congrArg (fun id => ConstructorId.mk id 0) (Option.some.inj (leftSelected.symm.trans rightSelected))
  | constructed leftAuth leftSelected leftArity leftPacking =>
    cases b with
    | constructed rightAuth rightSelected rightArity rightPacking =>
      exact Option.some.inj (leftSelected.symm.trans rightSelected)

/-- Raw IDs distinguish aliases even when the native catalog owner is shared. -/
theorem DataMeaning.equivalent {registry : Registry} {catalog : Catalog}
    {leftTag rightTag : ConstructorId} {left right leftPayload rightPayload : Dynamic.Value}
    (a : DataMeaning registry catalog leftTag left leftPayload)
    (b : DataMeaning registry catalog rightTag right rightPayload) :
    Dynamic.ValueEquivalent leftPayload rightPayload ↔ Dynamic.ValueEquivalent left right := by
  cases a with
  | @proxy leftInner leftId leftWord leftAuth leftSelected =>
    cases b with
    | @proxy rightInner rightId rightWord rightAuth rightSelected =>
      constructor
      · rintro ⟨same, _⟩
        have words := Dynamic.Value.word.inj same
        have raw := (leftAuth.ids_equal_iff rightAuth).mp words
        have inners := SourceCoreRawMetadata.Metadata.proxy.inj raw
        subst rightInner
        exact ⟨rfl, .proxy _⟩
      · rintro ⟨same, _⟩
        have inners := Dynamic.Value.proxy.inj same
        subst rightInner
        have words := (leftAuth.ids_equal_iff rightAuth).mpr rfl
        subst rightWord
        exact ⟨rfl, .word _⟩
    | constructed => constructor <;> rintro ⟨same, _⟩ <;> cases same
  | @constructed leftMetadata leftId leftTag leftSources leftPacked leftAuth leftSelected leftArity leftPacking =>
    cases b with
    | proxy => constructor <;> rintro ⟨same, _⟩ <;> cases same
    | @constructed rightMetadata rightId rightTag rightSources rightPacked rightAuth rightSelected rightArity rightPacking =>
      rw [product_equivalent]
      constructor
      · rintro ⟨⟨ids, _⟩, fields⟩
        have raw := (leftAuth.ids_equal_iff rightAuth).mp (Dynamic.Value.word.inj ids)
        have metadata := SourceCoreRawMetadata.Metadata.constructor.inj raw
        subst rightMetadata
        have fields := (pack_equivalent leftPacking rightPacking (leftArity.trans rightArity.symm)).mp fields
        rcases fields with ⟨rfl, comparable⟩
        exact ⟨rfl, .constructed _ _ comparable⟩
      · rintro ⟨same, comparable⟩
        obtain ⟨metadata, values⟩ := Dynamic.Value.constructed.inj same
        subst rightMetadata
        subst rightSources
        have ids := (leftAuth.ids_equal_iff rightAuth).mpr rfl
        subst rightId
        cases comparable with
        | constructed _ _ fields =>
          exact ⟨⟨rfl, .word _⟩, (pack_equivalent leftPacking rightPacking rfl).mpr ⟨rfl, fields⟩⟩

inductive Carrier (profile : Bool) : Ty → Prop where
  | unit : Carrier profile .unit
  | bool : Carrier profile .bool
  | word : Carrier profile .word
  | integer : Carrier profile .integer
  | product {left right} (a : Carrier profile left) (b : Carrier profile right) : Carrier profile (.product left right)
  | namedData (id : DataTypeId) : Carrier profile (.namedData id)
  | mapping (id : DataTypeId) (value : Ty) : Carrier profile (.product .word (.product (.sum .unit value) (.namedData id)))
  | function (parameter result : Ty) (plain : profile = false) : Carrier profile (TaggedFunction.functionType parameter result)
  | contracted (parameter result : Ty) (marked : profile = true) : Carrier profile (CallableContract.functionType parameter result)

theorem Carrier.not_sum {profile : Bool} {left right : Ty} : ¬ Carrier profile (.sum left right) := by
  intro impossible; cases impossible

theorem Carrier.not_mapping_tail {profile : Bool} {value : Ty} {id : DataTypeId} :
    ¬ Carrier profile (.product (.sum .unit value) (.namedData id)) := by
  intro impossible
  cases impossible with
  | product first => exact first.not_sum

theorem Carrier.not_tagged_contract {parameter result : Ty} :
    ¬ Carrier true (TaggedFunction.functionType parameter result) := by
  intro impossible
  cases impossible with
  | product first => exact first.not_sum
  | function _ _ impossible => cases impossible

theorem Carrier.product_not_mapping {catalog : Catalog} {left right : Ty}
    (second : Carrier catalog.callableContracts right) :
    SourceCoreCompatibleDataEquality.isMappingCarrier catalog (.product left right) = false := by
  cases left <;> try rfl
  cases right <;> try rfl
  rename_i head tail
  cases head <;> try rfl
  rename_i a b
  cases a <;> try rfl
  cases tail <;> try rfl
  exact False.elim second.not_mapping_tail

theorem Carrier.product_contract_shape {profile : Bool} {left right : Ty}
    (first : Carrier profile left) :
    (profile && SourceCoreDataEquality.isCallableContractType (.product left right)) = false := by
  cases profile with
  | false => rfl
  | true =>
    cases first with
    | unit | bool | word | integer | namedData | mapping | contracted => rfl
    | function _ _ impossible => cases impossible
    | product head tail =>
      cases head with
      | unit | bool | word | integer | product | namedData | mapping | contracted => rfl
      | function _ _ impossible => cases impossible

inductive Observation (catalog : Catalog) (registry : Registry) (identities : Dynamic.Value → Word → Prop) :
    Ty → Dynamic.Value → Value → Prop where
  | unit : Observation catalog registry identities .unit .unit .unit
  | bool (value : Bool) : Observation catalog registry identities .bool (.bool value) (.bool value)
  | word (value : Word) : Observation catalog registry identities .word (.word value) (.word value)
  | integer (value : Int) : Observation catalog registry identities .integer (.integer value) (.integer value)
  | product {leftType rightType : Ty} {left right : Dynamic.Value} {a b : Value}
      (first : Observation catalog registry identities leftType left a)
      (second : Observation catalog registry identities rightType right b) :
      Observation catalog registry identities (.product leftType rightType) (.product left right) (.pair a b)
  | mapping (id : DataTypeId) (valueType : Ty)
      (recognized : SourceCoreCompatibleDataEquality.isMappingCarrier catalog
        (.product .word (.product (.sum .unit valueType) (.namedData id))) = true)
      (key value : TypeSystem.Ty) (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
      Observation catalog registry identities (.product .word (.product (.sum .unit valueType) (.namedData id)))
        (.mapping key value entries) carrier
  | identified {source : Dynamic.Value} {identity : Word} (parameter result : Ty) (code : Value)
      (meaning : identities source identity) (profile : catalog.callableContracts = false) :
      Observation catalog registry identities (TaggedFunction.functionType parameter result)
        source (.pair (.inRight .unit (.word identity)) code)
  | anonymous (source : Dynamic.Closure) (parameter result : Ty) (code : Value)
      (profile : catalog.callableContracts = false) :
      Observation catalog registry identities (TaggedFunction.functionType parameter result)
        (.closure source) (.pair (.inLeft .word .unit) code)
  | contractedIdentified {source : Dynamic.Value} {identity : Word} (parameter result : Ty)
      (code : Value) (contract : Word) (meaning : identities source identity)
      (profile : catalog.callableContracts = true) :
      Observation catalog registry identities (CallableContract.functionType parameter result)
        source (.pair (.pair (.inRight .unit (.word identity)) code) (.word contract))
  | contractedAnonymous (source : Dynamic.Closure) (parameter result : Ty)
      (code : Value) (contract : Word) (profile : catalog.callableContracts = true) :
      Observation catalog registry identities (CallableContract.functionType parameter result)
        (.closure source) (.pair (.pair (.inLeft .word .unit) code) (.word contract))
  | data {id : DataTypeId} {index : Nat} {entry : SourceCoreDataCatalog.Entry}
      {source packed : Dynamic.Value} {payloadType : Ty} {payload : Value}
      (selected : catalog.entries[id.index]? = some entry)
      (notMapping : ∀ key value, entry.sourceType ≠ .mapping key value)
      (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType)
      (meaning : DataMeaning registry catalog ⟨id, index⟩ source packed)
      (representation : Observation catalog registry identities payloadType packed payload) :
      Observation catalog registry identities (.namedData id) source (.constructed ⟨id, index⟩ payload)

theorem Observation.carrier {catalog : Catalog} {registry : Registry}
    {identities : Dynamic.Value → Word → Prop} {type : Ty} {source : Dynamic.Value} {value : Value}
    (observed : Observation catalog registry identities type source value) : Carrier catalog.callableContracts type := by
  induction observed with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .product first second
  | mapping => exact .mapping _ _
  | identified _ _ _ _ profile | anonymous _ _ _ _ profile => exact .function _ _ profile
  | contractedIdentified _ _ _ _ _ profile | contractedAnonymous _ _ _ _ _ profile => exact .contracted _ _ profile
  | data => exact .namedData _

end Solcore.SourceSemantics.CoreLowering.CompatibleEquality
