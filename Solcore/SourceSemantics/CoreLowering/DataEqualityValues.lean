import Solcore.SourceSemantics.CoreLowering.DataValueTyping
import Solcore.SourceSemantics.CoreLowering.DataEquality

/-! The finite part of a value observed by source equality. Mapping contents
and closure code are deliberately opaque: equality never evaluates them.
Nominal constructor metadata and proxy identities remain authenticated. This
relation is an equality observation, not a replacement for heap typing or a
general source-value representation relation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataEqualityValues
open Core Frontend SourceInference DataEquality DataPatternValues

theorem identity_entry {catalog : SourceCoreDataCatalog.Catalog} {type : TypeSystem.Ty}
    {id : DataTypeId} (selected : catalog.identity? type = some id) :
    ∃ entry, catalog.entries[id.index]? = some entry ∧ entry.sourceType = SourceCoreDataCatalog.erase type := by
  unfold SourceCoreDataCatalog.Catalog.identity? at selected
  cases found : catalog.entries.zipIdx.find? (fun item => decide (item.1.sourceType = SourceCoreDataCatalog.erase type)) with
  | none => simp [found] at selected
  | some item =>
    have member := List.mk_mem_zipIdx_iff_getElem?.mp (List.mem_of_find?_eq_some found)
    have same : item.1.sourceType = SourceCoreDataCatalog.erase type := by simpa using List.find?_some found
    simp only [found, Option.map_some, Option.some.injEq] at selected
    subst id
    exact ⟨item.1, member, same⟩

theorem erase_nominal {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId}
    {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments)) :
    SourceCoreDataCatalog.erase type = type := by
  cases type <;> try rfl
  all_goals simp [SourceCoreDataCatalog.nominalParts] at nominal

/-- Authentication determines the complete instantiation, including its
parameter substitution; equality observes that retained metadata. -/
theorem metadata_eq {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {left right : DataConstructorInstantiation} {tag : ConstructorId}
    (leftAccepted : catalog.resolveConstructor signatures left = .ok tag)
    (rightAccepted : catalog.resolveConstructor signatures right = .ok tag)
    (sameResult : left.resultType = right.resultType) : left = right := by
  have constructors := DataPatternAuthenticity.constructor_eq_of_same_tag
    (SourceCoreDataValues.resolveConstructor_lookup leftAccepted)
    (SourceCoreDataValues.resolveConstructor_lookup rightAccepted)
  obtain ⟨leftSignature, leftConstructor, leftSelected, leftCtor, leftParameters, leftResult, leftPayloads⟩ :=
    DataPatternAuthenticity.metadataFacts leftAccepted
  obtain ⟨rightSignature, rightConstructor, rightSelected, rightCtor, rightParameters, rightResult, rightPayloads⟩ :=
    DataPatternAuthenticity.metadataFacts rightAccepted
  rw [constructors] at leftSelected leftCtor
  have sameSignature := List.singleton_inj.mp (leftSelected.symm.trans rightSelected)
  subst rightSignature
  have sameConstructor := List.singleton_inj.mp (leftCtor.symm.trans rightCtor)
  subst rightConstructor
  have arguments : left.parameterSubstitution.map Prod.snd = right.parameterSubstitution.map Prod.snd := by
    have same := congrArg SourceCoreDataCatalog.nominalParts (leftResult.symm.trans (sameResult.trans rightResult))
    simpa [DataPatternAuthenticity.nominalParts_nominal] using same
  have substitutions : left.parameterSubstitution = right.parameterSubstitution := by
    have a := List.zip_of_prod leftParameters (rfl : left.parameterSubstitution.map Prod.snd = _)
    have b := List.zip_of_prod rightParameters (rfl : right.parameterSubstitution.map Prod.snd = _)
    rw [arguments] at a
    exact a.trans b.symm
  have payloads : left.payloadTypes = right.payloadTypes := by
    rw [leftPayloads, rightPayloads, substitutions]
  cases left; cases right
  simp_all

inductive Carrier (callableContracts : Bool) : Ty → Prop where
  | unit : Carrier callableContracts .unit
  | bool : Carrier callableContracts .bool
  | word : Carrier callableContracts .word
  | integer : Carrier callableContracts .integer
  | product {left right : Ty} (first : Carrier callableContracts left) (second : Carrier callableContracts right) :
      Carrier callableContracts (.product left right)
  | namedData (id : DataTypeId) : Carrier callableContracts (.namedData id)
  | function (parameter result : Ty) (profile : callableContracts = false) :
      Carrier callableContracts (TaggedFunction.functionType parameter result)
  | contractedFunction (parameter result : Ty) (profile : callableContracts = true) :
      Carrier callableContracts (CallableContract.functionType parameter result)

theorem Carrier.not_sum {profile : Bool} {left right : Ty} : ¬ Carrier profile (.sum left right) := by
  intro impossible
  cases impossible

theorem Carrier.not_tagged_contract {parameter result : Ty} :
    ¬ Carrier true (TaggedFunction.functionType parameter result) := by
  intro impossible
  cases impossible with
  | product first => exact Carrier.not_sum first
  | function _ _ profile => cases profile

theorem Carrier.product_contract_shape {profile : Bool} {left right : Ty}
    (first : Carrier profile left) :
    (profile && SourceCoreDataEquality.isCallableContractType (.product left right)) = false := by
  cases profile with
  | false => rfl
  | true =>
      cases first with
      | unit | bool | word | integer | namedData | contractedFunction => rfl
      | function _ _ impossible => cases impossible
      | product head tail =>
          cases head with
          | unit | bool | word | integer | product | namedData | contractedFunction => rfl
          | function _ _ impossible => cases impossible

inductive Observation (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures)
    (identities : Dynamic.Value → Word → Prop) : Ty → Dynamic.Value → Value → Prop where
  | unit : Observation catalog signatures identities .unit .unit .unit
  | bool (value : Bool) : Observation catalog signatures identities .bool (.bool value) (.bool value)
  | word (value : Word) : Observation catalog signatures identities .word (.word value) (.word value)
  | integer (value : Int) : Observation catalog signatures identities .integer (.integer value) (.integer value)
  | product {leftType rightType : Ty} {left right : Dynamic.Value} {a b : Value}
      (first : Observation catalog signatures identities leftType left a)
      (second : Observation catalog signatures identities rightType right b) :
      Observation catalog signatures identities (.product leftType rightType) (.product left right) (.pair a b)
  | proxy {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry} (inner : TypeSystem.Ty)
      (selected : catalog.entries[id.index]? = some entry) (sourceType : entry.sourceType = .proxy inner) :
      Observation catalog signatures identities (.namedData id) (.proxy inner) (.constructed ⟨id, 0⟩ .unit)
  | mapping {id : DataTypeId} {entry : SourceCoreDataCatalog.Entry} {registeredKey registeredValue : TypeSystem.Ty}
      (selected : catalog.entries[id.index]? = some entry)
      (sourceType : entry.sourceType = .mapping registeredKey registeredValue)
      (key value : TypeSystem.Ty) (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
      Observation catalog signatures identities (.namedData id) (.mapping key value entries) carrier
  | identified {source : Dynamic.Value} {identity : Word} (parameter result : Ty) (code : Value)
      (meaning : identities source identity) (profile : catalog.callableContracts = false) :
      Observation catalog signatures identities (TaggedFunction.functionType parameter result)
        source (.pair (.inRight .unit (.word identity)) code)
  | anonymous (source : Dynamic.Closure) (parameter result : Ty) (code : Value)
      (profile : catalog.callableContracts = false) :
      Observation catalog signatures identities (TaggedFunction.functionType parameter result)
        (.closure source) (.pair (.inLeft .word .unit) code)
  | contractedIdentified {source : Dynamic.Value} {identity : Word} (parameter result : Ty)
      (code : Value) (contract : Word) (meaning : identities source identity)
      (profile : catalog.callableContracts = true) :
      Observation catalog signatures identities (CallableContract.functionType parameter result)
        source (.pair (.pair (.inRight .unit (.word identity)) code) (.word contract))
  | contractedAnonymous (source : Dynamic.Closure) (parameter result : Ty)
      (code : Value) (contract : Word) (profile : catalog.callableContracts = true) :
      Observation catalog signatures identities (CallableContract.functionType parameter result)
        (.closure source) (.pair (.pair (.inLeft .word .unit) code) (.word contract))
  | constructed {id : DataTypeId} {index : Nat} {entry : SourceCoreDataCatalog.Entry}
      {metadata : DataConstructorInstantiation} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
      {sources : List Dynamic.Value} {packed : Dynamic.Value} {payloadType : Ty} {payload : Value}
      (selected : catalog.entries[id.index]? = some entry)
      (sourceType : entry.sourceType = metadata.resultType)
      (nominal : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments))
      (authenticated : catalog.resolveConstructor signatures metadata = .ok ⟨id, index⟩)
      (registered : catalog.definitions.lookupConstructorPayloadType? ⟨id, index⟩ = some payloadType)
      (arity : sources.length = metadata.payloadTypes.length)
      (packing : Dynamic.ValuesPack sources packed)
      (representation : Observation catalog signatures identities payloadType packed payload) :
      Observation catalog signatures identities (.namedData id) (.constructed metadata sources)
        (.constructed ⟨id, index⟩ payload)

theorem Observation.carrier {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {type : Ty} {source : Dynamic.Value} {value : Value}
    (observed : Observation catalog signatures identities type source value) :
    Carrier catalog.callableContracts type := by
  induction observed with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ first second => exact .product first second
  | proxy | mapping | constructed => exact .namedData _
  | identified _ _ _ _ profile | anonymous _ _ _ _ profile => exact .function _ _ profile
  | contractedIdentified _ _ _ _ _ profile | contractedAnonymous _ _ _ _ _ profile =>
      exact .contractedFunction _ _ profile

theorem Observation.proxy_of_identity {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {inner : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? (.proxy inner) = some id) :
    Observation catalog signatures identities (.namedData id) (.proxy inner) (.constructed ⟨id, 0⟩ .unit) := by
  obtain ⟨entry, found, same⟩ := identity_entry selected
  exact .proxy inner found same

/-- Source equality rejects every mapping pair without examining entries.
Only the actual catalog identity is needed for this observation. -/
theorem Observation.mapping_of_identity {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {key value : TypeSystem.Ty} {id : DataTypeId}
    (selected : catalog.identity? (.mapping key value) = some id)
    (entries : List (Dynamic.Value × Dynamic.Value)) (carrier : Value) :
    Observation catalog signatures identities (.namedData id) (.mapping key value entries) carrier := by
  obtain ⟨entry, found, same⟩ := identity_entry selected
  exact .mapping found same key value entries carrier

/-- The existing authenticated scalar/product/nominal relation supplies the
equality observation automatically, including the exact constructor arity. -/
theorem TypedValueRep.observation {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {identities : Dynamic.Value → Word → Prop} {sourceType : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value}
    (represented : DataPatternTypedValues.TypedValueRep catalog signatures sourceType source value) :
    ∃ type, catalog.project sourceType = .ok type ∧ Observation catalog signatures identities type source value := by
  induction represented using DataPatternTypedValues.TypedValueRep.rec
    (motive_2 := fun types sources values _ => ∃ coreTypes packed,
      types.mapM catalog.project = .ok coreTypes ∧ Dynamic.ValuesPack sources packed ∧
        Observation catalog signatures identities (SourceCoreDataMatches.bundleType coreTypes) packed (packValues values)) with
  | unit => exact ⟨_, rfl, .unit⟩
  | bool value => exact ⟨_, rfl, .bool value⟩
  | word value => exact ⟨_, rfl, .word value⟩
  | integer value => exact ⟨_, rfl, .integer value⟩
  | product left right first second =>
    obtain ⟨a, projectA, observedA⟩ := first
    obtain ⟨b, projectB, observedB⟩ := second
    exact ⟨_, by simp [SourceCoreDataCatalog.Catalog.project, projectA, projectB, bind, Except.bind, pure, Except.pure],
      .product observedA observedB⟩
  | @constructed type metadata tag declaration arguments sources values nominal result authenticated payloads ih =>
    obtain ⟨types, packed, projected, packing, observed⟩ := ih
    obtain ⟨registered, projectedRegistered, registeredPayload⟩ := DataValueTyping.resolveConstructor_payload authenticated
    have same := Except.ok.inj (projected.symm.trans projectedRegistered)
    subst registered
    have identity := DataPatternAuthenticity.constructor_identity (SourceCoreDataValues.resolveConstructor_lookup authenticated)
    obtain ⟨entry, selected, sourceType⟩ := identity_entry identity
    have nominalResult : SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
      rw [result]; exact nominal
    rw [erase_nominal nominalResult] at sourceType
    obtain ⟨coreType, projection, typed⟩ := DataValueTyping.TypedValueRep.project_typed
      (.constructed nominal result authenticated payloads)
    have typeEq : coreType = .namedData tag.owner := by
      cases typed []
      rfl
    subst coreType
    exact ⟨_, projection, .constructed selected sourceType nominalResult authenticated registeredPayload
      (DataPatternTypedValues.TypedValuesRep.length payloads).1.symm packing observed⟩
  | nil => exact ⟨[], .unit, rfl, .nil, .unit⟩
  | @cons sourceType source value sourceTypes sources values head tail headIH tailIH =>
    obtain ⟨type, projection, observed⟩ := headIH
    obtain ⟨types, packed, projected, packing, rest⟩ := tailIH
    have generated : (sourceType :: sourceTypes).mapM catalog.project = .ok (type :: types) := by
      simp [List.mapM_cons, projection, projected, bind, Except.bind, pure, Except.pure]
    cases tail with
    | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at projected
      subst types
      exact ⟨_, _, generated, .singleton _, observed⟩
    | @cons secondType secondSource secondValue remainingSourceTypes remainingSources remainingValues second remaining =>
      have nonempty : types ≠ [] := by
        intro empty
        rw [List.mapM_cons] at projected
        cases first : catalog.project secondType <;> simp [first, bind, Except.bind] at projected
        rename_i firstValue
        cases remainingTypes : List.mapM catalog.project remainingSourceTypes <;> simp [remainingTypes, pure, Except.pure, empty] at projected
      cases types with
      | nil => contradiction
      | cons firstType restTypes => exact ⟨_, _, generated, .cons packing, .product observed rest⟩

end Solcore.SourceSemantics.CoreLowering.DataEqualityValues
