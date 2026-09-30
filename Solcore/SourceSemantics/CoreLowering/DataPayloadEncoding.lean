import Solcore.SourceSemantics.CoreLowering.DataPayloadDefaults

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
