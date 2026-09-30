import Solcore.SourceSemantics.CoreLowering.DataPatternDecision

/-! Bridge from the authenticated public data encoder to independent source
values. The profile below only bounds supported forms; actual constructor
metadata and Core payloads come from successful encoding. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
open Core Frontend Frontend.SourceInference
open DataPatternValues DataPatternTypedValues DataPatternAuthenticity
abbrev PublicValue := SourceCoreDataValues.Value
abbrev EncodingContext := SourceCoreDataValues.Context

inductive TypeProfile : TypeSystem.Ty → Prop where
  | unit : TypeProfile .unit
  | bool : TypeProfile .bool
  | word : TypeProfile .word
  | integer : TypeProfile .integer
  | product {left right : TypeSystem.Ty} : TypeProfile left → TypeProfile right → TypeProfile (.product left right)
  | nominal {type : TypeSystem.Ty} {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
      (parts : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments)) : TypeProfile type

mutual
  inductive CarrierProfile : PublicValue → Prop where
    | unit : CarrierProfile .unit
    | bool (value : Bool) : CarrierProfile (.bool value)
    | word (value : Word) : CarrierProfile (.word value)
    | integer (value : Int) : CarrierProfile (.integer value)
    | product {left right : PublicValue} : CarrierProfile left → CarrierProfile right → CarrierProfile (.product left right)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List PublicValue}
        (types : ∀ type ∈ metadata.payloadTypes, TypeProfile type)
        (values : CarriersProfile payloads) : CarrierProfile (.constructed metadata payloads)
  inductive CarriersProfile : List PublicValue → Prop where
    | nil : CarriersProfile []
    | cons {head : PublicValue} {tail : List PublicValue} : CarrierProfile head → CarriersProfile tail → CarriersProfile (head :: tail)
end

mutual
  /-- Structural public/source identity, retaining all nominal metadata. -/
  inductive Means : PublicValue → Dynamic.Value → Prop where
    | unit : Means .unit .unit
    | bool (value : Bool) : Means (.bool value) (.bool value)
    | word (value : Word) : Means (.word value) (.word value)
    | integer (value : Int) : Means (.integer value) (.integer value)
    | product {left right : PublicValue} {a b : Dynamic.Value} : Means left a → Means right b → Means (.product left right) (.product a b)
    | constructed {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {arguments : List Dynamic.Value} :
        Meanings payloads arguments → Means (.constructed metadata payloads) (.constructed metadata arguments)
  inductive Meanings : List PublicValue → List Dynamic.Value → Prop where
    | nil : Meanings [] []
    | cons {head : PublicValue} {tail : List PublicValue} {source : Dynamic.Value} {sources : List Dynamic.Value} :
        Means head source → Meanings tail sources → Meanings (head :: tail) (source :: sources)
end

theorem Means.functional {value : PublicValue} {left right : Dynamic.Value}
    (first : Means value left) (second : Means value right) : left = right := by
  induction first using Means.rec
      (motive_2 := fun values sources _ => ∀ other, Meanings values other → sources = other) generalizing right with
  | unit => cases second; rfl
  | bool => cases second; rfl
  | word => cases second; rfl
  | integer => cases second; rfl
  | product _ _ leftIH rightIH =>
    cases second with
    | product left right => rw [leftIH left, rightIH right]
  | constructed _ ih => cases second with
    | constructed values => rw [ih _ values]
  | nil => rename_i other relation; cases relation; rfl
  | cons _ _ headIH tailIH =>
    rename_i other relation
    cases relation with
    | cons head tail => rw [headIH head, tailIH _ tail]

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (accepted : first >>= next = .ok value) : ∃ input, first = .ok input ∧ next input = .ok value := by
  cases first <;> simp_all [bind, Except.bind]
private theorem mapError_ok {α ε δ : Type} {first : Except ε α} {convert : ε → δ} {value : α}
    (accepted : first.mapError convert = .ok value) : first = .ok value := by
  cases first <;> cases accepted
  rfl

private theorem constructed_encoding {fuel : Nat} {context : EncodingContext} {expected : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {core : Value}
    (profile : TypeProfile expected)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context expected (.constructed metadata payloads) = .ok core) :
    metadata.resultType = expected ∧ ∃ tag payload,
      context.checked.catalog.resolveConstructor context.signatures metadata = .ok tag ∧
      SourceCoreDataValues.encodePayloadsRaw fuel context metadata.payloadTypes payloads 0 = .ok payload ∧
      core = .constructed tag payload := by
  cases expected <;> try (solve | cases profile)
  all_goals try (solve | cases profile with | nominal parts => cases parts)
  all_goals
    simp only [SourceCoreDataValues.encodeRaw] at accepted
    split at accepted
    · rename_i same
      obtain ⟨tag, resolved, accepted⟩ := bind_ok accepted
      obtain ⟨payload, encoded, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨same, tag, payload, mapError_ok resolved, encoded, rfl⟩
    · simp_all [pure, Except.pure, bind, Except.bind, throw]

private theorem nominal_result {context : EncodingContext} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
    (accepted : context.checked.catalog.resolveConstructor context.signatures metadata = .ok tag) :
    ∃ declaration arguments, SourceCoreDataCatalog.nominalParts metadata.resultType = some (declaration, arguments) := by
  obtain ⟨signature, _, _, _, _, result, _⟩ := metadataFacts accepted
  rw [result]
  exact ⟨_, _, nominalParts_nominal _ _⟩

private theorem constructed_nonNominal {fuel : Nat} {context : EncodingContext} {expected : TypeSystem.Ty}
    {metadata : DataConstructorInstantiation} {payloads : List PublicValue} {core : Value}
    (profile : TypeProfile expected) (notNominal : SourceCoreDataCatalog.nominalParts expected = none)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context expected (.constructed metadata payloads) = .ok core) : False := by
  obtain ⟨same, tag, _, resolved, _, _⟩ := constructed_encoding profile accepted
  obtain ⟨_, _, nominal⟩ := nominal_result resolved
  rw [same, notNominal] at nominal
  cases nominal


private def EncodingSound (fuel : Nat) (context : EncodingContext) : Prop :=
  ∀ type value core, TypeProfile type → CarrierProfile value →
    SourceCoreDataValues.encodeRaw fuel context type value = .ok core →
    ∃ source, Means value source ∧ TypedValueRep context.checked.catalog context.signatures type source core

private def PayloadSound (fuel : Nat) (context : EncodingContext) : Prop :=
  ∀ types values index core, (∀ type ∈ types, TypeProfile type) → CarriersProfile values →
    SourceCoreDataValues.encodePayloadsRaw fuel context types values index = .ok core →
    ∃ sources cores, Meanings values sources ∧ TypedValuesRep context.checked.catalog context.signatures types sources cores ∧
      core = packValues cores

private theorem constructed_sound {fuel : Nat} {context : EncodingContext} (induction : PayloadSound fuel context)
    {type : TypeSystem.Ty} {value : Value} {metadata : DataConstructorInstantiation} {payloads : List PublicValue}
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, arguments))
    (types : ∀ type ∈ metadata.payloadTypes, TypeProfile type) (values : CarriersProfile payloads)
    (accepted : SourceCoreDataValues.encodeRaw (fuel + 1) context type (.constructed metadata payloads) = .ok value) :
    ∃ source, Means (.constructed metadata payloads) source ∧ TypedValueRep context.checked.catalog context.signatures type source value := by
  obtain ⟨same, tag, payload, authenticated, encoded, valueEq⟩ := constructed_encoding (.nominal nominal) accepted
  obtain ⟨sources, cores, meanings, representations, packing⟩ := induction _ _ _ _ types values encoded
  subst value
  subst payload
  exact ⟨.constructed metadata sources, .constructed meanings, .constructed nominal same authenticated representations⟩

private theorem raw_sound (fuel : Nat) (context : EncodingContext) : EncodingSound fuel context ∧ PayloadSound fuel context := by
  induction fuel with
  | zero =>
    constructor
    · intro type value core typeProfile valueProfile accepted
      cases accepted
    · intro types values index core typesProfile valuesProfile accepted
      cases types with
      | nil => cases values with
        | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], .nil, .nil, rfl⟩
        | cons => simp [SourceCoreDataValues.encodePayloadsRaw, bind, Except.bind, throw] at accepted
      | cons type types =>
        simp only [SourceCoreDataValues.encodePayloadsRaw] at accepted
        split at accepted <;> cases accepted
  | succ fuel ih =>
    constructor
    · intro type value core typeProfile valueProfile accepted
      cases typeProfile with
      | unit =>
        cases valueProfile <;> try (solve | cases accepted)
        case unit => cases accepted; exact ⟨.unit, .unit, .unit⟩
        case constructed types values => exact False.elim (constructed_nonNominal .unit rfl accepted)
      | bool =>
        cases valueProfile <;> try (solve | cases accepted)
        case bool actual => cases accepted; exact ⟨.bool actual, .bool _, .bool _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .bool rfl accepted)
      | word =>
        cases valueProfile <;> try (solve | cases accepted)
        case word actual => cases accepted; exact ⟨.word actual, .word _, .word _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .word rfl accepted)
      | integer =>
        cases valueProfile <;> try (solve | cases accepted)
        case integer actual => cases accepted; exact ⟨.integer actual, .integer _, .integer _⟩
        case constructed types values => exact False.elim (constructed_nonNominal .integer rfl accepted)
      | product leftTypeProfile rightTypeProfile =>
        cases valueProfile <;> try (solve | cases accepted)
        case constructed types values => exact False.elim (constructed_nonNominal (.product leftTypeProfile rightTypeProfile) rfl accepted)
        case product leftProfile rightProfile =>
          simp only [SourceCoreDataValues.encodeRaw] at accepted
          obtain ⟨leftCore, leftEncoded, accepted⟩ := bind_ok accepted
          obtain ⟨rightCore, rightEncoded, accepted⟩ := bind_ok accepted
          cases accepted
          obtain ⟨leftSource, leftMeaning, leftRepresentation⟩ := ih.1 _ _ _ leftTypeProfile leftProfile (mapError_ok leftEncoded)
          obtain ⟨rightSource, rightMeaning, rightRepresentation⟩ := ih.1 _ _ _ rightTypeProfile rightProfile (mapError_ok rightEncoded)
          exact ⟨.product leftSource rightSource, .product leftMeaning rightMeaning, .product leftRepresentation rightRepresentation⟩
      | nominal nominal =>
        cases type <;> try (solve | cases nominal)
        case constructor constructor =>
          cases constructor <;> try (solve | cases nominal)
          case declaration declaration =>
            cases valueProfile <;> try (solve | cases accepted)
            case constructed types values => exact constructed_sound ih.2 nominal types values accepted
        case application function argument =>
          cases valueProfile <;> try (solve | cases accepted)
          case constructed types values => exact constructed_sound ih.2 nominal types values accepted
    · intro types values index core typesProfile valuesProfile accepted
      by_cases length : types.length = values.length
      · cases types with
        | nil =>
          cases values with
          | nil => simp [SourceCoreDataValues.encodePayloadsRaw] at accepted; subst core; exact ⟨[], [], .nil, .nil, rfl⟩
          | cons => simp at length
        | cons type types =>
          cases values with
          | nil => simp at length
          | cons value values =>
            cases valuesProfile with
            | cons headProfile tailProfile =>
              have headType := typesProfile type (by simp)
              have tailTypes : ∀ type ∈ types, TypeProfile type := fun t member => typesProfile t (by simp [member])
              cases types with
              | nil =>
                have empty : values = [] := by simpa using length.symm
                subst values
                simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
                obtain ⟨source, meaning, representation⟩ := ih.1 _ _ _ headType headProfile (mapError_ok accepted)
                exact ⟨[source], [core], .cons meaning .nil, .cons representation .nil, rfl⟩
              | cons next types =>
                simp only [SourceCoreDataValues.encodePayloadsRaw, length, ne_eq, not_true_eq_false, ↓reduceIte] at accepted
                obtain ⟨headCore, headEncoded, accepted⟩ := bind_ok accepted
                obtain ⟨tailCore, tailEncoded, accepted⟩ := bind_ok accepted
                cases accepted
                obtain ⟨source, meaning, representation⟩ := ih.1 _ _ _ headType headProfile (mapError_ok headEncoded)
                obtain ⟨sources, cores, meanings, representations, packed⟩ := ih.2 _ _ _ _ tailTypes tailProfile tailEncoded
                cases cores with
                | nil => cases representations
                | cons first cores =>
                  refine ⟨source :: sources, headCore :: first :: cores, .cons meaning meanings, .cons representation representations, ?_⟩
                  simp only [packValues]
                  rw [packed]
      · unfold SourceCoreDataValues.encodePayloadsRaw at accepted
        simp [length, bind, Except.bind, throw] at accepted

/-- Successful public encoding automatically supplies the typed independent
value relation inside the stated scalar/product/nominal feature profile. -/
theorem encodes_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.Encodes fuel context type publicValue core) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  (raw_sound fuel context).1 type publicValue core types values encoded.generated

theorem encode_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.encode fuel context type publicValue = .ok core) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  encodes_represents types values (SourceCoreDataValues.encodes_of_encode encoded)

theorem decode_represents {fuel : Nat} {context : EncodingContext} {type : TypeSystem.Ty}
    {publicValue : PublicValue} {core : Value} (types : TypeProfile type) (values : CarrierProfile publicValue)
    (decoded : SourceCoreDataValues.decode fuel context type core = .ok publicValue) :
    ∃ source, Means publicValue source ∧ TypedValueRep context.checked.catalog context.signatures type source core :=
  encodes_represents types values (SourceCoreDataValues.encodes_of_decode decoded)


/-- Compose the actual public boundary and actual pattern compiler, producing
both the independent source value and the complete finite matcher outcome. -/
theorem encode_matcher_run_preserves (compilation : SourceCoreDataMatches.Context)
    (compilationFuel encodingFuel : Nat) (source : TypedSource) (scope : SourceCoreDataMatches.Scope)
    (site : StatementId) (span : Syntax.SourceSpan) (expected : TypeSystem.Ty) (pattern : TypedMatchPattern)
    (compiled : SourceCoreDataMatches.CertifiedPattern compilation.checked.catalog.definitions)
    (accepted : SourceCoreDataMatches.compilePattern compilation compilationFuel source scope site span expected pattern = .ok compiled)
    (context : SourceSemantics.Context) (valid : DataPatternLeaves.ContextValid compilation context)
    {publicValue : PublicValue} {core : Value} (types : TypeProfile expected) (values : CarrierProfile publicValue)
    (encoded : SourceCoreDataValues.encode encodingFuel ⟨compilation.checked, compilation.signatures⟩ expected publicValue = .ok core)
    (environment : Environment) (store : Store) :
    ∃ sourceValue outcome, Means publicValue sourceValue ∧
      DataPatternLeaves.OutcomeRep compilation.checked.catalog context pattern compiled.pattern sourceValue outcome ∧
      (∃ required, ∀ fuel, required ≤ fuel →
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (core :: environment) store) = .done outcome store) ∧
      (∀ fuel actual finalStore,
        runStateful fuel (State.initial (.apply compiled.pattern.matcher (.var 0)) (core :: environment) store) = .done actual finalStore →
        actual = outcome ∧ finalStore = store) := by
  obtain ⟨sourceValue, meaning, represented⟩ := encode_represents types values encoded
  obtain ⟨outcome, outcomeMeaning, finite, reflected⟩ := DataPatternDecision.compilePattern_run_preserves compilation compilationFuel
    source scope site span expected pattern compiled accepted context valid represented environment store
  exact ⟨sourceValue, outcome, meaning, outcomeMeaning, finite, reflected⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternEncoding
