import Solcore.SourceSemantics.CoreLowering.CompatiblePatternCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleConstructorMetadata
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadMembers

/-! Source-shaped product inversion for compatible match inputs. Function
carriers are native products too, so inversion uses the retained source runtime
view and authentic constructor metadata. No function observation or evaluation
law is required to preserve arbitrary bound payloads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
open Core Frontend SourceInference GeneralHeap DataPatternValues CompatiblePayload
open CompatibleConstructorMetadata
variable {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
  {mapping : LocationMap} {world : StoreTyping}

private theorem unit_view {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    SourceCoreRawMetadata.runtimeType expected = .unit → source = .unit ∧ value = .unit ∧ type = .unit := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit => intro _; exact ⟨rfl, rfl, rfl⟩
  | bool | word | integer | product | function | proxy | mappingValue =>
    intro impossible
    simp [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.unit, TypeSystem.Ty.bool,
      TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | constructed metadata owner selected projected registered payloads _ =>
    intro impossible
    obtain ⟨signature, constructor, arguments, _, _, _, _, _, result⟩ := facts (constructor_authenticated metadata owner)
    have parts := congrArg SourceCoreDataCatalog.nominalParts impossible
    rw [result, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at parts
    simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit] at parts
  | compatible same related ih => intro viewed; exact ih (same.symm.trans viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- Normalized Unit inputs really contain Unit, including staged aliases. -/
theorem unit_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type)
    (viewed : SourceCoreRawMetadata.runtimeType expected = .unit) :
    source = .unit ∧ value = .unit ∧ type = .unit := unit_view represented viewed

private def ProductFields (expected : TypeSystem.Ty) (source : Dynamic.Value) (value : Value) (type : Ty) : Prop :=
  ∀ left right, SourceCoreRawMetadata.runtimeType expected =
      .product (SourceCoreRawMetadata.runtimeType left) (SourceCoreRawMetadata.runtimeType right) →
    ∃ first second a b aType bType, source = .product first second ∧ value = .pair a b ∧
      type = .product aType bType ∧
      ValueRep checked registry functions mapping world left first a aType ∧
      ValueRep checked registry functions mapping world right second b bType

private theorem product_view {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ProductFields (checked := checked) (registry := registry) (functions := functions)
      (mapping := mapping) (world := world) expected source value type := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | function | proxy | mappingValue =>
    intro left right impossible
    simp [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.unit, TypeSystem.Ty.bool,
      TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | product first second firstIH secondIH =>
    intro left right viewed
    have same := TypeSystem.Ty.product.inj viewed
    exact ⟨_, _, _, _, _, _, rfl, rfl, rfl, .compatible same.1.symm first, .compatible same.2.symm second⟩
  | constructed metadata owner selected projected registered payloads _ =>
    intro left right impossible
    obtain ⟨signature, constructor, arguments, _, _, _, _, _, result⟩ := facts (constructor_authenticated metadata owner)
    have parts := congrArg SourceCoreDataCatalog.nominalParts impossible
    rw [result, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at parts
    simp [SourceCoreDataCatalog.nominalParts] at parts
  | compatible same related ih => intro left right viewed; exact ih left right (same.symm.trans viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- Source products preserve component representations, raw aliases and native
types, even when the components are closures, mappings or proxies. -/
theorem product_fields {left right : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world (.product left right) source value type) :
    ∃ first second a b aType bType, source = .product first second ∧ value = .pair a b ∧
      type = .product aType bType ∧
      ValueRep checked registry functions mapping world left first a aType ∧
      ValueRep checked registry functions mapping world right second b bType :=
  product_view represented left right rfl

private theorem nominal_source {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ∀ declaration arguments,
      SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) = some (declaration, arguments) →
      ∃ metadata sources, source = .constructed metadata sources := by
  induction represented using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue =>
    intro declaration arguments impossible
    simp [SourceCoreRawMetadata.runtimeType, SourceCoreDataCatalog.nominalParts,
      TypeSystem.Ty.unit, TypeSystem.Ty.bool, TypeSystem.Ty.word, TypeSystem.Ty.integer] at impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same related ih => intro declaration arguments viewed; exact ih declaration arguments (same ▸ viewed)
  | nil | cons | empty | entry | absent | present => trivial

/-- A nominal source view recovers an authenticated constructor and its exact
raw payload vector; native tag shape alone is not used as source authenticity. -/
theorem nominal_fields {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (represented : ValueRep checked registry functions mapping world expected source value type)
    {declaration : Resolved.DeclarationId} {arguments : List TypeSystem.Ty}
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType expected) = some (declaration, arguments)) :
    ∃ metadata sources tag id values types, source = .constructed metadata sources ∧
      value = .constructed tag (.pair (.word id) (packValues values)) ∧ type = .namedData tag.owner ∧
      ConstructorFields checked registry functions mapping world expected metadata tag id sources values types := by
  obtain ⟨metadata, sources, sourceEq⟩ := nominal_source represented _ _ nominal
  obtain ⟨tag, id, values, types, nativeEq, typeEq, fields⟩ := constructor_fields represented sourceEq
  exact ⟨metadata, sources, tag, id, values, types, sourceEq, nativeEq, typeEq, fields⟩

/-- Unpack exactly the arity accepted by the actual compiler. The singleton
case retains an entire function carrier, rather than projecting its fields. -/
theorem unpack {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    {count : Nat} {types : List TypeSystem.Ty}
    (unpacked : SourceCoreCompatibleDataMatches.unpackTypes count expected = some types)
    (represented : ValueRep checked registry functions mapping world expected source value type) :
    ∃ sources values coreTypes, ValuesRep checked registry functions mapping world types sources values coreTypes ∧
      Dynamic.ValuesPack sources source ∧ value = packValues values ∧
      type = SourceCoreCompatibleCatalog.packTypes coreTypes := by
  induction count using Nat.strongRecOn generalizing expected source value type types with
  | ind count ih =>
    cases count with
    | zero =>
      simp only [SourceCoreCompatibleDataMatches.unpackTypes] at unpacked
      split at unpacked
      · rename_i same
        subst expected
        cases unpacked
        obtain ⟨rfl, rfl, rfl⟩ := unit_fields represented rfl
        exact ⟨[], [], [], .nil, .nil, rfl, rfl⟩
      · contradiction
    | succ count =>
      cases count with
      | zero => cases unpacked; exact ⟨[source], [value], [type], .cons represented .nil, .singleton _, rfl, rfl⟩
      | succ count =>
        cases expected <;> simp only [SourceCoreCompatibleDataMatches.unpackTypes] at unpacked
        all_goals try contradiction
        rename_i leftType rightType
        cases rest : SourceCoreCompatibleDataMatches.unpackTypes (count + 1) rightType with
        | none => simp [rest] at unpacked
        | some tail =>
          simp [rest] at unpacked
          subst types
          obtain ⟨first, second, a, b, aType, bType, rfl, rfl, rfl, firstRep, secondRep⟩ := product_fields represented
          obtain ⟨sources, values, coreTypes, tailRep, packing, valueEq, typeEq⟩ := ih (count + 1) (by omega) rest secondRep
          have lengths := CompatiblePayload.ValuesRep.length tailRep
          have typeLength := CompatiblePatternCertificates.unpackTypes_length rest
          cases sources with
          | nil => simp only [List.length_nil] at lengths; omega
          | cons head sources =>
            cases values with
            | nil => simp only [List.length_nil, List.length_cons] at lengths; omega
            | cons value values =>
              cases coreTypes with
              | nil => simp only [List.length_nil, List.length_cons] at lengths; omega
              | cons coreType coreTypes =>
                exact ⟨first :: head :: sources, a :: value :: values, aType :: coreType :: coreTypes,
                  .cons firstRep tailRep, .cons packing,
                  by simp only [packValues]; rw [valueEq],
                  by simp only [SourceCoreCompatibleCatalog.packTypes]; rw [typeEq]⟩
end Solcore.SourceSemantics.CoreLowering.CompatiblePatternValues
