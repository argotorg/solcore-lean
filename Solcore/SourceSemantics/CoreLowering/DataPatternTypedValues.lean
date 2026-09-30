import Solcore.SourceSemantics.CoreLowering.DataPatternSuccess

/-! A closed value profile for complete pattern decisions. Unlike Core typing,
this relation authenticates every nominal constructor's retained source
metadata and recursively checks its payload type list. Function, mapping,
proxy and staged values are outside this proof profile. -/

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues
open Core Frontend Frontend.SourceInference
open DataPatternValues

mutual
  inductive TypedValueRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
      TypeSystem.Ty → Dynamic.Value → Value → Prop where
    | unit : TypedValueRep catalog signatures .unit .unit .unit
    | bool (value : Bool) : TypedValueRep catalog signatures .bool (.bool value) (.bool value)
    | word (value : Word) : TypedValueRep catalog signatures .word (.word value) (.word value)
    | integer (value : Int) : TypedValueRep catalog signatures .integer (.integer value) (.integer value)
    | product {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
        (first : TypedValueRep catalog signatures leftType left a)
        (second : TypedValueRep catalog signatures rightType right b) :
        TypedValueRep catalog signatures (.product leftType rightType) (.product left right) (.pair a b)
    | constructed {type : TypeSystem.Ty} {metadata : DataConstructorInstantiation} {tag : ConstructorId}
        {declaration : Resolved.DeclarationId} {typeArguments : List TypeSystem.Ty}
        {arguments : List Dynamic.Value} {values : List Value}
        (nominal : SourceCoreDataCatalog.nominalParts type = some (declaration, typeArguments))
        (result : metadata.resultType = type)
        (authenticated : catalog.resolveConstructor signatures metadata = .ok tag)
        (payloads : TypedValuesRep catalog signatures metadata.payloadTypes arguments values) :
        TypedValueRep catalog signatures type (.constructed metadata arguments) (.constructed tag (packValues values))
  inductive TypedValuesRep (catalog : SourceCoreDataCatalog.Catalog) (signatures : ProgramSignatures) :
      List TypeSystem.Ty → List Dynamic.Value → List Value → Prop where
    | nil : TypedValuesRep catalog signatures [] [] []
    | cons {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
        {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
        (head : TypedValueRep catalog signatures type source value)
        (tail : TypedValuesRep catalog signatures types sources values) :
        TypedValuesRep catalog signatures (type :: types) (source :: sources) (value :: values)
end

theorem TypedValueRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (represented : TypedValueRep catalog signatures type source value) : ValueRep catalog source value := by
  induction represented using TypedValueRep.rec
      (motive_2 := fun _ sources values _ => ValuesRep catalog sources values) with
  | unit => exact .unit
  | bool => exact .bool _
  | word => exact .word _
  | integer => exact .integer _
  | product _ _ first second => exact .product first second
  | constructed _ _ authenticated _ ih => exact .constructed (SourceCoreDataValues.resolveConstructor_lookup authenticated) ih
  | nil => exact .nil
  | cons _ _ head tail => exact .cons head tail

theorem TypedValuesRep.erase {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values) : ValuesRep catalog sources values := by
  induction types generalizing sources values with
  | nil => cases represented; exact .nil
  | cons type types ih => cases represented with
    | cons head tail => exact .cons (TypedValueRep.erase head) (ih tail)

theorem TypedValuesRep.length {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {types : List TypeSystem.Ty} {sources : List Dynamic.Value} {values : List Value}
    (represented : TypedValuesRep catalog signatures types sources values) :
    types.length = sources.length ∧ types.length = values.length := by
  induction types generalizing sources values with
  | nil => cases represented; exact ⟨rfl, rfl⟩
  | cons type types ih => cases represented with
    | cons head tail => have result := ih tail; exact ⟨congrArg Nat.succ result.1, congrArg Nat.succ result.2⟩

theorem TypedValueRep.unpack {catalog : SourceCoreDataCatalog.Catalog} {signatures : ProgramSignatures}
    {type : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {count : Nat} {types : List TypeSystem.Ty}
    (unpacked : SourceCoreDataMatches.unpackTypes count type = some types)
    (represented : TypedValueRep catalog signatures type source value) :
    ∃ sources values, TypedValuesRep catalog signatures types sources values ∧
      Dynamic.ValuesPack sources source ∧ value = packValues values := by
  induction count using Nat.strongRecOn generalizing type source value types with
  | ind count ih =>
    cases count with
    | zero =>
      simp only [SourceCoreDataMatches.unpackTypes] at unpacked
      split at unpacked
      · rename_i same
        subst type
        cases unpacked
        cases represented with
        | unit => exact ⟨[], [], .nil, .nil, rfl⟩
        | constructed nominal => simp [SourceCoreDataCatalog.nominalParts, TypeSystem.Ty.unit] at nominal
      · contradiction
    | succ count =>
      cases count with
      | zero =>
        cases unpacked
        exact ⟨[source], [value], .cons represented .nil, .singleton _, rfl⟩
      | succ count =>
        cases type <;> simp only [SourceCoreDataMatches.unpackTypes] at unpacked
        all_goals try contradiction
        rename_i leftType rightType
        cases rest : SourceCoreDataMatches.unpackTypes (count + 1) rightType with
        | none => simp [rest] at unpacked
        | some tail =>
          simp [rest] at unpacked
          subst types
          cases represented with
          | constructed nominal => simp [SourceCoreDataCatalog.nominalParts] at nominal
          | product first second =>
            obtain ⟨sources, values, representation, packing, valueEq⟩ := ih (count + 1) (by omega) rest second
            have nonempty : sources ≠ [] := by
              have length := (TypedValuesRep.length representation).1
              have typeLength := DataPatternCertificates.unpackTypes_length rest
              intro empty
              rw [empty] at length
              simp only [List.length_nil] at length
              omega
            cases sources with
            | nil => contradiction
            | cons head sources =>
              cases values with
              | nil =>
                have lengths := TypedValuesRep.length representation
                simp only [List.length_nil, List.length_cons] at lengths
                omega
              | cons value values =>
                exact ⟨_ :: head :: sources, _ :: value :: values, .cons first representation,
                  .cons packing, by simp only [packValues]; rw [valueEq]⟩

end Solcore.SourceSemantics.CoreLowering.DataPatternTypedValues
