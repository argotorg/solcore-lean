import Solcore.Frontend.ProgramSignatureFormationProperties

/-! Focused examples for flexible-variable bounds of formed signatures. -/

set_option autoImplicit false

namespace Tests.ProgramSignatureFormation

open Solcore Solcore.Frontend Solcore.TypeSystem

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    (next : Nat) :
    (Ty.function (Ty.product Ty.word Ty.bool) Ty.unit).VariablesBelow next := by
  have validated :
      SignatureTypeFormationValidated signatures owner parameters
        (.function (.product Ty.word Ty.bool) Ty.unit) :=
    .function (.product (.builtin .word) (.builtin .bool)) (.builtin .unit)
  exact validated.variablesBelow next

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {dataType : ProgramDataSignature}
    (cataloged : dataType ∈ signatures.dataTypes)
    (noParameters : dataType.parameters = [])
    (next : Nat) :
    (Ty.nominal dataType.id []).VariablesBelow next := by
  have validated :
      SignatureTypeFormationValidated signatures owner parameters
        (Ty.nominal dataType.id []) :=
    .dataNominal dataType [] cataloged (by simp [noParameters]) .nil
  exact validated.variablesBelow next

example {signatures : ProgramSignatures}
    {owner : Resolved.DeclarationId}
    {parameters : List TypeParameterId}
    {dataType : ProgramDataSignature}
    (cataloged : dataType ∈ signatures.dataTypes)
    (noParameters : dataType.parameters = [])
    (next : Nat) :
    ∀ type ∈ [Ty.nominal dataType.id [],
        .function (.product Ty.word Ty.bool) Ty.unit],
      type.VariablesBelow next := by
  have validated :
      SignatureTypesFormationValidated signatures owner parameters
        [Ty.nominal dataType.id [],
          .function (.product Ty.word Ty.bool) Ty.unit] :=
    .cons
      (.dataNominal dataType [] cataloged (by simp [noParameters]) .nil)
      (.cons
        (.function (.product (.builtin .word) (.builtin .bool))
          (.builtin .unit))
        .nil)
  exact validated.variablesBelow next

end Tests.ProgramSignatureFormation
