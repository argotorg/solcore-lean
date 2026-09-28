import Solcore.Frontend.ProgramSignatureFormationProperties

/-! Focused examples for flexible-variable bounds of formed signatures. -/

set_option autoImplicit false

namespace Tests.ProgramSignatureFormation

open Solcore Solcore.Frontend Solcore.TypeSystem

private def emptySignatures : ProgramSignatures := {
  functions := []
  implRules := []
  traits := []
  implementations := []
}

private def rangeDomain : TypeVarId := ⟨0⟩

private def rangeResidual : TypeVarId := ⟨1⟩

private def openRange : Substitution :=
  [(rangeDomain, .function (.variable rangeResidual) .word)]

/-- Final inference ranges may retain flexible variables when each replacement
is checked in its own complete free-variable scope. -/
example (owner : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
      openRange = .ok () := by
  rfl

/-- Recovery types are rejected even in an otherwise open inference range. -/
example (owner : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
        [(rangeDomain, .error)] =
      .error (.recoveryType owner) := by
  rfl

/-- An uncataloged nominal cannot enter a finalized substitution range. -/
example (owner nominal : Resolved.DeclarationId) :
    validateInferenceSubstitutionRangeFormation emptySignatures owner []
        [(rangeDomain, Ty.nominal nominal [])] =
      .error (.unknownNominal owner nominal) := by
  rfl

/-- Successful executable range validation exposes the pointwise open
formation witness used by source-semantics soundness. -/
example (owner : Resolved.DeclarationId) :
    InferenceSubstitutionRangeFormationValidated emptySignatures owner []
      openRange := by
  exact validateInferenceSubstitutionRangeFormation_success (by rfl)

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
