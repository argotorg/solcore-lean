import Solcore.Frontend.SourceCoreElaboration

/-! Checked laws for the typed-source-to-Core elaboration boundary. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreElaboration

open SourceInference TypeSystem

@[simp] theorem lowerType_unit (site : ErrorSite) :
    lowerType site .unit = .ok .unit := by
  rfl

@[simp] theorem lowerType_bool (site : ErrorSite) :
    lowerType site .bool = .ok .bool := by
  rfl

@[simp] theorem lowerType_word (site : ErrorSite) :
    lowerType site .word = .ok .word := by
  rfl

theorem lowerType_product {site : ErrorSite} {left right : Ty}
    {loweredLeft loweredRight : Core.Ty}
    (leftAccepted : lowerType site left = .ok loweredLeft)
    (rightAccepted : lowerType site right = .ok loweredRight) :
    lowerType site (.product left right) =
      .ok (.product loweredLeft loweredRight) := by
  simp [lowerType, leftAccepted, rightAccepted, bind, Except.bind,
    pure, Pure.pure, Except.pure]

@[simp] theorem reconcileConsumedRequirements_nil
    (declaration : Resolved.DeclarationId) (solved : List RequirementId) :
    reconcileConsumedRequirements declaration solved [] = .ok solved := by
  rfl

@[simp] theorem reconcileConsumedRequirements_single
    (declaration : Resolved.DeclarationId) :
    reconcileConsumedRequirements declaration [⟨0⟩] [⟨0⟩] =
      .ok [] := by
  rfl

@[simp] theorem reconcileConsumedRequirements_unknown
    (declaration : Resolved.DeclarationId) (requirement : RequirementId) :
    reconcileConsumedRequirements declaration [] [requirement] =
      .error {
        site := .declaration declaration
        reason := .unknownConsumedRequirement requirement
      } := by
  rfl

@[simp] theorem reconcileConsumedRequirements_duplicate
    (declaration : Resolved.DeclarationId) :
    reconcileConsumedRequirements declaration [⟨0⟩] [⟨0⟩, ⟨0⟩] =
      .error {
        site := .declaration declaration
        reason := .duplicateConsumedRequirement ⟨0⟩
      } := by
  rfl

/-- Every successful source elaboration carries the independently checked Core
typing equation at its public boundary. -/
@[simp] theorem ElaboratedFunction.resolved_lowers
    (function : ElaboratedFunction) :
    function.resolved.lower? function.inputs.ids = some function.core :=
  function.resolvedLowered

@[simp] theorem ElaboratedFunction.core_infers
    (function : ElaboratedFunction) :
    Core.infer? function.inputs.values function.core =
      some function.returnType :=
  function.coreTypeChecked

end Solcore.Frontend.SourceCoreElaboration
