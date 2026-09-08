import Solcore.Frontend.RuntimeParameters

/-! Exact success, failure, and independent result uniqueness for the explicit
runtime parameter profile. No executable binding premise enters the judgment. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeParametersBind.complete {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} {output : LocalInputs}
    (bound : RuntimeParametersBind types owner params args output) :
    bindRuntimeParameters? types owner params args = some output :=
  bindRuntimeParameters?_iff.mpr bound

theorem bindRuntimeParameters?_sound {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} {output : LocalInputs}
    (result : bindRuntimeParameters? types owner params args = some output) :
    RuntimeParametersBind types owner params args output :=
  bindRuntimeParameters?_iff.mp result

theorem bindRuntimeParameters?_eq_none_iff {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {params : List Syntax.FunctionParameter}
    {args : List TypedRuntimeArgument} :
    bindRuntimeParameters? types owner params args = none ↔
      ¬ ∃ output, RuntimeParametersBind types owner params args output := by
  constructor
  · intro result ⟨output, bound⟩
    have accepted := bound.complete
    rw [result] at accepted
    cases accepted
  · intro absent
    cases result : bindRuntimeParameters? types owner params args with
    | none => rfl
    | some output => exact False.elim (absent ⟨output, bindRuntimeParameters?_sound result⟩)

/-- Uniqueness holds even when the initial inputs contain repeated names;
the new parameters themselves must still avoid every earlier spelling. -/
theorem RuntimeParametersBindFrom.result_unique {types : TypeNameTable}
    {owner : Resolved.DeclarationId} {initial left right : LocalInputs}
    {params : List Syntax.FunctionParameter} {args : List TypedRuntimeArgument}
    (leftBound : RuntimeParametersBindFrom types owner initial params args left)
    (rightBound : RuntimeParametersBindFrom types owner initial params args right) :
    left = right := by
  induction leftBound with
  | nil => cases rightBound; rfl
  | cons _ _ _ ih =>
      cases rightBound with
      | cons _ _ tail => exact ih tail

end Solcore.Frontend
