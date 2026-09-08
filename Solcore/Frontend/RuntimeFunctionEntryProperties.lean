import Solcore.Frontend.RuntimeFunctionEntry

/-! Exact preparation preserves header, positional inputs, and the actual
body Core. No safety claim is made for an arbitrary prepared record. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionPrepares.complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    prepareRuntimeFunction? types owner declaration arguments = some prepared := by
  simp only [prepareRuntimeFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
    preparation.parameters.complete, preparation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem prepareRuntimeFunction?_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (accepted : prepareRuntimeFunction? types owner declaration arguments = some prepared) :
    RuntimeFunctionPrepares types owner declaration arguments prepared := by
  simp only [prepareRuntimeFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      bindRuntimeParameters?_sound parameters, elaborateTerminalReturnBody?_elaborates body⟩
  next => cases result

theorem prepareRuntimeFunction?_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeFunction? types owner declaration arguments = some prepared ↔
      RuntimeFunctionPrepares types owner declaration arguments prepared :=
  ⟨prepareRuntimeFunction?_sound, RuntimeFunctionPrepares.complete⟩

/-- The independent relation itself determines the complete prepared record. -/
theorem RuntimeFunctionPrepares.result_unique {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {left right : PreparedRuntimeFunction}
    (first : RuntimeFunctionPrepares types owner declaration arguments left)
    (second : RuntimeFunctionPrepares types owner declaration arguments right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem RuntimeFunctionPrepares.hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    RuntimeFunctionHasType types owner declaration arguments prepared.returnType :=
  ⟨prepared.inputs, preparation.header, preparation.parameters, preparation.body.hasType⟩

/-- Whole-entry typing includes declared return agreement, unlike body-only typing. -/
theorem runtimeFunctionHasType_iff_prepares {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} {returnType : Core.Ty} :
    RuntimeFunctionHasType types owner declaration arguments returnType ↔
      ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared ∧
        prepared.returnType = returnType := by
  constructor
  · rintro ⟨inputs, header, parameters, typing⟩
    obtain ⟨core, body⟩ := typing.elaborates_exact
    exact ⟨⟨inputs, core, returnType⟩, ⟨header, parameters, body⟩, rfl⟩
  · rintro ⟨prepared, preparation, rfl⟩
    exact preparation.hasType

theorem prepareRuntimeFunction?_eq_none_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument} :
    prepareRuntimeFunction? types owner declaration arguments = none ↔
      ¬ ∃ prepared, RuntimeFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro rejected ⟨prepared, preparation⟩
    have accepted := preparation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : prepareRuntimeFunction? types owner declaration arguments with
    | none => rfl
    | some prepared => exact False.elim (missing ⟨prepared, prepareRuntimeFunction?_sound accepted⟩)

theorem RuntimeFunctionPrepares.core_hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction}
    (preparation : RuntimeFunctionPrepares types owner declaration arguments prepared) :
    Core.HasType (Resolved.LocalScope.values prepared.inputs.context) prepared.core prepared.returnType :=
  elaborateTerminalReturnBody?_core_hasType preparation.body.complete

end Solcore.Frontend
