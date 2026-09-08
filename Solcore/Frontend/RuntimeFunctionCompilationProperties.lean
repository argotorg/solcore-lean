import Solcore.Frontend.RuntimeFunctionCompilation

/-! Exact value-free compilation preserves the whole entry contract and types
its open Core. Neither compilation nor these laws construct runtime arguments. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeFunctionCompiles.complete {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    compileRuntimeFunction? types owner declaration = some compiled := by
  simp only [compileRuntimeFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
    compilation.parameters.complete, compilation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem compileRuntimeFunction?_sound {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeFunction? types owner declaration = some compiled) :
    RuntimeFunctionCompiles types owner declaration compiled := by
  simp only [compileRuntimeFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header,
      declareRuntimeParameters?_sound parameters, elaborateReturnBody?_elaborates body⟩
  next => cases result

theorem compileRuntimeFunction?_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeFunction? types owner declaration = some compiled ↔
      RuntimeFunctionCompiles types owner declaration compiled :=
  ⟨compileRuntimeFunction?_sound, RuntimeFunctionCompiles.complete⟩

/-- Uniqueness follows from independent parameter and exact body evidence,
not merely from the fact that two Core expressions have the same type. -/
theorem RuntimeFunctionCompiles.result_unique {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeFunctionCompiles types owner declaration left)
    (second : RuntimeFunctionCompiles types owner declaration right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have inputsEq : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨coreEq, typeEq⟩ := first.body.result_unique second.body
  cases coreEq
  cases typeEq
  rfl

theorem compileRuntimeFunction?_eq_none_iff {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} :
    compileRuntimeFunction? types owner declaration = none ↔
      ¬ ∃ compiled, RuntimeFunctionCompiles types owner declaration compiled := by
  constructor
  · intro rejected ⟨compiled, compilation⟩
    have accepted := compilation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : compileRuntimeFunction? types owner declaration with
    | none => rfl
    | some compiled => exact False.elim (missing ⟨compiled, compileRuntimeFunction?_sound accepted⟩)

/-- The actual output is typed in its parameter context. This does not close
the Core expression or supply an environment in which to execute it. -/
theorem RuntimeFunctionCompiles.core_hasType {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeFunctionCompiles types owner declaration compiled) :
    Core.HasType (Resolved.LocalScope.values compiled.inputs.context) compiled.core compiled.returnType :=
  elaborateReturnBody?_core_hasType compilation.body.complete

end Solcore.Frontend
