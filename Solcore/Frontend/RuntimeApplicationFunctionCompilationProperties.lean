import Solcore.Frontend.RuntimeApplicationFunctionCompilation
import Solcore.Frontend.LocalApplicationReturnBodyProperties

/-! Exact value-free compilation belongs to this application-return profile.
The shared data record supplies no old compilation or runtime safety evidence. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem RuntimeApplicationFunctionCompiles.complete
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    compileRuntimeApplicationFunction? types owner declaration = some compiled := by
  simp only [compileRuntimeApplicationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
    compilation.parameters.complete, compilation.body.complete, bind, Option.bind_some,
    ↓reduceIte, pure]

theorem compileRuntimeApplicationFunction?_sound
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (accepted : compileRuntimeApplicationFunction? types owner declaration = some compiled) :
    RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  simp only [compileRuntimeApplicationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
  obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
  split at result
  next same =>
    change inferredType = returnType at same
    subst inferredType
    cases result
    exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
      elaborateLocalApplicationReturnBody?_sound body⟩
  next => cases result

theorem compileRuntimeApplicationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeApplicationFunction? types owner declaration = some compiled ↔
      RuntimeApplicationFunctionCompiles types owner declaration compiled :=
  ⟨compileRuntimeApplicationFunction?_sound, RuntimeApplicationFunctionCompiles.complete⟩

/-- Independent parameter identity and exact original body evidence determine
the entire record, not just a Core expression with the same result type. -/
theorem RuntimeApplicationFunctionCompiles.result_unique
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {left right : CompiledRuntimeFunction}
    (first : RuntimeApplicationFunctionCompiles types owner declaration left)
    (second : RuntimeApplicationFunctionCompiles types owner declaration right) : left = right := by
  rcases left with ⟨leftInputs, leftCore, leftType⟩
  rcases right with ⟨rightInputs, rightCore, rightType⟩
  have sameInputs : leftInputs = rightInputs := first.parameters.result_unique second.parameters
  subst rightInputs
  obtain ⟨sameCore, sameType⟩ := first.body.result_unique second.body
  cases sameCore
  cases sameType
  rfl

theorem compileRuntimeApplicationFunction?_eq_none_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {declaration : Syntax.FunctionDecl} :
    compileRuntimeApplicationFunction? types owner declaration = none ↔
      ¬ ∃ compiled, RuntimeApplicationFunctionCompiles types owner declaration compiled := by
  constructor
  · intro rejected ⟨compiled, compilation⟩
    have accepted := compilation.complete
    rw [rejected] at accepted
    cases accepted
  · intro missing
    cases accepted : compileRuntimeApplicationFunction? types owner declaration with
    | none => rfl
    | some compiled => exact False.elim (missing ⟨compiled, compileRuntimeApplicationFunction?_sound accepted⟩)

/-- The exact output remains open in the original parameter context. No actual
arguments, world, store or execution guarantee follow from this static law. -/
theorem RuntimeApplicationFunctionCompiles.core_hasType
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction}
    (compilation : RuntimeApplicationFunctionCompiles types owner declaration compiled) :
    Core.HasType (Resolved.LocalScope.values compiled.inputs.context) compiled.core compiled.returnType :=
  compilation.body.core_hasType

end Solcore.Frontend
