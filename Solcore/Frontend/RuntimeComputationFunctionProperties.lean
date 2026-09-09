import Solcore.Frontend.RuntimeComputationFunctionCompilation
import Solcore.Frontend.RuntimeComputationFunctionEntry
import Solcore.Frontend.LocalComputationReturnTreeProperties

/-! Exact whole-record success is characterized by this profile's independent
header, parameter and mixed-body evidence. Actual preparation retains its own
input record; neither erasure nor old entry provenance supplies runtime values. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem compileRuntimeComputationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileRuntimeComputationFunction? types owner declaration = some compiled ↔
      RuntimeComputationFunctionCompiles types owner declaration compiled := by
  constructor
  · intro accepted
    simp only [compileRuntimeComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
        elaborateLocalComputationReturnTree?_iff.mp body⟩
    next => cases result
  · intro compilation
    simp only [compileRuntimeComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
      compilation.parameters.complete, elaborateLocalComputationReturnTree?_iff.mpr compilation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

theorem prepareRuntimeComputationFunction?_iff
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareRuntimeComputationFunction? types owner declaration arguments = some prepared ↔
      RuntimeComputationFunctionPrepares types owner declaration arguments prepared := by
  constructor
  · intro accepted
    simp only [prepareRuntimeComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, bindRuntimeParameters?_sound parameters,
        elaborateLocalComputationReturnTree?_iff.mp body⟩
    next => cases result
  · intro preparation
    simp only [prepareRuntimeComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
      preparation.parameters.complete, elaborateLocalComputationReturnTree?_iff.mpr preparation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

end Solcore.Frontend
