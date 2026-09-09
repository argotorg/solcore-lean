import Solcore.Frontend.ComputationFunctionCompilation
import Solcore.Frontend.ComputationFunctionEntry
import Solcore.Frontend.ComputationReturnTreeProperties

set_option autoImplicit false

namespace Solcore.Frontend

/-! Exact whole-record success is characterized by this profile's independent
header, parameter and mixed-body evidence. Actual preparation retains its own
input record; neither erasure nor old entry provenance supplies runtime values. -/

theorem compileComputationFunction?_iff
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {compiled : CompiledRuntimeFunction} :
    compileComputationFunction? checkChild types owner declaration = some compiled ↔
      ComputationFunctionCompiles ChildElab types owner declaration compiled := by
  constructor
  · intro accepted
    simp only [compileComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, declareRuntimeParameters?_sound parameters,
        (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mp body⟩
    next => cases result
  · intro compilation
    simp only [compileComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr compilation.header,
      compilation.parameters.complete, (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mpr compilation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

theorem prepareComputationFunction?_iff
    {checkChild : LocalNameTable → Resolved.Context → Syntax.Expr → Option (Core.Expr × Core.Ty)}
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    (childCorrect : ∀ {table context source core type},
      checkChild table context source = some (core, type) ↔ ChildElab table context source core type)
    {types : TypeNameTable} {owner : Resolved.DeclarationId}
    {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
    {prepared : PreparedRuntimeFunction} :
    prepareComputationFunction? checkChild types owner declaration arguments = some prepared ↔
      ComputationFunctionPrepares ChildElab types owner declaration arguments prepared := by
  constructor
  · intro accepted
    simp only [prepareComputationFunction?, bind, Option.bind_eq_some_iff, pure] at accepted
    obtain ⟨returnType, header, inputs, parameters, ⟨core, inferredType⟩, body, result⟩ := accepted
    split at result
    next same =>
      change inferredType = returnType at same
      subst inferredType
      cases result
      exact ⟨interpretRuntimeFunctionHeader?_iff.mp header, bindRuntimeParameters?_sound parameters,
        (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mp body⟩
    next => cases result
  · intro preparation
    simp only [prepareComputationFunction?, interpretRuntimeFunctionHeader?_iff.mpr preparation.header,
      preparation.parameters.complete, (elaborateComputationReturnTree?_iff (checkChild := checkChild) (ChildElab := ChildElab) childCorrect).mpr preparation.body,
      bind, Option.bind_some, ↓reduceIte, pure]

end Solcore.Frontend
