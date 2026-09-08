import Solcore.Frontend.RuntimeParameterReferenceProperties
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties

/-! Return any source-positioned runtime argument through the complete explicit
entry contract. Header and full parameter binding remain premises; neither a
selected argument nor a hand-built prepared record bypasses entry checking. -/

set_option autoImplicit false

namespace Solcore.Frontend

variable {types : TypeNameTable} {owner : Resolved.DeclarationId}
  {declaration : Syntax.FunctionDecl} {arguments : List TypedRuntimeArgument}
  {inputs : LocalInputs} {index : Nat} {parameterSpan : Syntax.SourceSpan}
  {name : Syntax.Identifier} {annotation : Syntax.TypeExpr} {argument : TypedRuntimeArgument}
  {blockSpan returnSpan span nameSpan : Syntax.SourceSpan}

theorem runtimeFunction_parameter_prepares
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩) :
    RuntimeFunctionPrepares types owner declaration arguments
      { inputs, core := .var (arguments.length - 1 - index), returnType := argument.type } := by
  refine ⟨header, bound, ?_⟩
  rw [bodyShape]
  apply TypedLetReturnBodyElaborates.terminal
  simpa only [LocalInputs.toTypeInputs_names, LocalInputs.toTypeInputs_context] using
    (TerminalReturnTreeElaborates.single
      (bound.reference_return_elaborates_at parameterAt argumentAt blockSpan returnSpan span nameSpan))

theorem runtimeFunction_parameter_cost
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩)
    (store : Core.Store) :
    RuntimeFunctionEvaluatesWithCost types owner declaration arguments
      store argument.type argument.value store 1 := by
  apply RuntimeFunctionEvaluatesWithCost.intro
    (runtimeFunction_parameter_prepares bound parameterAt argumentAt header bodyShape)
  rw [bodyShape]
  exact .terminal (.single (.expression (bound.reference_cost_at parameterAt argumentAt span nameSpan store)))

/-- Fuel zero retains the actual Core variable and full prepared environment;
every positive fuel returns this exact argument without changing the store. -/
theorem runRuntimeFunction?_parameter
    (bound : RuntimeParametersBind types owner declaration.value.signature.parameters.elements arguments inputs)
    (parameterAt : declaration.value.signature.parameters.elements[index]? =
      some ⟨parameterSpan, .typed none name annotation⟩)
    (argumentAt : arguments[index]? = some argument)
    (header : RuntimeFunctionHeader types declaration.value.signature argument.type)
    (bodyShape : declaration.value.body =
      ⟨blockSpan, [⟨returnSpan, .returnStmt (some ⟨span, .identifier ⟨nameSpan, name.value⟩⟩)⟩]⟩)
    (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? types owner declaration arguments fuel store = some (argument.type,
      if fuel = 0 then
        .outOfFuel (Core.State.initial (.var (arguments.length - 1 - index))
          (Resolved.LocalScope.values inputs.environment) store)
      else .done argument.value store) := by
  have preparation := runtimeFunction_parameter_prepares bound parameterAt argumentAt header bodyShape
  cases fuel with
  | zero =>
      have path := (bound.reference_cost_at parameterAt argumentAt span nameSpan store).checked_toSteps
        (bound.reference_elaborates_at parameterAt argumentAt span nameSpan) inputs.sameIds
      cases path with
      | cons transition _ =>
          have advanced := Core.advance_next_iff.mpr transition
          simp only [runRuntimeFunction?, preparation.complete, bind, Option.bind_some, pure,
            Core.runStateful, advanced, ↓reduceIte]
  | succ fuel =>
      have cost := runtimeFunction_parameter_cost bound parameterAt argumentAt header bodyShape store
      simpa only [Nat.succ_ne_zero, ↓reduceIte] using
        (cost.run_done_iff (fuel := fuel + 1)).mpr (by omega)

end Solcore.Frontend
