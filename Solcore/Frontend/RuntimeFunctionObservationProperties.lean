import Solcore.Frontend.RuntimeFunctionExecutionFactorization
import Solcore.Frontend.RuntimeFunctionEntryExecutionProperties

/-! Independently compiled declarations with the same ordered Core context and
actual Core tree have identical observations on common actual arguments. Source
names, type-name tables, owners, and source ranges need not agree. -/

set_option autoImplicit false

namespace Solcore.Frontend.RuntimeFunctionCompiles

variable {leftTypes rightTypes : TypeNameTable}
  {leftOwner rightOwner : Resolved.DeclarationId}
  {leftDeclaration rightDeclaration : Syntax.FunctionDecl}
  {leftCompiled rightCompiled : CompiledRuntimeFunction}

/-- Equal return types follow from independent compilation and Core typing
uniqueness; equality of the whole static input records is not required. -/
theorem returnType_eq_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core) :
    leftCompiled.returnType = rightCompiled.returnType := by
  have rightTyping := second.core_hasType
  rw [← contextValuesEq, ← coreEq] at rightTyping
  exact Core.typing_deterministic first.core_hasType rightTyping

/-- This equality includes argument rejection and every full stateful result.
The argument list itself is shared, not merely its list of types. -/
theorem run_eq_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core)
    (arguments : List TypedRuntimeArgument) (fuel : Nat) (store : Core.Store) :
    runRuntimeFunction? leftTypes leftOwner leftDeclaration arguments fuel store =
      runRuntimeFunction? rightTypes rightOwner rightDeclaration arguments fuel store := by
  have returnTypeEq := first.returnType_eq_of_same_core second contextValuesEq coreEq
  simp only [runRuntimeFunction?_factorization, first.complete, second.complete,
    bind, Option.bind_some, contextValuesEq, coreEq, returnTypeEq]

private theorem cost_of_same_run {arguments : List TypedRuntimeArgument}
    {initialStore finalStore : Core.Store} {type : Core.Ty} {value : Core.Value} {cost : Nat}
    (sameRun : ∀ fuel,
      runRuntimeFunction? leftTypes leftOwner leftDeclaration arguments fuel initialStore =
        runRuntimeFunction? rightTypes rightOwner rightDeclaration arguments fuel initialStore)
    (evaluation : RuntimeFunctionEvaluatesWithCost leftTypes leftOwner leftDeclaration arguments
      initialStore type value finalStore cost) :
    RuntimeFunctionEvaluatesWithCost rightTypes rightOwner rightDeclaration arguments
      initialStore type value finalStore cost := by
  have firstDone := evaluation.run_done_iff.mpr (Nat.le_refl cost)
  have secondDone := (sameRun cost).symm.trans firstDone
  obtain ⟨otherCost, otherEvaluation, otherBound⟩ := runRuntimeFunction?_done_iff_cost.mp secondDone
  have secondAtOwnCost := otherEvaluation.run_done_iff.mpr (Nat.le_refl otherCost)
  have firstAtOtherCost := (sameRun otherCost).trans secondAtOwnCost
  have originalBound : cost ≤ otherCost := evaluation.run_done_iff.mp firstAtOtherCost
  have sameCost : otherCost = cost := Nat.le_antisymm otherBound originalBound
  exact sameCost ▸ otherEvaluation

/-- Two exact completion thresholds recover the identical independent cost.
The result type, value, both stores, and supplied arguments remain fixed; no
additional typing, termination, or argument-acceptance premise is introduced. -/
theorem cost_iff_of_same_core
    (first : RuntimeFunctionCompiles leftTypes leftOwner leftDeclaration leftCompiled)
    (second : RuntimeFunctionCompiles rightTypes rightOwner rightDeclaration rightCompiled)
    (contextValuesEq : Resolved.LocalScope.values leftCompiled.inputs.context =
      Resolved.LocalScope.values rightCompiled.inputs.context)
    (coreEq : leftCompiled.core = rightCompiled.core)
    {arguments : List TypedRuntimeArgument} {initialStore finalStore : Core.Store}
    {type : Core.Ty} {value : Core.Value} {cost : Nat} :
    RuntimeFunctionEvaluatesWithCost leftTypes leftOwner leftDeclaration arguments
        initialStore type value finalStore cost ↔
      RuntimeFunctionEvaluatesWithCost rightTypes rightOwner rightDeclaration arguments
        initialStore type value finalStore cost := by
  constructor
  · exact cost_of_same_run
      (fun fuel => first.run_eq_of_same_core second contextValuesEq coreEq arguments fuel initialStore)
  · exact cost_of_same_run
      (fun fuel => (first.run_eq_of_same_core second contextValuesEq coreEq arguments fuel initialStore).symm)

end Solcore.Frontend.RuntimeFunctionCompiles
