import Solcore.Core.Correspondence

/-! Exact application protocol for the actual closure and captured environment.
The known body cost is lifted unchanged; outer frames are retained, not run. -/

set_option autoImplicit false

namespace Solcore.Frontend.CostStepComposition

open Core

private theorem transition_append {start finish : State}
    (step : Transition start finish) (continuation : List Frame) :
    Transition { start with continuation := start.continuation ++ continuation }
      { finish with continuation := finish.continuation ++ continuation } := by
  cases step <;> simp only [List.cons_append] <;> constructor <;> assumption

private theorem steps_append {cost : Nat} {start finish : State}
    (path : Steps cost start finish) (continuation : List Frame) :
    Steps cost { start with continuation := start.continuation ++ continuation }
      { finish with continuation := finish.continuation ++ continuation } := by
  induction path with
  | refl => exact .refl
  | cons step _ ih => exact .cons (transition_append step continuation) ih

/-- Evaluate the original function and argument in the caller environment,
then the actual body under the argument followed by its captured values.
The three added transitions neither inspect nor execute the outer continuation.
No typing, purity, store-invariance or termination premise is inferred. -/
theorem apply {environment capturedEnvironment : Environment}
    {initialStore argumentStore bodyStore finalStore : Store}
    {function argument body : Expr} {parameterType resultType : Ty}
    {argumentValue result : Value} {continuation : List Frame}
    {functionCost argumentCost bodyCost : Nat}
    (functionPath : Steps functionCost
      ⟨.eval function environment, .applyArgument argument environment :: continuation, initialStore⟩
      ⟨.ret (.closure parameterType resultType body capturedEnvironment),
        .applyArgument argument environment :: continuation, argumentStore⟩)
    (argumentPath : Steps argumentCost
      ⟨.eval argument environment,
        .applyClosure parameterType resultType body capturedEnvironment :: continuation, argumentStore⟩
      ⟨.ret argumentValue,
        .applyClosure parameterType resultType body capturedEnvironment :: continuation, bodyStore⟩)
    (bodyPath : Steps bodyCost
      (State.initial body (argumentValue :: capturedEnvironment) bodyStore)
      (State.final result finalStore)) :
    Steps (functionCost + argumentCost + bodyCost + 3)
      ⟨.eval (.apply function argument) environment, continuation, initialStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
  have lifted : Steps bodyCost
      ⟨.eval body (argumentValue :: capturedEnvironment), continuation, bodyStore⟩
      ⟨.ret result, continuation, finalStore⟩ := by
    simpa only [State.initial, State.final, List.nil_append] using steps_append bodyPath continuation
  have path := Steps.cons .enterApply
    (functionPath.trans (.cons .beginArgument (argumentPath.trans (.cons .invokeClosure lifted))))
  simpa only [Nat.add_assoc] using path

end Solcore.Frontend.CostStepComposition
