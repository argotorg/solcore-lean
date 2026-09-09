import Solcore.Frontend.ComputationReturnTreeTypingProperties
import Solcore.Frontend.ComputationReturnTreeCostProperties
import Solcore.Core.Safety

/-! Runtime-world safety for the original shared body. The actual environment
and store share one world; the exact successful cost is not a source bound.
Pending continuations receive local paths, not an untyped completion claim. -/

set_option autoImplicit false

namespace Solcore.Frontend

theorem ComputationReturnTreeElaborates.runtime_typed_execution
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {ChildEval : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Prop}
    {ChildCost : LocalNameTable → Resolved.Environment → Core.Store → Syntax.Expr → Core.Value → Core.Store → Nat → Prop}
    {F : Core.Expr → Prop}
    (childCoreType : ∀ {table context source core type},
      ChildElab table context source core type → Core.HasType context.values core type)
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (childInserts : ∀ {core}, F core → ∀ leading suffix inserted {initialStore finalStore value},
      Core.Evaluates (leading ++ inserted :: suffix) initialStore (core.weakenAt leading.length) value finalStore ↔
        Core.Evaluates (leading ++ suffix) initialStore core value finalStore)
    (childExecution : ∀ {table context environment source core type},
      ChildElab table context source core type → environment.ids = context.ids →
      ∀ {initialStore finalStore value}, ChildEval table environment initialStore source value finalStore ↔
        Core.Evaluates environment.values initialStore core value finalStore)
    (childCostIff : ∀ {table environment initialStore source value finalStore},
      ChildEval table environment initialStore source value finalStore ↔
        ∃ cost, ChildCost table environment initialStore source value finalStore cost)
    (childPaths : ∀ {expr}, F expr → ∀ (leading suffix : Core.Environment) (inserted : Core.Value),
      ∀ {initialStore finalStore value},
        Core.Evaluates (leading ++ suffix) initialStore expr value finalStore →
        ∃ cost, ∀ continuation,
          Core.Steps cost ⟨.eval expr (leading ++ suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩ ∧
          Core.Steps cost
            ⟨.eval (expr.weakenAt leading.length) (leading ++ inserted :: suffix), continuation, initialStore⟩
            ⟨.ret value, continuation, finalStore⟩)
    (childSteps : ∀ {table context environment initialStore finalStore source value cost},
      ChildCost table environment initialStore source value finalStore cost →
      ∀ {core type}, ChildElab table context source core type → environment.ids = context.ids →
      ∀ continuation, Core.Steps cost ⟨.eval core environment.values, continuation, initialStore⟩
        ⟨.ret value, continuation, finalStore⟩)
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {environment : Resolved.Environment} {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type)
    (sameIds : environment.ids = inputs.context.ids)
    {world : Core.StoreTyping} {store : Core.Store}
    (environmentTyped : Core.RuntimeEnvironmentHasTypes world environment.values inputs.context.values)
    (storeTyped : Core.StoreHasTypes world store) :
    ∃ finalWorld finalStore value cost, Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧ Core.RuntimeValueHasType finalWorld value type ∧
      ComputationReturnTreeEvaluatesWithCost ChildCost owner inputs.names environment
        store body value finalStore cost ∧
      (∀ continuation : List Core.Frame, Core.Steps cost
        ⟨.eval core environment.values, continuation, store⟩
        ⟨.ret value, continuation, finalStore⟩) ∧
      ∀ fuel, (Core.runStateful fuel (.initial core environment.values store) =
          .done value finalStore ↔ cost ≤ fuel) ∧
        ((∃ checkpoint, Core.runStateful fuel (.initial core environment.values store) =
          .outOfFuel checkpoint) ↔ fuel < cost) := by
  have definitionsWellFormed : Core.DataEnvironment.WellFormed [] := by
    intro definition member
    cases member
  obtain ⟨finalWorld, finalStore, value, extension, finalTyped, evaluated, valueTyped⟩ :=
    Core.well_typed_evaluates (elaboration.core_hasType childCoreType)
      definitionsWellFormed environmentTyped storeTyped
  have raw := (ComputationReturnTreeElaborates.evaluates_iff (F := F)
    (ChildElab := ChildElab) (ChildEval := ChildEval)
    childMembership childWeakening childInserts childExecution elaboration sameIds).mpr evaluated
  obtain ⟨cost, counted⟩ := (computationReturnTreeEvaluates_iff_exists_cost
    (ChildEval := ChildEval) (ChildCost := ChildCost) childCostIff).mp raw
  have paths := ComputationReturnTreeEvaluatesWithCost.toStepsWithContinuation (F := F)
    childMembership childWeakening childPaths childSteps counted elaboration sameIds
  exact ⟨finalWorld, finalStore, value, cost, extension, finalTyped, valueTyped, counted,
    paths, fun _ => ⟨(paths []).runStateful_done_iff, (paths []).runStateful_outOfFuel_iff⟩⟩

end Solcore.Frontend
