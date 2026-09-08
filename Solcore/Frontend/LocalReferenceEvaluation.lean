import Solcore.Frontend.LocalReferenceProperties
import Solcore.Resolved.EvaluationProperties
import Solcore.Core.Machine

set_option autoImplicit false

namespace Solcore.Frontend

/-- Independent evaluation of a supported canonical reference. Looking up a
local value does not call a closure, dereference a cell, or modify a store. -/
inductive LocalReferenceEvaluates (table : LocalNameTable) (environment : Resolved.Environment) :
    Syntax.Expr → Core.Value → Prop where
  | reference {source : Syntax.Expr} {id : Resolved.LocalId} {value : Core.Value}
      (resolved : ResolvesLocalReference table source id)
      (found : Resolved.LocalScope.Lookup environment id value) :
      LocalReferenceEvaluates table environment source value

theorem LocalReferenceEvaluates.deterministic
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {left right : Core.Value}
    (first : LocalReferenceEvaluates table environment source left)
    (second : LocalReferenceEvaluates table environment source right) : left = right := by
  cases first with
  | reference leftResolved leftFound =>
      cases second with
      | reference rightResolved rightFound =>
          cases leftResolved.id_unique rightResolved
          exact leftFound.value_unique rightFound

/-- Named reference evaluation selects an exact positional Core variable. -/
theorem LocalReferenceEvaluates.toCore
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {value : Core.Value} (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) (.var id) (.var index) ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store (.var index) value store := by
  cases evaluation with
  | reference resolved found =>
      obtain ⟨index, indexed, atValue⟩ := found.indexed
      exact ⟨_, index, resolved, .var indexed, .var atValue⟩

/-- References cost exactly one Core transition, independently of grouping
depth, source ranges, and the supplied store. At zero fuel the initial state is retained. -/
theorem LocalReferenceEvaluates.exact_run
    {table : LocalNameTable} {environment : Resolved.Environment} {source : Syntax.Expr}
    {value : Core.Value} (evaluation : LocalReferenceEvaluates table environment source value)
    (store : Core.Store) :
    ∃ id index, ResolvesLocalReference table source id ∧
      Resolved.LocalScope.IndexOf (Resolved.LocalScope.ids environment) id index ∧
      Core.runStateful 0
        (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) =
        .outOfFuel (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) ∧
      ∀ fuel, Core.runStateful (fuel + 1)
        (Core.State.initial (.var index) (Resolved.LocalScope.values environment) store) =
        .done value store := by
  cases evaluation with
  | reference resolved found =>
      obtain ⟨index, indexed, atValue⟩ := found.indexed
      refine ⟨_, index, resolved, indexed, ?_, ?_⟩
      · simp [Core.runStateful, Core.State.initial, Core.advance, atValue]
      · intro fuel
        simp [Core.runStateful, Core.State.initial, Core.advance, atValue]

end Solcore.Frontend
