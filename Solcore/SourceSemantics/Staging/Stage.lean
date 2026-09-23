import Solcore.TypeSystem.Type

/-!
Declarative source-stage lattice.

These judgments are owned by the source semantics.  They do not mention the
executable stage classifier, so a later correspondence theorem can compare the
two definitions without making successful analysis a premise of the spec.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics.Staging

/-- Availability of a source value relative to staged evaluation. -/
inductive Stage where
  | comptime
  | runtime
  | deferred
  deriving Repr, DecidableEq

/-- The declarative join of a source-ordered collection of stages. -/
inductive StagesJoin : List Stage → Stage → Prop where
  | comptime
      {stages : List Stage}
      (onlyComptime : ∀ stage, stage ∈ stages → stage = .comptime) :
      StagesJoin stages .comptime
  | runtime
      {stages : List Stage}
      (containsRuntime : .runtime ∈ stages) :
      StagesJoin stages .runtime
  | deferred
      {stages : List Stage}
      (noRuntime : .runtime ∉ stages)
      (containsDeferred : .deferred ∈ stages) :
      StagesJoin stages .deferred

/-- Types whose values exist only while staged source evaluation is active. -/
inductive ComptimeOnlyType : TypeSystem.Ty → Prop where
  | integer : ComptimeOnlyType .integer
  | marked (inner : TypeSystem.Ty) : ComptimeOnlyType (.comptime inner)

namespace StagesJoin

@[simp] theorem nil : StagesJoin [] .comptime := by
  exact .comptime (by simp)

@[simp] theorem singleton (stage : Stage) : StagesJoin [stage] stage := by
  cases stage with
  | comptime => exact .comptime (by simp)
  | runtime => exact .runtime (by simp)
  | deferred => exact .deferred (by simp) (by simp)

/-- Declarative stage aggregation has exactly one result. -/
theorem unique
    {stages : List Stage} {left right : Stage}
    (leftJoin : StagesJoin stages left)
    (rightJoin : StagesJoin stages right) :
    left = right := by
  cases leftJoin with
  | comptime onlyComptime =>
      cases rightJoin with
      | comptime => rfl
      | runtime containsRuntime =>
          have impossible := onlyComptime .runtime containsRuntime
          contradiction
      | deferred _ containsDeferred =>
          have impossible := onlyComptime .deferred containsDeferred
          contradiction
  | runtime containsRuntime =>
      cases rightJoin with
      | comptime onlyComptime =>
          have impossible := onlyComptime .runtime containsRuntime
          contradiction
      | runtime => rfl
      | deferred noRuntime _ => exact False.elim (noRuntime containsRuntime)
  | deferred noRuntime containsDeferred =>
      cases rightJoin with
      | comptime onlyComptime =>
          have impossible := onlyComptime .deferred containsDeferred
          contradiction
      | runtime containsRuntime => exact False.elim (noRuntime containsRuntime)
      | deferred => rfl

end StagesJoin

end Solcore.SourceSemantics.Staging
