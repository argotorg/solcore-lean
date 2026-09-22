import Solcore.Frontend.SourceStageAnalysis

/-! Algebraic laws for aggregation of source staging classifications. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceStageAnalysis.Stage

open Solcore.Frontend.SourceStageAnalysis

private theorem comptime_beq_runtime :
    (Stage.comptime == Stage.runtime) = false := rfl

private theorem runtime_beq_runtime :
    (Stage.runtime == Stage.runtime) = true := rfl

private theorem deferred_beq_runtime :
    (Stage.deferred == Stage.runtime) = false := rfl

private theorem comptime_beq_comptime :
    (Stage.comptime == Stage.comptime) = true := rfl

private theorem runtime_beq_comptime :
    (Stage.runtime == Stage.comptime) = false := rfl

private theorem deferred_beq_comptime :
    (Stage.deferred == Stage.comptime) = false := rfl

private theorem any_runtime_true_iff (stages : List Stage) :
    stages.any (fun stage => stage == .runtime) = true ↔
      .runtime ∈ stages := by
  rw [List.any_eq_true]
  constructor
  · rintro ⟨stage, member, equal⟩
    cases stage with
    | comptime =>
        simp only [comptime_beq_runtime, Bool.false_eq_true] at equal
    | runtime => exact member
    | deferred =>
        simp only [deferred_beq_runtime, Bool.false_eq_true] at equal
  · intro member
    exact ⟨.runtime, member, runtime_beq_runtime⟩

private theorem all_comptime_true_iff (stages : List Stage) :
    stages.all (fun stage => stage == .comptime) = true ↔
      ∀ stage ∈ stages, stage = .comptime := by
  rw [List.all_eq_true]
  constructor
  · intro all stage member
    have equal := all stage member
    cases stage with
    | comptime => rfl
    | runtime =>
        simp only [runtime_beq_comptime, Bool.false_eq_true] at equal
    | deferred =>
        simp only [deferred_beq_comptime, Bool.false_eq_true] at equal
  · intro all stage member
    rw [all stage member]
    exact comptime_beq_comptime

/-- The empty collection has no runtime dependency. -/
@[simp] theorem join_nil : join [] = .comptime := by
  rfl

/-- Aggregating exactly one stage returns that stage. -/
@[simp] theorem join_singleton (stage : Stage) : join [stage] = stage := by
  cases stage <;> rfl

/-- A runtime occurrence dominates every other stage in the collection. -/
theorem join_eq_runtime_of_mem {stages : List Stage}
    (member : .runtime ∈ stages) :
    join stages = .runtime := by
  have present := any_runtime_true_iff stages |>.mpr member
  simp only [join, present, if_true]

/-- A collection containing only compile-time stages stays compile-time. -/
theorem join_eq_comptime_of_forall {stages : List Stage}
    (all : ∀ stage ∈ stages, stage = .comptime) :
    join stages = .comptime := by
  have onlyComptime := all_comptime_true_iff stages |>.mpr all
  have noRuntime : stages.any (fun stage => stage == .runtime) = false := by
    apply Bool.eq_false_iff.mpr
    intro present
    have member := any_runtime_true_iff stages |>.mp present
    have equal := all .runtime member
    cases equal
  simp only [join, noRuntime, onlyComptime, Bool.false_eq_true, if_false]
  simp

/-- Deferred is precisely a non-runtime collection with a deferred member. -/
theorem join_eq_deferred_iff (stages : List Stage) :
    join stages = .deferred ↔
      .runtime ∉ stages ∧ .deferred ∈ stages := by
  constructor
  · intro joined
    constructor
    · intro member
      have runtime := join_eq_runtime_of_mem member
      rw [joined] at runtime
      contradiction
    · by_cases present : .deferred ∈ stages
      · exact present
      · have all : ∀ stage ∈ stages, stage = .comptime := by
          intro stage member
          cases stage with
          | comptime => rfl
          | runtime =>
              have runtimeJoined := join_eq_runtime_of_mem member
              rw [joined] at runtimeJoined
              contradiction
          | deferred => exact False.elim (present member)
        have comptime := join_eq_comptime_of_forall all
        rw [joined] at comptime
        contradiction
  · rintro ⟨runtimeAbsent, deferredMember⟩
    have noRuntime : stages.any (fun stage => stage == .runtime) = false := by
      apply Bool.eq_false_iff.mpr
      exact fun present =>
        runtimeAbsent (any_runtime_true_iff stages |>.mp present)
    have notAll : stages.all (fun stage => stage == .comptime) ≠ true := by
      intro all
      have equal :=
        all_comptime_true_iff stages |>.mp all .deferred deferredMember
      cases equal
    have notComptime :
        stages.all (fun stage => stage == .comptime) = false :=
      Bool.eq_false_iff.mpr notAll
    simp only [join, noRuntime, notComptime, Bool.false_eq_true, if_false]

/-- Joining concatenated inputs is the same as joining their aggregate stages. -/
theorem join_append (left right : List Stage) :
    join (left ++ right) = join [join left, join right] := by
  generalize leftRuntime :
    left.any (fun stage => stage == .runtime) = leftHasRuntime
  generalize rightRuntime :
    right.any (fun stage => stage == .runtime) = rightHasRuntime
  generalize leftComptime :
    left.all (fun stage => stage == .comptime) = leftIsComptime
  generalize rightComptime :
    right.all (fun stage => stage == .comptime) = rightIsComptime
  cases leftHasRuntime <;> cases rightHasRuntime <;>
    cases leftIsComptime <;> cases rightIsComptime
  all_goals simp only [join, List.any_append, List.all_append,
    List.any_cons, List.any_nil, List.all_cons, List.all_nil,
    leftRuntime, rightRuntime, leftComptime, rightComptime,
    Bool.false_or, Bool.true_or, Bool.or_false, Bool.false_and,
    Bool.true_and, Bool.and_true]
  all_goals simp [comptime_beq_runtime, runtime_beq_runtime,
    deferred_beq_runtime, comptime_beq_comptime, deferred_beq_comptime]

end Solcore.Frontend.SourceStageAnalysis.Stage
