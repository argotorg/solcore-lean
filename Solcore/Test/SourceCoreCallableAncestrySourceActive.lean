import Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! These are source-metadata substitution bounds, not native code-context or
runtime ancestry ownership theorems. The actual owned witness factories supply
the closure/domain facts; no caller-provided matcher soundness is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestrySourceActive
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles.SourceComposition

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (active : Substitution)
    (reachable : Reachable (generators table) active) :
    RangesClosed active ∧ active.domain.Nodup ∧ active ⊆ alphabet (generators table) ∧
      active.length ≤ (domainAlphabet (generators table)).length ∧ active ∈ keySpace (generators table) :=
  ⟨reachable.closed (generators_valid table), reachable.domain_unique (generators_valid table),
    reachable.entries (generators_valid table), reachable.length_bound (generators_valid table),
    reachable.keySpace_member (generators_valid table)⟩

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (reached : List Substitution)
    (unique : reached.Nodup) (authentic : ∀ active ∈ reached, Reachable (generators table) active) :
    reached.length ≤ capacity (generators table) := owned_reached_count_bound table reached unique authentic

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (steps : List Substitution)
    (selected : ∀ own ∈ steps, own ∈ generators table) :
    (steps.foldl (fun active own => own.compose active) []).length ≤ (domainAlphabet (generators table)).length :=
  (Reachable.foldl .empty steps selected).length_bound (generators_valid table)

private def first : Substitution := [(⟨0⟩, .word)]
private def second : Substitution := [(⟨1⟩, .bool)]
private def conflicting : Substitution := [(⟨0⟩, .bool)]
private def choices : List Substitution := [first, second, conflicting]
private def combined : Substitution := second.compose first

example : combined = [(⟨0⟩, .word), (⟨1⟩, .bool)] := rfl
example : combined ≠ [] ∧ combined ∉ choices := by decide
example : combined ≠ first.compose second := by decide
example : conflicting.compose combined = combined := rfl
private theorem combined_reachable : Reachable choices combined := by
  have initial : Reachable choices first :=
    .step (own := first) .empty (by simp [choices])
  exact .step initial (show second ∈ choices by simp [choices])

example : Reachable choices combined := combined_reachable

example (count : Nat) : Reachable choices
    ((List.replicate count second).foldl (fun active own => own.compose active) combined) := by
  apply Reachable.foldl combined_reachable
  intro own member
  have same := List.eq_of_mem_replicate member
  simpa only [same] using (show second ∈ choices by simp [choices])

example : (domainAlphabet choices).length = 2 := by decide
example : capacity choices = 13 := by decide
example : (keySpace choices).length = 13 := keySpace_length choices

end Tests.SourceCoreCallableAncestrySourceActive
