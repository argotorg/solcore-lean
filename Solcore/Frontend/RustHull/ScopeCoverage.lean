import Solcore.Frontend.RustHull.SemanticsCorrespondenceSupport
import Solcore.Frontend.RustHull.Effects

/-! The compiler cannot introduce an ordinary readable source name that is
absent from the source environment. Administrative names use the exact prefix
rejected by the Hull variable guard. This premise complements EnvironmentRel,
which relates values after the two lookups have succeeded. -/
set_option autoImplicit false

namespace Solcore.Frontend.RustHull.Correspondence

def ScopeCoverage (source : Semantics.Environment) (scope : Scope) : Prop :=
  ∀ name binding index,
    name.startsWith Effects.reservedPrefix = false →
    scope.lookup name = .ok (binding, index) →
    ∃ location, Semantics.lookupLocation source name = some location

theorem ScopeCoverage.empty (source : Semantics.Environment) : ScopeCoverage source [] := by
  intro name binding index _ looked
  simp [Scope.lookup, fail] at looked

theorem ScopeCoverage.temporary {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (type : Core.Ty) :
    ScopeCoverage source (scope.temporary type) := by
  intro name binding index allowed looked
  rw [Scope.temporary, scope_lookup_cons] at looked
  simp only [Option.none_beq_some, Bool.false_eq_true, ↓reduceIte] at looked
  cases old : scope.lookup name with
  | error error => simp only [old] at looked; contradiction
  | ok pair =>
      rcases pair with ⟨oldBinding, oldIndex⟩
      exact covered name oldBinding oldIndex allowed old

theorem ScopeCoverage.addLocal {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (name : String) (type : Core.Ty) (location : Nat) :
    ScopeCoverage ((name, location) :: source) (scope.addLocal name type) := by
  intro query binding index allowed looked
  by_cases same : name = query
  · subst query
    exact ⟨location, by simp [Semantics.lookupLocation]⟩
  · rw [Scope.addLocal, scope_lookup_cons] at looked
    simp only [Option.some_beq_some, beq_iff_eq, same, ↓reduceIte] at looked
    cases old : scope.lookup query with
    | error error => simp only [old] at looked; contradiction
    | ok pair =>
        rcases pair with ⟨oldBinding, oldIndex⟩
        obtain ⟨previous, found⟩ := covered query oldBinding oldIndex allowed old
        exact ⟨previous, by simpa [Semantics.lookupLocation, same] using found⟩

/-- Adding an administrative binding cannot create a new source variable:
the actual variable guard rejects its name before looking in the scope. -/
theorem ScopeCoverage.reserved {source : Semantics.Environment} {scope : Scope}
    (covered : ScopeCoverage source scope) (head : Binding)
    (reserved : ∀ name, head.name = some name → name.startsWith Effects.reservedPrefix = true) :
    ScopeCoverage source (head :: scope) := by
  intro name binding index allowed looked
  rw [scope_lookup_cons] at looked
  split at looked
  · rename_i named
    have forbidden := reserved name (beq_iff_eq.mp named)
    simp only [allowed] at forbidden
    contradiction
  · cases old : scope.lookup name with
    | error error => simp only [old] at looked; contradiction
    | ok pair =>
        rcases pair with ⟨oldBinding, oldIndex⟩
        exact covered name oldBinding oldIndex allowed old

theorem ScopeCoverage.of_reserved (source : Semantics.Environment) (scope : Scope)
    (reserved : ∀ binding ∈ scope, ∀ name, binding.name = some name →
      name.startsWith Effects.reservedPrefix = true) : ScopeCoverage source scope := by
  induction scope with
  | nil => exact .empty source
  | cons head rest ih =>
      apply ScopeCoverage.reserved
        (ih (fun binding member => reserved binding (List.mem_cons_of_mem head member))) head
      exact reserved head (List.mem_cons_self ..)

end Solcore.Frontend.RustHull.Correspondence
