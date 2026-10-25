import Solcore.Frontend.RustHull.ScopeCoverage
import Solcore.Frontend.RustHull.FunctionInstallationCorrespondence

/-! The actual source argument binder establishes coverage of the compiler's
parameter scope. Equal arities also exclude the malformed argument outcome. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

theorem bindArguments_exists {σ : Type} {arguments : List Arg} {sources : List Semantics.Value}
    (arity : arguments.length = sources.length) (environment : Semantics.Environment)
    (state : Semantics.State σ) :
    ∃ finalEnvironment finalState,
      Semantics.bindArguments arguments sources environment state = some (finalEnvironment, finalState) := by
  induction arguments generalizing sources environment state with
  | nil =>
      cases sources with
      | nil => exact ⟨environment, state, rfl⟩
      | cons => simp at arity
  | cons argument arguments ih =>
      cases sources with
      | nil => simp at arity
      | cons source sources =>
          exact ih (Nat.succ.inj arity) ((argument.name, state.heap.length) :: environment)
            (Semantics.allocate state source).2

/-- Follow the same allocations and name insertions returned by bindArguments;
no second initializer is used to establish body coverage. -/
theorem ScopeCoverage.bindArguments {σ : Type} {arguments : List Arg} {types : List Core.Ty}
    {sources : List Semantics.Value} {environment finalEnvironment : Semantics.Environment}
    {state finalState : Semantics.State σ} {scope : Scope}
    (covered : ScopeCoverage environment scope) (arity : arguments.length = types.length)
    (bound : Semantics.bindArguments arguments sources environment state = some (finalEnvironment, finalState)) :
    ScopeCoverage finalEnvironment (parameterScope arguments types scope) := by
  induction arguments generalizing types sources environment state scope with
  | nil =>
      cases types with
      | cons => simp at arity
      | nil =>
          cases sources with
          | cons => cases bound
          | nil =>
              cases bound
              exact covered
  | cons argument arguments ih =>
      cases types with
      | nil => simp at arity
      | cons type types =>
          cases sources with
          | nil => cases bound
          | cons source sources =>
              have tail := ih (covered.addLocal argument.name type state.heap.length)
                (Nat.succ.inj arity) bound
              simpa only [parameterScope, List.zip_cons_cons, List.foldl_cons] using tail

end Solcore.Frontend.RustHull.Correspondence
