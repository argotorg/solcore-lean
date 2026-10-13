import Solcore.Frontend.ProgramChecking

/-! Method selection rechecks the compiler's synthetic signature at its fixed
budget. This receipt keeps complete checker carriers aligned with the original
retained methods, independently of the budget used to check the whole program. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
open Frontend SourceInference

abbrev Checked (program : CheckedProgram) : Prop :=
  ImplementationMethodBodiesChecked program.environment program.signatures 1024
    (implementationMethodCheckTargets program.signatures) program.methods

theorem of_loaded {loaded : LoadedProgram} {program : CheckedProgram}
    (accepted : Frontend.checkLoadedProgram loaded 1024 = .ok program) : Checked program :=
  (checkLoadedProgram_success_body_checks accepted).2

theorem of_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram}
    (accepted : Frontend.checkProgram raw 1024 = .ok program) : Checked program := by
  obtain ⟨loaded, _loaded, accepted⟩ := checkProgram_success_load accepted
  exact of_loaded accepted

private theorem empty_targets {environment : ProgramEnvironment} {signatures : ProgramSignatures}
    {fuel : Nat} {targets : List ImplementationMethodCheckTarget}
    (checked : ImplementationMethodBodiesChecked environment signatures fuel targets []) :
    targets = [] := by cases checked; rfl

theorem of_empty_loaded {loaded : LoadedProgram} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkLoadedProgram loaded checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  have original := (checkLoadedProgram_success_body_checks accepted).2
  rw [empty] at original
  have targets := empty_targets original
  unfold Checked
  rw [targets, empty]
  exact .nil

theorem of_empty_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkProgram raw checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  obtain ⟨loaded, _loaded, accepted⟩ := checkProgram_success_load accepted
  exact of_empty_loaded accepted empty

end Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
