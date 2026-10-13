import Solcore.Frontend.ProgramChecking

/-! Method selection and the original program check retain their actual
successful budgets. Complete checker results agree across those budgets. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
open Frontend SourceInference

abbrev Checked (program : CheckedProgram) : Prop :=
  ∃ checkingFuel, ImplementationMethodBodiesChecked program.environment program.signatures checkingFuel
    (implementationMethodCheckTargets program.signatures) program.methods

theorem of_loaded {loaded : LoadedProgram} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkLoadedProgram loaded checkingFuel = .ok program) : Checked program :=
  ⟨checkingFuel, (checkLoadedProgram_success_body_checks accepted).2⟩

theorem of_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkProgram raw checkingFuel = .ok program) : Checked program := by
  obtain ⟨loaded, _loaded, accepted⟩ := checkProgram_success_load accepted
  exact of_loaded accepted

theorem of_empty_loaded {loaded : LoadedProgram} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkLoadedProgram loaded checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  have _ := empty
  exact of_loaded accepted

theorem of_empty_checked {raw : Workspace.RawWorkspace} {program : CheckedProgram} {checkingFuel : Nat}
    (accepted : Frontend.checkProgram raw checkingFuel = .ok program)
    (empty : program.methods = []) : Checked program := by
  have _ := empty
  exact of_checked accepted

end Solcore.SourceSemantics.CoreLowering.CallableMethodBodyCoherence
