import Solcore.Frontend.SourceRuntimeLinking
import Solcore.Frontend.SourceRuntimeProperties

/-! Static checking provenance retained by the finite graph linker. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- The runtime checker does not replace its input program on success. -/
theorem Program.check_preserves_program
    (raw : Program) (checked : CheckedProgram)
    (accepted : raw.check = .ok checked) :
    checked.program = raw := by
  unfold Program.check at accepted
  split at accepted
  · cases accepted
  · simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
    · cases accepted
      rfl

/-- Rechecking the program stored in a linker-produced checked carrier yields
that exact carrier, not merely another value with the same table. -/
theorem CheckedProgram.check_idempotent_of_checkedBy
    (checked : CheckedProgram)
    (checkedBy : ∃ raw : Program, raw.check = .ok checked) :
    checked.program.check = .ok checked := by
  obtain ⟨raw, accepted⟩ := checkedBy
  rw [Program.check_preserves_program raw checked accepted]
  exact accepted

end Solcore.Frontend.SourceRuntime

namespace Solcore.Frontend.SourceRuntimeLinking

/-- Every linked entry retains a genuinely checked executable program. -/
theorem LinkedEntry.program_check (entry : LinkedEntry) :
    entry.program.program.check = .ok entry.program :=
  SourceRuntime.CheckedProgram.check_idempotent_of_checkedBy
    entry.program entry.checkedBy

theorem LinkedEntry.program_isWellTyped (entry : LinkedEntry) :
    entry.program.program.IsWellTyped :=
  ⟨entry.program, entry.program_check⟩

/-- The source body selected by a linked entry has a checked graph typing
derivation at its own parameter context and result type. -/
theorem LinkedEntry.selectedBody_hasType (entry : LinkedEntry) :
    ∃ definition,
      entry.program.program.findDefinition? entry.key = some definition ∧
      SourceRuntime.Expr.InfersType entry.program.program
        (definition.parameters.map fun parameter =>
          (parameter.1, SourceRuntime.StaticType.value parameter.2))
        definition.body definition.resultType := by
  obtain ⟨definition, found, _, _⟩ := entry.definitionMatches
  exact ⟨definition, found,
    entry.program_isWellTyped.foundDefinition_hasType found⟩

/-- Deeply typed positional Core arguments and an initial store induce the
graph runner's exact selected-definition input premise. -/
theorem LinkedEntry.runtimeInputsHaveType
    (entry : LinkedEntry) (arguments : List Core.Value)
    (store : Core.Store) (world : Core.StoreTyping)
    (argumentsTyping : Core.RuntimeEnvironmentHasTypes world arguments
      (entry.inputs.map Prod.snd))
    (storeTyping : Core.StoreHasTypes world store) :
    ∃ definition,
      entry.program.RuntimeInputsHaveType entry.key arguments store
        definition world := by
  obtain ⟨definition, found, parameters, _⟩ := entry.definitionMatches
  refine ⟨definition, ⟨found, ?_, storeTyping⟩⟩
  simpa [SourceRuntime.Definition.signature, parameters] using
    argumentsTyping

end Solcore.Frontend.SourceRuntimeLinking
