import Solcore.Frontend.SourceRuntimeDeepProperties
import Solcore.Frontend.SourceRuntimeLinkingSafetyProperties

/-! Deep graph preservation at the checked and linked entry boundaries. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceRuntime

/-- Core arguments acquire the graph value relation pointwise when converted
at the checked entry boundary. -/
theorem GraphArgumentsHaveTypes.ofCore
    {world : Core.StoreTyping} {arguments : List Core.Value}
    {types : List Core.Ty} {definitions : Core.DataEnvironment}
    (program : Program)
    (typing : Core.RuntimeEnvironmentHasTypes world arguments types
      definitions) :
    GraphArgumentsHaveTypes program world (arguments.map Value.ofCore)
      types definitions := by
  apply Core.RuntimeEnvironmentHasTypes.rec
      (motive_1 := fun _ _ _ _ => True)
      (motive_2 := fun values context relationDefinitions _ =>
        GraphArgumentsHaveTypes program world (values.map Value.ofCore)
          context relationDefinitions)
      (t := typing)
  case unit => intros; trivial
  case bool => intros; trivial
  case word => intros; trivial
  case pair => intros; trivial
  case inLeft => intros; trivial
  case inRight => intros; trivial
  case closure => intros; trivial
  case cellRef => intros; trivial
  case constructed => intros; trivial
  case nil => exact .nil
  case cons =>
    intro _ _ _ _ _ head _ _ tailIH
    exact .cons (Value.GraphHasType.ofCore head) tailIH

/-- The real checked runner's successful result and final store are deeply
typed when the selected entry is checker-certified and the caller supplies
deeply typed arguments and an initial store. -/
theorem CheckedProgram.RuntimeInputsHaveType.run_done_deep
    {checked : CheckedProgram} {fuel : Nat} {entry : Key}
    {arguments : List Core.Value} {initialStore finalStore : Core.Store}
    {value : Value} {definition : Definition}
    {world : Core.StoreTyping} {definitions : Core.DataEnvironment}
    (typing : checked.RuntimeInputsHaveType entry arguments initialStore
      definition world definitions)
    (checkedBy : checked.program.check = .ok checked)
    (completed : checked.run fuel entry arguments initialStore =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      Value.GraphHasType checked.program finalWorld value
        definition.resultType definitions := by
  have bundleTyping : Value.GraphHasType checked.program world
      (packValues (arguments.map Value.ofCore))
      (parameterType definition.parameters) definitions := by
    have packed := (GraphArgumentsHaveTypes.ofCore checked.program
      typing.argumentsTyping).packValues
    simpa [Definition.signature, parameterType_eq_bundleType_map] using packed
  have wellTyped : checked.program.IsWellTyped := ⟨checked, checkedBy⟩
  have applied : applyValue checked.program
      (evaluate fuel checked.program) fuel (.global entry)
      (arguments.map Value.ofCore) initialStore =
        .done value finalStore := by
    unfold CheckedProgram.run at completed
    simp only [typing.found] at completed
    split at completed
    · contradiction
    · cases fuel with
      | zero => simp at completed
      | succ n => simpa using completed
  exact applyValue_global_done_deep
    (evaluate fuel checked.program)
    (evaluate_preserves_graph_type checked.program wellTyped fuel)
    wellTyped typing.found
    bundleTyping typing.storeTyping applied

end Solcore.Frontend.SourceRuntime

namespace Solcore.Frontend.SourceRuntimeLinking

/-- The checked-program deep entry theorem, specialized to the selected
linked definition and its public positional input types. -/
theorem LinkedEntry.run_done_deep
    (entry : LinkedEntry) {fuel : Nat}
    {arguments : List Core.Value} {initialStore finalStore : Core.Store}
    {value : SourceRuntime.Value} {world : Core.StoreTyping}
    {definitions : Core.DataEnvironment}
    (argumentsTyping : Core.RuntimeEnvironmentHasTypes world arguments
      (entry.inputs.map Prod.snd) definitions)
    (storeTyping : Core.StoreHasTypes world initialStore)
    (completed : entry.program.run fuel entry.key arguments initialStore =
      .done value finalStore) :
    ∃ finalWorld,
      Core.WorldExtends world finalWorld ∧
      Core.StoreHasTypes finalWorld finalStore ∧
      SourceRuntime.Value.GraphHasType entry.program.program finalWorld value
        entry.resultType definitions := by
  obtain ⟨definition, found, parameters, resultType⟩ :=
    entry.definitionMatches
  have input : entry.program.RuntimeInputsHaveType entry.key arguments
      initialStore definition world definitions := by
    refine ⟨found, ?_, storeTyping⟩
    simpa [SourceRuntime.Definition.signature, parameters] using
      argumentsTyping
  have result := input.run_done_deep entry.program_check completed
  simpa [resultType] using result

end Solcore.Frontend.SourceRuntimeLinking
