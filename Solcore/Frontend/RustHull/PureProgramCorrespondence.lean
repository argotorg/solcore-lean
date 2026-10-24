import Solcore.Frontend.RustHull.PureFunctionCorrespondence
import Solcore.Frontend.RustHull.PublicProgramCorrespondence

/-! Public multiple-function correspondence for syntactically pure entries.
Actual builtin classification and signature compilation discharge expression
preservation; the caller supplies no intermediate compiler or heap invariant. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open ScalarExecution

theorem prepare_pure_program_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ function, program.functions.find? (·.name == entry) = some function →
      ∀ statement ∈ function.body, PureStatement program.functions statement)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, Resumes (run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  exact StatementCorrespondence.prepare_program_resumes accepted
    (fun signatures compiled function selected statement member =>
      (eligible function selected statement member).straightLine effects
        (SignatureNames.compiled compiled) (fun _ _ => True)) initialExternal

theorem prepare_pure_program_run {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ function, program.functions.find? (·.name == entry) = some function →
      ∀ statement ∈ function.body, PureStatement program.functions statement)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel, required ≤ fuel → run prepared fuel = .done targetValue finalStore := by
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ :=
    StatementCorrespondence.prepare_program accepted
      (fun signatures compiled function selected statement member =>
        (eligible function selected statement member).straightLine effects
          (SignatureNames.compiled compiled) (fun _ _ => True)) initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro result final evaluated normal
  obtain ⟨world, target, finalStore, related, executed, heap⟩ := execute result final evaluated normal
  obtain ⟨required, completed⟩ := evaluation_run_complete executed
  exact ⟨world, target, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.Correspondence
