import Solcore.Frontend.RustHull.RenamedFunctionBodyCorrespondence
import Solcore.Frontend.RustHull.ProgramSelectionCorrespondence
import Solcore.Frontend.RustHull.GlobalInvocationCorrespondence

/-! Multiple actual compiled Hull functions connected to independent source
execution and the public scalar preparation, execution and resumption APIs.
The eligible entry body may use the established normal expression fragment;
global allocation and installation are derived from compilation itself. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence ScalarExecution

theorem compile_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled)
    (selected : program.functions.find? (·.name == entry) = some function)
    (eligible : ∀ signatures, program.functions.mapM (signature fuel) = .ok signatures →
      ∀ statement ∈ function.body,
        StraightLine program.functions effects signatures (fun _ _ => True) statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel compiled.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction program.functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {environment : Core.Environment} {initialStore callStore : Core.Store}
    {argument : Core.Expr}
    (argumentEvaluated : Core.Evaluates environment initialStore argument (bundleValues targets) callStore)
    (heapRelated : HeapRel world initial.heap callStore) :
    ∃ extension targetValue finalStore,
      ResultRel compiled.result sourceResult targetValue ∧
      Core.Evaluates environment initialStore (.apply compiled.expression argument) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore := by
  obtain ⟨own, allocated, assembled, rfl⟩ := compile_components accepted
  obtain ⟨signatures, codes, sourceFunction, code, index, signaturesCompiled,
    sourceSelected, signatureCompiled, codesCompiled, codeFound, ownEqual,
    functionCompiled, allocatedEqual⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  subst own
  subst allocated
  have aligned := codesCompiled.aligned signaturesCompiled
  have initializedHeap := heapRelated.initializeGlobals signatures codes (bundleValues targets :: environment)
  have installed := InstalledGlobals.initialize aligned (bundleValues targets :: environment) callStore
  obtain ⟨extension, targetValue, finalStore, related, bodyExecuted, finalHeap, _⟩ :=
    lowerFunction_body_renamed (unrestrictedExternalFrame σ) signatureCompiled functionCompiled
      (eligible signatures signaturesCompiled) values sourceEvaluated normal
      (mapping := globalShift index)
      (environment := installationEnvironment
        (globalEnvironment signatures callStore.length (bundleValues targets :: environment)) index)
      initializedHeap trivial
  have invoked := globalInvocation_evaluates (runtimeValues := []) aligned codeFound installed bodyExecuted
  have assembledExecution := globalInitialization_evaluates aligned invoked
  exact ⟨extension, targetValue, finalStore, related,
    Core.Evaluates.apply .lambda argumentEvaluated assembledExecution, finalHeap⟩

/-- Successful public preparation chooses the actual entry and derives its
source arguments from the real parser. No initialized heap, closure table or
argument typing premise is supplied by the caller. -/
theorem prepare_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ signatures, program.functions.mapM (signature compilationFuel) = .ok signatures →
      ∀ function, program.functions.find? (·.name == entry) = some function →
      ∀ statement ∈ function.body,
        StraightLine program.functions effects signatures (fun _ _ => True) statement)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          Core.Evaluates [] [] prepared.expression targetValue finalStore ∧
          HeapRel world final.heap finalStore := by
  obtain ⟨sources, targets, compiled, inputsRelated, valuesRelated, arguments⟩ :=
    prepare_argument_correspondence accepted
  obtain ⟨own, allocated, assembled, _⟩ := compile_components compiled
  obtain ⟨signatures, codes, function, code, index, _, selected, _⟩ := assemble_selection assembled
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final sourceEvaluated normal
  obtain ⟨world, value, finalStore, related, executed, heap⟩ :=
    compile_program compiled selected (fun signatures accepted => eligible signatures accepted function selected)
      valuesRelated sourceEvaluated normal (arguments [] []) (HeapRel.empty [])
  exact ⟨world, value, finalStore, related, executed, heap⟩

/-- Every finite sequence of real public resumptions has the normal source
value and represented heap exactly when its accumulated fuel reaches the
actual Core transition count. All global closures come from the real compiler. -/
theorem prepare_program_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ signatures, program.functions.mapM (signature compilationFuel) = .ok signatures →
      ∀ function, program.functions.find? (·.name == entry) = some function →
      ∀ statement ∈ function.body,
        StraightLine program.functions effects signatures (fun _ _ => True) statement)
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
  obtain ⟨function, sources, selected, inputsRelated, sourceExecution⟩ :=
    prepare_program accepted eligible initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final sourceEvaluated normal
  obtain ⟨world, value, finalStore, related, evaluated, heap⟩ :=
    sourceExecution sourceResult final sourceEvaluated normal
  obtain ⟨required, completed⟩ := evaluation_resumes_exact evaluated
  exact ⟨world, value, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
