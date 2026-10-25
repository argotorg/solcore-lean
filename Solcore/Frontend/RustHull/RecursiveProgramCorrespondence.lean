import Solcore.Frontend.RustHull.DerivationProgramCorrespondence
import Solcore.Frontend.RustHull.PublicProgramCorrespondence

/-! Public meaning preservation for every finite source execution of the
accepted eligible program. Actual compilation and initialized arguments rule
out malformed observations; result classification is a conclusion. Recursive
calls, loops and matches follow the independent source derivation. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open NamedCallCorrespondence ScalarExecution DerivationCorrespondence

/-- Compile, allocate, install and invoke the selected entry of a recursive
program. Named calls, builtins and structured loops retain the independent
source result and heap, including all callee parameter allocations. -/
theorem compile_recursive_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled)
    (selected : program.functions.find? (·.name == entry) = some function)
    (eligible : RecursiveProgram program.functions)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel compiled.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction program.functions effects function sources initial sourceResult final)
    {world : World} {environment : Core.Environment} {initialStore callStore : Core.Store}
    {argument : Core.Expr}
    (argumentEvaluated : Core.Evaluates environment initialStore argument (bundleValues targets) callStore)
    (heapRelated : HeapRel world initial.heap callStore) :
    ∃ extension targetValue finalStore,
      ResultRel compiled.result sourceResult targetValue ∧
      Core.Evaluates environment initialStore (.apply compiled.expression argument) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore := by
  obtain ⟨own, allocated, assembled, rfl⟩ := StatementCorrespondence.compile_components accepted
  have sourceUnique := assemble_names_unique assembled
  obtain ⟨signatures, codes, sourceFunction, code, index, signaturesCompiled,
    sourceSelected, signatureCompiled, codesCompiled, codeFound, ownEqual,
    _, allocatedEqual⟩ := assemble_selection assembled
  have sameFunction := Option.some.inj (selected.symm.trans sourceSelected)
  subst sourceFunction
  subst own
  subst allocated
  have aligned := codesCompiled.aligned signaturesCompiled
  have signatureTable := compiledSignatures signaturesCompiled
  have unique : (signatures.map Signature.name).Nodup := by
    rw [signatureTable.names]
    exact sourceUnique
  obtain ⟨selectedOwn, signatureSelected, selectedCompiled⟩ := signatureTable.source_selected selected
  have sameOwn := Except.ok.inj (selectedCompiled.symm.trans signatureCompiled)
  subst selectedOwn
  have globals := GlobalEnvironmentRel.of_lookup aligned
    (scope := globalScope signatures [])
    (fun slot closure found => globalScope_lookup unique
      (by simp only [← aligned, List.getElem?_map, found, Option.map_some]) [])
    callStore.length (bundleValues targets :: environment)
  have covered : ScopeCoverage [] (globalScope signatures []) := by
    apply ScopeCoverage.of_reserved
    intro binding member name named
    simp only [globalScope, List.append_nil, List.mem_map] at member
    obtain ⟨signature, _, rfl⟩ := member
    cases Option.some.inj named
    exact slotName_reserved _
  have initializedHeap := (StateRel.trivial (source := initial) heapRelated).initializeGlobals signatures codes
    (bundleValues targets :: environment)
  have installed := InstalledGlobals.initialize aligned (bundleValues targets :: environment) callStore
  obtain ⟨extension, targetValue, finalStore, related, bodyExecuted, finalHeap, _⟩ :=
    (DerivationProgramCorrespondence.function_preserves (model := StateModel.trivial σ) (slots := [])
      signaturesCompiled codesCompiled unique covered globals (EffectEnvironmentRel.empty _ _ _) eligible
      sourceEvaluated) selected signatureSelected codeFound values initializedHeap installed
  have invoked := globalInvocation_evaluates (runtimeValues := []) aligned codeFound installed bodyExecuted
  have assembledExecution := globalInitialization_evaluates aligned invoked
  exact ⟨extension, targetValue, finalStore, related,
    Core.Evaluates.apply .lambda argumentEvaluated assembledExecution, finalHeap.toHeapRel⟩

/-- Actual public preparation supplies the selected function, source arguments
and empty initial heap. The public premise is syntactic recursive eligibility;
no closure correspondence or function-body preservation is assumed. -/
theorem prepare_recursive_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : RecursiveProgram program.functions)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        ∃ world targetValue finalStore,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          Core.Evaluates [] [] prepared.expression targetValue finalStore ∧ HeapRel world final.heap finalStore := by
  obtain ⟨sources, targets, compiled, inputsRelated, valuesRelated, arguments⟩ :=
    prepare_argument_correspondence accepted
  obtain ⟨own, allocated, assembled, _⟩ := StatementCorrespondence.compile_components compiled
  obtain ⟨signatures, codes, function, code, index, _, selected, _⟩ := assemble_selection assembled
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated
  exact compile_recursive_program compiled selected eligible valuesRelated evaluated
    (arguments [] []) (HeapRel.empty [])

/-- Every genuine public checkpoint chain for a finite eligible source
execution completes with its represented result and heap exactly when combined
fuel reaches the actual transition count. Otherwise it remains resumable.
No premise restricts the source result to values or language failures. -/
theorem prepare_recursive_program_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : RecursiveProgram program.functions)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, Resumes (run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ := prepare_recursive_program accepted eligible initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated
  obtain ⟨world, targetValue, finalStore, related, executed, heap⟩ := execute sourceResult final evaluated
  obtain ⟨required, completed⟩ := evaluation_resumes_exact executed
  exact ⟨world, targetValue, finalStore, required, related, heap, completed⟩

theorem prepare_recursive_program_run {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : RecursiveProgram program.functions)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel, required ≤ fuel → run prepared fuel = .done targetValue finalStore := by
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ := prepare_recursive_program accepted eligible initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated
  obtain ⟨world, targetValue, finalStore, related, executed, heap⟩ := execute sourceResult final evaluated
  obtain ⟨required, completed⟩ := evaluation_run_complete executed
  exact ⟨world, targetValue, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.Correspondence
