import Solcore.Frontend.RustHull.Internal.PublicFunctions
import Solcore.Frontend.RustHull.Internal.NamedFunctions
import Solcore.Frontend.RustHull.Internal.Derivations
import Solcore.Frontend.RustHull.Internal.Statements
import Solcore.Frontend.RustHull.Internal.LoweringFacts

/-!
# Hull function meaning preservation

Finite independent Hull evaluations reach actual compilation and every chain of public resumptions,
for functions and programs without external effects. Main theorems:
`Correspondence.prepare_recursive_program_resumes`, `Correspondence.prepare_ranked_program_resumes`,
`Correspondence.prepare_pure_program_resumes`.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.PureProgramCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RankedProgramCorrespondence
/-! Meaning preservation for finite, acyclic named-call programs. Every named
call decreases a syntactic function rank. The proof closes all function-body
induction premises against the actual compiler and installed closure table. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open NamedCallCorrespondence ScalarExecution

def RankedProgram (functions : List Function) (rank : String → Nat) : Prop :=
  ∀ function ∈ functions, ∀ statement ∈ function.body,
    RankedStatement functions rank (rank function.name) statement

/-- The exact body of every selected installed closure preserves independent
source execution. The decreasing rank discharges named-call induction; all
signatures and closure identities are extracted from actual compilation. -/
theorem ranked_functions_preserve {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {fuel : Nat} {functions : List Function} {signatures : List Signature} {scope : Scope}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (signaturesCompiled : functions.mapM (signature fuel) = .ok signatures)
    (codesCompiled : CompiledGlobals fuel signatures scope (functions.zip signatures).reverse codes)
    (unique : (signatures.map Signature.name).Nodup)
    (globals : GlobalEnvironmentRel codes locations scope Core.Renaming.id captured)
    {rank : String → Nat} (eligible : RankedProgram functions rank)
    {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (sourceSelected : functions.find? (·.name == name) = some function)
    (signatureSelected : signatures.find? (·.name == name) = some code.own)
    (codeFound : codes[index]? = some code) :
    ∀ sources initial final source,
      FunctionExecutionPreserves functions effects codes locations captured function code index
        sources initial final source := by
  generalize levelEq : rank function.name = level
  induction level using Nat.strongRecOn generalizing name function code index with
  | ind level ih =>
      have names := SignatureNames.compiled signaturesCompiled
      have resolve : ∀ name function, functions.find? (·.name == name) = some function →
          ∃ (index : Nat) (code : GlobalCode), signatures.find? (·.name == name) = some code.own ∧
            codes[index]? = some code := by
        intro name function found
        obtain ⟨index, code, selected, codeFound, _⟩ :=
          compiledFunction_resolve signaturesCompiled codesCompiled found
        exact ⟨index, code, selected, codeFound⟩
      have bodyEligible : ∀ statement ∈ function.body,
          ContextualStatementCorrespondence.StraightLine functions effects signatures codes locations captured statement := by
        intro statement member
        apply (eligible function (List.mem_of_find?_eq_some sourceSelected) statement member).straightLine
          effects names resolve
        intro callee calleeFunction calleeCode calleeIndex sourceFound signatureFound found decreases
        exact ih (rank calleeFunction.name) (by simpa only [levelEq] using decreases)
          sourceFound signatureFound found rfl
      obtain ⟨signatureCompiled, functionCompiled⟩ :=
        compiledFunction_at signaturesCompiled codesCompiled unique sourceSelected signatureSelected codeFound
      have captures : GlobalEnvironmentRel codes locations scope (globalShift index)
          (installationEnvironment captured index) := by
        change GlobalEnvironmentRel codes locations scope (fun slot => index + slot)
          (List.replicate index .unit ++ captured)
        simpa only [List.length_replicate, Core.Renaming.id] using
          globals.prepend (List.replicate index .unit)
      intro sources initial final source evaluated targets values world store heap installed
      obtain ⟨extension, target, finalStore, related, executed, finalHeap, finalInstalled⟩ :=
        ContextualStatementCorrespondence.lowerFunction_body_contextual signatureCompiled functionCompiled
          bodyEligible values evaluated ⟨_, rfl⟩ captures heap installed
      cases related with
      | value valueRelated => exact ⟨extension, _, finalStore, valueRelated, executed, finalHeap, finalInstalled⟩

/-- Compile, allocate, install and invoke the selected entry of a ranked
program. Named function calls and nested builtin calls retain the independent
normal source result and heap, including all callee parameter allocations. -/
theorem compile_ranked_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled)
    (selected : program.functions.find? (·.name == entry) = some function)
    {rank : String → Nat} (eligible : RankedProgram program.functions rank)
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
  have initializedHeap := heapRelated.initializeGlobals signatures codes (bundleValues targets :: environment)
  have installed := InstalledGlobals.initialize aligned (bundleValues targets :: environment) callStore
  obtain ⟨source, rfl⟩ := normal
  obtain ⟨extension, targetValue, finalStore, related, bodyExecuted, finalHeap, _⟩ :=
    ranked_functions_preserve signaturesCompiled codesCompiled unique globals eligible
      selected signatureSelected codeFound sources initial final source sourceEvaluated values initializedHeap installed
  have invoked := globalInvocation_evaluates (runtimeValues := []) aligned codeFound installed bodyExecuted
  have assembledExecution := globalInitialization_evaluates aligned invoked
  exact ⟨extension, .inRight .word targetValue, finalStore, .value related,
    Core.Evaluates.apply .lambda argumentEvaluated assembledExecution, finalHeap⟩

/-- Actual public preparation supplies the selected function, source arguments
and empty initial heap. The public premise is syntactic ranked eligibility;
no closure correspondence or function-body preservation is assumed. -/
theorem prepare_ranked_program {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    {rank : String → Nat} (eligible : RankedProgram program.functions rank)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          Core.Evaluates [] [] prepared.expression targetValue finalStore ∧ HeapRel world final.heap finalStore := by
  obtain ⟨sources, targets, compiled, inputsRelated, valuesRelated, arguments⟩ :=
    prepare_argument_correspondence accepted
  obtain ⟨own, allocated, assembled, _⟩ := StatementCorrespondence.compile_components compiled
  obtain ⟨signatures, codes, function, code, index, _, selected, _⟩ := assemble_selection assembled
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated normal
  exact compile_ranked_program compiled selected eligible valuesRelated evaluated normal
    (arguments [] []) (HeapRel.empty [])

/-- Every genuine public checkpoint chain for an eligible normal source
execution completes with that source result and heap exactly when its combined
fuel reaches the actual transition count. Otherwise it remains resumable. -/
theorem prepare_ranked_program_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    {rank : String → Nat} (eligible : RankedProgram program.functions rank)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, Resumes (run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ := prepare_ranked_program accepted eligible initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated normal
  obtain ⟨world, targetValue, finalStore, related, executed, heap⟩ := execute sourceResult final evaluated normal
  obtain ⟨required, completed⟩ := evaluation_resumes_exact executed
  exact ⟨world, targetValue, finalStore, required, related, heap, completed⟩

theorem prepare_ranked_program_run {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {entry : String} {inputs : List String} {compilationFuel : Nat}
    {prepared : Prepared} (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    {rank : String → Nat} (eligible : RankedProgram program.functions rank)
    (initialExternal : σ) :
    ∃ function sources, program.functions.find? (·.name == entry) = some function ∧
      InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction program.functions effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel, required ≤ fuel → run prepared fuel = .done targetValue finalStore := by
  obtain ⟨function, sources, selected, inputsRelated, execute⟩ := prepare_ranked_program accepted eligible initialExternal
  refine ⟨function, sources, selected, inputsRelated, ?_⟩
  intro sourceResult final evaluated normal
  obtain ⟨world, targetValue, finalStore, related, executed, heap⟩ := execute sourceResult final evaluated normal
  obtain ⟨required, completed⟩ := evaluation_run_complete executed
  exact ⟨world, targetValue, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RecursiveProgramCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.Correspondence
/-! Independent Hull meaning and its connection to the actual Core compiler.

Accepted programs with local variables and structured control are
connected without a body-correctness assumption: actual input parsing,
compilation, function installation, parameter initialization, local heap, normal
result or language fault and every finite chain of public resumptions are covered. Expression
eligibility is syntactic and includes structured values, conditionals and
nested calls to pure builtins and named functions. Assignments update local
variables or nested product fields, retaining the heap on a failed RHS. Pattern
matching uses actual tests, skips rejected arms, and allocates the selected
payload binder before its body. Blocks, loop initializers,
conditions, bodies, post statements, break and continue use the actual Core loop
closure and retain its self cell across calls and nested loops. Induction on
the independent source execution covers loops and recursive calls whenever
that execution finishes with a value or language fault. The ranked theorem supplies an interface for
acyclic call graphs. Pure entry functions are also connected in arbitrary accepted
multi-function programs. The Word identity and recursive countdown families
additionally supply source executions for every Word input. Pure builtin
correspondence is compositional. Language faults retain their exact reason
and the heap at the failure, including faults in loop stages or call arguments.
Malformed source observations and divergence remain separate proof obligations.
This module does not claim an unrestricted Hull or contract theorem; external
effects remain explicit source interfaces until their concrete implementations
are related separately.
-/
end
