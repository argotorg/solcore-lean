import Solcore.Frontend.RustHull.FunctionBodyCorrespondence
import Solcore.Frontend.RustHull.FunctionAssemblyCorrespondence

/-! Independent Hull function execution connected to the actual scalar compiler
and public run/resume boundary. Eligibility states the current expression and
statement fragment explicitly. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence ScalarExecution

theorem unrestrictedExternalFrame (σ : Type) :
    ExternalFrame (fun (_ : σ) (_ : Core.Store) => True) := by
  constructor <;> intros <;> trivial

theorem compile_components {program : Program} {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled) :
    ∃ own allocated,
      assemble program.functions entry [] fuel = .ok (own, allocated) ∧
      compiled = ⟨entry, own.parameters, own.result,
        .lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) allocated⟩ := by
  by_cases exported : entry ∈ program.entryPoints
  · simp only [compile, exported, ↓reduceIte] at accepted
    obtain ⟨⟨own, allocated⟩, assembled, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨inferred, _, accepted⟩ := lower_bind_eq_ok.mp accepted
    obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp accepted
    cases checked
    cases returned
    exact ⟨own, allocated, assembled, rfl⟩
  · simp [compile, exported, fail, Bind.bind, Except.bind] at accepted

theorem lowerFunction_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {expression argument : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own = .ok expression)
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures external statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {environment : Core.Environment} {initialStore callStore : Core.Store}
    (argumentEvaluated : Core.Evaluates environment initialStore argument (bundleValues targets) callStore)
    (heapRelated : HeapRel world initial.heap callStore)
    (externalRelated : external initial.external callStore) :
    ∃ extension targetValue finalStore,
      ResultRel own.result sourceResult targetValue ∧
      Core.Evaluates environment initialStore (.apply expression argument) targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  cases sourceEvaluated with
  | body bound executed =>
      rename_i allocated sourceEnvironment control
      have controlNormal : NormalControl control := by
        obtain ⟨value, same⟩ := normal
        cases control <;> first | trivial | simp [Semantics.finishFunction] at same
      exact lowerFunction_apply frame signatureCompiled compiled eligible values bound executed controlNormal
        argumentEvaluated heapRelated externalRelated
  | arity mismatch =>
      obtain ⟨value, same⟩ := normal
      contradiction

/-- One actual exported Hull function, with any accepted number of arguments,
executes with the same normal source result and source heap. The compiler's
administrative function cell is initialized here and remains outside that heap. -/
theorem compile_single_function {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {fuel : Nat} {compiled : Compiled}
    (accepted : compile program entry fuel = .ok compiled)
    (eligible : ∀ own, signature fuel function = .ok own →
      ∀ statement ∈ function.body,
        StraightLine [function] effects [own] (fun _ _ => True) statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel compiled.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction [function] effects function sources initial sourceResult final)
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
  rw [functions] at assembled
  obtain ⟨_, signatureCompiled, closure, closureCompiled, rfl⟩ := assemble_single_components assembled
  obtain ⟨statements, _, closureShape⟩ := lowerFunction_components closureCompiled
  let body := own.parameters.zipIdx.foldr (fun (type, index) body =>
    Core.Expr.letE (Core.OptionalCell.allocateInitialized type
      (projectArgument index own.parameters.length (.var index))) body)
      (finishedBody own.result statements)
  change closure = .lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body at closureShape
  subst closure
  have installedHeap : HeapRel world initial.heap
      (singleFunctionStore own body (bundleValues targets) environment callStore) :=
    heapRelated.appendCore _
  have supplied : Core.Evaluates
      (singleFunctionEnvironment own (bundleValues targets) environment callStore)
      (singleFunctionStore own body (bundleValues targets) environment callStore)
      (.var 1) (bundleValues targets)
      (singleFunctionStore own body (bundleValues targets) environment callStore) := .var rfl
  obtain ⟨extension, targetValue, finalStore, related, evaluated, finalHeap, _⟩ :=
    lowerFunction_source (unrestrictedExternalFrame σ) signatureCompiled closureCompiled
      (eligible own signatureCompiled) values sourceEvaluated normal supplied installedHeap trivial
  exact ⟨extension, targetValue, finalStore, related,
    singleFunction_apply argumentEvaluated evaluated, finalHeap⟩

/-- Public preparation derives the independent source arguments and the empty
initial source heap from the actual parser and initializer. Eligible normal
source executions then determine the exact Core value and represented heap. -/
theorem prepare_single_function {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {inputs : List String} {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ own, signature compilationFuel function = .ok own →
      ∀ statement ∈ function.body,
        StraightLine [function] effects [own] (fun _ _ => True) statement)
    (initialExternal : σ) :
    ∃ sources, InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction [function] effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          Core.Evaluates [] [] prepared.expression targetValue finalStore ∧
          HeapRel world final.heap finalStore := by
  obtain ⟨sources, targets, compiled, inputsRelated, valuesRelated, arguments⟩ :=
    prepare_argument_correspondence accepted
  refine ⟨sources, inputsRelated, ?_⟩
  intro sourceResult final sourceEvaluated normal
  obtain ⟨world, value, finalStore, related, executed, heap⟩ :=
    compile_single_function functions compiled eligible valuesRelated sourceEvaluated normal
      (arguments [] []) (HeapRel.empty [])
  exact ⟨world, value, finalStore, related, executed, heap⟩

/-- Every finite chain of genuine public checkpoints preserves the meaning of
an eligible normal source execution. Completion has the source value and heap
exactly when the total supplied fuel reaches its transition count. -/
theorem prepare_single_function_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {inputs : List String} {compilationFuel : Nat} {prepared : Prepared}
    (accepted : prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ own, signature compilationFuel function = .ok own →
      ∀ statement ∈ function.body,
        StraightLine [function] effects [own] (fun _ _ => True) statement)
    (initialExternal : σ) :
    ∃ sources, InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction [function] effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, Resumes (run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  obtain ⟨sources, inputsRelated, sourceExecution⟩ := prepare_single_function functions accepted eligible initialExternal
  refine ⟨sources, inputsRelated, ?_⟩
  intro sourceResult final sourceEvaluated normal
  obtain ⟨world, value, finalStore, related, evaluated, heap⟩ := sourceExecution sourceResult final sourceEvaluated normal
  obtain ⟨required, completed⟩ := evaluation_resumes_exact evaluated
  exact ⟨world, value, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.StatementCorrespondence
