import Solcore.Frontend.RustHull.Internal.Statements
import Solcore.Frontend.RustHull.Internal.NamedFunctions

/-!
# Public function correspondence

The public theorems for call-free and single functions, and the ranked expression interface that the
program theorems use.
-/

section
-- leanmerge: from Solcore.Frontend.RustHull.IndexedInjectionCorrespondence
/-! Indexed source sum injections agree with the nested sums emitted by the
actual compiler, including transparent named layouts and the final payload. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.PureExpressionCorrespondence

open Correspondence StatementCorrespondence

theorem inject_evaluates (shape : Semantics.Shape) {index : Nat} {payloadType : Core.Ty}
    {source : Semantics.Value} {target : Core.Value} (related : ValueRel payloadType source target)
    {value expression : Core.Expr}
    (compiled : inject index (coreType shape) payloadType value = .ok expression)
    {environment : Core.Environment} {initial final : Core.Store} {mapping : Core.Renaming}
    (evaluated : Core.Evaluates environment initial (value.rename mapping) target final) :
    ∃ sourceResult targetResult,
      Semantics.injectShape? index shape source = some sourceResult ∧
      ValueRel (coreType shape) sourceResult targetResult ∧
      Core.Evaluates environment initial (expression.rename mapping) targetResult final := by
  induction shape generalizing index expression with
  | sum left right _ ih =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, inject, ↓reduceIte] at compiled
        obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases returned
        have same := expectType_eq_of_ok matched
        exact ⟨.inl source, .inLeft (coreType right) target,
          by simp [Semantics.injectShape?], .inl (same ▸ related), .inLeft evaluated⟩
      · simp only [coreType, inject, zero, ↓reduceIte] at compiled
        obtain ⟨nested, nestedCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
        cases returned
        obtain ⟨sourceResult, targetResult, injected, resultRelated, resultEvaluated⟩ := ih nestedCompiled
        exact ⟨.inr sourceResult, .inRight (coreType left) targetResult,
          by simp [Semantics.injectShape?, zero, injected], .inr resultRelated, .inRight resultEvaluated⟩
  | word | bool | unit | product =>
      by_cases zero : index = 0
      · subst index
        simp only [coreType, inject, ↓reduceIte] at compiled
        obtain ⟨checked, matched, returned⟩ := lower_bind_eq_ok.mp compiled
        cases checked
        cases returned
        have same := expectType_eq_of_ok matched
        exact ⟨source, target, by simp [Semantics.injectShape?],
          by simpa only [coreType, same] using related, evaluated⟩
      · simp [coreType, inject, zero, fail, Bind.bind, Except.bind] at compiled

private theorem indexedInjection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr} {index : Nat}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.injectionResult index target value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i otherIndex otherTarget otherOperand operandResult kind evaluated
  cases operandResult with
  | fault reason => simp [Semantics.Result.bind] at resultEq
  | value value => exact ⟨value, evaluated, rfl⟩

theorem indexedInjection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {external : σ → Core.Store → Prop}
    {operand : Expr} (preserves : NormalExprPreserves functions effects signatures external operand)
    (index : Nat) (type target : Ty) (span : Option Span) :
    NormalExprPreserves functions effects signatures external
      ⟨type, .inK index target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, sourceResult⟩ := indexedInjection_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated heap externalRelated
      obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
      rw [← targetShape] at injectionCompiled
      have supplied : Core.Evaluates (targetValue :: environment) finalStore
          ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
      obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
        inject_evaluates shape related injectionCompiled supplied
      have same : sourceInjected = sourceValue := by
        simpa [Semantics.injectionResult, Semantics.inject?, sourceShape, sourceInjection] using sourceResult
      subst sourceInjected
      refine ⟨extension, targetInjected, finalStore, ?_, ?_, finalHeap, finalExternal⟩
      · simpa only [targetShape] using injectionRelated
      · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

end Solcore.Frontend.RustHull.PureExpressionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PublicFunctionCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.CallFreeCorrespondence
/-! A syntactic Hull fragment with a complete normal-execution connection to
the public Core runner. Eligibility contains no semantic preservation premise:
the expression and statement proofs are derived from the syntax below. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

inductive CallFree : Expr → Prop where
  | word (type text span) : CallFree ⟨type, .word text, span⟩
  | bool (type value span) : CallFree ⟨type, .bool value, span⟩
  | unit (type span) : CallFree ⟨type, .unit, span⟩
  | var (type name span) : CallFree ⟨type, .var name, span⟩
  | pair {left right} (leftPure : CallFree left) (rightPure : CallFree right) (type span) :
      CallFree ⟨type, .pair left right, span⟩
  | fst {value} (pure : CallFree value) (type span) : CallFree ⟨type, .fst value, span⟩
  | snd {value} (pure : CallFree value) (type span) : CallFree ⟨type, .snd value, span⟩
  | inl {value} (pure : CallFree value) (type target span) : CallFree ⟨type, .inl target value, span⟩
  | inr {value} (pure : CallFree value) (type target span) : CallFree ⟨type, .inr target value, span⟩
  | inK {value} (pure : CallFree value) (index type target span) :
      CallFree ⟨type, .inK index target value, span⟩
  | conditional {test yes no} (testPure : CallFree test) (yesPure : CallFree yes) (noPure : CallFree no)
      (type target span) : CallFree ⟨type, .ifThen target test yes no, span⟩

theorem CallFree.preserves {σ : Type} (functions : List Function) (effects : Semantics.ExternalSemantics σ)
    (signatures : List Signature) (external : σ → Core.Store → Prop) {expression : Expr}
    (eligible : CallFree expression) :
    StatementCorrespondence.NormalExprPreserves functions effects signatures external expression := by
  induction eligible with
  | word type text span => exact PureExpressionCorrespondence.word functions effects signatures external type text span
  | bool type value span => exact PureExpressionCorrespondence.bool functions effects signatures external type value span
  | unit type span => exact PureExpressionCorrespondence.unit functions effects signatures external type span
  | var type name span => exact PureExpressionCorrespondence.read functions effects signatures external type name span
  | pair _ _ type span leftIH rightIH => exact PureExpressionCorrespondence.pair leftIH rightIH type span
  | fst _ type span ih => exact PureExpressionCorrespondence.projection ih false type span
  | snd _ type span ih => exact PureExpressionCorrespondence.projection ih true type span
  | inl _ type target span ih => exact PureExpressionCorrespondence.injection ih false type target span
  | inr _ type target span ih => exact PureExpressionCorrespondence.injection ih true type target span
  | inK _ index type target span ih => exact PureExpressionCorrespondence.indexedInjection ih index type target span
  | conditional _ _ _ type target span testIH yesIH noIH =>
      exact PureExpressionCorrespondence.conditional testIH yesIH noIH type target span

def CallFreeStatement (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value => CallFree value
  | _ => False

theorem CallFreeStatement.straightLine {σ : Type} (functions : List Function)
    (effects : Semantics.ExternalSemantics σ) (signatures : List Signature)
    (external : σ → Core.Store → Prop) {statement : Stmt} (eligible : CallFreeStatement statement) :
    StatementCorrespondence.StraightLine functions effects signatures external statement := by
  cases statement with | mk kind span =>
  cases kind <;> simp only [CallFreeStatement, StatementCorrespondence.StraightLine] at eligible ⊢
  all_goals try first
    | exact eligible
    | exact eligible.preserves functions effects signatures external
  rename_i lhs rhs
  cases lhs with | mk type kind span =>
  cases kind
  all_goals first
    | exact eligible
    | exact eligible.preserves functions effects signatures external

/-- Accepted public inputs and a syntactically call-free function determine
the same normal result and local heap in independent Hull execution and every
finite public Core resume chain. Source parameters and Core administrative
cells are initialized by the real parser/compiler path. -/
theorem prepare_callFree_function_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {inputs : List String} {compilationFuel : Nat} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ statement ∈ function.body, CallFreeStatement statement)
    (initialExternal : σ) :
    ∃ sources, ScalarExecution.InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction [function] effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  apply StatementCorrespondence.prepare_single_function_resumes functions accepted
    (fun own _ statement member => (eligible statement member).straightLine [function] effects [own]
      (fun _ _ => True)) initialExternal

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PureFunctionCorrespondence
/-! Syntactic eligibility for pure Hull expressions, including nested builtin
calls. Actual signature compilation establishes name resolution, so the public
function theorem requires no user-supplied expression preservation proof. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence

/-- The source and compiled signature tables expose the same function names. -/
def SignatureNames (functions : List Function) (signatures : List Signature) : Prop :=
  signatures.map Signature.name = functions.map Function.name

theorem SignatureNames.compiled {fuel : Nat} {functions : List Function} {signatures : List Signature}
    (compiled : functions.mapM (signature fuel) = .ok signatures) : SignatureNames functions signatures := by
  induction functions generalizing signatures with
  | nil => cases compiled; rfl
  | cons function rest ih =>
      simp only [List.mapM_cons] at compiled
      obtain ⟨own, ownCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨others, othersCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      have head := signature_name ownCompiled
      have tail := ih othersCompiled
      change own.name :: others.map Signature.name = function.name :: rest.map Function.name
      rw [head]
      exact congrArg (List.cons function.name) tail

theorem SignatureNames.single {fuel : Nat} {function : Function} {own : Signature}
    (compiled : signature fuel function = .ok own) : SignatureNames [function] [own] := by
  exact congrArg (fun name => [name]) (signature_name compiled)

theorem SignatureNames.absent {functions : List Function} {signatures : List Signature}
    (names : SignatureNames functions signatures) {name : String}
    (absent : functions.find? (·.name == name) = none) : signatures.find? (·.name == name) = none := by
  simp only [List.find?_eq_none, beq_iff_eq] at absent ⊢
  intro selected member equal
  have inNames : selected.name ∈ signatures.map Signature.name := List.mem_map.mpr ⟨selected, member, rfl⟩
  rw [names] at inNames
  obtain ⟨function, functionMember, sameName⟩ := List.mem_map.mp inNames
  exact absent function functionMember (sameName.trans equal)

/-- These expressions use only local values and pure builtins. A builtin name
may not be shadowed by a source function, matching independent source lookup. -/
inductive PureExpression (functions : List Function) : Expr → Prop where
  | word (type text span) : PureExpression functions ⟨type, .word text, span⟩
  | bool (type value span) : PureExpression functions ⟨type, .bool value, span⟩
  | unit (type span) : PureExpression functions ⟨type, .unit, span⟩
  | var (type name span) : PureExpression functions ⟨type, .var name, span⟩
  | pair {left right} (leftPure : PureExpression functions left) (rightPure : PureExpression functions right)
      (type span) : PureExpression functions ⟨type, .pair left right, span⟩
  | fst {value} (pure : PureExpression functions value) (type span) :
      PureExpression functions ⟨type, .fst value, span⟩
  | snd {value} (pure : PureExpression functions value) (type span) :
      PureExpression functions ⟨type, .snd value, span⟩
  | inl {value} (pure : PureExpression functions value) (type target span) :
      PureExpression functions ⟨type, .inl target value, span⟩
  | inr {value} (pure : PureExpression functions value) (type target span) :
      PureExpression functions ⟨type, .inr target value, span⟩
  | inK {value} (pure : PureExpression functions value) (index type target span) :
      PureExpression functions ⟨type, .inK index target value, span⟩
  | conditional {test yes no} (testPure : PureExpression functions test)
      (yesPure : PureExpression functions yes) (noPure : PureExpression functions no)
      (type target span) : PureExpression functions ⟨type, .ifThen target test yes no, span⟩
  | call {name arguments operation}
      (classified : PureCallCorrespondence.pureBuiltin? name = some operation)
      (notFunction : functions.find? (·.name == name) = none)
      (argumentsPure : ∀ argument ∈ arguments, PureExpression functions argument)
      (type span) : PureExpression functions ⟨type, .call name arguments, span⟩

theorem PureExpression.preserves {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures) (external : σ → Core.Store → Prop)
    {expression : Expr} (eligible : PureExpression functions expression) :
    StatementCorrespondence.NormalExprPreserves functions effects signatures external expression := by
  induction eligible with
  | word type text span => exact PureExpressionCorrespondence.word functions effects signatures external type text span
  | bool type value span => exact PureExpressionCorrespondence.bool functions effects signatures external type value span
  | unit type span => exact PureExpressionCorrespondence.unit functions effects signatures external type span
  | var type name span => exact PureExpressionCorrespondence.read functions effects signatures external type name span
  | pair _ _ type span leftIH rightIH => exact PureExpressionCorrespondence.pair leftIH rightIH type span
  | fst _ type span ih => exact PureExpressionCorrespondence.projection ih false type span
  | snd _ type span ih => exact PureExpressionCorrespondence.projection ih true type span
  | inl _ type target span ih => exact PureExpressionCorrespondence.injection ih false type target span
  | inr _ type target span ih => exact PureExpressionCorrespondence.injection ih true type target span
  | inK _ index type target span ih => exact PureExpressionCorrespondence.indexedInjection ih index type target span
  | conditional _ _ _ type target span testIH yesIH noIH =>
      exact PureExpressionCorrespondence.conditional testIH yesIH noIH type target span
  | call classified notFunction _ type span ih =>
      exact PureCallCorrespondence.call classified notFunction (names.absent notFunction) ih type span

def PureStatement (functions : List Function) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value => PureExpression functions value
  | _ => False

theorem PureStatement.straightLine {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures) (external : σ → Core.Store → Prop)
    {statement : Stmt} (eligible : PureStatement functions statement) :
    StatementCorrespondence.StraightLine functions effects signatures external statement := by
  cases statement with | mk kind span =>
  cases kind <;> simp only [PureStatement, StatementCorrespondence.StraightLine] at eligible ⊢
  all_goals try first
    | exact eligible
    | exact eligible.preserves effects names external
  rename_i lhs rhs
  cases lhs with | mk type kind span =>
  cases kind
  all_goals first
    | exact eligible
    | exact eligible.preserves effects names external

/-- Actual accepted public preparation supplies source arguments and initializes
all Core administrative cells. Pure syntax then determines the same normal
source result and represented source heap after every public resume chain. -/
theorem prepare_pure_function_resumes {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {inputs : List String} {compilationFuel : Nat} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ statement ∈ function.body, PureStatement [function] statement)
    (initialExternal : σ) :
    ∃ sources, ScalarExecution.InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction [function] effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧
          HeapRel world final.heap finalStore ∧
          ∀ fuel additional last, ScalarExecution.Resumes (ScalarExecution.run prepared fuel) additional last →
            (last = .done targetValue finalStore ↔ required ≤ fuel + additional) ∧
            ((∃ checkpoint, last = .outOfFuel checkpoint) ↔ fuel + additional < required) := by
  exact StatementCorrespondence.prepare_single_function_resumes functions accepted
    (fun own compiled statement member => (eligible statement member).straightLine effects
      (SignatureNames.single compiled) (fun _ _ => True)) initialExternal

/-- With sufficient fuel the actual public runner returns the independently
specified source result and heap for a syntactically pure function. -/
theorem prepare_pure_function_run {σ : Type} {effects : Semantics.ExternalSemantics σ}
    {program : Program} {function : Function} (functions : program.functions = [function])
    {entry : String} {inputs : List String} {compilationFuel : Nat} {prepared : ScalarExecution.Prepared}
    (accepted : ScalarExecution.prepare program entry inputs compilationFuel = .ok prepared)
    (eligible : ∀ statement ∈ function.body, PureStatement [function] statement)
    (initialExternal : σ) :
    ∃ sources, ScalarExecution.InputsRel prepared.compiled.parameters inputs sources ∧
      ∀ sourceResult final,
        Semantics.EvalFunction [function] effects function sources ⟨[], initialExternal⟩ sourceResult final →
        (∃ value, sourceResult = .value value) →
        ∃ world targetValue finalStore required,
          ResultRel prepared.compiled.result sourceResult targetValue ∧ HeapRel world final.heap finalStore ∧
          ∀ fuel, required ≤ fuel → ScalarExecution.run prepared fuel = .done targetValue finalStore := by
  obtain ⟨sources, inputsRelated, execute⟩ := StatementCorrespondence.prepare_single_function functions accepted
    (fun own compiled statement member => (eligible statement member).straightLine effects
      (SignatureNames.single compiled) (fun _ _ => True)) initialExternal
  refine ⟨sources, inputsRelated, ?_⟩
  intro result final evaluated normal
  obtain ⟨world, target, finalStore, related, executed, heap⟩ := execute result final evaluated normal
  obtain ⟨required, completed⟩ := ScalarExecution.evaluation_run_complete executed
  exact ⟨world, target, finalStore, required, related, heap, completed⟩

end Solcore.Frontend.RustHull.Correspondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
/-! Structural Hull expressions can contain named calls while retaining their
actual installed function cells. Local and global environments are shifted
together under administrative binders; heap changes remain exact. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
open Correspondence StatementCorrespondence NamedCallCorrespondence

theorem pure {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures)
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {expression : Expr} (eligible : PureExpression functions expression) :
    ContextualExprPreserves functions effects signatures codes locations captured expression :=
  contextual_of_normal (eligible.preserves effects names (fun _ store => InstalledGlobals codes locations captured store))

private theorem pair_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {left right : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment ⟨type, .pair left right, span⟩
      initial (.value sourceValue) final) :
    ∃ leftValue rightValue middle,
      sourceValue = .pair leftValue rightValue ∧
      Semantics.EvalExpr functions effects sourceEnvironment left initial (.value leftValue) middle ∧
      Semantics.EvalExpr functions effects sourceEnvironment right middle (.value rightValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherLeft otherRight leftValue rightResult kind first second
  cases rightResult with
  | fault reason => simp [Semantics.Result.map] at resultEq
  | value rightValue =>
      simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
      exact ⟨leftValue, rightValue, resultEq, middle, first, second⟩

theorem pair_rename (leftType rightType : Core.Ty) (left right : Core.Expr)
    (mapping : Core.Renaming) :
    (Core.LocalSequence.pair leftType rightType left right).rename mapping =
      Core.LocalSequence.pair leftType rightType (left.rename mapping) (right.rename mapping) := by
  simp [Core.LocalSequence.pair, Core.LanguageResult.bind, Core.LanguageResult.success,
    Core.Expr.rename, Core.Renaming.lift]

theorem pair {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {left right : Expr} (leftPreserves : ContextualExprPreserves functions effects signatures codes locations captured left)
    (rightPreserves : ContextualExprPreserves functions effects signatures codes locations captured right)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured ⟨type, .pair left right, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨leftValue, rightValue, middle, rfl, leftSource, rightSource⟩ := pair_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨leftCode, rightCode, leftCompiled, rightCompiled, rfl⟩ :=
        lowerExpression_pair_components compiled
      obtain ⟨leftExtension, targetLeft, middleStore, leftRelated, leftEvaluation, middleHeap, middleExternal⟩ :=
        leftPreserves leftSource leftCompiled environmentRelated globals heap externalRelated
      have middleEnvironment := (environmentRelated.extendWorld leftExtension).prepend [targetLeft]
      obtain ⟨rightExtension, targetRight, finalStore, rightRelated, rightEvaluation, finalHeap, finalExternal⟩ :=
        rightPreserves rightSource rightCompiled middleEnvironment (globals.prepend [targetLeft]) middleHeap middleExternal
      refine ⟨leftExtension ++ rightExtension, .pair targetLeft targetRight, finalStore,
        .pair leftRelated rightRelated, ?_, ?_, finalExternal⟩
      · have renamed : (rightCode.expression.rename mapping).weakenAt 0 =
            rightCode.expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        change Core.Evaluates environment store
          ((Core.LocalSequence.pair leftCode.type rightCode.type
            leftCode.expression rightCode.expression).rename mapping) _ _
        rw [pair_rename]
        apply Core.LocalSequence.pair_success _ _ leftEvaluation
        simpa [renamed] using rightEvaluation
      · simpa only [List.append_assoc] using finalHeap

private theorem projection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .snd operand else .fst operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.projectResult right value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value => exact ⟨value, evaluated, rfl⟩

theorem projection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (right : Bool) (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, if right then .snd operand else .fst operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, projected⟩ := projection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_projection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      rw [operandType] at related
      cases related with
      | pair leftRelated rightRelated =>
          cases right <;> simp only [Semantics.projectResult, Bool.false_eq_true, ↓reduceIte,
            Semantics.Result.value.injEq] at projected ⊢
          all_goals cases projected
          · exact ⟨extension, _, finalStore, leftRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.first (.var rfl))),
              finalHeap, finalExternal⟩
          · exact ⟨extension, _, finalStore, rightRelated,
              Core.LanguageResult.bind_success _ evaluation (.inRight (.second (.var rfl))),
              finalHeap, finalExternal⟩

private theorem injection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr}
    {span : Option Span} {sourceValue : Semantics.Value} (right : Bool)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, if right then .inr target operand else .inl target operand, span⟩
      initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      sourceValue = (if right then .inr value else .inl value) := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases right <;> cases evaluated <;> simp_all
  all_goals
    rename_i otherTarget otherOperand operandResult kind evaluated
    cases operandResult with
    | fault reason => simp [Semantics.Result.bind] at resultEq
    | value value =>
        cases found : Semantics.shape otherTarget with
        | none => simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
        | some shape =>
            cases shape <;> simp [Semantics.Result.bind, Semantics.sumInjectionResult, found] at resultEq
            exact ⟨value, evaluated, resultEq⟩

theorem injection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (right : Bool) (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, if right then .inr target operand else .inl target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, rfl⟩ := injection_source right evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, leftType, rightType, _, operandCompiled, operandType, rfl⟩ :=
        lowerExpression_injection_components right compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      rw [operandType] at related
      cases right <;> simp only [Bool.false_eq_true, ↓reduceIte] at related ⊢
      · exact ⟨extension, .inLeft rightType targetValue, finalStore, .inl related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inLeft (.var rfl))),
          finalHeap, finalExternal⟩
      · exact ⟨extension, .inRight leftType targetValue, finalStore, .inr related,
          Core.LanguageResult.bind_success _ evaluation (.inRight (.inRight (.var rfl))),
          finalHeap, finalExternal⟩

private theorem conditional_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {conditionExpr yes no : Expr}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .ifThen target conditionExpr yes no, span⟩ initial (.value sourceValue) final) :
    ∃ middle value truth,
      Semantics.EvalExpr functions effects sourceEnvironment conditionExpr initial (.value value) middle ∧
      Semantics.condition? value = some truth ∧
      Semantics.EvalExpr functions effects sourceEnvironment (if truth then yes else no)
        middle (.value sourceValue) final := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  case ifTrue => exact ⟨_, _, by assumption, Or.inr ⟨by assumption, by assumption⟩⟩
  case ifFalse => exact ⟨_, _, by assumption, Or.inl ⟨by assumption, by assumption⟩⟩

theorem choose_rename (type : Core.Ty) (conditionExpr yes no : Core.Expr) (mapping : Core.Renaming) :
    (Core.LocalControl.choose type conditionExpr yes no).rename mapping =
      Core.LocalControl.choose type (conditionExpr.rename mapping) (yes.rename mapping) (no.rename mapping) := by
  simp [Core.LocalControl.choose, Core.LanguageResult.bind, Core.Expr.rename, Core.Renaming.lift]

theorem conditional {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {conditionExpr yes no : Expr}
    (conditionPreserves : ContextualExprPreserves functions effects signatures codes locations captured conditionExpr)
    (yesPreserves : ContextualExprPreserves functions effects signatures codes locations captured yes)
    (noPreserves : ContextualExprPreserves functions effects signatures codes locations captured no)
    (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .ifThen target conditionExpr yes no, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, conditionValue, truth, conditionSource, tested, branchSource⟩ := conditional_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨conditionCode, test, yesCode, noCode, conditionCompiled, testCompiled,
        yesCompiled, noCompiled, yesType, noType, expressionEqual⟩ :=
        lowerExpression_conditional_components compiled
      obtain ⟨conditionExtension, targetCondition, middleStore, conditionRelated,
        conditionEvaluation, middleHeap, middleExternal⟩ :=
        conditionPreserves conditionSource conditionCompiled environmentRelated globals heap externalRelated
      have testEvaluation := ExpressionCorrespondence.condition_evaluates
        testCompiled conditionRelated tested conditionEvaluation
      have middleEnvironment :=
        (environmentRelated.extendWorld conditionExtension).prepend [.bool truth]
      have branchPreserves : ContextualExprPreserves functions effects signatures codes locations captured
          (if truth then yes else no) := by cases truth <;> assumption
      have branchCompiled : lowerExpression fuel signatures scope (if truth then yes else no) =
          .ok (if truth then yesCode else noCode) := by cases truth <;> assumption
      obtain ⟨branchExtension, targetValue, finalStore, related, branchEvaluation, finalHeap, finalExternal⟩ :=
        branchPreserves branchSource branchCompiled middleEnvironment (globals.prepend [.bool truth]) middleHeap middleExternal
      refine ⟨conditionExtension ++ branchExtension, targetValue, finalStore, ?_, ?_, ?_, finalExternal⟩
      · cases truth <;> simpa only [Bool.false_eq_true, ↓reduceIte, yesType, noType] using related
      · have renamed (expression : Core.Expr) : (expression.rename mapping).weakenAt 0 =
            expression.rename (fun index => 1 + mapping index) := by
          simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
          congr 1
          funext index
          simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
        rw [expressionEqual, choose_rename]
        cases truth with
        | false =>
            apply Core.LocalControl.choose_false _ testEvaluation
            simpa [renamed] using branchEvaluation
        | true =>
            apply Core.LocalControl.choose_true _ testEvaluation
            simpa [renamed] using branchEvaluation
      · simpa only [List.append_assoc] using finalHeap

private theorem indexedInjection_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {type target : Ty} {operand : Expr} {index : Nat}
    {span : Option Span} {sourceValue : Semantics.Value}
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .inK index target operand, span⟩ initial (.value sourceValue) final) :
    ∃ value, Semantics.EvalExpr functions effects sourceEnvironment operand initial (.value value) final ∧
      Semantics.injectionResult index target value = .value sourceValue := by
  generalize resultEq : Semantics.Result.value sourceValue = result at evaluated
  cases evaluated <;> simp_all
  rename_i otherIndex otherTarget otherOperand operandResult kind evaluated
  cases operandResult with
  | fault reason => simp [Semantics.Result.bind] at resultEq
  | value value => exact ⟨value, evaluated, rfl⟩

theorem indexedInjection {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {operand : Expr} (preserves : ContextualExprPreserves functions effects signatures codes locations captured operand)
    (index : Nat) (type target : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .inK index target operand, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨value, sourceEvaluation, sourceResult⟩ := indexedInjection_source evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨operandCode, targetType, injected, targetCompiled, operandCompiled, injectionCompiled, rfl⟩ :=
        lowerExpression_indexedInjection_components compiled
      obtain ⟨extension, targetValue, finalStore, related, evaluation, finalHeap, finalExternal⟩ :=
        preserves sourceEvaluation operandCompiled environmentRelated globals heap externalRelated
      obtain ⟨shape, sourceShape, targetShape⟩ := lowerType_shape targetCompiled
      rw [← targetShape] at injectionCompiled
      have supplied : Core.Evaluates (targetValue :: environment) finalStore
          ((Core.Expr.var 0).rename (Core.Renaming.lift mapping)) targetValue finalStore := .var rfl
      obtain ⟨sourceInjected, targetInjected, sourceInjection, injectionRelated, injectionEvaluation⟩ :=
        PureExpressionCorrespondence.inject_evaluates shape related injectionCompiled supplied
      have same : sourceInjected = sourceValue := by
        simpa [Semantics.injectionResult, Semantics.inject?, sourceShape, sourceInjection] using sourceResult
      subst sourceInjected
      refine ⟨extension, targetInjected, finalStore, ?_, ?_, finalHeap, finalExternal⟩
      · simpa only [targetShape] using injectionRelated
      · exact Core.LanguageResult.bind_success _ evaluation (.inRight injectionEvaluation)

open PureCallCorrespondence ScalarExecution

private theorem exprs_cons {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {argument : Expr} {rest : List Expr} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment (argument :: rest)
      initial (.value sources) final) :
    ∃ source values middle, sources = source :: values ∧
      Semantics.EvalExpr functions effects sourceEnvironment argument initial (.value source) middle ∧
      Semantics.EvalExprs functions effects sourceEnvironment rest middle (.value values) final := by
  generalize resultEq : Semantics.Result.value sources = result at evaluated
  cases evaluated with
  | cons head tail =>
      rename_i middle source result
      cases result with
      | fault reason => simp [Semantics.Result.map] at resultEq
      | value values =>
          simp only [Semantics.Result.map, Semantics.Result.value.injEq] at resultEq
          exact ⟨source, values, middle, resultEq, head, tail⟩
  | fault => cases resultEq

theorem arguments_preserve {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment} {arguments : List Expr}
    (preserves : ∀ argument ∈ arguments, ContextualExprPreserves functions effects signatures codes locations captured argument)
    {sourceEnvironment : Semantics.Environment} {initial final : Semantics.State σ}
    {sources : List Semantics.Value}
    (evaluated : Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value sources) final)
    {fuel : Nat} {scope : Scope} {lowered : List Lowered}
    (compiled : arguments.mapM (lowerExpression fuel signatures scope) = .ok lowered)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (environmentRelated : EnvironmentRel world sourceEnvironment scope mapping environment)
    (globals : GlobalEnvironmentRel codes locations scope mapping environment)
    (heap : HeapRel world initial.heap store) (externalRelated : InstalledGlobals codes locations captured store) :
    ∃ extension targets finalStore,
      ArgumentsRel lowered sources targets ∧
      Core.Evaluates environment store ((packArguments lowered).expression.rename mapping)
        (.inRight .word (bundleValues targets)) finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ InstalledGlobals codes locations captured finalStore := by
  induction arguments generalizing initial final sources lowered world mapping environment store with
  | nil =>
      cases compiled
      cases evaluated
      exact ⟨[], [], store, .nil, .inRight .unit, by simpa using heap, externalRelated⟩
  | cons argument rest ih =>
      obtain ⟨source, sources, middle, rfl, head, tail⟩ := exprs_cons evaluated
      simp only [List.mapM_cons] at compiled
      obtain ⟨headCode, headCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
      obtain ⟨tailCode, tailCompiled, returned⟩ := lower_bind_eq_ok.mp compiled
      cases returned
      obtain ⟨headExtension, target, middleStore, related, headEvaluation, middleHeap, middleExternal⟩ :=
        preserves argument (by simp) head headCompiled environmentRelated globals heap externalRelated
      cases rest with
      | nil =>
          cases tailCompiled
          cases tail
          exact ⟨headExtension, [target], middleStore, .cons related .nil,
            headEvaluation, middleHeap, middleExternal⟩
      | cons next rest =>
          have tailPreserves : ∀ value ∈ next :: rest,
              ContextualExprPreserves functions effects signatures codes locations captured value := by
            intro value member
            exact preserves value (by simp [member])
          have middleEnvironment := (environmentRelated.extendWorld headExtension).prepend [target]
          obtain ⟨tailExtension, targets, finalStore, tailRelated, tailEvaluation, finalHeap, finalExternal⟩ :=
            ih tailPreserves tail tailCompiled middleEnvironment (globals.prepend [target]) middleHeap middleExternal
          have nonempty : tailCode ≠ [] := by
            intro empty
            subst tailCode
            simp only [List.mapM_cons] at tailCompiled
            obtain ⟨_, _, tailCompiled⟩ := lower_bind_eq_ok.mp tailCompiled
            obtain ⟨_, _, returned⟩ := lower_bind_eq_ok.mp tailCompiled
            cases returned
          have targetsNonempty : targets ≠ [] := by
            intro empty
            subst targets
            cases tailRelated
            exact nonempty rfl
          refine ⟨headExtension ++ tailExtension, target :: targets, finalStore,
            .cons related tailRelated, ?_, ?_, finalExternal⟩
          · have renamed : ((packArguments tailCode).expression.rename mapping).weakenAt 0 =
                (packArguments tailCode).expression.rename (fun index => 1 + mapping index) := by
              simp only [← Core.Expr.rename_insertion, Core.Expr.rename_comp]
              congr 1
              funext index
              simp [Core.Renaming.comp, Core.Renaming.insertion, Nat.add_comm]
            cases tailCode with
            | nil => exact (nonempty rfl).elim
            | cons nextCode restCode =>
                change Core.Evaluates environment store
                  ((Core.LocalSequence.pair headCode.type (packArguments (nextCode :: restCode)).type
                    headCode.expression (packArguments (nextCode :: restCode)).expression).rename mapping) _ _
                rw [pair_rename]
                have tailEvaluation' : Core.Evaluates (target :: environment) middleStore
                    (((packArguments (nextCode :: restCode)).expression.rename mapping).weakenAt 0)
                    (.inRight .word (bundleValues targets)) finalStore := by
                  rw [renamed]
                  exact tailEvaluation
                have paired := Core.LocalSequence.pair_success headCode.type
                  (packArguments (nextCode :: restCode)).type headEvaluation tailEvaluation'
                cases targets with
                | nil => exact (targetsNonempty rfl).elim
                | cons firstTarget restTargets => exact paired
          · simpa only [List.append_assoc] using finalHeap

theorem namedCall {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat}
    {captured : Core.Environment} {name : String} {function : Function} {code : GlobalCode} {index : Nat}
    (foundFunction : functions.find? (·.name == name) = some function)
    (foundSignature : signatures.find? (·.name == name) = some code.own)
    (foundCode : codes[index]? = some code)
    (preservesFunction : ∀ sources initial final source,
      FunctionExecutionPreserves functions effects codes locations captured function code index sources initial final source)
    {arguments : List Expr}
    (preservesArguments : ∀ argument ∈ arguments,
      ContextualExprPreserves functions effects signatures codes locations captured argument)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured
      ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final sourceValue evaluated
  obtain ⟨middle, sources, argumentsSource, called⟩ := call_source evaluated
  have functionSource := call_function_source foundFunction called
  intro fuel scope lowered compiled world mapping environment store locals globals heap installed
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨argumentCodes, functionCode, argumentsCompiled, argumentTypes, functionCompiled, _, rfl⟩ :=
        call_components foundSignature compiled
      have foundName : (code.own.name == name) = true :=
        List.find?_some (p := fun (own : Signature) => own.name == name) foundSignature
      have sameName : code.own.name = name := by simpa only [beq_iff_eq] using foundName
      rw [← sameName] at functionCompiled
      have functionEvaluation := global_read_evaluates foundCode globals installed functionCompiled
      let closure := Core.Value.closure (bundleType code.own.parameters)
        (Core.LanguageResult.resultType code.own.result) (code.body.rename (globalShift index).lift)
        (installationEnvironment captured index)
      have argumentLocals := locals.prepend [closure]
      obtain ⟨argumentExtension, targets, argumentStore, argumentsRelated,
        argumentsEvaluation, argumentHeap, argumentGlobals⟩ :=
        arguments_preserve preservesArguments argumentsSource argumentsCompiled argumentLocals
          (globals.prepend [closure]) heap installed
      have values : ValuesRel code.own.parameters sources targets :=
        argumentTypes ▸ ArgumentsRel.values argumentsRelated
      obtain ⟨callExtension, target, finalStore, related, bodyEvaluation, finalHeap, finalGlobals⟩ :=
        preservesFunction sources middle final sourceValue functionSource values argumentHeap argumentGlobals
      exact ⟨argumentExtension ++ callExtension, target, finalStore, related,
        call_evaluates functionEvaluation argumentsEvaluation bodyEvaluation,
        by simpa only [List.append_assoc] using finalHeap, finalGlobals⟩

private theorem builtin_source {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {sourceEnvironment : Semantics.Environment}
    {initial final : Semantics.State σ} {name : String} {type : Ty} {arguments : List Expr}
    {span : Option Span} {source : Semantics.Value} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (evaluated : Semantics.EvalExpr functions effects sourceEnvironment
      ⟨type, .call name arguments, span⟩ initial (.value source) final) :
    ∃ values, Semantics.EvalExprs functions effects sourceEnvironment arguments initial (.value values) final ∧
      Semantics.primitive? name type values = some (.value source) := by
  generalize resultEq : Semantics.Result.value source = result at evaluated
  cases evaluated <;> simp_all
  rename_i middle otherName otherArguments values kind argumentsEvaluated called
  cases called with
  | function selected _ =>
      exact (notFunction _ (List.mem_of_find?_eq_some selected)
        (by simpa only [beq_iff_eq] using List.find?_some selected)).elim
  | primitive _ computed => exact ⟨values, argumentsEvaluated, computed⟩
  | external _ notPrimitive _ =>
      have known := pureBuiltin_known classified type values
      rw [notPrimitive] at known
      cases known

private theorem builtin_components {fuel : Nat} {signatures : List Signature} {scope : Scope}
    {name : String} {type : Ty} {arguments : List Expr} {span : Option Span} {lowered : Lowered}
    (notSignature : signatures.find? (·.name == name) = none)
    (compiled : lowerExpression (fuel + 1) signatures scope ⟨type, .call name arguments, span⟩ = .ok lowered) :
    ∃ expected codes, lowerType (fuel + 1) type = .ok expected ∧
      arguments.mapM (lowerExpression fuel signatures scope) = .ok codes ∧
      lowerBuiltin scope name expected codes = .ok lowered := by
  simp only [lowerExpression] at compiled
  obtain ⟨expected, typeCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨codes, argumentsCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  simp only [notSignature] at compiled
  obtain ⟨result, builtinCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨checked, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  cases returned
  exact ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩

/-- A source call to a pure builtin is compositional through the public
expression lowerer. The only induction premises concern its source arguments;
function resolution and the complete builtin dispatch are proved here. -/
theorem builtinCall {σ : Type} {functions : List Function} {effects : Semantics.ExternalSemantics σ}
    {signatures : List Signature} {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    {name : String} {arguments : List Expr} {operation : PureBuiltin}
    (classified : pureBuiltin? name = some operation)
    (notFunction : functions.find? (·.name == name) = none)
    (notSignature : signatures.find? (·.name == name) = none)
    (preserves : ∀ argument ∈ arguments, ContextualExprPreserves functions effects signatures codes locations captured argument)
    (type : Ty) (span : Option Span) :
    ContextualExprPreserves functions effects signatures codes locations captured ⟨type, .call name arguments, span⟩ := by
  intro sourceEnvironment initial final source evaluated
  obtain ⟨values, argumentsEvaluated, computed⟩ := builtin_source classified notFunction evaluated
  intro fuel scope lowered compiled world mapping environment store environmentRelated globals heap externalRelated
  cases fuel with
  | zero => simp [lowerExpression, fail] at compiled
  | succ fuel =>
      obtain ⟨expected, codes, typeCompiled, argumentsCompiled, builtinCompiled⟩ :=
        builtin_components notSignature compiled
      obtain ⟨extension, targets, finalStore, related, argumentsEvaluation, finalHeap, finalExternal⟩ :=
        arguments_preserve preserves argumentsEvaluated argumentsCompiled environmentRelated globals heap externalRelated
      obtain ⟨target, resultRelated, resultEvaluation⟩ :=
        builtin_preserves classified typeCompiled builtinCompiled computed related argumentsEvaluation
      exact ⟨extension, target, finalStore, resultRelated, resultEvaluation, finalHeap, finalExternal⟩

end Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RenamedFunctionBodyCorrespondence
/-! Real function bodies retain their source meaning under the administrative
renaming introduced by global closure installation. Parameter cells are still
derived from the supplied values and the actual initializer. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.StatementCorrespondence
open Correspondence ScalarExecution

theorem lowerFunction_body_renamed {σ : Type} {functions : List Function}
    {effects : Semantics.ExternalSemantics σ} {signatures : List Signature}
    {external : σ → Core.Store → Prop} (frame : ExternalFrame external)
    {typeFuel fuel : Nat} {scope : Scope} {function : Function} {own : Signature}
    {body : Core.Expr}
    (signatureCompiled : signature typeFuel function = .ok own)
    (compiled : lowerFunction fuel signatures scope function own =
      .ok (.lambda (bundleType own.parameters) (Core.LanguageResult.resultType own.result) body))
    (eligible : ∀ statement ∈ function.body, StraightLine functions effects signatures external statement)
    {sources : List Semantics.Value} {targets : List Core.Value}
    (values : ValuesRel own.parameters sources targets)
    {initial final : Semantics.State σ} {sourceResult : Semantics.Result Semantics.Value}
    (sourceEvaluated : Semantics.EvalFunction functions effects function sources initial sourceResult final)
    (normal : ∃ value, sourceResult = .value value)
    {world : World} {mapping : Core.Renaming} {environment : Core.Environment} {store : Core.Store}
    (heapRelated : HeapRel world initial.heap store)
    (externalRelated : external initial.external store) :
    ∃ extension targetValue finalStore,
      ResultRel own.result sourceResult targetValue ∧
      Core.Evaluates (bundleValues targets :: environment) store (body.rename mapping.lift)
        targetValue finalStore ∧
      HeapRel (world ++ extension) final.heap finalStore ∧ external final.external finalStore := by
  cases sourceEvaluated with
  | arity mismatch => obtain ⟨value, same⟩ := normal; contradiction
  | body bound sourceExecuted =>
      rename_i allocated sourceEnvironment control
      have controlNormal : NormalControl control := by
        obtain ⟨value, same⟩ := normal
        cases control <;> first | trivial | simp [Semantics.finishFunction] at same
      obtain ⟨arity, resultCompiled⟩ := signature_components signatureCompiled
      obtain ⟨statements, statementsCompiled, bodyShape⟩ := lowerFunction_components compiled
      have bodyEqual := Core.Expr.lambda.inj bodyShape
      rcases bodyEqual with ⟨_, _, rfl⟩
      have emptyEnvironment : EnvironmentRel world [] (scope.temporary (bundleType own.parameters))
          mapping.lift (bundleValues targets :: environment) := by
        intro name sourceLocation binding index found looked
        simp [Semantics.lookupLocation] at found
      obtain ⟨parameterExtension, sourceEnvironment', allocated', environment', store',
          sourceBound, cells, parametersRelated, allocatedHeap, allocatedExternal⟩ :=
        initialize_parameters_renamed values arity emptyEnvironment heapRelated externalRelated
          (fun _ _ _ _ hypothesis => frame.allocate hypothesis)
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (bound.symm.trans sourceBound))
      obtain ⟨extension, targetValue, finalStore, related, executed, finalHeap, finalExternal⟩ :=
        straight_line_body frame resultCompiled statementsCompiled eligible sourceExecuted controlNormal
          parametersRelated allocatedHeap allocatedExternal
      have initialized := cells.evaluates_renamed (allValues := targets) (start := 0)
        (mapping := mapping.lift) rfl
        (fun index value found => by simpa only [Nat.zero_add] using found) executed
      refine ⟨parameterExtension ++ extension, targetValue, finalStore, related, ?_, ?_, finalExternal⟩
      · simpa only [parameterCode, values.length.2] using initialized
      · simpa only [List.append_assoc] using finalHeap

end Solcore.Frontend.RustHull.StatementCorrespondence
end

section
-- leanmerge: from Solcore.Frontend.RustHull.PublicProgramCorrespondence
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
end

section
-- leanmerge: from Solcore.Frontend.RustHull.RankedExpressionCorrespondence
/-! A syntactic acyclic Hull fragment. Named calls decrease an explicit natural
rank; pure builtins and structural operations retain the current bound. The
function induction premise concerns only lower-rank installed callees. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.Correspondence
open NamedCallCorrespondence

inductive RankedExpression (functions : List Function) (rank : String → Nat) (bound : Nat) : Expr → Prop where
  | word (type text span) : RankedExpression functions rank bound ⟨type, .word text, span⟩
  | bool (type value span) : RankedExpression functions rank bound ⟨type, .bool value, span⟩
  | unit (type span) : RankedExpression functions rank bound ⟨type, .unit, span⟩
  | var (type name span) : RankedExpression functions rank bound ⟨type, .var name, span⟩
  | pair {left right} (leftRanked : RankedExpression functions rank bound left)
      (rightRanked : RankedExpression functions rank bound right) (type span) :
      RankedExpression functions rank bound ⟨type, .pair left right, span⟩
  | fst {value} (ranked : RankedExpression functions rank bound value) (type span) :
      RankedExpression functions rank bound ⟨type, .fst value, span⟩
  | snd {value} (ranked : RankedExpression functions rank bound value) (type span) :
      RankedExpression functions rank bound ⟨type, .snd value, span⟩
  | inl {value} (ranked : RankedExpression functions rank bound value) (type target span) :
      RankedExpression functions rank bound ⟨type, .inl target value, span⟩
  | inr {value} (ranked : RankedExpression functions rank bound value) (type target span) :
      RankedExpression functions rank bound ⟨type, .inr target value, span⟩
  | inK {value} (ranked : RankedExpression functions rank bound value) (index type target span) :
      RankedExpression functions rank bound ⟨type, .inK index target value, span⟩
  | conditional {test yes no} (testRanked : RankedExpression functions rank bound test)
      (yesRanked : RankedExpression functions rank bound yes) (noRanked : RankedExpression functions rank bound no)
      (type target span) : RankedExpression functions rank bound ⟨type, .ifThen target test yes no, span⟩
  | builtin {name arguments operation}
      (classified : PureCallCorrespondence.pureBuiltin? name = some operation)
      (notFunction : functions.find? (·.name == name) = none)
      (argumentsRanked : ∀ argument ∈ arguments, RankedExpression functions rank bound argument)
      (type span) : RankedExpression functions rank bound ⟨type, .call name arguments, span⟩
  | named {name arguments function}
      (foundFunction : functions.find? (·.name == name) = some function)
      (decreases : rank function.name < bound)
      (argumentsRanked : ∀ argument ∈ arguments, RankedExpression functions rank bound argument)
      (type span) : RankedExpression functions rank bound ⟨type, .call name arguments, span⟩

theorem PureExpression.ranked {functions : List Function} {expression : Expr}
    (eligible : PureExpression functions expression) (rank : String → Nat) (bound : Nat) :
    RankedExpression functions rank bound expression := by
  induction eligible with
  | word type text span => exact .word type text span
  | bool type value span => exact .bool type value span
  | unit type span => exact .unit type span
  | var type name span => exact .var type name span
  | pair _ _ type span leftIH rightIH => exact .pair leftIH rightIH type span
  | fst _ type span ih => exact .fst ih type span
  | snd _ type span ih => exact .snd ih type span
  | inl _ type target span ih => exact .inl ih type target span
  | inr _ type target span ih => exact .inr ih type target span
  | inK _ index type target span ih => exact .inK ih index type target span
  | conditional _ _ _ type target span testIH yesIH noIH =>
      exact .conditional testIH yesIH noIH type target span
  | call classified notFunction _ type span ih => exact .builtin classified notFunction ih type span

/-- Source and compiled lookup are explicit premises here; the assembly proof
supplies them from the actual compiler. Only a smaller rank needs a function
execution induction hypothesis. -/
theorem RankedExpression.preserves {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures)
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (resolve : ∀ name function, functions.find? (·.name == name) = some function →
      ∃ (index : Nat) (code : GlobalCode), signatures.find? (·.name == name) = some code.own ∧ codes[index]? = some code)
    {rank : String → Nat} {bound : Nat}
    (lower : ∀ name function code index,
      functions.find? (·.name == name) = some function →
      signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
      rank function.name < bound →
      ∀ sources initial final source,
        FunctionExecutionPreserves functions effects codes locations captured function code index
          sources initial final source)
    {expression : Expr} (eligible : RankedExpression functions rank bound expression) :
    ContextualExprPreserves functions effects signatures codes locations captured expression := by
  induction eligible with
  | word type text span =>
      exact ContextualExpressionCorrespondence.pure effects names (.word type text span)
  | bool type value span =>
      exact ContextualExpressionCorrespondence.pure effects names (.bool type value span)
  | unit type span => exact ContextualExpressionCorrespondence.pure effects names (.unit type span)
  | var type name span => exact ContextualExpressionCorrespondence.pure effects names (.var type name span)
  | pair _ _ type span leftIH rightIH => exact ContextualExpressionCorrespondence.pair leftIH rightIH type span
  | fst _ type span ih => exact ContextualExpressionCorrespondence.projection ih false type span
  | snd _ type span ih => exact ContextualExpressionCorrespondence.projection ih true type span
  | inl _ type target span ih => exact ContextualExpressionCorrespondence.injection ih false type target span
  | inr _ type target span ih => exact ContextualExpressionCorrespondence.injection ih true type target span
  | inK _ index type target span ih => exact ContextualExpressionCorrespondence.indexedInjection ih index type target span
  | conditional _ _ _ type target span testIH yesIH noIH =>
      exact ContextualExpressionCorrespondence.conditional testIH yesIH noIH type target span
  | builtin classified notFunction _ type span ih =>
      exact ContextualExpressionCorrespondence.builtinCall classified notFunction (names.absent notFunction) ih type span
  | @named name arguments function foundFunction decreases _ type span ih =>
      obtain ⟨index, code, foundSignature, foundCode⟩ := resolve name function foundFunction
      exact ContextualExpressionCorrespondence.namedCall foundFunction foundSignature foundCode
        (lower name function code index foundFunction foundSignature foundCode decreases) ih type span

def RankedStatement (functions : List Function) (rank : String → Nat) (bound : Nat) (statement : Stmt) : Prop :=
  match statement.kind with
  | .letDecl _ _ | .comment _ => True
  | .assign ⟨_, .var _, _⟩ value | .expression value | .returnStmt value => RankedExpression functions rank bound value
  | _ => False

theorem RankedStatement.straightLine {σ : Type} {functions : List Function}
    (effects : Semantics.ExternalSemantics σ) {signatures : List Signature}
    (names : SignatureNames functions signatures)
    {codes : List GlobalCode} {locations : Nat → Nat} {captured : Core.Environment}
    (resolve : ∀ name function, functions.find? (·.name == name) = some function →
      ∃ (index : Nat) (code : GlobalCode), signatures.find? (·.name == name) = some code.own ∧ codes[index]? = some code)
    {rank : String → Nat} {bound : Nat}
    (lower : ∀ name function code index,
      functions.find? (·.name == name) = some function →
      signatures.find? (·.name == name) = some code.own → codes[index]? = some code →
      rank function.name < bound →
      ∀ sources initial final source,
        FunctionExecutionPreserves functions effects codes locations captured function code index
          sources initial final source)
    {statement : Stmt} (eligible : RankedStatement functions rank bound statement) :
    ContextualStatementCorrespondence.StraightLine functions effects signatures codes locations captured statement := by
  cases statement with | mk kind span =>
  cases kind <;> simp only [RankedStatement, ContextualStatementCorrespondence.StraightLine] at eligible ⊢
  all_goals try first
    | exact eligible
    | exact eligible.preserves effects names resolve lower
  rename_i lhs rhs
  cases lhs with | mk type kind span =>
  cases kind
  all_goals first
    | exact eligible
    | exact eligible.preserves effects names resolve lower

end Solcore.Frontend.RustHull.Correspondence
end
