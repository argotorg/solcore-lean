import Solcore.Frontend.RustHull.CallFreeCorrespondence
import Solcore.Frontend.RustHull.PureCallCorrespondence

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
