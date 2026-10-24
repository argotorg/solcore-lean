import Solcore.Frontend.RustHull.IndexedInjectionCorrespondence
import Solcore.Frontend.RustHull.PublicFunctionCorrespondence

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
