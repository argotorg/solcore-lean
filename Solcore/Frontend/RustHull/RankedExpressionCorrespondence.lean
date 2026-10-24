import Solcore.Frontend.RustHull.ContextualExpressionCorrespondence
import Solcore.Frontend.RustHull.ContextualStatementCorrespondence

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
