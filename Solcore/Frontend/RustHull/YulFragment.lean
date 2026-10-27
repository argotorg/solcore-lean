import Solcore.Frontend.RustHull.Syntax

/-! The inline Yul the common recursive proof accepts: statement lists of `let`
with one name, assignment to one name, expression statements, nested blocks,
`if` and `switch` without string case literals, over literals, variables and
calls of supported names. Effect layers that support no name accept no block. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.YulFragment

mutual
  inductive ExpressionEligible (supported : String → Prop) : YulExpr → Prop where
    | literal {value : YulLit} {span : Option Span} : ExpressionEligible supported ⟨.literal value, span⟩
    | ident {name : YulName} {span : Option Span} : ExpressionEligible supported ⟨.ident name, span⟩
    | call {name : YulName} {arguments : List YulExpr} {span : Option Span} (named : supported name.name)
        (eligible : ArgumentsEligible supported arguments) :
        ExpressionEligible supported ⟨.call name arguments, span⟩

  inductive ArgumentsEligible (supported : String → Prop) : List YulExpr → Prop where
    | nil : ArgumentsEligible supported []
    | cons {argument : YulExpr} {rest : List YulExpr} (head : ExpressionEligible supported argument)
        (tail : ArgumentsEligible supported rest) : ArgumentsEligible supported (argument :: rest)
end

inductive StatementEligible (supported : String → Prop) : YulStmt → Prop where
  | letValue {name : YulName} {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.letDecl [name] (some value), span⟩
  | letZero {name : YulName} {span : Option Span} : StatementEligible supported ⟨.letDecl [name] none, span⟩
  | assign {name : YulName} {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.assign [name] value, span⟩
  | expression {value : YulExpr} {span : Option Span} (eligible : ExpressionEligible supported value) :
      StatementEligible supported ⟨.expression value, span⟩
  | block {body : List YulStmt} {span : Option Span}
      (eligible : ∀ statement ∈ body, StatementEligible supported statement) :
      StatementEligible supported ⟨.block body, span⟩
  | ifThen {condition : YulExpr} {body : List YulStmt} {span : Option Span}
      (tested : ExpressionEligible supported condition)
      (eligible : ∀ statement ∈ body, StatementEligible supported statement) :
      StatementEligible supported ⟨.ifThen condition body, span⟩
  | switch {value : YulExpr} {cases : List YulCase} {defaultBody : Option (List YulStmt)} {span : Option Span}
      (scrutinee : ExpressionEligible supported value) (literals : ∀ arm ∈ cases, ∀ text, arm.lit ≠ .string text)
      (arms : ∀ arm ∈ cases, ∀ statement ∈ arm.body, StatementEligible supported statement)
      (defaults : ∀ statement ∈ defaultBody.getD [], StatementEligible supported statement) :
      StatementEligible supported ⟨.switch value cases defaultBody, span⟩

def Eligible (supported : String → Prop) (body : List YulStmt) : Prop :=
  (∃ name, supported name) ∧ ∀ statement ∈ body, StatementEligible supported statement

theorem Eligible.empty {body : List YulStmt} (eligible : Eligible (fun _ => False) body) : False := by
  obtain ⟨⟨_, impossible⟩, _⟩ := eligible
  exact impossible

end Solcore.Frontend.RustHull.YulFragment
