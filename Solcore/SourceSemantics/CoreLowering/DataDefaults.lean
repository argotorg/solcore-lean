import Solcore.Frontend.SourceCoreDefaultValue
import Solcore.SourceSemantics.Dynamic.Default
import Solcore.Core.Correspondence

set_option autoImplicit false

namespace Solcore.SourceSemantics.CoreLowering.DataDefaults

open Core Frontend
open SourceCoreDefaultValue

/-- The proxy/mapping identity is the exact catalog lookup. No arbitrary
runtime proxy payload is normalized into this relation. -/
inductive Tree (catalog : SourceCoreDataCatalog.Catalog) :
    TypeSystem.Ty → Dynamic.Value → Value → Expr → Prop where
  | unit : Tree catalog .unit .unit .unit .unit
  | bool : Tree catalog .bool (.bool false) (.bool false) (.bool false)
  | word : Tree catalog .word (.word Word.zero) (.word Word.zero) (.word Word.zero)
  | integer : Tree catalog .integer (.integer 0) (.integer 0) (.integer 0)
  | product {leftTy rightTy : TypeSystem.Ty} {left right : Dynamic.Value}
      {leftValue rightValue : Value} {leftExpr rightExpr : Expr}
      (leftTree : Tree catalog leftTy left leftValue leftExpr)
      (rightTree : Tree catalog rightTy right rightValue rightExpr) :
      Tree catalog (.product leftTy rightTy) (.product left right)
        (.pair leftValue rightValue) (.pair leftExpr rightExpr)
  | proxy (inner : TypeSystem.Ty) (id : DataTypeId)
      (identity : catalog.identity? (.proxy inner) = some id) :
      Tree catalog (.proxy inner) (.proxy inner) (.constructed ⟨id, 0⟩ .unit)
        (.construct ⟨id, 0⟩ .unit)
  | mapping (key value : TypeSystem.Ty) (id : DataTypeId)
      (identity : catalog.identity? (.mapping key value) = some id) :
      Tree catalog (.mapping key value) (.mapping key value [])
        (.constructed ⟨id, 0⟩ .unit) (.construct ⟨id, 0⟩ .unit)
  | comptime {inner : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {expression : Expr}
      (innerTree : Tree catalog inner source value expression) :
      Tree catalog (.comptime inner) source value expression

theorem Tree.meaning {catalog : Catalog} {type : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {expression : Expr}
    (tree : Tree catalog type source value expression) : Dynamic.DefaultValue type source := by
  induction tree with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .product left right
  | proxy inner _ _ => exact .proxy inner
  | mapping key value _ _ => exact .mapping key value
  | comptime _ inner => exact .comptime inner

theorem Tree.evaluates {catalog : Catalog} {type : TypeSystem.Ty}
    {source : Dynamic.Value} {value : Value} {expression : Expr}
    (tree : Tree catalog type source value expression) (environment : Environment) (store : Store) :
    Evaluates environment store expression value store := by
  induction tree with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | integer => exact .integer
  | product _ _ left right => exact .pair left right
  | proxy | mapping => exact .construct .unit
  | comptime _ inner => exact inner

/-- Every accepted present default has an independent source meaning. -/
theorem tree_of_defaultExpression (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (expression : Expr) (accepted : defaultExpression fuel catalog type = .ok (some expression)) :
    ∃ source value, Tree catalog type source value expression := by
  induction fuel generalizing type expression with
  | zero => simp [defaultExpression] at accepted
  | succ fuel ih =>
    cases type with
    | «variable» | parameter | application | function | error => simp [defaultExpression] at accepted
    | constructor constructor =>
      cases constructor with
      | declaration => simp [defaultExpression] at accepted
      | builtin builtin =>
        cases builtin <;> simp [defaultExpression, pure, Except.pure] at accepted <;> subst expression
        · exact ⟨_, _, .unit⟩
        · exact ⟨_, _, .bool⟩
        · exact ⟨_, _, .word⟩
        · exact ⟨_, _, .integer⟩
    | product left right =>
      cases leftResult : defaultExpression fuel catalog left with
      | error => simp [defaultExpression, leftResult, bind, Except.bind] at accepted
      | ok leftExpr =>
        cases rightResult : defaultExpression fuel catalog right with
        | error => simp [defaultExpression, leftResult, rightResult, bind, Except.bind] at accepted
        | ok rightExpr =>
          cases leftExpr <;> cases rightExpr <;>
            simp [defaultExpression, leftResult, rightResult, bind, Except.bind, pure, Except.pure] at accepted
          rename_i leftExpr rightExpr
          subst expression
          obtain ⟨left, leftValue, leftTree⟩ := ih left leftExpr leftResult
          obtain ⟨right, rightValue, rightTree⟩ := ih right rightExpr rightResult
          exact ⟨_, _, .product leftTree rightTree⟩
    | proxy inner =>
      cases identity : catalog.identity? (.proxy inner) with
      | none => simp [defaultExpression, identity] at accepted
      | some id =>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
        subst expression
        exact ⟨_, _, .proxy inner id identity⟩
    | mapping key value =>
      cases identity : catalog.identity? (.mapping key value) with
      | none => simp [defaultExpression, identity] at accepted
      | some id =>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
        subst expression
        exact ⟨_, _, .mapping key value id identity⟩
    | comptime inner =>
      obtain ⟨source, value, tree⟩ := ih inner expression accepted
      exact ⟨source, value, .comptime tree⟩

/-- A successful absent answer never discards a source default. Fuel exhaustion
is an error, not an absent answer. -/
theorem absent_has_no_default (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (accepted : defaultExpression fuel catalog type = .ok none) :
    ∀ source, ¬ Dynamic.DefaultValue type source := by
  induction fuel generalizing type with
  | zero => simp [defaultExpression] at accepted
  | succ fuel ih =>
    intro source meaning
    cases meaning with
    | unit => simp [TypeSystem.Ty.unit, defaultExpression] at accepted
    | bool => simp [TypeSystem.Ty.bool, defaultExpression] at accepted
    | word => simp [TypeSystem.Ty.word, defaultExpression] at accepted
    | integer => simp [TypeSystem.Ty.integer, defaultExpression] at accepted
    | proxy inner =>
      cases identity : catalog.identity? (.proxy inner) <;>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
    | mapping key value =>
      cases identity : catalog.identity? (.mapping key value) <;>
        simp [defaultExpression, identity, pure, Except.pure] at accepted
    | comptime inner => exact ih _ accepted _ inner
    | @product leftTy rightTy _ _ leftDefault rightDefault =>
      cases leftResult : defaultExpression fuel catalog leftTy with
      | error => simp [defaultExpression, leftResult, bind, Except.bind] at accepted
      | ok left =>
        cases rightResult : defaultExpression fuel catalog rightTy with
        | error => simp [defaultExpression, leftResult, rightResult, bind, Except.bind] at accepted
        | ok right =>
          cases left with
          | none => exact ih _ leftResult _ leftDefault
          | some left =>
            cases right with
            | none => exact ih _ rightResult _ rightDefault
            | some right => simp [defaultExpression, leftResult, rightResult, bind, Except.bind, pure, Except.pure] at accepted

/-- Accepted code, independent default meaning, finite execution, and unchanged
store follow together. No executable source evaluator is a premise. -/
theorem defaultExpression_run_preserves (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty)
    (expression : Expr) (accepted : defaultExpression fuel catalog type = .ok (some expression))
    (environment : Environment) (store : Store) :
    ∃ source value required, Tree catalog type source value expression ∧
      Dynamic.DefaultValue type source ∧ ∀ budget, required ≤ budget →
        runStateful budget (State.initial expression environment store) = .done value store := by
  obtain ⟨source, value, tree⟩ := tree_of_defaultExpression fuel catalog type expression accepted
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel (tree.evaluates environment store)
  exact ⟨source, value, required, tree, tree.meaning, complete⟩

inductive ResultRepresents (catalog : Catalog) (type : TypeSystem.Ty) (coreType : Core.Ty) : Value → Prop where
  | absent (missing : ∀ source, ¬ Dynamic.DefaultValue type source) :
      ResultRepresents catalog type coreType (.inLeft coreType .unit)
  | present {source : Dynamic.Value} {value : Value} {expression : Expr}
      (tree : Tree catalog type source value expression) :
      ResultRepresents catalog type coreType (.inRight .unit value)

/-- Prepared code retains its generator equation, so this public theorem needs
no extra certificate premise and covers both present and absent defaults. -/
theorem prepared_preserves {checked : SourceCoreDataCatalog.Checked}
    (prepared : Prepared checked) (environment : Environment) (store : Store) :
    ∃ value, ResultRepresents checked.catalog prepared.sourceType prepared.type value ∧
      Evaluates environment store prepared.expression value store := by
  cases generatedDefault : prepared.default with
  | none =>
    have generated := prepared.generated
    rw [generatedDefault] at generated
    refine ⟨_, .absent (absent_has_no_default _ _ _ generated), ?_⟩
    rw [prepared.expression_eq, generatedDefault]
    exact .inLeft .unit
  | some expression =>
    have generated := prepared.generated
    rw [generatedDefault] at generated
    obtain ⟨source, value, tree⟩ := tree_of_defaultExpression _ _ _ _ generated
    refine ⟨_, .present tree, ?_⟩
    rw [prepared.expression_eq, generatedDefault]
    exact .inRight (tree.evaluates environment store)

theorem prepared_run_preserves {checked : SourceCoreDataCatalog.Checked}
    (prepared : Prepared checked) (environment : Environment) (store : Store) :
    ∃ value required, ResultRepresents checked.catalog prepared.sourceType prepared.type value ∧
      ∀ budget, required ≤ budget →
        runStateful budget (State.initial prepared.expression environment store) = .done value store := by
  obtain ⟨value, represented, evaluation⟩ := prepared_preserves prepared environment store
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluation
  exact ⟨value, required, represented, complete⟩

end Solcore.SourceSemantics.CoreLowering.DataDefaults
