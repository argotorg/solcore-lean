import Solcore.Resolved.ScopeProperties
import Solcore.Resolved.Eval

/-! Concrete consumers separate local scope, type checking, and selected-branch
evaluation without imposing a source-name or identity-freshness policy. -/

set_option autoImplicit false

namespace Tests.ResolvedScope

open Solcore Solcore.Resolved

private def modulePath : Workspace.ModulePath := ⟨[⟨"Scope", by decide⟩], by decide⟩
private def binder : LocalId := ⟨⟨⟨.main, modulePath⟩, 0⟩, 0⟩
private def badUnary : Expr := .unary .boolNot .unit
private def selfInitializer : Expr := .letE binder (.var binder) .unit
private def boundBody : Expr := .letE binder .unit (.var binder)
private def skippedElse : Expr := .ifE (.bool true) .unit (.var binder)
private def skippedThen : Expr := .ifE (.bool false) (.var binder) .unit

theorem wellScoped_unary_can_be_ill_typed :
    WellScoped [] badUnary ∧ badUnary.lower? [] = some (.unary .boolNot .unit) ∧
      ¬ ∃ type, HasType [] badUnary type := by
  refine ⟨.unary .unit, (Lowers.unary Lowers.unit).complete, ?_⟩
  rintro ⟨type, typing⟩
  cases typing with
  | unary operand => cases operand

theorem self_initializer_out_of_scope :
    ¬ WellScoped [] selfInitializer ∧ selfInitializer.lower? [] = none := by
  have missing : ¬ WellScoped [] selfInitializer := by
    intro valid
    cases valid with
    | letE initializer _ =>
        cases initializer with
        | var member => simp at member
  exact ⟨missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem binder_available_in_body :
    WellScoped [] boundBody ∧ boundBody.lower? [] = some (.letE .unit (.var 0)) :=
  ⟨.letE .unit (.var (by simp)), (Lowers.letE Lowers.unit (.var .head)).complete⟩

theorem skipped_else_still_requires_scope (store : Core.Store) :
    Evaluates [] store skippedElse .unit store ∧ ¬ WellScoped [] skippedElse ∧
      skippedElse.lower? [] = none := by
  have missing : ¬ WellScoped [] skippedElse := by
    intro valid
    cases valid with
    | ifE _ _ branch =>
        cases branch with
        | var member => simp at member
  exact ⟨.ifTrue .bool .unit, missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem skipped_then_still_requires_scope (store : Core.Store) :
    Evaluates [] store skippedThen .unit store ∧ ¬ WellScoped [] skippedThen ∧
      skippedThen.lower? [] = none := by
  have missing : ¬ WellScoped [] skippedThen := by
    intro valid
    cases valid with
    | ifE _ branch _ =>
        cases branch with
        | var member => simp at member
  exact ⟨.ifFalse .bool .unit, missing, Expr.lower?_eq_none_iff_not_wellScoped.mpr missing⟩

theorem duplicate_scope_keeps_first_index :
    WellScoped [binder, binder] (.var binder) ∧
      (Expr.var binder).lower? [binder, binder] = some (.var 0) :=
  ⟨.var (by simp), (Lowers.var .head).complete⟩

end Tests.ResolvedScope
