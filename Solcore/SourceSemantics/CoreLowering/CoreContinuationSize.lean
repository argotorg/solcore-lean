import Solcore.SourceSemantics.CoreLowering.CoreContinuationAgreement

/-! A real prefix retains a subderivation of the original native evaluation.
The Boolean distinguishes strict prefixes from an empty prefix. Forgetting
sizes recovers ordinary continuation agreement; the converse is not asserted. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CoreProof
open Core

structure ContinuationSize (strict : Bool) (environment : Environment) (store : Store) (whole : Expr)
    (nextEnvironment : Environment) (nextStore : Store) (next : Expr) : Prop where
  wrap : ∀ {result finalStore}, Evaluates nextEnvironment nextStore next result finalStore →
    Evaluates environment store whole result finalStore
  remaining : ∀ {size result finalStore}, EvaluationSize size environment store whole result finalStore →
    ∃ child, (if strict then child < size else child ≤ size) ∧
      EvaluationSize child nextEnvironment nextStore next result finalStore

namespace ContinuationSize
variable {a b : Bool} {environment middleEnvironment nextEnvironment : Environment}
  {store middleStore nextStore : Store} {whole middle next : Expr}

/-- Erasure is the only direction that chooses a size for an unsized input. -/
theorem agreement (receipt : ContinuationSize a environment store whole nextEnvironment nextStore next) :
    ContinuationAgreement environment store whole nextEnvironment nextStore next := by
  refine ⟨receipt.wrap, ?_⟩
  intro result finalStore evaluated
  obtain ⟨size, sized⟩ := evaluation_has_size evaluated
  obtain ⟨child, _, completed⟩ := receipt.remaining sized
  exact completed.sound

theorem weak (receipt : ContinuationSize a environment store whole nextEnvironment nextStore next) :
    ContinuationSize false environment store whole nextEnvironment nextStore next := by
  refine ⟨receipt.wrap, ?_⟩
  intro size result finalStore evaluated
  obtain ⟨child, bound, completed⟩ := receipt.remaining evaluated
  exact ⟨child, by cases a <;> simp_all <;> omega, completed⟩

theorem refl (environment : Environment) (store : Store) (code : Expr) :
    ContinuationSize false environment store code environment store code :=
  ⟨id, fun evaluated => ⟨_, Nat.le_refl _, evaluated⟩⟩

theorem trans (first : ContinuationSize a environment store whole middleEnvironment middleStore middle)
    (second : ContinuationSize b middleEnvironment middleStore middle nextEnvironment nextStore next) :
    ContinuationSize (a || b) environment store whole nextEnvironment nextStore next := by
  refine ⟨fun evaluated => first.wrap (second.wrap evaluated), ?_⟩
  intro size result finalStore evaluated
  obtain ⟨middleSize, firstBound, middleEval⟩ := first.remaining evaluated
  obtain ⟨child, lastBound, completed⟩ := second.remaining middleEval
  exact ⟨child, by cases a <;> cases b <;> simp_all <;> omega, completed⟩

theorem letE {environment : Environment} {before middle : Store} {initializer body : Expr} {value : Value}
    (evaluated : Evaluates environment before initializer value middle) :
    ContinuationSize true environment before (.letE initializer body) (value :: environment) middle body := by
  refine ⟨fun body => .letE evaluated body, ?_⟩
  intro size result finalStore original
  exact original.let_body evaluated

theorem bind {environment : Environment} {before middle : Store} {computation body : Expr} {type : Ty} {value : Value}
    (evaluated : Evaluates environment before computation (.inRight .word value) middle) :
    ContinuationSize true environment before (LanguageResult.bind type computation body) (value :: environment) middle body := by
  refine ⟨fun body => LanguageResult.bind_success type evaluated body, ?_⟩
  intro size result finalStore original
  exact original.bind_success evaluated

theorem case_left {environment : Environment} {before middle : Store} {scrutinee left right : Expr}
    {rightType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inLeft rightType value) middle) :
    ContinuationSize true environment before (.caseE scrutinee left right) (value :: environment) middle left := by
  refine ⟨fun body => .caseLeft evaluated body, ?_⟩
  intro size result finalStore original
  exact original.case_left evaluated

theorem case_right {environment : Environment} {before middle : Store} {scrutinee left right : Expr}
    {leftType : Ty} {value : Value}
    (evaluated : Evaluates environment before scrutinee (.inRight leftType value) middle) :
    ContinuationSize true environment before (.caseE scrutinee left right) (value :: environment) middle right := by
  refine ⟨fun body => .caseRight evaluated body, ?_⟩
  intro size result finalStore original
  exact original.case_right evaluated

end ContinuationSize
/-- Ordered lexical slots and canonical values grow by prefixes of equal
length. Their elements are not identified with administrative temporaries. -/
def CanonicalPrefix {α : Type} (scope : List α) (canonical : Environment)
    (nextScope : List α) (nextCanonical : Environment) : Prop :=
  ∃ addedScope addedValues, addedScope.length = addedValues.length ∧
    nextScope = addedScope ++ scope ∧ nextCanonical = addedValues ++ canonical

namespace CanonicalPrefix
theorem refl {α : Type} (scope : List α) (canonical : Environment) :
    CanonicalPrefix scope canonical scope canonical := ⟨[], [], rfl, rfl, rfl⟩

theorem cons {α : Type} (scope : List α) (canonical : Environment) (binding : α) (value : Value) :
    CanonicalPrefix scope canonical (binding :: scope) (value :: canonical) :=
  ⟨[binding], [value], rfl, rfl, rfl⟩

theorem trans {α : Type} {scope middleScope nextScope : List α}
    {canonical middleCanonical nextCanonical : Environment}
    (first : CanonicalPrefix scope canonical middleScope middleCanonical)
    (second : CanonicalPrefix middleScope middleCanonical nextScope nextCanonical) :
    CanonicalPrefix scope canonical nextScope nextCanonical := by
  obtain ⟨firstScope, firstValues, firstLength, rfl, rfl⟩ := first
  obtain ⟨lastScope, lastValues, lastLength, rfl, rfl⟩ := second
  exact ⟨lastScope ++ firstScope, lastValues ++ firstValues,
    by simp [firstLength, lastLength], by simp [List.append_assoc], by simp [List.append_assoc]⟩

theorem fold {α β : Type} (scope : List α) (canonical : Environment) (bindings : List β) (project : β → α)
    {added : Environment} (same : added.length = bindings.length) :
    CanonicalPrefix scope canonical (bindings.foldl (fun current binding => project binding :: current) scope)
      (added ++ canonical) := by
  have ordered : ∀ current, bindings.foldl (fun scope binding => project binding :: scope) current =
      bindings.reverse.map project ++ current := by
    clear same
    induction bindings with
    | nil => intro current; rfl
    | cons head tail ih =>
      intro current
      simp only [List.foldl_cons, ih, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
        List.append_assoc, List.cons_append, List.nil_append]
  exact ⟨bindings.reverse.map project, added, by simp [same], ordered scope, rfl⟩
end CanonicalPrefix

end Solcore.SourceSemantics.CoreLowering.CoreProof
