import Solcore.Resolved.ScopeExtensionEvaluationProperties
import Solcore.Resolved.Scope

/-! Fresh insertion reflects evaluation when the original expression is
well-scoped. Without original scoping, insertion could enable a previously
missing variable. The retained prefix can contain the new identity, including
through an inner let binder; values and both stores are preserved exactly. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Insertion neither changes nor creates a lookup for an originally present
identity. Its independent first-match value is retained even with duplicates. -/
theorem LocalScope.lookup_insert_fresh_iff {α : Type} {leading suffix : LocalScope α}
    {id newId : LocalId} {value newValue : α}
    (member : id ∈ LocalScope.ids (leading ++ suffix))
    (fresh : newId ∉ LocalScope.ids suffix) :
    LocalScope.Lookup (leading ++ (newId, newValue) :: suffix) id value ↔
      LocalScope.Lookup (leading ++ suffix) id value := by
  constructor
  · intro found
    cases original : LocalScope.lookup? (leading ++ suffix) id with
    | none => exact False.elim ((LocalScope.lookup?_eq_none_iff.mp original) member)
    | some oldValue =>
        have oldFound := LocalScope.lookup?_iff.mp original
        have same := (oldFound.insert_fresh fresh).value_unique found
        cases same
        exact oldFound
  · intro found
    exact found.insert_fresh fresh

/-- Every evaluation after fresh insertion comes from the old environment,
provided all references in the original expression were already in scope. -/
theorem Evaluates.reflect_insert_fresh {leading suffix : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId}
    (evaluation : Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore)
    (scopeValid : WellScoped (LocalScope.ids (leading ++ suffix)) expr)
    (fresh : newId ∉ LocalScope.ids suffix) :
    Evaluates (leading ++ suffix) initialStore expr value finalStore := by
  induction expr generalizing leading initialStore finalStore value with
  | unit => cases evaluation; exact .unit
  | bool actual => cases evaluation; exact .bool
  | word actual => cases evaluation; exact .word
  | var id =>
      cases scopeValid with
      | var member =>
          cases evaluation with
          | var found => exact .var ((LocalScope.lookup_insert_fresh_iff member fresh).mp found)
  | unary op operand ih =>
      cases scopeValid with
      | unary childScoped =>
          cases evaluation with
          | unary child applied => exact .unary (ih child childScoped) applied
  | binary op left right leftIH rightIH =>
      cases scopeValid with
      | binary leftScoped rightScoped =>
          cases evaluation with
          | binary leftEvaluation rightEvaluation applied =>
              exact .binary (leftIH leftEvaluation leftScoped) (rightIH rightEvaluation rightScoped) applied
  | wordLt left right leftIH rightIH =>
      cases scopeValid with
      | wordLt leftScoped rightScoped =>
          cases evaluation with
          | wordLt leftEvaluation rightEvaluation =>
              exact .wordLt (leftIH leftEvaluation leftScoped) (rightIH rightEvaluation rightScoped)
  | letE binder expr body valueIH bodyIH =>
      cases scopeValid with
      | letE valueScoped bodyScoped =>
          cases evaluation with
          | @letE _ _ _ _ _ _ _ boundValue _ valueEvaluation bodyEvaluation =>
              exact .letE (valueIH valueEvaluation valueScoped)
                (bodyIH (leading := (binder, boundValue) :: leading) bodyEvaluation bodyScoped)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases scopeValid with
      | ifE conditionScoped thenScoped elseScoped =>
          cases evaluation with
          | ifTrue conditionEvaluation branchEvaluation =>
              exact .ifTrue (conditionIH conditionEvaluation conditionScoped) (thenIH branchEvaluation thenScoped)
          | ifFalse conditionEvaluation branchEvaluation =>
              exact .ifFalse (conditionIH conditionEvaluation conditionScoped) (elseIH branchEvaluation elseScoped)

theorem WellScoped.evaluates_insert_fresh_iff {leading suffix : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId} (scopeValid : WellScoped (LocalScope.ids (leading ++ suffix)) expr)
    (fresh : newId ∉ LocalScope.ids suffix) :
    Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore ↔
      Evaluates (leading ++ suffix) initialStore expr value finalStore :=
  ⟨fun evaluation => evaluation.reflect_insert_fresh scopeValid fresh,
    fun evaluation => evaluation.insert_fresh fresh⟩

theorem WellScoped.evaluates_weaken_fresh_iff {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId} (scopeValid : WellScoped (LocalScope.ids environment) expr)
    (fresh : newId ∉ LocalScope.ids environment) :
    Evaluates ((newId, newValue) :: environment) initialStore expr value finalStore ↔
      Evaluates environment initialStore expr value finalStore :=
  WellScoped.evaluates_insert_fresh_iff (leading := []) scopeValid fresh

/-- The allocator provides only freshness; original scoping is still required
to reflect evaluations rather than merely preserve existing ones. -/
theorem WellScoped.evaluates_weaken_allocated_iff {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value : Core.Value}
    (scopeValid : WellScoped (LocalScope.ids environment) expr)
    (owner : DeclarationId) (newValue : Core.Value) :
    Evaluates ((freshLocalId owner (LocalScope.ids environment), newValue) :: environment)
      initialStore expr value finalStore ↔
      Evaluates environment initialStore expr value finalStore :=
  scopeValid.evaluates_weaken_fresh_iff (freshLocalId_not_mem owner (LocalScope.ids environment))

end Solcore.Resolved
