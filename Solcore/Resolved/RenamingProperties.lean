import Solcore.Resolved.Renaming
import Solcore.Resolved.TypingProperties
import Solcore.Resolved.EvaluationProperties

/-! Injective identity changes preserve exact elaboration, types, and evaluation.
Injectivity prevents distinct binders or references from being merged. No
freshness, successful whole-expression lowering, or source-name policy is
silently assumed by the independent evaluation invariance theorem. -/

set_option autoImplicit false

namespace Solcore.Resolved

namespace LocalScope

@[simp] theorem ids_mapIds {α : Type} (mapping : LocalId → LocalId) (scope : LocalScope α) :
    ids (mapIds mapping scope) = (ids scope).map mapping := by
  simp [mapIds, ids, List.map_map, Function.comp_def]

@[simp] theorem values_mapIds {α : Type} (mapping : LocalId → LocalId) (scope : LocalScope α) :
    values (mapIds mapping scope) = values scope := by
  simp [mapIds, values, List.map_map, Function.comp_def]

theorem index?_map (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (scope : List LocalId) (id : LocalId) :
    index? (scope.map mapping) (mapping id) = index? scope id := by
  induction scope with
  | nil => rfl
  | cons candidate rest ih =>
      have same : mapping candidate = mapping id ↔ candidate = id :=
        ⟨fun equal => injective equal, congrArg mapping⟩
      simp only [List.map_cons, index?, same, ih]

theorem lookup?_mapIds {α : Type} (mapping : LocalId → LocalId)
    (injective : Function.Injective mapping) (scope : LocalScope α) (id : LocalId) :
    lookup? (mapIds mapping scope) (mapping id) = lookup? scope id := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨candidate, value⟩
      have same : mapping candidate = mapping id ↔ candidate = id :=
        ⟨fun equal => injective equal, congrArg mapping⟩
      simpa only [mapIds, List.map_cons, lookup?, same] using
        congrArg (fun result => if candidate = id then some value else result) ih

theorem lookup_mapIds_iff {α : Type} (mapping : LocalId → LocalId)
    (injective : Function.Injective mapping) {scope : LocalScope α} {id : LocalId} {value : α} :
    Lookup (mapIds mapping scope) (mapping id) value ↔ Lookup scope id value := by
  rw [← lookup?_iff, lookup?_mapIds mapping injective, lookup?_iff]

theorem indexOf_map_iff (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    {scope : List LocalId} {id : LocalId} {index : Nat} :
    IndexOf (scope.map mapping) (mapping id) index ↔ IndexOf scope id index := by
  rw [← index?_iff, index?_map mapping injective, index?_iff]

end LocalScope

@[simp] theorem Expr.renameIds_id (expr : Expr) : expr.renameIds id = expr := by
  induction expr <;> simp_all [Expr.renameIds]

theorem Expr.renameIds_comp (expr : Expr) (first second : LocalId → LocalId) :
    (expr.renameIds first).renameIds second = expr.renameIds (second ∘ first) := by
  induction expr <;> simp_all [Expr.renameIds, Function.comp_def]

/-- The same positional Core expression is produced, including failure when
an identity is absent. No default position or alpha-equivalence quotient is used. -/
theorem Expr.lower?_renameIds (mapping : LocalId → LocalId)
    (injective : Function.Injective mapping) (expr : Expr) (scope : List LocalId) :
    (expr.renameIds mapping).lower? (scope.map mapping) = expr.lower? scope := by
  induction expr generalizing scope with
  | unit | bool | word => rfl
  | var id => simp only [renameIds, lower?, LocalScope.index?_map mapping injective]
  | unary op operand ih => simp only [renameIds, lower?, ih]
  | binary op left right leftIH rightIH => simp only [renameIds, lower?, leftIH, rightIH]
  | letE binder value body valueIH bodyIH =>
      simpa only [renameIds, lower?, List.map_cons, valueIH] using
        congrArg (fun loweredBody => do
          return Core.Expr.letE (← value.lower? scope) (← loweredBody))
          (bodyIH (binder :: scope))
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      simp only [renameIds, lower?, conditionIH, thenIH, elseIH]

theorem lowers_renameIds_iff (mapping : LocalId → LocalId)
    (injective : Function.Injective mapping) {scope : List LocalId} {expr : Expr} {core : Core.Expr} :
    Lowers (scope.map mapping) (expr.renameIds mapping) core ↔ Lowers scope expr core := by
  rw [← Expr.lower?_iff, Expr.lower?_renameIds mapping injective, Expr.lower?_iff]

theorem infer?_renameIds (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    (context : Context) (expr : Expr) :
    infer? (LocalScope.mapIds mapping context) (expr.renameIds mapping) = infer? context expr := by
  simp only [infer?, LocalScope.ids_mapIds, Expr.lower?_renameIds mapping injective,
    LocalScope.values_mapIds]

theorem typing_renameIds_iff (mapping : LocalId → LocalId) (injective : Function.Injective mapping)
    {context : Context} {expr : Expr} {type : Core.Ty} :
    HasType (LocalScope.mapIds mapping context) (expr.renameIds mapping) type ↔
      HasType context expr type := by
  rw [typing_iff_infer, infer?_renameIds mapping injective, ← typing_iff_infer]

/-- Evaluation invariance is independent of lowering and therefore also
covers successful evaluation with unresolved identities in skipped branches. -/
theorem evaluates_renameIds_iff (mapping : LocalId → LocalId)
    (injective : Function.Injective mapping) {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value : Core.Value} :
    Evaluates (LocalScope.mapIds mapping environment) initialStore (expr.renameIds mapping) value finalStore ↔
      Evaluates environment initialStore expr value finalStore := by
  induction expr generalizing environment initialStore finalStore value with
  | unit => constructor <;> intro evaluation <;> cases evaluation <;> exact .unit
  | bool actual => constructor <;> intro evaluation <;> cases evaluation <;> exact .bool
  | word actual => constructor <;> intro evaluation <;> cases evaluation <;> exact .word
  | var id =>
      constructor
      · intro evaluation
        cases evaluation with
        | var found => exact .var ((LocalScope.lookup_mapIds_iff mapping injective).mp found)
      · intro evaluation
        cases evaluation with
        | var found => exact .var ((LocalScope.lookup_mapIds_iff mapping injective).mpr found)
  | unary op operand ih =>
      constructor
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary (ih.mp child) applied
      · intro evaluation
        cases evaluation with
        | unary child applied => exact .unary (ih.mpr child) applied
  | binary op left right leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | binary first second applied => exact .binary (leftIH.mp first) (rightIH.mp second) applied
      · intro evaluation
        cases evaluation with
        | binary first second applied => exact .binary (leftIH.mpr first) (rightIH.mpr second) applied
  | letE binder expr body valueIH bodyIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | letE bound rest => exact .letE (valueIH.mp bound) (bodyIH.mp rest)
      · intro evaluation
        cases evaluation with
        | letE bound rest => exact .letE (valueIH.mpr bound) (bodyIH.mpr rest)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | ifTrue conditionEvaluation branchEvaluation =>
            exact .ifTrue (conditionIH.mp conditionEvaluation) (thenIH.mp branchEvaluation)
        | ifFalse conditionEvaluation branchEvaluation =>
            exact .ifFalse (conditionIH.mp conditionEvaluation) (elseIH.mp branchEvaluation)
      · intro evaluation
        cases evaluation with
        | ifTrue conditionEvaluation branchEvaluation =>
            exact .ifTrue (conditionIH.mpr conditionEvaluation) (thenIH.mpr branchEvaluation)
        | ifFalse conditionEvaluation branchEvaluation =>
            exact .ifFalse (conditionIH.mpr conditionEvaluation) (elseIH.mpr branchEvaluation)

end Solcore.Resolved
