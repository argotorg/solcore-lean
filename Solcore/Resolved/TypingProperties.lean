import Solcore.Resolved.Typing
import Solcore.Resolved.LocalScopeProperties
import Solcore.Resolved.LoweringProperties
import Solcore.Resolved.LocalFragmentProperties

/-! Independent resolved-local typing agrees with elaboration to the existing
Core checker. These laws do not resolve source names or assign source syntax
any literal, mutation, or staging meaning. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Every independently typed local expression has a type-preserving lowering. -/
theorem HasType.lowers {context : Context} {expr : Expr} {type : Core.Ty}
    (typing : HasType context expr type) :
    ∃ core, Lowers (LocalScope.ids context) expr core ∧
      Core.HasType (LocalScope.values context) core type := by
  induction typing with
  | unit => exact ⟨.unit, .unit, .unit⟩
  | bool => exact ⟨_, .bool, .bool⟩
  | word => exact ⟨_, .word, .word⟩
  | var found =>
      obtain ⟨index, indexed, atType⟩ := found.indexed
      exact ⟨.var index, .var indexed, .var atType⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered, leftTyped⟩ := leftIH
      obtain ⟨right, rightLowered, rightTyped⟩ := rightIH
      exact ⟨_, .pair leftLowered rightLowered, .pair leftTyped rightTyped⟩
  | unary _ ih =>
      obtain ⟨core, lowered, typed⟩ := ih
      exact ⟨_, .unary lowered, .unary typed⟩
  | binary _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered, leftTyped⟩ := leftIH
      obtain ⟨right, rightLowered, rightTyped⟩ := rightIH
      exact ⟨_, .binary leftLowered rightLowered, .binary leftTyped rightTyped⟩
  | wordLt _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered, leftTyped⟩ := leftIH
      obtain ⟨right, rightLowered, rightTyped⟩ := rightIH
      exact ⟨_, .wordLt leftLowered rightLowered, leftTyped.wordLt rightTyped⟩
  | letE _ _ valueIH bodyIH =>
      obtain ⟨value, valueLowered, valueTyped⟩ := valueIH
      obtain ⟨body, bodyLowered, bodyTyped⟩ := bodyIH
      exact ⟨_, .letE valueLowered bodyLowered, .letE valueTyped bodyTyped⟩
  | ifE _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨condition, conditionLowered, conditionTyped⟩ := conditionIH
      obtain ⟨thenBranch, thenLowered, thenTyped⟩ := thenIH
      obtain ⟨elseBranch, elseLowered, elseTyped⟩ := elseIH
      exact ⟨_, .ifE conditionLowered thenLowered elseLowered,
        .ifE conditionTyped thenTyped elseTyped⟩

private theorem reflects_type_aux {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) {context : Context} {type : Core.Ty}
    (scopeEq : LocalScope.ids context = scope)
    (typing : Core.HasType (LocalScope.values context) core type) :
    HasType context expr type := by
  induction lowered generalizing context type with
  | unit => cases typing; exact .unit
  | bool => cases typing; exact .bool
  | word => cases typing; exact .word
  | var indexed =>
      cases typing with
      | var atType =>
          exact .var (LocalScope.lookup_of_indexed (scopeEq ▸ indexed) atType)
  | pair _ _ leftIH rightIH =>
      cases typing with
      | pair leftTyped rightTyped =>
          exact .pair (leftIH scopeEq leftTyped) (rightIH scopeEq rightTyped)
  | unary _ ih =>
      cases typing with
      | unary operandTyped => exact .unary (ih scopeEq operandTyped)
  | binary _ _ leftIH rightIH =>
      cases typing with
      | binary leftTyped rightTyped =>
          exact .binary (leftIH scopeEq leftTyped) (rightIH scopeEq rightTyped)
  | wordLt _ rightLowered leftIH rightIH =>
      obtain ⟨rfl, leftTyped, rightTyped⟩ := typing.wordLt_inv_local_right rightLowered.localFragment
      exact .wordLt (leftIH scopeEq leftTyped) (rightIH scopeEq rightTyped)
  | @letE scope binder value body coreValue coreBody _ _ valueIH bodyIH =>
      cases typing with
      | @letE _ _ _ _ valueType _ valueTyped bodyTyped =>
          apply HasType.letE (valueIH scopeEq valueTyped)
          exact bodyIH (context := (binder, valueType) :: context)
            (by simpa only [LocalScope.ids, List.map_cons] using
              congrArg (List.cons binder) scopeEq) bodyTyped
  | ifE _ _ _ conditionIH thenIH elseIH =>
      cases typing with
      | ifE conditionTyped thenTyped elseTyped =>
          exact .ifE (conditionIH scopeEq conditionTyped)
            (thenIH scopeEq thenTyped) (elseIH scopeEq elseTyped)

/-- Core typing of an exact lowering reflects to independent local typing. -/
theorem Lowers.reflects_type {context : Context} {expr : Expr} {core : Core.Expr}
    {type : Core.Ty} (lowered : Lowers (LocalScope.ids context) expr core)
    (typing : Core.HasType (LocalScope.values context) core type) :
    HasType context expr type :=
  reflects_type_aux lowered rfl typing

/-- Every exact lowering retains the independently assigned local type. -/
theorem Lowers.preserves_type {context : Context} {expr : Expr} {core : Core.Expr}
    {type : Core.Ty} (lowered : Lowers (LocalScope.ids context) expr core)
    (typing : HasType context expr type) :
    Core.HasType (LocalScope.values context) core type := by
  obtain ⟨other, otherLowered, otherTyped⟩ := typing.lowers
  have same : other = core := otherLowered.deterministic lowered
  simpa only [same] using otherTyped

/-- Successful elaboration neither creates nor loses local typing derivations. -/
theorem Lowers.typing_iff {context : Context} {expr : Expr} {core : Core.Expr}
    {type : Core.Ty} (lowered : Lowers (LocalScope.ids context) expr core) :
    HasType context expr type ↔ Core.HasType (LocalScope.values context) core type :=
  ⟨lowered.preserves_type, lowered.reflects_type⟩

/-- Every successful executable check has an independent local typing derivation. -/
theorem infer_sound {context : Context} {expr : Expr} {type : Core.Ty}
    (accepted : infer? context expr = some type) : HasType context expr type := by
  cases lowerResult : expr.lower? (LocalScope.ids context) with
  | none => simp [infer?, lowerResult] at accepted
  | some core =>
      exact (Expr.lower?_iff.mp lowerResult).reflects_type
        (Core.infer_sound (by simpa [infer?, lowerResult] using accepted))

/-- Independently typed local expressions are accepted by the executable checker. -/
theorem infer_complete {context : Context} {expr : Expr} {type : Core.Ty}
    (typing : HasType context expr type) : infer? context expr = some type := by
  obtain ⟨core, lowered, typed⟩ := typing.lowers
  simp [infer?, Expr.lower?_iff.mpr lowered, Core.infer_complete typed]

theorem typing_iff_infer {context : Context} {expr : Expr} {type : Core.Ty} :
    HasType context expr type ↔ infer? context expr = some type :=
  ⟨infer_complete, infer_sound⟩

/-- First-match local lookup gives one type even when identities are repeated. -/
theorem typing_deterministic {context : Context} {expr : Expr} {left right : Core.Ty}
    (leftTyped : HasType context expr left) (rightTyped : HasType context expr right) :
    left = right :=
  Option.some.inj ((infer_complete leftTyped).symm.trans (infer_complete rightTyped))

end Solcore.Resolved
