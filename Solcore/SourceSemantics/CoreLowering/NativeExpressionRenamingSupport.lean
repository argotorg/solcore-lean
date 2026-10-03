import Solcore.SourceSemantics.CoreLowering.NativeExpressionContextSupport

/-! Reflection of free-slot bounds follows the actual renamed syntax, including
each binder. It does not transport runtime captures or infer source authority. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
open Core NativeExpressionContextSupport

def ReflectsBound (mapping : Renaming) (source target : Nat) : Prop :=
  ∀ index, mapping index < target → index < source

theorem ReflectsBound.lift {mapping : Renaming} {source target : Nat}
    (reflects : ReflectsBound mapping source target) :
    ReflectsBound mapping.lift (source + 1) (target + 1) := by
  intro index bound
  cases index with
  | zero => omega
  | succ index =>
    simp only [Renaming.lift] at bound
    have := reflects index (by omega)
    omega

mutual
  theorem reflects : ∀ (code : Expr) {mapping : Renaming} {source target : Nat},
      ReflectsBound mapping source target → supported (code.rename mapping) target = true →
      supported code source = true
    | .unit, _, _, _, _, _ | .bool _, _, _, _, _, _
    | .word _, _, _, _, _, _ | .integer _, _, _, _, _, _ => rfl
    | .var index, _, _, _, bound, support => by
      simp only [Expr.rename, supported, decide_eq_true_eq] at support ⊢
      exact bound index support
    | .pair a b, _, _, _, bound, support
    | .apply a b, _, _, _, bound, support
    | .storeCell a b, _, _, _, bound, support
    | .binary _ a b, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects a bound support.1, reflects b bound support.2⟩
    | .first a, _, _, _, bound, support | .second a, _, _, _, bound, support
    | .inLeft _ a, _, _, _, bound, support | .inRight _ a, _, _, _, bound, support
    | .newCell _ a, _, _, _, bound, support | .loadCell a, _, _, _, bound, support
    | .construct _ a, _, _, _, bound, support | .unary _ a, _, _, _, bound, support =>
      reflects a bound support
    | .lambda _ _ body, _, _, _, bound, support => reflects body bound.lift support
    | .letE a b, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects a bound support.1, reflects b bound.lift support.2⟩
    | .caseE a b c, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨⟨reflects a bound support.1.1, reflects b bound.lift support.1.2⟩,
        reflects c bound.lift support.2⟩
    | .ifE a b c, _, _, _, bound, support
    | .ternary _ a b c, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨⟨reflects a bound support.1.1, reflects b bound support.1.2⟩,
        reflects c bound support.2⟩
    | .matchData _ _ value branches, _, _, _, bound, support => by
      simp only [Expr.rename, supported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects value bound support.1, branches_reflect branches bound support.2⟩

  theorem branches_reflect : ∀ (branches : List Expr) {mapping : Renaming} {source target : Nat},
      ReflectsBound mapping source target →
      branchesSupported (Expr.renameList branches mapping.lift) target = true →
      branchesSupported branches source = true
    | [], _, _, _, _, _ => rfl
    | head :: tail, _, _, _, bound, support => by
      simp only [Expr.renameList, branchesSupported, Bool.and_eq_true] at support ⊢
      exact ⟨reflects head bound.lift support.1, branches_reflect tail bound support.2⟩
end

theorem shift (code : Expr) (count bound : Nat)
    (support : supported (code.rename (fun index => index + count)) (bound + count) = true) :
    supported code bound = true :=
  reflects code (by intro index smaller; dsimp at smaller; omega) support

end Solcore.SourceSemantics.CoreLowering.NativeExpressionRenamingSupport
