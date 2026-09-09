import Solcore.Frontend.ComputationReturnTree
import Solcore.Frontend.ComputationBodyFragmentProperties

/-! Exact body provenance closes child membership through all hidden binders.
Only the child's syntactic membership and weakening laws are required. -/

set_option autoImplicit false

namespace Solcore.Frontend

private theorem fold_fragment {F : Core.Expr → Prop}
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    (entries : List (Syntax.MatchCase × (Option Core.Word × Core.Expr)))
    (defaultEntry : Option (Syntax.Block × Core.Expr))
    (branches : ∀ entry ∈ entries, ComputationBodyFragment F entry.2.2)
    (fallback : ∀ entry ∈ defaultEntry.toList, ComputationBodyFragment F entry.2)
    {core : Core.Expr}
    (lowered : entries.foldr
      (fun entry tail => match entry.2.1 with
        | none => some (entry.2.2.weakenAt 0)
        | some word => tail.map fun body => .ifE (.binary .wordEq (.var 0) (.word word)) (entry.2.2.weakenAt 0) body)
      (defaultEntry.map fun entry => entry.2.weakenAt 0) = some core) :
    ComputationBodyFragment F core := by
  induction entries generalizing core with
  | nil =>
      cases defaultEntry with
      | none => simp at lowered
      | some entry =>
          simp only [List.foldr_nil, Option.map_some, Option.some.injEq] at lowered
          subst core
          exact (fallback entry (by simp)).weakenAt childWeakening 0
  | cons entry rest ih =>
      cases tag : entry.2.1 with
      | none =>
          simp only [List.foldr_cons, tag, Option.some.injEq] at lowered
          subst core
          exact (branches entry (by simp)).weakenAt childWeakening 0
      | some word =>
          simp only [List.foldr_cons, tag, Option.map_eq_some_iff] at lowered
          obtain ⟨body, tail, rfl⟩ := lowered
          exact .ifE .wordTest ((branches entry (by simp)).weakenAt childWeakening 0)
            (ih (fun item member => branches item (by simp [member])) tail)

theorem ComputationReturnTreeElaborates.core_fragment
    {ChildElab : LocalNameTable → Resolved.Context → Syntax.Expr → Core.Expr → Core.Ty → Prop}
    {F : Core.Expr → Prop}
    (childMembership : ∀ {table context source core type}, ChildElab table context source core type → F core)
    (childWeakening : ∀ {core}, F core → ∀ cutoff, F (core.weakenAt cutoff))
    {types : TypeNameTable} {owner : Resolved.DeclarationId} {inputs : LocalTypeInputs}
    {body : Syntax.Block} {core : Core.Expr} {type : Core.Ty}
    (elaboration : ComputationReturnTreeElaborates ChildElab types owner inputs body core type) :
    ComputationBodyFragment F core := by
  induction elaboration with
  | bare => exact .unit
  | expression child => exact .leaf (childMembership child)
  | block _ ih => exact ih
  | binding _ _ child _ ih => exact .letE (.leaf (childMembership child)) ih
  | inferred _ child _ ih => exact .letE (.leaf (childMembership child)) ih
  | discard child _ ih => exact .letE (.leaf (childMembership child)) (ComputationBodyFragment.weakenAt childWeakening ih 0)
  | conditional guard _ _ yesIH noIH => exact .ifE (.leaf (childMembership guard)) yesIH noIH
  | wordMatch scrutinee _ _ _ _ _ _ lowered branchesIH defaultIH =>
      exact .letE (.leaf (childMembership scrutinee))
        (fold_fragment childWeakening _ _ branchesIH defaultIH lowered)

end Solcore.Frontend
