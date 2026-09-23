import Solcore.Resolved.ScopeProperties
import Solcore.Resolved.TypingProperties
import Solcore.Core.Derived

/-! Inserting a fresh outer identity preserves every existing local reference.
The prefix formulation passes under arbitrary let binders, including binders
whose identity equals the inserted identity. Only the original outer scope is
required to omit that identity; no whole-syntax freshness premise is needed. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- First-match positions in the unchanged prefix stay fixed; positions in
the outer scope shift by one. The prefix may itself contain the inserted ID. -/
theorem LocalScope.IndexOf.insert_fresh
    {scope kept : List LocalId} {newId id : LocalId} {index : Nat}
    (fresh : newId ∉ scope) (indexed : LocalScope.IndexOf (kept ++ scope) id index) :
    LocalScope.IndexOf (kept ++ newId :: scope) id
      (Core.Renaming.insertion kept.length index) := by
  induction kept generalizing index with
  | nil =>
      have different : newId ≠ id := by
        intro same
        subst id
        have present := LocalScope.index?_iff.mpr indexed
        have absent := LocalScope.index?_eq_none_iff.mpr fresh
        simp only [List.nil_append, absent] at present
        cases present
      simpa only [List.nil_append, List.length_nil, Core.Renaming.insertion,
        Nat.zero_le, ↓reduceIte] using LocalScope.IndexOf.tail different indexed
  | cons candidate kept ih =>
      cases indexed with
      | head =>
          simpa [Core.Renaming.insertion] using
            (LocalScope.IndexOf.head (scope := kept ++ newId :: scope) (id := id))
      | tail different indexed =>
          have recursive := LocalScope.IndexOf.tail different (ih indexed)
          simpa only [List.cons_append, List.length_cons, ← Core.Renaming.lift_insertion,
            Core.Renaming.lift] using recursive

/-- Structural elaboration respects insertion under any retained prefix. -/
theorem Lowers.insert_fresh
    {scope kept : List LocalId} {newId : LocalId} {expr : Expr} {core : Core.Expr}
    (fresh : newId ∉ scope) (lowered : Lowers (kept ++ scope) expr core) :
    Lowers (kept ++ newId :: scope) expr (core.weakenAt kept.length) := by
  induction expr generalizing kept core with
  | unit => cases lowered; simp only [Core.Expr.weakenAt]; exact .unit
  | bool value => cases lowered; simp only [Core.Expr.weakenAt]; exact .bool
  | word value => cases lowered; simp only [Core.Expr.weakenAt]; exact .word
  | var id =>
      cases lowered with
      | var indexed =>
          simpa only [← Core.Expr.rename_insertion, Core.Expr.rename] using
            Lowers.var (indexed.insert_fresh fresh)
  | pair left right leftIH rightIH =>
      cases lowered with
      | pair leftLowered rightLowered =>
          simp only [Core.Expr.weakenAt]
          exact .pair (leftIH leftLowered) (rightIH rightLowered)
  | unary op operand ih =>
      cases lowered with
      | unary child => simp only [Core.Expr.weakenAt]; exact .unary (ih child)
  | binary op left right leftIH rightIH =>
      cases lowered with
      | binary leftLowered rightLowered =>
          simp only [Core.Expr.weakenAt]
          exact .binary (leftIH leftLowered) (rightIH rightLowered)
  | wordLt left right leftIH rightIH =>
      cases lowered with
      | wordLt leftLowered rightLowered =>
          rw [Core.Expr.weakenAt_wordLt]
          exact .wordLt (leftIH leftLowered) (rightIH rightLowered)
  | letE binder value body valueIH bodyIH =>
      cases lowered with
      | letE valueLowered bodyLowered =>
          simp only [Core.Expr.weakenAt]
          exact .letE (valueIH valueLowered)
            (by simpa only [List.cons_append, List.length_cons] using
              bodyIH (kept := binder :: kept) bodyLowered)
  | ifE condition thenBranch elseBranch conditionIH thenIH elseIH =>
      cases lowered with
      | ifE conditionLowered thenLowered elseLowered =>
          simp only [Core.Expr.weakenAt]
          exact .ifE (conditionIH conditionLowered) (thenIH thenLowered) (elseIH elseLowered)

/-- A new outer local shifts only free Core positions, not named occurrences. -/
theorem Lowers.weaken_fresh
    {scope : List LocalId} {newId : LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) (fresh : newId ∉ scope) :
    Lowers (newId :: scope) expr (core.weakenAt 0) := by
  simpa only [List.nil_append, List.length_nil] using
    Lowers.insert_fresh (kept := []) fresh lowered

theorem WellScoped.weaken_fresh
    {scope : List LocalId} {newId : LocalId} {expr : Expr}
    (scopeValid : WellScoped scope expr) (fresh : newId ∉ scope) :
    WellScoped (newId :: scope) expr := by
  obtain ⟨core, lowered⟩ := scopeValid.lowers
  exact (lowered.weaken_fresh fresh).wellScoped

/-- Under successful original scoping, executable insertion is exactly Core
weakening. Without that premise, insertion could resolve an absent reference. -/
theorem Expr.lower?_weaken_fresh
    {scope : List LocalId} {newId : LocalId} {expr : Expr}
    (scopeValid : WellScoped scope expr) (fresh : newId ∉ scope) :
    expr.lower? (newId :: scope) = (expr.lower? scope).map (fun core => core.weakenAt 0) := by
  obtain ⟨core, lowered⟩ := scopeValid.lowers
  rw [lowered.complete, (lowered.weaken_fresh fresh).complete]
  rfl

/-- The added entry has an arbitrary type and need not differ from the types
already present. Freshness concerns its resolved identity, not source spelling. -/
theorem HasType.weaken_fresh
    {context : Context} {newId : LocalId} {expr : Expr} {type : Core.Ty}
    (typing : HasType context expr type) (fresh : newId ∉ LocalScope.ids context)
    (inserted : Core.Ty) : HasType ((newId, inserted) :: context) expr type := by
  obtain ⟨core, lowered, coreTyped⟩ := typing.lowers
  exact (lowered.weaken_fresh fresh).reflects_type (context := (newId, inserted) :: context) (by
    simpa only [LocalScope.values, List.map_cons, Core.Context.insertAt] using
      coreTyped.weakenAt (inserted := inserted) 0)

end Solcore.Resolved
