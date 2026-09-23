import Solcore.Resolved.Expr
import Solcore.Resolved.LoweringProperties
import Solcore.Resolved.Typing
import Solcore.Core.Derived
import Solcore.Resolved.Eval
import Solcore.Resolved.FreshIdentity

set_option autoImplicit false

namespace Solcore.Resolved

/-- Type-independent local scope validity. Every syntactic branch must be
scoped. A binder extends only its body, and repeated identities are permitted. -/
inductive WellScoped : List LocalId → Expr → Prop where
  | unit {scope} : WellScoped scope .unit
  | bool {scope value} : WellScoped scope (.bool value)
  | word {scope value} : WellScoped scope (.word value)
  | var {scope id} : id ∈ scope → WellScoped scope (.var id)
  | pair {scope left right} :
      WellScoped scope left → WellScoped scope right →
      WellScoped scope (.pair left right)
  | unary {scope op operand} :
      WellScoped scope operand → WellScoped scope (.unary op operand)
  | binary {scope op left right} :
      WellScoped scope left → WellScoped scope right →
      WellScoped scope (.binary op left right)
  | wordLt {scope left right} :
      WellScoped scope left → WellScoped scope right → WellScoped scope (.wordLt left right)
  | letE {scope binder value body} :
      WellScoped scope value → WellScoped (binder :: scope) body →
      WellScoped scope (.letE binder value body)
  | ifE {scope condition thenBranch elseBranch} :
      WellScoped scope condition → WellScoped scope thenBranch →
      WellScoped scope elseBranch →
      WellScoped scope (.ifE condition thenBranch elseBranch)

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.ScopeProperties`
-/

/-! Local scope validity exactly characterizes successful structural lowering.
This boundary is independent of operand types and requires no identity freshness. -/

set_option autoImplicit false

namespace Solcore.Resolved

theorem Lowers.wellScoped {scope : List LocalId} {expr : Expr} {core : Core.Expr}
    (lowered : Lowers scope expr core) : WellScoped scope expr := by
  induction lowered with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var indexed =>
      apply WellScoped.var
      induction indexed with
      | head => exact List.mem_cons_self
      | tail _ _ ih => exact List.mem_cons_of_mem _ ih
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | wordLt _ _ leftIH rightIH => exact .wordLt leftIH rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

/-- In-scope references always have an exact first-match positional lowering. -/
theorem WellScoped.lowers {scope : List LocalId} {expr : Expr}
    (scopeValid : WellScoped scope expr) : ∃ core, Lowers scope expr core := by
  induction scopeValid with
  | unit => exact ⟨_, .unit⟩
  | bool => exact ⟨_, .bool⟩
  | word => exact ⟨_, .word⟩
  | @var scope id member =>
      cases result : LocalScope.index? scope id with
      | none => exact False.elim ((LocalScope.index?_eq_none_iff.mp result) member)
      | some index => exact ⟨_, .var (LocalScope.index?_iff.mp result)⟩
  | pair _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered⟩ := leftIH
      obtain ⟨right, rightLowered⟩ := rightIH
      exact ⟨_, .pair leftLowered rightLowered⟩
  | unary _ ih =>
      obtain ⟨core, lowered⟩ := ih
      exact ⟨_, .unary lowered⟩
  | binary _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered⟩ := leftIH
      obtain ⟨right, rightLowered⟩ := rightIH
      exact ⟨_, .binary leftLowered rightLowered⟩
  | wordLt _ _ leftIH rightIH =>
      obtain ⟨left, leftLowered⟩ := leftIH
      obtain ⟨right, rightLowered⟩ := rightIH
      exact ⟨_, .wordLt leftLowered rightLowered⟩
  | letE _ _ valueIH bodyIH =>
      obtain ⟨value, valueLowered⟩ := valueIH
      obtain ⟨body, bodyLowered⟩ := bodyIH
      exact ⟨_, .letE valueLowered bodyLowered⟩
  | ifE _ _ _ conditionIH thenIH elseIH =>
      obtain ⟨condition, conditionLowered⟩ := conditionIH
      obtain ⟨thenBranch, thenLowered⟩ := thenIH
      obtain ⟨elseBranch, elseLowered⟩ := elseIH
      exact ⟨_, .ifE conditionLowered thenLowered elseLowered⟩

theorem wellScoped_iff_lowers {scope : List LocalId} {expr : Expr} :
    WellScoped scope expr ↔ ∃ core, Lowers scope expr core :=
  ⟨WellScoped.lowers, fun ⟨_, lowered⟩ => lowered.wellScoped⟩

/-- No out-of-scope reference can be hidden by structural elaboration. -/
theorem Expr.lower?_eq_none_iff_not_wellScoped {scope : List LocalId} {expr : Expr} :
    expr.lower? scope = none ↔ ¬ WellScoped scope expr := by
  rw [Expr.lower?_eq_none_iff, wellScoped_iff_lowers]

theorem Expr.lower?_isSome_iff_wellScoped {scope : List LocalId} {expr : Expr} :
    (expr.lower? scope).isSome = true ↔ WellScoped scope expr := by
  cases result : expr.lower? scope with
  | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
      exact Expr.lower?_eq_none_iff_not_wellScoped.mp result
  | some core =>
      simp only [Option.isSome_some, true_iff]
      exact (Expr.lower?_sound result).wellScoped

/-- Independent typing checks scope in all branches, including unselected ones. -/
theorem HasType.wellScoped {context : Context} {expr : Expr} {type : Core.Ty}
    (typing : HasType context expr type) : WellScoped (LocalScope.ids context) expr := by
  induction typing with
  | unit => exact .unit
  | bool => exact .bool
  | word => exact .word
  | var found => exact .var (List.mem_map.mpr ⟨_, found.mem, rfl⟩)
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | unary _ ih => exact .unary ih
  | binary _ _ leftIH rightIH => exact .binary leftIH rightIH
  | wordLt _ _ leftIH rightIH => exact .wordLt leftIH rightIH
  | letE _ _ valueIH bodyIH => exact .letE valueIH bodyIH
  | ifE _ _ _ conditionIH thenIH elseIH => exact .ifE conditionIH thenIH elseIH

/-- A missing local variable is rejected instead of receiving a default index. -/
theorem Expr.lower?_var_eq_none_iff {scope : List LocalId} {id : LocalId} :
    (Expr.var id).lower? scope = none ↔ id ∉ scope := by
  rw [Expr.lower?_eq_none_iff_not_wellScoped]
  constructor
  · intro rejected member
    exact rejected (.var member)
  · intro missing scopeValid
    cases scopeValid with
    | var member => exact missing member

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.ScopeExtensionProperties`
-/

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

/-!
## Consolidated module: `Solcore.Resolved.ScopeExtensionEvaluationProperties`
-/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Inserting an absent identity behind a retained prefix preserves existing lookup.
The retained prefix may itself contain the inserted identity. -/
theorem LocalScope.Lookup.insert_fresh {α : Type} {leading suffix : LocalScope α}
    {id newId : LocalId} {value newValue : α}
    (found : LocalScope.Lookup (leading ++ suffix) id value)
    (fresh : newId ∉ LocalScope.ids suffix) :
    LocalScope.Lookup (leading ++ (newId, newValue) :: suffix) id value := by
  induction leading with
  | nil =>
      have different : newId ≠ id := by
        intro same
        apply fresh
        rw [same]
        exact List.mem_map.mpr ⟨_, found.mem, rfl⟩
      exact .tail different found
  | cons entry rest ih =>
      rcases entry with ⟨candidate, entryValue⟩
      cases found with
      | head => exact .head
      | tail different found => exact .tail different (ih found)

private theorem evaluation_insert_aux
    {environment : Environment} {initialStore finalStore : Core.Store}
    {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore) :
    ∀ (leading suffix : Environment), environment = leading ++ suffix →
      ∀ (newId : LocalId) (newValue : Core.Value), newId ∉ LocalScope.ids suffix →
        Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore := by
  induction evaluation with
  | unit => intros; exact .unit
  | bool => intros; exact .bool
  | word => intros; exact .word
  | pair _ _ leftIH rightIH =>
      intro leading suffix split newId newValue fresh
      exact .pair (leftIH leading suffix split newId newValue fresh)
        (rightIH leading suffix split newId newValue fresh)
  | var found =>
      intro leading suffix split newId newValue fresh
      rw [split] at found
      exact .var (found.insert_fresh fresh)
  | unary _ applied ih =>
      intro leading suffix split newId newValue fresh
      exact .unary (ih leading suffix split newId newValue fresh) applied
  | binary _ _ applied leftIH rightIH =>
      intro leading suffix split newId newValue fresh
      exact .binary (leftIH leading suffix split newId newValue fresh)
        (rightIH leading suffix split newId newValue fresh) applied
  | wordLt _ _ leftIH rightIH =>
      intro leading suffix split newId newValue fresh
      exact .wordLt (leftIH leading suffix split newId newValue fresh)
        (rightIH leading suffix split newId newValue fresh)
  | @letE environment initialStore middleStore finalStore binder value body boundValue result
      _ _ valueIH bodyIH =>
      intro leading suffix split newId newValue fresh
      exact .letE (valueIH leading suffix split newId newValue fresh)
        (bodyIH ((binder, boundValue) :: leading) suffix
          (by simpa only [List.cons_append] using congrArg (List.cons (binder, boundValue)) split)
          newId newValue fresh)
  | ifTrue _ _ conditionIH branchIH =>
      intro leading suffix split newId newValue fresh
      exact .ifTrue (conditionIH leading suffix split newId newValue fresh)
        (branchIH leading suffix split newId newValue fresh)
  | ifFalse _ _ conditionIH branchIH =>
      intro leading suffix split newId newValue fresh
      exact .ifFalse (conditionIH leading suffix split newId newValue fresh)
        (branchIH leading suffix split newId newValue fresh)

/-- Existing evaluations survive fresh insertion, with exactly the same value
and store. Neither typing nor elaboration of skipped branches is required. -/
theorem Evaluates.insert_fresh {leading suffix : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId}
    (evaluation : Evaluates (leading ++ suffix) initialStore expr value finalStore)
    (fresh : newId ∉ LocalScope.ids suffix) :
    Evaluates (leading ++ (newId, newValue) :: suffix) initialStore expr value finalStore :=
  evaluation_insert_aux evaluation leading suffix rfl newId newValue fresh

theorem Evaluates.weaken_fresh {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value newValue : Core.Value}
    {newId : LocalId} (evaluation : Evaluates environment initialStore expr value finalStore)
    (fresh : newId ∉ LocalScope.ids environment) :
    Evaluates ((newId, newValue) :: environment) initialStore expr value finalStore :=
  Evaluates.insert_fresh (leading := []) evaluation fresh

/-- The allocator supplies the precise local freshness premise needed by evaluation. -/
theorem Evaluates.weaken_allocated {environment : Environment}
    {initialStore finalStore : Core.Store} {expr : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore expr value finalStore)
    (owner : DeclarationId) (newValue : Core.Value) :
    Evaluates ((freshLocalId owner (LocalScope.ids environment), newValue) :: environment)
      initialStore expr value finalStore :=
  evaluation.weaken_fresh (freshLocalId_not_mem owner (LocalScope.ids environment))

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.ScopeExtensionReflectionProperties`
-/

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
  | pair left right leftIH rightIH =>
      cases scopeValid with
      | pair leftScoped rightScoped =>
          cases evaluation with
          | pair leftEvaluation rightEvaluation =>
              exact .pair (leftIH leftEvaluation leftScoped) (rightIH rightEvaluation rightScoped)
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
