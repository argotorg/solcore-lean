import Solcore.Resolved.Expr
import Solcore.Resolved.Typing
import Solcore.Core.Internal.DerivedForms
import Solcore.Resolved.Eval
import Solcore.Resolved.Identity

/-!
# Scope and renaming

Well-scoped expressions and weakening of `Resolved.Evaluates`, uniform renaming of identities, and
the word less-than builder with explicit identities.
-/

section
-- leanmerge: from Solcore.Resolved.Scope
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
end

section
-- leanmerge: from Solcore.Resolved.Renaming
/-! Uniform renaming of resolved local identities. Both references and let
binders are renamed; literal values and selected primitives remain unchanged.
This operation does not rename source spellings or allocate fresh identities. -/

set_option autoImplicit false

namespace Solcore.Resolved

def LocalScope.mapIds {α : Type} (mapping : LocalId → LocalId)
    (scope : LocalScope α) : LocalScope α :=
  scope.map (fun entry => (mapping entry.1, entry.2))

def Expr.renameIds (mapping : LocalId → LocalId) : Expr → Expr
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .var id => .var (mapping id)
  | .pair left right => .pair (left.renameIds mapping) (right.renameIds mapping)
  | .unary op operand => .unary op (operand.renameIds mapping)
  | .binary op left right => .binary op (left.renameIds mapping) (right.renameIds mapping)
  | .wordLt left right => .wordLt (left.renameIds mapping) (right.renameIds mapping)
  | .letE binder value body =>
      .letE (mapping binder) (value.renameIds mapping) (body.renameIds mapping)
  | .ifE condition thenBranch elseBranch =>
      .ifE (condition.renameIds mapping) (thenBranch.renameIds mapping) (elseBranch.renameIds mapping)

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.RenamingProperties`
-/

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
  | pair left right leftIH rightIH => simp only [renameIds, lower?, leftIH, rightIH]
  | unary op operand ih => simp only [renameIds, lower?, ih]
  | binary op left right leftIH rightIH => simp only [renameIds, lower?, leftIH, rightIH]
  | wordLt left right leftIH rightIH => simp only [renameIds, lower?, leftIH, rightIH]
  | letE binder value body valueIH bodyIH =>
      simp only [renameIds, lower?, valueIH]
      rw [← List.map_cons, bodyIH (binder :: scope)]
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
  | pair left right leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | pair first second => exact .pair (leftIH.mp first) (rightIH.mp second)
      · intro evaluation
        cases evaluation with
        | pair first second => exact .pair (leftIH.mpr first) (rightIH.mpr second)
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
  | wordLt left right leftIH rightIH =>
      constructor
      · intro evaluation
        cases evaluation with
        | wordLt first second => exact .wordLt (leftIH.mp first) (rightIH.mp second)
      · intro evaluation
        cases evaluation with
        | wordLt first second => exact .wordLt (leftIH.mpr first) (rightIH.mpr second)
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
end

section
-- leanmerge: from Solcore.Resolved.WordLessWithIds
/-! An explicit-identity builder for ordered Word less-than. The two operands
are evaluated once, left before right; only their retained values are swapped.
No identity is allocated and no source resolver or expression constructor is
extended. Freshness concerns the outer scope, not inner source binders. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Retain both operand values before comparing the right Word to the left.
The caller supplies both identities; this builder does not enforce hygiene. -/
def Expr.wordLtWithIds (leftId rightId : LocalId) (left right : Expr) : Expr :=
  .letE leftId left
    (.letE rightId right (.binary .wordGt (.var rightId) (.var leftId)))

/-- Structural renaming commutes even for noninjective identity maps. This
identity alone does not assert that such a map preserves hygiene or meaning. -/
@[simp] theorem Expr.renameIds_wordLtWithIds (leftId rightId : LocalId)
    (left right : Expr) (mapping : LocalId → LocalId) :
    (Expr.wordLtWithIds leftId rightId left right).renameIds mapping =
      Expr.wordLtWithIds (mapping leftId) (mapping rightId)
        (left.renameIds mapping) (right.renameIds mapping) :=
  rfl

/-- Exact lowering includes weakening the right operand under the retained
left value. The second identity may already occur in the original scope. -/
theorem Lowers.wordLtWithIds {scope : List LocalId} {leftId rightId : LocalId}
    {left right : Expr} {leftCore rightCore : Core.Expr}
    (lowerLeft : Lowers scope left leftCore)
    (lowerRight : Lowers scope right rightCore)
    (leftFresh : leftId ∉ scope) (different : rightId ≠ leftId) :
    Lowers scope (Expr.wordLtWithIds leftId rightId left right)
      (Core.Expr.wordLt leftCore rightCore) := by
  rw [Core.Expr.wordLt_expansion]
  exact .letE lowerLeft (.letE (lowerRight.weaken_fresh leftFresh)
    (.binary (.var .head) (.var (.tail different .head))))

/-- Both original operands are checked as Words before introducing the
temporary bindings. No freshness assumption is imposed on inner binders. -/
theorem HasType.wordLtWithIds {context : Context} {leftId rightId : LocalId}
    {left right : Expr}
    (leftTyping : HasType context left .word)
    (rightTyping : HasType context right .word)
    (leftFresh : leftId ∉ LocalScope.ids context) (different : rightId ≠ leftId) :
    HasType context (Expr.wordLtWithIds leftId rightId left right) .bool :=
  .letE leftTyping (.letE (rightTyping.weaken_fresh leftFresh .word)
    (.binary (.var .head) (.var (.tail different .head))))

theorem Expr.lower?_wordLtWithIds {scope : List LocalId} {leftId rightId : LocalId}
    {left right : Expr} {leftCore rightCore : Core.Expr}
    (lowerLeft : left.lower? scope = some leftCore)
    (lowerRight : right.lower? scope = some rightCore)
    (leftFresh : leftId ∉ scope) (different : rightId ≠ leftId) :
    (Expr.wordLtWithIds leftId rightId left right).lower? scope =
      some (Core.Expr.wordLt leftCore rightCore) :=
  ((Expr.lower?_sound lowerLeft).wordLtWithIds
    (Expr.lower?_sound lowerRight) leftFresh different).complete

theorem infer_wordLtWithIds {context : Context} {leftId rightId : LocalId}
    {left right : Expr}
    (leftInferred : infer? context left = some .word)
    (rightInferred : infer? context right = some .word)
    (leftFresh : leftId ∉ LocalScope.ids context) (different : rightId ≠ leftId) :
    infer? context (Expr.wordLtWithIds leftId rightId left right) = some .bool :=
  infer_complete ((infer_sound leftInferred).wordLtWithIds
    (infer_sound rightInferred) leftFresh different)

end Solcore.Resolved

/-!
## Consolidated module: `Solcore.Resolved.WordLessWithIdsEvaluationProperties`
-/

/-! Ordered evaluation for explicit comparison temporaries. Freshness prevents
capture of existing right references; original right scoping is additionally
needed for reflection, since insertion can otherwise enable a missing name. -/

set_option autoImplicit false

namespace Solcore.Resolved

/-- Both original operands evaluate exactly once in source order. No type,
allocation or whole-expression scoping premise is needed in this direction. -/
theorem Evaluates.wordLtWithIds
    {environment : Environment} {initialStore middleStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {leftWord rightWord : Core.Word}
    (leftEvaluation : Evaluates environment initialStore left (.word leftWord) middleStore)
    (rightEvaluation : Evaluates environment middleStore right (.word rightWord) finalStore)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    Evaluates environment initialStore (Expr.wordLtWithIds leftId rightId left right)
      (.bool (decide (leftWord < rightWord))) finalStore :=
  .letE leftEvaluation (.letE (rightEvaluation.weaken_fresh leftFresh)
    (.binary (.var .head) (.var (.tail different .head)) rfl))

/-- Reflection recovers the original right evaluation, not an evaluation enabled
by its new surrounding temporary. The second temporary may shadow an outer ID. -/
theorem Evaluates.wordLtWithIds_inv
    {environment : Environment} {initialStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {value : Core.Value}
    (evaluation : Evaluates environment initialStore
      (Expr.wordLtWithIds leftId rightId left right) value finalStore)
    (rightScoped : WellScoped (LocalScope.ids environment) right)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    ∃ leftWord rightWord middleStore,
      Evaluates environment initialStore left (.word leftWord) middleStore ∧
      Evaluates environment middleStore right (.word rightWord) finalStore ∧
      value = .bool (decide (leftWord < rightWord)) := by
  cases evaluation with
  | @letE _ _ _ _ _ _ _ boundLeft _ leftEvaluation bodyEvaluation =>
      cases bodyEvaluation with
      | @letE _ _ _ _ _ _ _ boundRight _ rightEvaluation comparison =>
          cases comparison with
          | binary rightReference leftReference applied =>
              cases rightReference with
              | var foundRight =>
                  cases foundRight.value_unique .head
                  cases leftReference with
                  | var foundLeft =>
                      cases foundLeft.value_unique (.tail different .head)
                      cases boundRight <;> cases boundLeft <;>
                        simp only [Core.BinaryOp.apply, reduceCtorEq] at applied
                      case word.word rightWord leftWord =>
                        cases applied
                        exact ⟨leftWord, rightWord, _, leftEvaluation,
                          rightScoped.evaluates_weaken_fresh_iff leftFresh |>.mp rightEvaluation, rfl⟩

/-- Exact two-child semantics under the necessary original-right scope and
hygiene premises. No executable-run assumption occurs on either side. -/
theorem wordLtWithIds_evaluates_iff
    {environment : Environment} {initialStore finalStore : Core.Store}
    {leftId rightId : LocalId} {left right : Expr} {value : Core.Value}
    (rightScoped : WellScoped (LocalScope.ids environment) right)
    (leftFresh : leftId ∉ LocalScope.ids environment) (different : rightId ≠ leftId) :
    Evaluates environment initialStore (Expr.wordLtWithIds leftId rightId left right)
      value finalStore ↔
      ∃ leftWord rightWord middleStore,
        Evaluates environment initialStore left (.word leftWord) middleStore ∧
        Evaluates environment middleStore right (.word rightWord) finalStore ∧
        value = .bool (decide (leftWord < rightWord)) := by
  constructor
  · intro evaluation
    exact evaluation.wordLtWithIds_inv rightScoped leftFresh different
  · rintro ⟨leftWord, rightWord, middleStore, leftEvaluation, rightEvaluation, rfl⟩
    exact leftEvaluation.wordLtWithIds rightEvaluation leftFresh different

end Solcore.Resolved
end
