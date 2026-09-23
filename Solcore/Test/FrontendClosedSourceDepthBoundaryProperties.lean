import Solcore.Frontend.ClosedSource
import Solcore.Frontend.LocalReference
import Solcore.Resolved.LocalScope

/- Independent original witnesses and separate whole-Option calculations. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDepthBoundaries
open Solcore Solcore.Frontend

private def groups (spans : Nat → Syntax.SourceSpan) (leaf : Syntax.SourceSpan)
    (name : Syntax.Identifier) : Nat → Syntax.Expr
  | 0 => ⟨leaf, .identifier name⟩
  | n + 1 => ⟨spans n, .group (groups spans leaf name n)⟩

private def blocks (spans : Nat → Syntax.SourceSpan) (returned : Syntax.SourceSpan)
    (child : Syntax.Expr) : Nat → Syntax.Block
  | 0 => ⟨spans 0, [⟨returned, .returnStmt (some child)⟩]⟩
  | n + 1 => ⟨spans (n + 1), [⟨spans n, .block (blocks spans returned child n).value⟩]⟩

variable (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (captured : Resolved.LocalScope RuntimeValue) (store : List RuntimeValue)
  (name : Syntax.Identifier) (id : Resolved.LocalId) (value : RuntimeValue)
  (named : LocalNameTable.Lookup names name.value id)
  (found : Resolved.LocalScope.Lookup captured id value)
  (groupSpans blockSpans : Nat → Syntax.SourceSpan) (leaf returned : Syntax.SourceSpan)

include named found in
private theorem groups_original (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
      (groups groupSpans leaf name n) value store := by
  induction n with
  | zero => exact .reference named found
  | succ n ih => exact .group ih

include named found in
private theorem blocks_original (m n : Nat) :
    ClosedSourceBodyEvaluates owner names captured store
      (blocks blockSpans returned (groups groupSpans leaf name n) m) value store := by
  induction m with
  | zero => exact .expression (groups_original owner names captured store name id value
      named found groupSpans leaf n)
  | succ m ih =>
      apply ClosedSourceBodyEvaluates.block
      cases m <;> exact ih

include named found in
private theorem groups_run (n budget : Nat) :
    evaluateClosedSourceExpression? budget owner names captured store
      (groups groupSpans leaf name n) =
      if n + 1 ≤ budget then some (value, store) else none := by
  induction n generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simp only [groups, evaluateClosedSourceExpression?,
            LocalNameTable.lookup?_iff.mpr named, Resolved.LocalScope.lookup?_iff.mpr found,
            bind, Option.bind_some, pure, Nat.le_add_left, ↓reduceIte]
  | succ n ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceExpression?]
      | succ budget =>
          simpa only [groups, evaluateClosedSourceExpression?, Nat.succ_le_succ_iff] using ih budget

include named found in
private theorem blocks_run (m n budget : Nat) :
    evaluateClosedSourceBody? budget owner names captured store
      (blocks blockSpans returned (groups groupSpans leaf name n) m) =
      if m + n + 2 ≤ budget then some (value, store) else none := by
  induction m generalizing budget with
  | zero =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          simpa only [blocks, evaluateClosedSourceBody?, Nat.zero_add,
            Nat.succ_le_succ_iff, Nat.add_assoc] using
            groups_run owner names captured store name id value named found groupSpans leaf n budget
  | succ m ih =>
      cases budget with
      | zero => simp [evaluateClosedSourceBody?]
      | succ budget =>
          have same : (m + 1) + n + 2 ≤ budget + 1 ↔ m + n + 2 ≤ budget := by omega
          cases m <;> simpa only [blocks, evaluateClosedSourceBody?, same] using ih budget

private theorem cutoff_unique {α : Type} (f : Nat → Option α) (value : α)
    (required previous : Nat)
    (formula : ∀ n, f n = if required ≤ n then some value else none)
    (below : f previous = none) (atNext : f (previous + 1) = some value) :
    required = previous + 1 := by
  have lower : previous < required := by
    by_cases order : required ≤ previous
    · have impossible := formula previous
      rw [if_pos order, below] at impossible
      cases impossible
    · omega
  have upper : required ≤ previous + 1 := by
    by_cases order : required ≤ previous + 1
    · exact order
    · have impossible := formula (previous + 1)
      rw [if_neg order, atNext] at impossible
      cases impossible
  omega

include named found in
theorem independent_groups_determine_the_general_cutoff (n : Nat) :
    ClosedSourceExpressionEvaluates owner names captured store
        (groups groupSpans leaf name n) value store ∧
      ∃ required : Nat, required = n + 1 ∧ ∀ budget,
        evaluateClosedSourceExpression? budget owner names captured store
          (groups groupSpans leaf name n) =
          if required ≤ budget then some (value, store) else none := by
  have original := groups_original owner names captured store name id value
    named found groupSpans leaf n
  obtain ⟨required, _, formula⟩ :=
    Solcore.Frontend.ClosedSourceExpressionEvaluates.exact_depth_threshold original
  have below := groups_run owner names captured store name id value
    named found groupSpans leaf n n
  have atNext := groups_run owner names captured store name id value
    named found groupSpans leaf n (n + 1)
  simp only [Nat.not_succ_le_self, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨original, required, cutoff_unique _ _ required n formula below atNext, formula⟩

include named found in
theorem independent_blocks_determine_the_general_cutoff (m n : Nat) :
    ClosedSourceBodyEvaluates owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) value store ∧
      ∃ required : Nat, required = m + n + 2 ∧ ∀ budget,
        evaluateClosedSourceBody? budget owner names captured store
          (blocks blockSpans returned (groups groupSpans leaf name n) m) =
          if required ≤ budget then some (value, store) else none := by
  have original := blocks_original owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n
  obtain ⟨required, _, formula⟩ :=
    Solcore.Frontend.ClosedSourceBodyEvaluates.exact_depth_threshold original
  have below := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 1)
  have atNext := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 2)
  simp only [show ¬ m + n + 2 ≤ m + n + 1 by omega, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨original, required, cutoff_unique _ _ required (m + n + 1)
    formula below atNext, formula⟩

include named found in
theorem actual_group_boundaries_lift_and_restrict
    (n small large : Nat) (early : small ≤ n) (late : n + 1 ≤ large) :
    evaluateClosedSourceExpression? n owner names captured store
        (groups groupSpans leaf name n) = none ∧
      evaluateClosedSourceExpression? (n + 1) owner names captured store
        (groups groupSpans leaf name n) = some (value, store) ∧
      evaluateClosedSourceExpression? small owner names captured store
        (groups groupSpans leaf name n) = none ∧
      evaluateClosedSourceExpression? large owner names captured store
        (groups groupSpans leaf name n) = some (value, store) := by
  have below := groups_run owner names captured store name id value
    named found groupSpans leaf n n
  have atNext := groups_run owner names captured store name id value
    named found groupSpans leaf n (n + 1)
  simp only [Nat.not_succ_le_self, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨below, atNext,
    Solcore.Frontend.evaluateClosedSourceExpression?_none_of_le early below,
    Solcore.Frontend.evaluateClosedSourceExpression?_monotone late atNext⟩

include named found in
theorem actual_block_boundaries_lift_and_restrict
    (m n small large : Nat) (early : small ≤ m + n + 1) (late : m + n + 2 ≤ large) :
    evaluateClosedSourceBody? (m + n + 1) owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = none ∧
      evaluateClosedSourceBody? (m + n + 2) owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = some (value, store) ∧
      evaluateClosedSourceBody? small owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = none ∧
      evaluateClosedSourceBody? large owner names captured store
        (blocks blockSpans returned (groups groupSpans leaf name n) m) = some (value, store) := by
  have below := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 1)
  have atNext := blocks_run owner names captured store name id value
    named found groupSpans blockSpans leaf returned m n (m + n + 2)
  simp only [show ¬ m + n + 2 ≤ m + n + 1 by omega, ↓reduceIte] at below
  simp only [Nat.le_refl, ↓reduceIte] at atNext
  exact ⟨below, atNext,
    Solcore.Frontend.evaluateClosedSourceBody?_none_of_le early below,
    Solcore.Frontend.evaluateClosedSourceBody?_monotone late atNext⟩

end Tests.ClosedSourceDepthBoundaries
