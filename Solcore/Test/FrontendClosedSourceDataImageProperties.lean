import Solcore.Frontend.ClosedSourceDataExpressionProperties
import Solcore.Frontend.ClosedSourceEvaluation
import Solcore.Frontend.LocalExpressionEvaluationProperties
import Solcore.Frontend.RuntimeValueProperties

/- Independent original paths keep arbitrary Core payloads and lexical rows literal. -/
set_option autoImplicit false
namespace Tests.ClosedSourceDataImages
open Solcore Solcore.Frontend

private def branch (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 0, .tuple ⟨spans 1, [
    ⟨spans 2, .group ⟨spans 3, .identifier left⟩⟩,
    ⟨spans 4, .tuple ⟨spans 5, []⟩⟩,
    ⟨spans 6, .identifier right⟩,
    ⟨spans 7, .literal literal⟩]⟩⟩

private def source (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (guard left right : Syntax.Identifier) : Syntax.Expr :=
  ⟨spans 8, .conditional ⟨spans 9, .identifier guard⟩ (spans 10)
    (branch spans literal left right) (spans 11) (branch spans literal right left)⟩

private def result (left right : Core.Value) (word : Core.Word) : Core.Value :=
  .pair left (.pair .unit (.pair right (.word word)))

private def chosenResult (choice : Bool) (left right : Core.Value) (word : Core.Word) : Core.Value :=
  if choice then result left right word else result right left word

private theorem mapped_lookup {environment : Resolved.Environment} {id : Resolved.LocalId}
    {value : Core.Value} (found : Resolved.LocalScope.Lookup environment id value) :
    Resolved.LocalScope.Lookup
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      id (RuntimeValue.ofCore value) := by
  induction found with
  | head => exact .head
  | tail different _ ih => exact .tail different ih

private theorem branch_syntax (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) : ClosedSourceDataExpression (branch spans literal left right) :=
  .many (.group .reference) (.many .unit (.pair .reference .literal))

private theorem original_branches (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
    (left right : Syntax.Identifier) (owner : Resolved.DeclarationId) (names : LocalNameTable)
    (environment : Resolved.Environment) (store : Core.Store)
    (leftId rightId : Resolved.LocalId) (leftValue rightValue : Core.Value) (word : Core.Word)
    (leftNamed : LocalNameTable.Lookup names left.value leftId)
    (rightNamed : LocalNameTable.Lookup names right.value rightId)
    (leftFound : Resolved.LocalScope.Lookup environment leftId leftValue)
    (rightFound : Resolved.LocalScope.Lookup environment rightId rightValue)
    (meaning : WordLiteralDenotes literal word) :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) (branch spans literal left right)
      (RuntimeValue.ofCore (result leftValue rightValue word)) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store (branch spans literal left right)
      (result leftValue rightValue word) store := by
  constructor
  · simp only [result, RuntimeValue.ofCore]
    exact .many (.group (.reference leftNamed (mapped_lookup leftFound)))
      (.many .unit (.pair (.reference rightNamed (mapped_lookup rightFound)) (.wordLiteral meaning)))
  · exact .many (.group (.identifier leftNamed leftFound))
      (.many .unit (.pair (.identifier rightNamed rightFound) (.wordLiteral meaning)))

section Family
variable (spans : Nat → Syntax.SourceSpan) (literal : Syntax.CoreLiteral)
  (guard left right : Syntax.Identifier) (choice : Bool)
  (owner : Resolved.DeclarationId) (names : LocalNameTable)
  (environment : Resolved.Environment) (store : Core.Store)
  (guardId leftId rightId : Resolved.LocalId) (leftValue rightValue : Core.Value) (word : Core.Word)
  (guardNamed : LocalNameTable.Lookup names guard.value guardId)
  (leftNamed : LocalNameTable.Lookup names left.value leftId)
  (rightNamed : LocalNameTable.Lookup names right.value rightId)
  (guardFound : Resolved.LocalScope.Lookup environment guardId (.bool choice))
  (leftFound : Resolved.LocalScope.Lookup environment leftId leftValue)
  (rightFound : Resolved.LocalScope.Lookup environment rightId rightValue)
  (meaning : WordLiteralDenotes literal word)

include guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning

local notation "original" => source spans literal guard left right
local notation "expected" => chosenResult choice leftValue rightValue word

/-- Both actual Bool paths have separately constructed closed/local original derivations. -/
theorem independent_original_data_paths :
    ClosedSourceDataExpression original ∧
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original
      (RuntimeValue.ofCore expected) (store.map RuntimeValue.ofCore) ∧
    LocalExpressionEvaluates names environment store original expected store := by
  have yes := original_branches spans literal left right owner names environment store
    leftId rightId leftValue rightValue word leftNamed rightNamed leftFound rightFound meaning
  have no := original_branches spans literal right left owner names environment store
    rightId leftId rightValue leftValue word rightNamed leftNamed rightFound leftFound meaning
  refine ⟨.conditional .reference (branch_syntax spans literal left right)
    (branch_syntax spans literal right left), ?_⟩
  cases choice with
  | false =>
      simp only [chosenResult, Bool.false_eq_true, ↓reduceIte]
      exact ⟨.conditionalFalse (.reference guardNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup guardFound)) no.1,
        .ifFalse (.identifier guardNamed guardFound) no.2⟩
  | true =>
      simp only [chosenResult, ↓reduceIte]
      exact ⟨.conditionalTrue (.reference guardNamed (by simpa only [RuntimeValue.ofCore] using mapped_lookup guardFound)) yes.1,
        .ifTrue (.identifier guardNamed guardFound) yes.2⟩

include owner in
/-- Whole original resolution and exact runtime identity lowering are independently available. -/
theorem independent_full_resolution_and_lowering :
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store := by
  let yes : Resolved.Expr := .pair (.var leftId) (.pair .unit (.pair (.var rightId) (.word word)))
  let no : Resolved.Expr := .pair (.var rightId) (.pair .unit (.pair (.var leftId) (.word word)))
  let resolved : Resolved.Expr := .ifE (.var guardId) yes no
  have resolution : ResolvesLocalExpression names original resolved :=
    .conditional (.identifier guardNamed)
      (.many (.group (.identifier leftNamed)) (.many .unit (.pair (.identifier rightNamed) (.wordLiteral meaning))))
      (.many (.group (.identifier rightNamed)) (.many .unit (.pair (.identifier leftNamed) (.wordLiteral meaning))))
  obtain ⟨guardIndex, guardAt, _⟩ := guardFound.indexed
  obtain ⟨leftIndex, leftAt, _⟩ := leftFound.indexed
  obtain ⟨rightIndex, rightAt, _⟩ := rightFound.indexed
  let yesCore : Core.Expr := .pair (.var leftIndex) (.pair .unit (.pair (.var rightIndex) (.word word)))
  let noCore : Core.Expr := .pair (.var rightIndex) (.pair .unit (.pair (.var leftIndex) (.word word)))
  let core : Core.Expr := .ifE (.var guardIndex) yesCore noCore
  have lowered : Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core :=
    .ifE (.var guardAt)
      (.pair (.var leftAt) (.pair .unit (.pair (.var rightAt) .word)))
      (.pair (.var rightAt) (.pair .unit (.pair (.var leftAt) .word)))
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  exact ⟨resolved, core, resolution, lowered, (resolution.core_evaluates_iff lowered).mp paths.2.2⟩

/-- The raw bridge identifies every actual result with the independent original endpoint. -/
theorem all_actual_local_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ClosedSourceExpressionEvaluates owner names
      (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
      (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
    actualValue = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore := by
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  constructor
  · intro actual
    obtain ⟨value, finalStore, same, finalSame, old⟩ := paths.1.local_evaluates_iff.mp actual
    obtain ⟨rfl, rfl⟩ := old.deterministic paths.2.2
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact paths.1.local_evaluates_iff.mpr ⟨expected, store, rfl, rfl, paths.2.2⟩

/-- The Core bridge is consumed in both directions at independently recovered runtime indices. -/
theorem all_actual_core_images {actualValue : RuntimeValue} {actualFinal : List RuntimeValue} :
    ∃ resolved core,
      ResolvesLocalExpression names original resolved ∧
      Resolved.Lowers (Resolved.LocalScope.ids environment) resolved core ∧
      Core.Evaluates (Resolved.LocalScope.values environment) store core expected store ∧
      (ClosedSourceExpressionEvaluates owner names
        (environment.map (fun entry => (entry.1, RuntimeValue.ofCore entry.2)))
        (store.map RuntimeValue.ofCore) original actualValue actualFinal ↔
       actualValue = RuntimeValue.ofCore expected ∧ actualFinal = store.map RuntimeValue.ofCore) := by
  obtain ⟨resolved, core, resolution, lowered, independent⟩ :=
    independent_full_resolution_and_lowering spans literal guard left right choice owner names environment store
      guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  have paths := independent_original_data_paths spans literal guard left right choice owner names environment store
    guardId leftId rightId leftValue rightValue word guardNamed leftNamed rightNamed guardFound leftFound rightFound meaning
  refine ⟨resolved, core, resolution, lowered, independent, ?_⟩
  constructor
  · intro actual
    obtain ⟨value, finalStore, same, finalSame, evaluated⟩ :=
      (paths.1.core_evaluates_iff resolution lowered).mp actual
    obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic evaluated independent
    exact ⟨same, finalSame⟩
  · rintro ⟨rfl, rfl⟩
    exact (paths.1.core_evaluates_iff resolution lowered).mpr
      ⟨expected, store, rfl, rfl, independent⟩

end Family
end Tests.ClosedSourceDataImages
