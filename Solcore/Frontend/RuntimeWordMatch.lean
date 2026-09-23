import Solcore.Frontend.RuntimeValue
import Solcore.Frontend.WordMatch

/-! Original ordered choice over mixed values. Only visited literal cases require
actual Words; wildcard/default never project values or inspect unvisited cases. -/

set_option autoImplicit false

namespace Solcore.Frontend

/-- Preserve first-match order and original selected syntax; only literal cases
require a Word, while wildcard/default accept every actual mixed value. -/
inductive RuntimeWordMatchChooses :
    RuntimeValue → List Syntax.MatchCase → Option Syntax.Block → Syntax.Block → Nat → Prop where
  | fallback {value : RuntimeValue} {defaultBody : Syntax.Block} :
      RuntimeWordMatchChooses value [] (some defaultBody) defaultBody 0
  | wildcard {value : RuntimeValue} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern none) :
      RuntimeWordMatchChooses value (first :: rest) defaultBody first.value.body 0
  | hit {word : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block}
      (meaning : WordMatchPatternClassifies first.value.pattern (some word)) :
      RuntimeWordMatchChooses (.word word) (first :: rest) defaultBody first.value.body 1
  | miss {word literal : Core.Word} {first : Syntax.MatchCase} {rest : List Syntax.MatchCase}
      {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
      (meaning : WordMatchPatternClassifies first.value.pattern (some literal))
      (different : word ≠ literal)
      (tail : RuntimeWordMatchChooses (.word word) rest defaultBody selected tests) :
      RuntimeWordMatchChooses (.word word) (first :: rest) defaultBody selected (tests + 1)

/-- The original selected block and literal comparison count are unique. -/
theorem RuntimeWordMatchChooses.deterministic
    {value : RuntimeValue} {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {left right : Syntax.Block}
    {leftTests rightTests : Nat}
    (first : RuntimeWordMatchChooses value cases defaultBody left leftTests)
    (second : RuntimeWordMatchChooses value cases defaultBody right rightTests) :
    left = right ∧ leftTests = rightTests := by
  induction first generalizing right rightTests with
  | fallback => cases second; exact ⟨rfl, rfl⟩
  | wildcard shape =>
      cases second with
      | wildcard _ => exact ⟨rfl, rfl⟩
      | hit meaning => cases shape.tag_unique meaning
      | miss meaning _ _ => cases shape.tag_unique meaning
  | hit meaning =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit _ => exact ⟨rfl, rfl⟩
      | miss other different _ => exact False.elim (different (meaning.value_unique other))
  | miss meaning different _ ih =>
      cases second with
      | wildcard shape => cases meaning.tag_unique shape
      | hit other => exact False.elim (different (other.value_unique meaning))
      | miss _ _ tail =>
          obtain ⟨rfl, rfl⟩ := ih tail
          exact ⟨rfl, rfl⟩

private theorem choice_reflect {actual : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (choice : RuntimeWordMatchChooses actual cases defaultBody selected tests) :
    ∀ value : Core.Value, actual = RuntimeValue.ofCore value →
      WordMatchChooses value cases defaultBody selected tests := by
  induction choice with
  | fallback => intro value same; exact .fallback
  | wildcard meaning => intro value same; exact .wildcard meaning
  | @hit word first rest defaultBody meaning =>
      intro value same
      have valueSame : Core.Value.word word = value := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using same)
      subst value
      exact .hit meaning
  | @miss word literal first rest defaultBody selected tests meaning different tail ih =>
      intro value same
      have valueSame : Core.Value.word word = value := RuntimeValue.ofCore_injective
        (by simpa only [RuntimeValue.ofCore] using same)
      subst value
      exact .miss meaning different (ih _ (by simp only [RuntimeValue.ofCore]))

/-- Every embedded old value has exactly its old original-choice derivations,
including arbitrary non-Word values and uninspected suffixes. -/
theorem runtimeWordMatchChooses_ofCore_iff {value : Core.Value}
    {cases : List Syntax.MatchCase} {defaultBody : Option Syntax.Block}
    {selected : Syntax.Block} {tests : Nat} :
    RuntimeWordMatchChooses (RuntimeValue.ofCore value) cases defaultBody selected tests ↔
      WordMatchChooses value cases defaultBody selected tests := by
  constructor
  · intro choice
    exact choice_reflect choice value rfl
  · intro choice
    induction choice with
    | fallback => exact .fallback
    | wildcard meaning => exact .wildcard meaning
    | hit meaning => simpa only [RuntimeValue.ofCore] using RuntimeWordMatchChooses.hit meaning
    | miss meaning different _ ih =>
        simp only [RuntimeValue.ofCore] at ih ⊢
        exact .miss meaning different ih

end Solcore.Frontend

/-!
## Consolidated module: `Solcore.Frontend.RuntimeWordMatchSelection`
-/

/- Original ordered selection only. Counts are visited literal comparisons,
not evaluator depth or execution cost. No projection or suffix inspection. -/

set_option autoImplicit false
namespace Solcore.Frontend

/-- Select an original body and count only visited literal comparisons. -/
def chooseRuntimeWordMatch? (value : RuntimeValue) (cases : List Syntax.MatchCase)
    (defaultBody : Option Syntax.Block) : Option (Syntax.Block × Nat) :=
  match cases with
  | [] => defaultBody.map (fun body => (body, 0))
  | first :: rest =>
      match interpretWordMatchPattern? first.value.pattern with
      | none => none
      | some none => some (first.value.body, 0)
      | some (some literal) =>
          match value with
          | .word word =>
              if word = literal then some (first.value.body, 1)
              else (chooseRuntimeWordMatch? value rest defaultBody).map (fun pair => (pair.1, pair.2 + 1))
          | _ => none

private theorem selection_sound {value : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat}
    (accepted : chooseRuntimeWordMatch? value cases defaultBody = some (selected, tests)) :
    RuntimeWordMatchChooses value cases defaultBody selected tests := by
  induction cases generalizing value selected tests with
  | nil =>
      cases defaultBody with
      | none => simp [chooseRuntimeWordMatch?] at accepted
      | some body =>
          simp only [chooseRuntimeWordMatch?, Option.map_some, Option.some.injEq, Prod.mk.injEq] at accepted
          obtain ⟨rfl, rfl⟩ := accepted
          exact .fallback
  | cons first rest ih =>
      cases pattern : interpretWordMatchPattern? first.value.pattern with
      | none => simp [chooseRuntimeWordMatch?, pattern] at accepted
      | some tag =>
          have meaning := interpretWordMatchPattern?_iff.mp pattern
          cases tag with
          | none =>
              simp only [chooseRuntimeWordMatch?, pattern, Option.some.injEq, Prod.mk.injEq] at accepted
              obtain ⟨rfl, rfl⟩ := accepted
              exact .wildcard meaning
          | some literal =>
              cases value <;> simp only [chooseRuntimeWordMatch?, pattern, reduceCtorEq] at accepted
              rename_i word
              by_cases same : word = literal
              · subst literal
                simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq] at accepted
                obtain ⟨rfl, rfl⟩ := accepted
                exact .hit meaning
              · simp only [same, ↓reduceIte] at accepted
                obtain ⟨⟨body, count⟩, tail, equal⟩ := Option.map_eq_some_iff.mp accepted
                cases equal
                exact .miss meaning same (ih tail)

/-- Executable selection agrees with the independent original-body/count judgment. -/
theorem chooseRuntimeWordMatch?_iff {value : RuntimeValue} {cases : List Syntax.MatchCase}
    {defaultBody : Option Syntax.Block} {selected : Syntax.Block} {tests : Nat} :
    chooseRuntimeWordMatch? value cases defaultBody = some (selected, tests) ↔
      RuntimeWordMatchChooses value cases defaultBody selected tests := by
  constructor
  · exact selection_sound
  · intro choice
    induction choice with
    | fallback => simp only [chooseRuntimeWordMatch?, Option.map_some]
    | wildcard meaning =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning]
    | hit meaning =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning, ↓reduceIte]
    | miss meaning different _ ih =>
        simp only [chooseRuntimeWordMatch?, interpretWordMatchPattern?_iff.mpr meaning,
          different, ↓reduceIte, ih, Option.map_some]

end Solcore.Frontend
