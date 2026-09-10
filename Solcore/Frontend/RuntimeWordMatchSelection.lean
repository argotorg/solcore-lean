import Solcore.Frontend.RuntimeWordMatch

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
