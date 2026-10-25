import Solcore.Frontend.RustHull.EffectEnvironmentCorrespondence
import Solcore.Frontend.RustHull.PureCallCorrespondence

/-! Compiler-derived argument constraints and actual reserved references for
concrete Hull builtin correspondence. -/
set_option autoImplicit false
namespace Solcore.Frontend.RustHull.EffectBuiltinCorrespondence
open Core Correspondence PureCallCorrespondence

private def checkWords (arguments : List Lowered) : LowerM PUnit :=
  forIn arguments PUnit.unit fun argument _ => do
    expectType .word argument.type
    pure (.yield PUnit.unit)

private theorem checkedWords {arguments : List Lowered}
    (checked : checkWords arguments = .ok PUnit.unit) :
    ∀ argument ∈ arguments, argument.type = .word := by
  induction arguments with
  | nil => simp
  | cons argument rest ih =>
      by_cases same : argument.type = .word
      · have tail : checkWords rest = .ok PUnit.unit := by
          simpa [checkWords, List.forIn_cons, expectType, same] using checked
        intro value member
        rcases List.mem_cons.mp member with rfl | member
        · exact same
        · exact ih tail value member
      · simp [checkWords, List.forIn_cons, expectType, Ne.symm same, fail,
          Bind.bind, Except.bind] at checked

theorem outer_components {name : String}
    {scope : Scope} {expected : Core.Ty} {arguments : List Lowered} {lowered : Lowered}
    (supported : Effects.supports name = true)
    (compiled : lowerBuiltin scope name expected arguments = .ok lowered) :
    (∀ argument ∈ arguments, argument.type = .word) ∧
    ∃ raw, Effects.lowerBuiltin (scope.temporary (packArguments arguments).type) name
      ((List.range arguments.length).map fun index => projectArgument index arguments.length (.var 0)) = .ok raw ∧
      expected = raw.type ∧ lowered = ⟨expected, LanguageResult.bind expected (packArguments arguments).expression raw.expression⟩ := by
  simp only [lowerBuiltin, supported, ↓reduceIte] at compiled
  obtain ⟨checked, words, compiled⟩ := lower_bind_eq_ok.mp compiled
  cases checked
  obtain ⟨raw, rawCompiled, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, typed, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  exact ⟨checkedWords words, raw, rawCompiled, expectType_eq_of_ok typed, (Except.ok.inj returned).symm⟩

theorem reference_evaluates {slots : List EffectSlot} {scope : Scope} {mapping : Renaming}
    {environment : Environment} {slot : EffectSlot} {reference : Core.Expr}
    (related : EffectEnvironmentRel slots scope mapping environment) (member : slot ∈ slots)
    (compiled : Effects.reference scope slot.name slot.type = .ok reference) (store : Store) :
    Evaluates environment store (reference.rename mapping) (.cellRef slot.type slot.location) store := by
  unfold Effects.reference at compiled
  obtain ⟨⟨binding, index⟩, looked, compiled⟩ := lower_bind_eq_ok.mp compiled
  obtain ⟨guard, _, returned⟩ := lower_bind_eq_ok.mp compiled
  cases guard
  cases returned
  exact .var (related slot member binding index looked)

theorem word_arguments {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) :
    ∃ (expressions : List Core.Expr) (values : List Core.Word),
      arguments = expressions.map (fun expression => Lowered.mk .word expression) ∧
      sources = values.map Semantics.Value.word ∧ targets = values.map Core.Value.word ∧
      expressions.length = values.length := by
  induction related with
  | nil => exact ⟨[], [], rfl, rfl, rfl, rfl⟩
  | @cons argument arguments source sources target targets head tail ih =>
      obtain ⟨expressions, values, rfl, rfl, rfl, lengths⟩ :=
        ih (fun member selected => words member (List.mem_cons_of_mem _ selected))
      have typed := words argument (List.mem_cons_self ..)
      cases argument with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word value =>
              exact ⟨expression :: expressions, value :: values, rfl, rfl, rfl, congrArg Nat.succ lengths⟩

theorem one_word {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 1) :
    ∃ expression value, arguments = [⟨.word, expression⟩] ∧
      sources = [.word value] ∧ targets = [.word value] := by
  obtain ⟨expressions, values, rfl, rfl, rfl, sizes⟩ := word_arguments related words
  simp only [List.length_map] at length
  cases expressions with
  | nil => cases length
  | cons expression rest =>
      have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj length)
      subst rest
      cases values with
      | nil => cases sizes
      | cons value rest =>
          have empty : rest = [] := List.eq_nil_of_length_eq_zero (Nat.succ.inj sizes.symm)
          subst rest
          exact ⟨expression, value, rfl, rfl, rfl⟩

theorem two_words {arguments : List Lowered} {sources : List Semantics.Value}
    {targets : List Core.Value} (related : ArgumentsRel arguments sources targets)
    (words : ∀ argument ∈ arguments, argument.type = .word) (length : arguments.length = 2) :
    ∃ first second left right, arguments = [⟨.word, first⟩, ⟨.word, second⟩] ∧
      sources = [.word left, .word right] ∧ targets = [.word left, .word right] := by
  cases related with
  | nil => cases length
  | @cons first rest source sources target targets head tail =>
      obtain ⟨second, right, rfl, rfl, rfl⟩ := one_word tail
        (fun argument member => words argument (List.mem_cons_of_mem _ member)) (Nat.succ.inj length)
      have typed := words first (List.mem_cons_self ..)
      cases first with
      | mk type expression =>
          simp only at typed
          subst type
          cases head with
          | word left => exact ⟨expression, second, left, right, rfl, rfl, rfl⟩

end Solcore.Frontend.RustHull.EffectBuiltinCorrespondence
