import Solcore.Frontend.TypedTraitResolution
import Solcore.SourceSemantics.Traits

/-!
Soundness bridge from the executable typed implementation-head matcher to the
declarative source-level implementation-head instantiation judgment.

This module deliberately stops at one successful head match.  Evidence-tree
soundness for the generic tabled resolver is layered on top separately.
-/

set_option autoImplicit false

namespace Solcore.SourceSemantics

open Frontend TypeSystem

namespace TraitResolutionSoundness

/-- Forget the frontend certificate wrapper while retaining both simultaneous
replacement maps unchanged. -/
def toImplSubstitution
    (substitution : TypedTraitResolution.RuleMatchSubstitution) :
    ImplSubstitution := {
  parameters := substitution.parameters
  variables := substitution.variables
}

@[simp] theorem toImplSubstitution_parameters
    (substitution : TypedTraitResolution.RuleMatchSubstitution) :
    (toImplSubstitution substitution).parameters = substitution.parameters :=
  rfl

@[simp] theorem toImplSubstitution_variables
    (substitution : TypedTraitResolution.RuleMatchSubstitution) :
    (toImplSubstitution substitution).variables = substitution.variables :=
  rfl

/-- The frontend and declarative simultaneous substitutions have identical
action on source types. -/
theorem toImplSubstitution_applyType
    (substitution : TypedTraitResolution.RuleMatchSubstitution)
    (type : Ty) :
    (toImplSubstitution substitution).applyType type =
      substitution.applyType type := by
  induction type with
  | «variable» metavariable => rfl
  | «parameter» parameter => rfl
  | constructor constructor => rfl
  | application function argument function_induction argument_induction =>
      simp only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType]
      rw [function_induction, argument_induction]
  | function parameter result parameter_induction result_induction =>
      simp only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType]
      rw [parameter_induction, result_induction]
  | product left right left_induction right_induction =>
      simp only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType]
      rw [left_induction, right_induction]
  | mapping key value key_induction value_induction =>
      simp only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType]
      rw [key_induction, value_induction]
  | proxy inner induction =>
      simpa only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType] using
        congrArg Ty.proxy induction
  | comptime inner induction =>
      simpa only [ImplSubstitution.applyType,
        TypedTraitResolution.RuleMatchSubstitution.applyType] using
        congrArg Ty.comptime induction
  | error => rfl

/-- The frontend and declarative simultaneous substitutions have identical
action on trait predicates. -/
theorem toImplSubstitution_applyPredicate
    (substitution : TypedTraitResolution.RuleMatchSubstitution)
    (predicate : ProgramPredicate) :
    (toImplSubstitution substitution).applyPredicate predicate =
      substitution.applyPredicate predicate := by
  cases predicate with
  | mk trait subject arguments =>
      simp only [ImplSubstitution.applyPredicate,
        TypedTraitResolution.RuleMatchSubstitution.applyPredicate]
      congr 1
      · exact toImplSubstitution_applyType substitution subject
      · apply List.map_congr_left
        intro type member
        exact toImplSubstitution_applyType substitution type

/-- Every successful executable typed implementation-head match is validated by
the independent declarative instantiation relation. -/
theorem matchImplHead?_sound
    {rule : ProgramImplRule} {goal : ProgramPredicate}
    {premises : List ProgramPredicate}
    (matched : TypedTraitResolution.matchImplHead? rule goal = some premises) :
    ImplHeadInstantiates rule goal premises := by
  obtain ⟨substitution, certificate⟩ :=
    TypedTraitResolution.matchImplHead?_certificate matched
  cases certificate with
  | intro parameters_nodup variables_nodup parameter_domain variable_domain
      head_eq premises_eq =>
      let declarative := toImplSubstitution substitution
      apply ImplHeadInstantiates.intro declarative
      · constructor
        · constructor
          · exact parameters_nodup
          · rw [ParameterSubstitution.domain, toImplSubstitution_parameters,
              parameter_domain]
        · constructor
          · exact variables_nodup
          · rw [toImplSubstitution_variables, variable_domain]
      · rw [toImplSubstitution_applyPredicate]
        exact head_eq
      · rw [← premises_eq]
        apply List.map_congr_left
        intro predicate member
        rw [toImplSubstitution_applyPredicate]

end TraitResolutionSoundness

end Solcore.SourceSemantics
