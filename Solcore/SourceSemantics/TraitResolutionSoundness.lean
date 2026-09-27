import Solcore.Frontend.TypedTraitResolution
import Solcore.Frontend.TraitResolutionProperties
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

mutual

/-- A generic resolver evidence certificate reconstructs a represented
semantic evidence tree and its declarative validity derivation. -/
theorem resolutionEvidenceValid_sound
    {rules : List ProgramImplRule} {goal : ProgramPredicate}
    {retained : TypedTraitResolution.Evidence}
    (valid : TraitResolution.ResolutionEvidenceValid
      (TypedTraitResolution.programOfRules rules) goal retained) :
    ∃ semantic,
      ImplementationEvidenceRepresents retained semantic ∧
        EvidenceValid [] rules goal semantic := by
  cases valid with
  | byImpl rule_mem id_eq matched premises =>
      obtain ⟨semanticPremises, representsPremises, validPremises⟩ :=
        resolutionPremisesValid_sound premises
      refine ⟨TraitEvidence.implementation goal _ semanticPremises,
        .byImpl representsPremises, ?_⟩
      apply EvidenceValid.implementation rule_mem id_eq
      · apply matchImplHead?_sound
        simpa [TypedTraitResolution.programOfRules,
          TypedTraitResolution.headMatcher] using matched
      · exact validPremises

/-- The premise-list certificate is converted pointwise while preserving the
goal order and retained-evidence shape. -/
theorem resolutionPremisesValid_sound
    {rules : List ProgramImplRule} {goals : List ProgramPredicate}
    {retained : List TypedTraitResolution.Evidence}
    (valid : TraitResolution.ResolutionPremisesValid
      (TypedTraitResolution.programOfRules rules) goals retained) :
    ∃ semantic,
      Forall₂ ImplementationEvidenceRepresents retained semantic ∧
        Forall₂ (EvidenceValid [] rules) goals semantic := by
  cases valid with
  | nil => exact ⟨[], .nil, .nil⟩
  | cons head tail =>
      obtain ⟨semanticHead, representsHead, validHead⟩ :=
        resolutionEvidenceValid_sound head
      obtain ⟨semanticTail, representsTail, validTail⟩ :=
        resolutionPremisesValid_sound tail
      exact ⟨semanticHead :: semanticTail,
        .cons representsHead representsTail,
        .cons validHead validTail⟩

end

/-- Successful typed resolution produces a represented semantic evidence tree
that is valid independently of fuel, memoization, or resolver priority. -/
theorem resolve_success_evidenceValid
    {rules : List ProgramImplRule} {maxDepth : Nat}
    {goal : ProgramPredicate} {retained : TypedTraitResolution.Evidence}
    (success : (TypedTraitResolution.resolve rules maxDepth goal).outcome =
      .success retained) :
    ∃ semantic,
      ImplementationEvidenceRepresents retained semantic ∧
        EvidenceValid [] rules goal semantic := by
  apply resolutionEvidenceValid_sound
  apply TraitResolution.resolve_success_sound
  simpa [TypedTraitResolution.resolve] using success

/-- Successful typed resolution entails its goal in the declarative trait
system with no explicit assumptions. -/
theorem resolve_success_entails
    {rules : List ProgramImplRule} {maxDepth : Nat}
    {goal : ProgramPredicate} {retained : TypedTraitResolution.Evidence}
    (success : (TypedTraitResolution.resolve rules maxDepth goal).outcome =
      .success retained) :
    Entails [] rules goal := by
  obtain ⟨semantic, _, valid⟩ := resolve_success_evidenceValid success
  exact ⟨semantic, valid⟩

/-- The source-inference implementation wrapper around successful resolver
evidence satisfies the retained-evidence bridge judgment. -/
theorem resolve_success_retainedEvidenceValid
    {rules : List ProgramImplRule} {maxDepth : Nat}
    {goal : ProgramPredicate} {retained : TypedTraitResolution.Evidence}
    (success : (TypedTraitResolution.resolve rules maxDepth goal).outcome =
      .success retained) :
    RetainedEvidenceValid [] rules goal
      (.implementation retained) := by
  obtain ⟨semantic, represents, valid⟩ :=
    resolve_success_evidenceValid success
  exact .intro (.implementation represents) valid

end TraitResolutionSoundness

end Solcore.SourceSemantics
