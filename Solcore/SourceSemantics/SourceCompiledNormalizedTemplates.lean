import Solcore.SourceSemantics.SourceCompiledNormalizedFormation

/-! Whole-body producer formation follows the real solver's row correspondence
to the exact templates owned by retained generalized initializers. No predicate
formation is inferred from evidence validity or template ownership alone. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledLocalFinalization
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceInferenceNormalizedCoercionFormation

private theorem solved_predicates_formed
    {context : SourceInference.Context} {state : State}
    {rows : List Requirement} {solved : List SolvedRequirement}
    {semantic : SourceSemantics.Context}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧ row.predicate = Detail.applyPredicate state requirement.predicate ∧
      Detail.solveRequirementEvidence context state requirement = .ok row.evidence) rows solved)
    (formed : ∀ requirement ∈ rows, PredicateAdmissible semantic
      (Detail.applyPredicate state requirement.predicate)) :
    ∀ row ∈ solved, PredicateAdmissible semantic row.predicate := by
  induction corresponds with
  | nil => simp
  | @cons requirement row requirements solved head tail ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · rw [head.2.1]
      exact formed requirement (by simp)
    · exact ih (fun requirement member => formed requirement (by simp [member])) candidate member

namespace Selected
variable {raw : Workspace.RawWorkspace} {compiled : SourceCoreCompiler.Compiled}
  {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}

theorem normalizedSolvedLedger (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true) :
    ∀ requirement ∈ selected.body.finalized.solvedRequirements,
      PredicateAdmissible semantic requirement.predicate := by
  apply solved_predicates_formed (solveRequirements_corresponds selected.body.resources.solve_success)
  intro requirement member
  rw [selected.body.solver_requirements] at member
  have formed := (selected.normalizedBodyFormation checked signatures parameters owner residual).2.requirements
    requirement member
  simpa only [Detail.applyPredicate, ← selected.body.resources.substitution_eq] using formed

/-- A retained template's predicate equals the exact solved row whose
formation was proved through the complete original producer traversal. -/
theorem normalizedTemplatePredicate (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {semantic : SourceSemantics.Context}
    (signatures : semantic.signatures = compiled.program.signatures)
    (parameters : semantic.typeParameters = selected.signature.scheme.parameters)
    (owner : semantic.currentDeclaration = some selected.signature.id)
    (residual : semantic.residualTypeVariables = true)
    {template : LocalSchemeTemplateOwner}
    (contains : ContainsLocalSchemeTemplate selected.body.finalized.typedSource template) :
    PredicateAdmissible semantic template.requirement.predicate := by
  obtain ⟨requirement, filtered, _, predicateEq, _⟩ := selected.body.resources.ledger.template_exact contains
  have present : requirement ∈ selected.body.finalized.solvedRequirements := by
    have filteredMember := filtered.symm ▸ List.mem_singleton_self requirement
    exact (List.mem_filter.mp filteredMember).1
  exact predicateEq ▸ selected.normalizedSolvedLedger checked signatures parameters owner residual requirement present

/-- Any actual finalized initializer receives qualified predicate formation,
including nested declarations and for-header items. -/
theorem normalizedBindingPredicates (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binding : InitializedLetBinding}
    (retained : binding ∈ initializedLetBindings selected.body.finalized.typedSource) :
    ∀ requirement ∈ binding.binder.schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target binding.binder) requirement.predicate := by
  intro requirement member
  apply selected.normalizedTemplatePredicate checked
    (semantic := localSchemeInitializerContext target binding.binder) signatures parameters owner residual
    (template := {binder := binding.binder, initializer := binding.initializer, requirement})
  exact List.mem_flatMap.mpr ⟨binding, retained, List.mem_map.mpr ⟨requirement, member, rfl⟩⟩

/-- The input is a real raw retained template, transformed by this exact
finalizer. It directly supplies the finalPredicates certificate interface. -/
theorem originalBindingPredicates (selected : Selected compiled row fuel)
    (checked : Frontend.checkProgram raw fuel = .ok compiled.program)
    {target : SourceSemantics.Context}
    (signatures : target.signatures = compiled.program.signatures)
    (parameters : target.typeParameters = selected.signature.scheme.parameters)
    (owner : target.currentDeclaration = some selected.signature.id)
    (residual : target.residualTypeVariables = true)
    {binder : TypedBinder} {initializer : NodeId}
    (retained : ∀ requirement ∈ binder.schemeRequirements,
      ContainsLocalSchemeTemplate
        (selected.body.returned.toTypedSource (selected.body.body.statements.map NodeId.statement))
        {binder, initializer, requirement}) :
    ∀ requirement ∈ (binder.applySubstitution selected.body.finalized.substitution).schemeRequirements,
      PredicateAdmissible (localSchemeInitializerContext target
        (binder.applySubstitution selected.body.finalized.substitution)) requirement.predicate := by
  intro requirement member
  rw [FlexibleSubstitution.applyTypedBinder_schemeRequirements] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  apply selected.normalizedTemplatePredicate checked
    (semantic := localSchemeInitializerContext target
      (binder.applySubstitution selected.body.finalized.substitution)) signatures parameters owner residual
    (template := FlexibleSubstitution.applyLocalSchemeTemplateOwner selected.body.finalized.substitution
      {binder, initializer, requirement := original})
  rw [selected.body.resources.source_eq]
  exact FlexibleSubstitution.ContainsLocalSchemeTemplate.applySubstitution
    selected.body.finalized.substitution (retained original originalMember)

end Selected
end Solcore.SourceSemantics.SourceCompiledLocalFinalization
