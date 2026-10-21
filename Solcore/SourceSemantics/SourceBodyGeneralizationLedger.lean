import Solcore.SourceSemantics.SourceBodyTemplateScope
import Solcore.SourceSemantics.SourceCompiledNonTemplateLedger
import Solcore.SourceSemantics.SourceCompiledInitializerOccurrence

/-! Actual completed-cache receipts classify every remaining flexible ledger
variable by its exact initialized source owner. This includes method bodies
and ordinary bodies discovered after the initial worklist. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceBodyGeneralizationLedger
open Frontend SourceInference TypeSystem SourceInferenceSoundness
open SourceCompiledLocalFinalization

/-- A flexible variable in the final solved ledger must come from a literal
retained template owner. Non-template rows are closed by actual specialization. -/
theorem variable_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate = owner.requirement.predicate ∧
      q ∈ owner.binder.scheme.quantified := by
  by_cases template : requirement.id ∈
      sourceLocalSchemeTemplateIds selected.body.finalized.typedSource
  · obtain ⟨owner, _occurrence, contains, sameId, samePredicate, _⟩ :=
      (selected.body.resources.ledger.template_scoped member template).exact_owner
    refine ⟨owner, contains, sameId, samePredicate, ?_⟩
    apply SourceBodyTemplateScope.cached_template_scoped artifact checked position selected contains
    simpa only [samePredicate] using occurs
  · have closed := SourceCompiledNonTemplateLedger.finalized_closed selected.body
      selected.specialized (SourceCompiledNonTemplateLedger.cached_closed cached position)
      member template
    rw [closed] at occurs
    exact False.elim (List.not_mem_nil occurs)

/-- Removing the current binder's template IDs leaves only different actual
owners; neither a row identity nor a predicate-to-owner pairing is assumed. -/
theorem other_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {binder : TypedBinder} {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (notOwn : requirement.id ∉ localSchemeTemplateIds binder)
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate selected.body.finalized.typedSource owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate = owner.requirement.predicate ∧
      owner.binder ≠ binder ∧ q ∈ owner.binder.scheme.quantified := by
  obtain ⟨owner, contains, sameId, samePredicate, quantified⟩ :=
    variable_owner artifact checked position selected member occurs
  refine ⟨owner, contains, sameId, samePredicate, ?_, quantified⟩
  intro sameBinder
  apply notOwn
  rw [sameId, ← sameBinder]
  exact List.mem_map.mpr
    ⟨owner.requirement, LocalSchemeTemplateOwner.requirement_mem contains, rfl⟩

/-- The same offending row identifies a different binder in the actual
inference source, before final substitution, as used by generalization traces. -/
theorem raw_other_owner {raw : Workspace.RawWorkspace} {fuel : Nat}
    {compiled : SourceCoreCompiler.Compiled} {cached : SourceCoreUnifiedCompilation.Compiled}
    (artifact : compiled.artifact? = some cached)
    (checked : checkProgram raw fuel = .ok compiled.program)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (position : cached.indexed.base.functions[index]? = some named)
    (selected : BodySelection compiled named.specialized fuel)
    {binder : TypedBinder} {requirement : SolvedRequirement}
    (member : requirement ∈ selected.body.finalized.solvedRequirements)
    (notOwn : requirement.id ∉
      localSchemeTemplateIds (binder.applySubstitution selected.body.finalized.substitution))
    {q : TypeVarId}
    (occurs : q ∈ TypedTraitResolution.predicateVariables requirement.predicate) :
    ∃ owner : LocalSchemeTemplateOwner,
      ContainsLocalSchemeTemplate (SourceCompiledGeneralizedSoundness.evidenceSource selected) owner ∧
      requirement.id = owner.requirement.templateRequirement ∧
      requirement.predicate =
        (FlexibleSubstitution.applyLocalSchemeTemplateOwner
          selected.body.finalized.substitution owner).requirement.predicate ∧
      owner.binder ≠ binder ∧ q ∈ owner.binder.scheme.quantified := by
  obtain ⟨finalOwner, contains, sameId, samePredicate, distinct, quantified⟩ :=
    other_owner artifact checked position selected member notOwn occurs
  rw [selected.body.resources.source_eq] at contains
  unfold ContainsLocalSchemeTemplate at contains
  rw [FlexibleSubstitution.localSchemeTemplateOwners_applySubstitution] at contains
  obtain ⟨owner, rawContains, transformed⟩ := List.mem_map.mp contains
  subst finalOwner
  refine ⟨owner, rawContains, sameId, samePredicate, ?_, quantified⟩
  intro same
  apply distinct
  exact congrArg (TypedBinder.applySubstitution selected.body.finalized.substitution) same

end Solcore.SourceSemantics.SourceBodyGeneralizationLedger
