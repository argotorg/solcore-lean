import Solcore.SourceSemantics.Dynamic.LocalSchemes

/-! Focused boundary tests for dynamic qualified-local instantiation. -/

set_option autoImplicit false

namespace Solcore.Test.SourceSemanticsLocalSchemes

open Frontend
open Frontend.SourceInference
open SourceSemantics
open SourceSemantics.Dynamic
open TypeSystem

private def templateId : RequirementId := ⟨200⟩
private def actualId : RequirementId := ⟨201⟩

private def templatePredicate (fresh : TypeVarId) : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate (.variable fresh)

private def actualPredicate : ProgramPredicate :=
  ProgramSignatures.builtinIntPredicate .word

private def templateRequirement (fresh : TypeVarId) :
    LocalSchemeRequirement := {
  templateRequirement := templateId
  predicate := templatePredicate fresh
}

private def binder (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) : TypedBinder := {
  id := ⟨owner, 200⟩
  name := "qualified"
  scheme := {
    quantified := [fresh]
    body := .function (.variable fresh) (.variable fresh)
  }
  schemeRequirements := [templateRequirement fresh]
}

private def templateRow (fresh : TypeVarId) : SolvedRequirement := {
  id := templateId
  predicate := templatePredicate fresh
  evidence := .assumption (templatePredicate fresh)
}

private def actualRow : SolvedRequirement := {
  id := actualId
  predicate := actualPredicate
  evidence := .assumption actualPredicate
}

private def useContext (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    Solcore.SourceSemantics.Context :=
  (((Context.ofSignatures signatures).withAssumptions
      [actualPredicate]).withSolvedRequirements
    [templateRow fresh, actualRow]).withLocal
      (binder owner fresh).id (binder owner fresh).scheme
      (binder owner fresh).schemeRequirements

private def callerEvidence : EvidenceEnvironment :=
  [(actualPredicate, .implementation actualPredicate
    ProgramSignatures.builtinIntWordRule.id [])]

private theorem formation (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    LocalSchemeRequirementsWellFormed (useContext signatures owner fresh)
      (binder owner fresh) := by
  constructor
  · simp [localSchemeTemplateIds, binder, templateRequirement]
  · intro requirement member
    simp [binder] at member
    subst requirement
    constructor
    · constructor
      · constructor
        · constructor
          · simp [useContext, localSchemeInitializerContext, binder,
              Context.ofSignatures, Context.withAssumptions,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables]
          · intro parameter parameterMember
            simp [useContext, localSchemeInitializerContext, binder,
              Context.ofSignatures, Context.withAssumptions,
              Context.withSolvedRequirements, Context.withLocal,
              Context.withTypeVariables] at parameterMember
        · apply TypeWellScoped.variable
          simp [admissibleTypeVariables, useContext,
            localSchemeInitializerContext, binder, Context.ofSignatures,
            Context.withAssumptions, Context.withSolvedRequirements,
            Context.withLocal, Context.withTypeVariables]
      · intro argument argumentMember
        simp [templateRequirement, templatePredicate,
          ProgramSignatures.builtinIntPredicate] at argumentMember
      · rfl
    · refine ⟨fresh, by simp [binder], ?_⟩
      simp [templateRequirement, templatePredicate,
        ProgramSignatures.builtinIntPredicate,
        Frontend.TypedTraitResolution.predicateVariables,
        TypeSystem.Ty.freeVariables]
    · refine ⟨templateRow fresh, ?_, rfl, rfl, rfl⟩
      change [templateRow fresh, actualRow].filter
        (fun candidate => candidate.id == (templateRow fresh).id) =
          [templateRow fresh]
      rfl

private theorem schemeWellFormed (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    SchemeWellFormed (useContext signatures owner fresh)
      (binder owner fresh).scheme := by
  constructor
  · simp [TypeParameterBindersWellFormed, useContext, Context.ofSignatures,
      Context.withAssumptions, Context.withSolvedRequirements,
      Context.withLocal]
  · simp [binder]
  · apply TypeWellScoped.function <;> apply TypeWellScoped.variable <;>
      simp [binder, admissibleTypeVariables, useContext, Context.ofSignatures,
        Context.withAssumptions, Context.withSolvedRequirements,
        Context.withLocal]

private theorem builtinHeadInstantiates :
    ImplHeadInstantiates ProgramSignatures.builtinIntWordRule
      actualPredicate [] := by
  refine .intro { parameters := [], variables := [] } ?_ rfl rfl
  exact ⟨ParameterSubstitution.exact_empty, ExactSubstitution.empty⟩

private theorem closedEvidenceValid (signatures : ProgramSignatures) :
    EvidenceValid [] signatures.resolutionRules actualPredicate
      (.implementation actualPredicate
        ProgramSignatures.builtinIntWordRule.id []) := by
  exact .implementation
    (by simp [ProgramSignatures.resolutionRules,
      ProgramSignatures.builtinResolutionRules])
    rfl builtinHeadInstantiates .nil

private theorem producesEvidence (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    RequirementsProduceEnvironment (useContext signatures owner fresh)
      callerEvidence [actualId] [actualPredicate] callerEvidence := by
  apply RequirementsProduceEnvironment.cons
  · apply RequirementProducesEvidence.intro
      (requirement := actualRow)
      (openEvidence := .assumption actualPredicate)
    · exact ⟨by simp [useContext, Context.withLocal,
        Context.withSolvedRequirements], rfl⟩
    · rfl
    · exact .assumption actualPredicate
    · apply SolvedRequirementValid.intro
      exact .intro (.assumption actualPredicate)
        (.assumption (by simp [useContext, Context.withLocal,
          Context.withSolvedRequirements, Context.withAssumptions,
          actualRow]))
    · exact .assumption .head
    · exact closedEvidenceValid signatures
  · exact .nil

private theorem runtimeInstantiation (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    LocalSchemeRuntimeInstantiation (useContext signatures owner fresh)
      callerEvidence (binder owner fresh) (.function .word .word) [actualId]
      [(fresh, .word)] callerEvidence := by
  refine {
    formation := formation signatures owner fresh
    scheme_well_formed := schemeWellFormed signatures owner fresh
    exact := ExactSubstitution.singleton fresh .word
    range := ?_
    result := ?_
    actual_requirements_unique := by simp [actualId]
    actual_templates_disjoint := ?_
    produces := ?_
  }
  · intro metavariable replacement member
    simp only [List.mem_cons, List.mem_nil_iff, or_false,
      Prod.mk.injEq] at member
    rcases member with ⟨rfl, rfl⟩
    exact {
      binders := by
        simp [TypeParameterBindersWellFormed, useContext,
          Context.ofSignatures, Context.withAssumptions,
          Context.withSolvedRequirements, Context.withLocal]
      typeWellScoped := .builtin .word
    }
  · simp [binder, TypeSystem.Substitution.apply,
      TypeSystem.Substitution.lookup?]
  · intro id actualMember templateMember
    have actualEq : id = actualId := by simpa using actualMember
    have templateEq : id = templateId := by
      simpa [localSchemeTemplateIds, binder, templateRequirement] using
        templateMember
    exact (show actualId ≠ templateId by decide) (actualEq.symm.trans templateEq)
  · simpa [instantiateLocalSchemePredicates, binder, templateRequirement,
      templatePredicate, actualPredicate,
      Frontend.TypedTraitResolution.applySubstitution,
      ProgramSignatures.builtinIntPredicate, TypeSystem.Substitution.apply,
      TypeSystem.Substitution.lookup?] using
      (producesEvidence signatures owner fresh)

private theorem callerCovers (signatures : ProgramSignatures)
    (owner : Resolved.DeclarationId) (fresh : TypeVarId) :
    callerEvidence.Covers (useContext signatures owner fresh) := by
  constructor
  · intro goal evidence found
    cases found with
    | head => exact closedEvidenceValid signatures
    | tail _ found => cases found
  · intro predicate member
    have same : predicate = actualPredicate := by
      simpa [useContext, Context.withLocal, Context.withSolvedRequirements,
        Context.withAssumptions] using member
    subst predicate
    exact ⟨_, .head⟩

/-- The dynamic witness projects back to the established static judgment. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    LocalSchemeInstantiationValid (useContext signatures owner fresh)
      (binder owner fresh) (.function .word .word) [actualId] :=
  (runtimeInstantiation signatures owner fresh).toLocalSchemeInstantiationValid

/-- The public projections expose arity, uniqueness, template separation, and
closed evidence validity without reopening the constructor. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    [actualId].length = (binder owner fresh).schemeRequirements.length ∧
      [actualId].Nodup ∧
      actualId ∉ localSchemeTemplateIds (binder owner fresh) ∧
      callerEvidence.Valid signatures.resolutionRules := by
  let instantiated := runtimeInstantiation signatures owner fresh
  exact ⟨instantiated.actual_requirements_length_eq,
    instantiated.actual_requirements_nodup,
    instantiated.actual_requirement_templates_disjoint actualId (by simp),
    instantiated.produced_evidence_valid⟩

/-- Local evidence is prepended to caller evidence.  This fixture deliberately
uses the same goal in both dictionaries, exercising the overlap fallback rather
than relying on a hidden disjointness premise. -/
example (signatures : ProgramSignatures) (owner : Resolved.DeclarationId)
    (fresh : TypeVarId) :
    (callerEvidence ++ callerEvidence).Covers
      ((useContext signatures owner fresh).withAssumptions
        ((useContext signatures owner fresh).assumptions ++
          instantiateLocalSchemePredicates [(fresh, .word)]
            (binder owner fresh))) :=
  (runtimeInstantiation signatures owner fresh).combined_evidence_covers
    (callerCovers signatures owner fresh)

end Solcore.Test.SourceSemanticsLocalSchemes
