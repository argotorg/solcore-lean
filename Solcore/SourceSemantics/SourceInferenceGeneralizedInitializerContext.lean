import Solcore.SourceSemantics.SourceInferenceActualContext
import Solcore.SourceSemantics.SourceInferenceExpressionRecursiveSoundness

/-! Entering a retained generalized initializer enlarges its lexical type and
predicate scopes. The caller's local typing invariant remains available at
that exact child boundary, including already generalized local bindings. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend SourceInference TypeSystem

namespace GeneralizedInitializerContext

private structure Expansion (source target : SourceSemantics.Context) : Prop where
  signatures : target.signatures = source.signatures
  parameters : target.typeParameters = source.typeParameters
  declaration : target.currentDeclaration = source.currentDeclaration
  variables : source.typeVariables ⊆ target.typeVariables
  residual : target.residualTypeVariables = source.residualTypeVariables
  solved : target.solvedRequirements = source.solvedRequirements

private theorem Expansion.admissibleVariables {source target : SourceSemantics.Context}
    (expanded : Expansion source target) (type : Ty) :
    admissibleTypeVariables source type ⊆ admissibleTypeVariables target type := by
  intro metavariable member
  simp only [admissibleTypeVariables, expanded.residual, List.mem_append] at member ⊢
  exact member.imp (fun proof => expanded.variables proof) id

private theorem Expansion.admissible {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {type : Ty}
    (formed : TypeAdmissible source type) : TypeAdmissible target type := by
  refine ⟨StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    expanded.parameters expanded.declaration formed.binders, ?_⟩
  exact TypeWellScoped.weakenTo (fun _ member => expanded.admissibleVariables type member)
    (StructuralSubstitution.TypeWellScoped.transportContext expanded.signatures
      expanded.parameters expanded.declaration formed.typeWellScoped)

private theorem Expansion.scheme {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {scheme : Scheme}
    (formed : SchemeWellFormed source scheme) : SchemeWellFormed target scheme := by
  refine ⟨StructuralSubstitution.TypeParameterBindersWellFormed.transportContext
    expanded.parameters expanded.declaration formed.binders, formed.quantified_nodup, ?_⟩
  apply TypeWellScoped.weakenTo ?_
    (StructuralSubstitution.TypeWellScoped.transportContext expanded.signatures
      expanded.parameters expanded.declaration formed.body)
  intro metavariable member
  simp only [List.mem_append] at member ⊢
  exact member.imp (fun proof => expanded.admissibleVariables scheme.body proof) id

private theorem Expansion.predicate {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {predicate : ProgramPredicate}
    (formed : PredicateAdmissible source predicate) : PredicateAdmissible target predicate := by
  refine ⟨expanded.admissible formed.subject,
    fun argument member => expanded.admissible (formed.arguments argument member), ?_⟩
  simpa only [expanded.signatures] using formed.trait

private theorem Expansion.initializer {source target : SourceSemantics.Context}
    (expanded : Expansion source target) (binder : TypedBinder) :
    Expansion (localSchemeInitializerContext source binder)
      (localSchemeInitializerContext target binder) := by
  refine ⟨expanded.signatures, expanded.parameters, expanded.declaration, ?_,
    expanded.residual, expanded.solved⟩
  intro metavariable member
  change metavariable ∈ source.typeVariables ++ binder.scheme.quantified at member
  change metavariable ∈ target.typeVariables ++ binder.scheme.quantified
  exact List.mem_append.mpr ((List.mem_append.mp member).imp (fun proof => expanded.variables proof) id)

private theorem Expansion.requirements {source target : SourceSemantics.Context}
    (expanded : Expansion source target) {binder : TypedBinder}
    (formed : LocalSchemeRequirementsWellFormed source binder) :
    LocalSchemeRequirementsWellFormed target binder := by
  refine ⟨formed.ids_unique, ?_⟩
  intro requirement member
  have entry := formed.entries requirement member
  refine ⟨(expanded.initializer binder).predicate entry.predicate,
    entry.depends_on_quantified, ?_⟩
  simpa only [expanded.solved] using entry.template

private theorem initializerExpansion (context : SourceSemantics.Context) (binder : TypedBinder) :
    Expansion context (localSchemeInitializerContext context binder) := by
  refine ⟨rfl, rfl, rfl, ?_, rfl, rfl⟩
  intro metavariable member
  exact List.mem_append_left _ member

end GeneralizedInitializerContext

theorem ActiveLocalContextInvariant.generalizedInitializer
    {state : State} {substitution : Substitution} {context : SourceSemantics.Context}
    (invariant : ActiveLocalContextInvariant state substitution context) (binder : TypedBinder) :
    ActiveLocalContextInvariant state substitution (localSchemeInitializerContext context binder) := by
  have expanded := GeneralizedInitializerContext.initializerExpansion context binder
  exact ⟨⟨invariant.aligned.ids_nodup, invariant.aligned.locals_perm, invariant.aligned.requirements_perm⟩, {
    schemes := fun candidate member => expanded.scheme (invariant.formation.schemes candidate member)
    requirements := fun candidate member => expanded.requirements (invariant.formation.requirements candidate member)
  }⟩

theorem RecursiveExpressionInvariant.generalizedInitializer
    {wholeContext : Frontend.SourceInference.Context} {finalized : Frontend.SourceInference.Result}
    {state : State} {context : SourceSemantics.Context}
    (invariant : RecursiveExpressionInvariant wholeContext finalized state context) (binder : TypedBinder) :
    RecursiveExpressionInvariant wholeContext finalized state (localSchemeInitializerContext context binder) := by
  exact {
    invariant with
    active := invariant.active.generalizedInitializer binder
    assumptionsMono := fun _ member => List.mem_append_left _ (invariant.assumptionsMono member)
  }

end Solcore.SourceSemantics.SourceInferenceSoundness
