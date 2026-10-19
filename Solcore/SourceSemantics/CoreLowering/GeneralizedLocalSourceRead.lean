import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalRuntimeInstantiation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
import Solcore.SourceSemantics.Staging.RecursiveTraceSize

/-! A reached generalized cell is materialized from original Source typing
and the actual caller dictionary. Static normalization does not replace the
original requirement spine or its descriptor's lexical context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
open Core Frontend SourceInference TypeSystem GeneralHeap

private theorem valid_at_binder {context : Context} {first second : TypedBinder}
    {type : TypeSystem.Ty} {requirements : List RequirementId}
    (scheme : first.scheme = second.scheme)
    (predicates : first.schemeRequirements = second.schemeRequirements)
    (valid : LocalSchemeInstantiationValid context first type requirements) :
    LocalSchemeInstantiationValid context second type requirements := by
  cases first with
  | mk firstId firstName firstScheme firstRequirements firstComptime firstSpan =>
    cases second with
    | mk secondId secondName secondScheme secondRequirements secondComptime secondSpan =>
      cases scheme
      cases predicates
      cases valid with
      | intro formation wellFormed substitution exact range result unique disjoint requirements =>
        refine .intro ⟨formation.ids_unique, ?_⟩ wellFormed substitution exact range result unique disjoint requirements
        intro requirement member
        have formed := formation.entries requirement member
        exact ⟨formed.predicate, formed.depends_on_quantified, formed.template⟩

/-- The genuine descriptor metadata identifies both its scheme and its
ordered principal requirements in the current lexical scope. -/
theorem instantiation_of_typed
    {source : TypedSource} {context : Context} {evidence : Dynamic.EvidenceEnvironment}
    {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure} {compiled : Substitution}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (typed : ExpressionHasType source context id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell)
    (descriptor : cell.generalized = some function)
    (principal : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements)
    (matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme node.rawType = some compiled)
    (covers : evidence.Covers context) :
    ∃ owned substitution produced,
      Dynamic.OrdinaryRequirementLayout node.requirements node.coercions owned ∧
      Dynamic.LocalSchemeRuntimeInstantiation context evidence function.binder node.rawType owned substitution produced := by
  generalize resultType : node.type = output at typed
  cases typed with
  | intro contains formTyped rawType _ _ requirements =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    cases same
    rw [form] at formTyped
    cases formTyped with
    | reference reference =>
      cases reference with
      | @«local» staticBinder raw owned schemeLookup requirementsLookup valid =>
        have identity := locals.lookup_generalized schemeLookup lookup read descriptor
        have principalEq := requirementsLookup.value_unique (identity.1 ▸ principal)
        have valid := valid_at_binder identity.2.symm principalEq valid
        have valid : LocalSchemeInstantiationValid context function.binder node.rawType _ := rawType ▸ valid
        obtain ⟨substitution, produced, runtime⟩ := GeneralizedLocalRuntimeInstantiation.of_valid matched valid covers
        cases requirements with
        | ordinary _ _ layout => exact ⟨_, substitution, produced, layout, runtime⟩

/-- This produces an actual staged Source step with the original requirement
identities. Its heap is unchanged because this admitted occurrence has no
output coercions. -/
theorem trace_of_typed
    {program : Program} {registry : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}
    {context : Context} {id : ExpressionId} {node : ExpressionNode} {name : String} {binder : Resolved.LocalId}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {location : Dynamic.Location}
    {cell : Dynamic.Cell} {function : Dynamic.GeneralizedClosure} {compiled : Substitution}
    (unique : NodeOccurrencesUnique invocation.source)
    (found : invocation.source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder)) (coercions : node.coercions = [])
    (typed : ExpressionHasType invocation.source context id node.type)
    (locals : Dynamic.EnvironmentAgrees heap context.locals environment)
    (lookup : Dynamic.Environment.LooksUp environment binder location)
    (read : Dynamic.Heap.Reads heap location cell) (descriptor : cell.generalized = some function)
    (fields : Dynamic.RuntimeContextFields function.definitionContext context)
    (principal : context.LocalSchemeRequirementsLookup function.binder.id function.binder.schemeRequirements)
    (matched : SourceSpecialization.matchClosedSchemeInstance? function.binder.scheme node.rawType = some compiled)
    (covers : invocation.evidence.Covers context) :
    ∃ owned substitution produced size,
      Dynamic.LocalSchemeRuntimeInstantiation context invocation.evidence function.binder node.rawType owned substitution produced ∧
      Staging.Recursive.Size.Expression program registry size invocation context environment heap id
        (.value (.closure (function.instantiate substitution
          (produced ++ invocation.evidence.applySubstitution substitution)))) heap := by
  obtain ⟨owned, substitution, produced, layout, runtime⟩ :=
    instantiation_of_typed unique found form typed locals lookup read descriptor principal matched covers
  refine ⟨owned, substitution, produced, Staging.Recursive.Size.stepSize [Staging.Recursive.Size.stepSize []], runtime, ?_⟩
  exact .generalizedLocal (lookupExpression?_sound found) form layout lookup read descriptor fields runtime
    (by rw [coercions]; exact .coercionsNil)

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalSourceRead
