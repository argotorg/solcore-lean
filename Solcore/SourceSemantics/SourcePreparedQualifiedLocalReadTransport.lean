import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadWitnesses
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.Frontend.SourceInference.TypedIRProperties

/-! An accepted original qualified read has no free outer scheme variables.
Its actual witness factory therefore survives every later source substitution. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadTransport
open Frontend SourceInference TypeSystem
open CoreLowering.CallableAncestryProfiles.SourceComposition
open SourcePreparedQualifiedLocalReadBindings
open CoreLowering.CallableCoercionPreparationSteps (Specialized bind_ok)

private theorem masked_fixed (active : Substitution) (variables : List TypeVarId)
    (type : Ty) (scope : ∀ v ∈ type.freeVariables, v ∈ variables) :
    (active.without variables).apply type = type := by
  apply Ty.apply_eq_self_of_domain_disjoint_freeVariables
  intro v member occurs
  have absent : (active.without variables).lookup? v = none := by
    rw [lookup_without, if_pos (scope v occurs)]
  exact ((Substitution.lookup?_eq_none_iff_not_mem_domain _ v).mp absent) member

/-- Concrete matching excludes all unquantified variables of the scheme body. -/
theorem scheme_scoped {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some substitution) :
    ∀ v ∈ scheme.body.freeVariables, v ∈ scheme.quantified := by
  obtain ⟨concrete, _unique, domain, applies⟩ := SourceSpecialization.matchClosedSchemeInstance?_sound matched
  have closed := concrete_closed concrete
  intro v occurs
  by_cases quantified : v ∈ scheme.quantified
  · exact quantified
  apply False.elim
  have outside := quantified
  have survives := FlexibleSubstitution.Substitution.mem_freeVariables_apply_of_not_mem_domain
    substitution (by rwa [domain]) occurs
  rw [applies, closed] at survives
  exact List.not_mem_nil survives

private theorem predicate_fixed (active : Substitution) (variables : List TypeVarId)
    (predicate : ProgramPredicate)
    (scope : ∀ v ∈ TypedTraitResolution.predicateVariables predicate, v ∈ variables) :
    TypedTraitResolution.applySubstitution (active.without variables) predicate = predicate := by
  have subject := masked_fixed active variables predicate.subject (by
    intro v occurs
    exact scope v (TypedTraitResolution.mem_predicateVariables_iff.mpr (.inl occurs)))
  have arguments : predicate.arguments.map (active.without variables).apply = predicate.arguments := by
    apply Eq.trans (b := List.map id _) ?_ (List.map_id _)
    apply List.map_congr_left
    intro type member
    exact masked_fixed active variables type (by
      intro v occurs
      exact scope v (TypedTraitResolution.mem_predicateVariables_iff.mpr (.inr ⟨type, member, occurs⟩)))
  cases predicate
  simp only [TypedTraitResolution.applySubstitution] at subject arguments ⊢
  simp only [subject, arguments]

/-- Both the scheme and each retained requirement are protected by the same
actual binder mask. No disjointness between unrelated substitutions is assumed. -/
theorem binder_fixed {caller : Specialized} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {bindings : List SourceCompilationPlan.LocalRequirementBinding}
    (receipt : BindingsReceipt caller binder node substitution bindings) (active : Substitution) :
    binder.applySubstitution active = binder := by
  have schemeBody := masked_fixed active binder.scheme.quantified binder.scheme.body
    (scheme_scoped receipt.matched)
  have requirements : binder.schemeRequirements.map
      (LocalSchemeRequirement.applySubstitution (active.without binder.scheme.quantified)) =
      binder.schemeRequirements := by
    apply Eq.trans (b := List.map id _) ?_ (List.map_id _)
    apply List.map_congr_left
    intro requirement member
    have predicate := predicate_fixed active binder.scheme.quantified requirement.predicate
      (fun v occurs => receipt.template_scoped member occurs)
    cases requirement
    simp only [LocalSchemeRequirement.applySubstitution] at predicate ⊢
    simp only [predicate]
    rfl
  simp only [TypedBinder.applySubstitution, Scheme.apply, mask_twice, schemeBody, requirements]

/-- Only the occurrence identity, uncoerced type, and requirement spine are
read by the factory. This equality preserves its complete evidence output. -/
theorem factory_node_congr (caller : Specialized)
    (available : SourceCompilationPlan.EvidenceEnvironment) (binder : TypedBinder)
    {left right : ExpressionNode} (id : left.id = right.id)
    (type : left.rawType = right.rawType) (requirements : left.requirements = right.requirements) :
    SourceCompilationPlan.localRequirementWitnesses caller available binder left =
      SourceCompilationPlan.localRequirementWitnesses caller available binder right := by
  simp only [SourceCompilationPlan.localRequirementWitnesses, SourceCompilationPlan.localRequirementBindings,
    id, type, requirements]

/-- The original successful factory yields the very same child substitution
and witnesses under any actual source-active substitution. -/
theorem witnesses_apply {caller : Specialized} {available : SourceCompilationPlan.EvidenceEnvironment}
    {binder : TypedBinder} {node : ExpressionNode} {substitution : Substitution}
    {witnesses : List SourceTypedRuntime.LocalRequirementWitness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node =
      .ok (substitution, witnesses)) (active : Substitution) :
    SourceCompilationPlan.localRequirementWitnesses caller available (binder.applySubstitution active)
      (node.applySubstitution active) = .ok (substitution, witnesses) := by
  have original := accepted
  unfold SourceCompilationPlan.localRequirementWitnesses at accepted
  obtain ⟨⟨child, bindings⟩, issued, _⟩ := bind_ok accepted
  have receipt := bindings_receipt issued
  have closed := concrete_closed (SourceSpecialization.matchClosedSchemeInstance?_sound receipt.matched).1
  rw [binder_fixed receipt active]
  rw [factory_node_congr caller available binder (left := node.applySubstitution active) (right := node) rfl
    (by rw [ExpressionNode.applySubstitution_rawType, fixed closed]) rfl]
  exact original

/-- Each compiled original read retains real witness preparation after every
source substitution, with the resolver output selected by that same scan. -/
theorem compiled_selected (compiled : SourceCoreCompiler.Compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} (present : Node.expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId} (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (detected : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) (active : Substitution) :
    ∃ available substitution witnesses,
      SourceCompilationPlan.resolveRuntimeEvidenceEnvironment compiled.program caller.key caller.assumptions = .ok available ∧
      SourceCompilationPlan.localRequirementWitnesses caller available (binder.applySubstitution active)
        (node.applySubstitution active) = .ok (substitution, witnesses) := by
  obtain ⟨available, resolved, checked⟩ := SourcePreparedQualifiedLocalReadWitnesses.compiled_selected compiled member
  obtain ⟨substitution, witnesses, factory⟩ := checked node present name localId form binder detected qualified
  exact ⟨available, substitution, witnesses, resolved, witnesses_apply factory active⟩

private theorem ordinary_all {node : ExpressionNode} {owned : List RequirementId}
    (selected : SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned)
    (count : owned.length = node.requirements.length) : owned = node.requirements := by
  have layout : node.requirements = owned ++ coercionRequirementIds node.coercions := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements? at selected
    dsimp only at selected
    split at selected <;> try contradiction
    split at selected <;> try contradiction
    rename_i layout
    cases selected
    exact layout
  have length := congrArg List.length layout
  simp only [List.length_append] at length
  have empty : coercionRequirementIds node.coercions = [] :=
    List.length_eq_zero_iff.mp (by omega)
  simpa only [empty, List.append_nil] using layout.symm

/-- Substitution changes coercion types while preserving the requirement IDs
used by the actual ordinary-requirement selector. -/
theorem ordinary_apply (node : ExpressionNode) (active : Substitution) :
    SourceCompilationPlan.ordinaryOwnedRequirements? (node.applySubstitution active) =
      SourceCompilationPlan.ordinaryOwnedRequirements? node := by
  have coercions : coercionRequirementIds (node.coercions.map (CoercionStep.applySubstitution active)) =
      coercionRequirementIds node.coercions := by
    simp only [coercionRequirementIds, List.flatMap_map, CoercionStep.applySubstitution, CoercionStep.requirements]
    rfl
  change (let requirements := node.requirements
          let ids := coercionRequirementIds (node.coercions.map (CoercionStep.applySubstitution active))
          if requirements.length < ids.length then none else
            let owned := requirements.take (requirements.length - ids.length)
            if requirements = owned ++ ids then some owned else none) =
         (let requirements := node.requirements
          let ids := coercionRequirementIds node.coercions
          if requirements.length < ids.length then none else
            let owned := requirements.take (requirements.length - ids.length)
            if requirements = owned ++ ids then some owned else none)
  rw [coercions]

/-- The exact raw node consumed by prepareRead is accepted on every substituted
qualified original read. All resolver, selector, and factory successes come
from the actual compiled plan. -/
theorem raw_of_preparation {program : CheckedProgram} {caller : Specialized}
    (covered : SourcePreparedQualifiedLocalReadWitnesses.Covered program caller)
    (metadata : SourceCompilationPlan.validateSpecializationMetadataWith true caller = .ok ())
    {node : ExpressionNode} (present : Node.expression node ∈ caller.function.typedBody.nodes)
    {name : String} {localId : Resolved.LocalId} (form : node.form = .reference name (.local localId))
    {binder : TypedBinder}
    (detected : SourceCompilationPlan.directLambdaLetBinder? caller.function.typedBody localId = some binder)
    (qualified : binder.schemeRequirements ≠ []) (active : Substitution) :
    ∃ available owned substitution witnesses,
      SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program caller.key caller.assumptions = .ok available ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? (node.applySubstitution active) = some owned ∧
      binder.applySubstitution active = binder ∧
      (node.applySubstitution active).rawType = node.rawType ∧
      SourceCompilationPlan.localRequirementWitnesses caller available (binder.applySubstitution active)
        {(node.applySubstitution active) with type := (node.applySubstitution active).rawType, requirements := owned, coercions := []} = .ok (substitution, witnesses) := by
  obtain ⟨available, resolved, checked⟩ := covered
  obtain ⟨substitution, witnesses, factory⟩ := checked node present name localId form binder detected qualified
  obtain ⟨owned, rawChild, rawBindings, selected, receipt⟩ :=
    SourcePreparedQualifiedLocalReadBindings.metadata_bindings metadata present form detected qualified
  have original := factory
  unfold SourceCompilationPlan.localRequirementWitnesses at original
  obtain ⟨⟨child, bindings⟩, issued, _⟩ := bind_ok original
  have originalReceipt := bindings_receipt issued
  have all := ordinary_all selected (receipt.count.symm.trans originalReceipt.count)
  have typeFixed : (node.applySubstitution active).rawType = node.rawType := by
    rw [ExpressionNode.applySubstitution_rawType]
    exact fixed (concrete_closed (SourceSpecialization.matchClosedSchemeInstance?_sound originalReceipt.matched).1) active
  refine ⟨available, owned, substitution, witnesses, resolved, ?_, binder_fixed originalReceipt active, typeFixed, ?_⟩
  · rw [ordinary_apply]; exact selected
  rw [binder_fixed originalReceipt active]
  apply Eq.trans (b := SourceCompilationPlan.localRequirementWitnesses caller available binder node) ?_ factory
  exact factory_node_congr caller available binder rfl typeFixed all

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadTransport
