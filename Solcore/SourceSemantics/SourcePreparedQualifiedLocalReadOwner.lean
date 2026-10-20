import Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadBindings
import Solcore.SourceSemantics.SourceCompiledLocalReadOrigins

/-! Actual local-instance discovery and original metadata validation select
the same complete lexical owner. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
open Frontend SourceInference SourceSpecializationWorklist TypeSystem

private theorem lookup_eq_head (source : TypedSource) (id : Resolved.LocalId) :
    SourceCompilationPlan.directLambdaLetBinder? source id =
      ((localLambdaBindings source).filter (fun binding => binding.binder.id == id)).head?.map
        (fun binding => binding.binder) := by
  have collected : localLambdaBindings source = source.nodes.filterMap (fun
      | .statement {form := .letDecl binder (some initializer), ..} =>
          if binder.scheme.quantified.isEmpty ||
              !SourceSpecialization.isDirectLambdaInitializer source initializer then none
          else some ({binder, initializer} : LocalLambdaBinding)
      | _ => none) := rfl
  rw [collected, ← List.head?_map, List.filter_filterMap, List.map_filterMap, List.head?_filterMap]
  unfold SourceCompilationPlan.directLambdaLetBinder?
  congr 1
  funext node
  cases node with
  | expression expression => rfl
  | statement statement =>
    cases statement with
    | mk sid span type form =>
      cases form <;> try rfl
      rename_i binder initializer
      cases initializer with
      | none => rfl
      | some initializer =>
        by_cases same : binder.id = id <;>
          cases empty : binder.scheme.quantified.isEmpty <;>
          cases direct : SourceSpecialization.isDirectLambdaInitializer source initializer <;>
          simp [same, empty, direct, Option.filter]

/-- Exact worklist selection fixes the result of the metadata owner's
first-match lookup, including the complete binder and its templates. -/
theorem selected_owner {source : TypedSource} {binding : LocalLambdaBinding}
    (selected : LocalLambdaBinding.Selected (localLambdaBindings source) binding) :
    SourceCompilationPlan.directLambdaLetBinder? source binding.binder.id = some binding.binder := by
  rw [lookup_eq_head]
  change ((localLambdaBindings source).filter
    (fun candidate => candidate.binder.id == binding.binder.id)).head?.map _ = _
  rw [selected]
  rfl

/-- Discovery supplies the exact owner selection for every root and
contextual instance. No uniqueness premise is added at the public boundary. -/
theorem discovered_owner {source : TypedSource} {contextFuel : Option Nat}
    {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances source contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances) :
    SourceCompilationPlan.directLambdaLetBinder? source localInstance.binding.binder.id =
      some localInstance.binding.binder :=
  selected_owner (localLambdaInstances_selected discovered localInstance member)

/-- The same discovered instance yields an original local reference and its
actual qualified metadata receipt, even when discovery used a parent context. -/
theorem compiled_instance (compiled : SourceCoreCompiler.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations)
    {contextFuel : Option Nat} {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances caller.function.typedBody contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances)
    (qualified : localInstance.binding.binder.schemeRequirements ≠ []) :
    ∃ node name owned substitution bindings,
      Node.expression node ∈ caller.function.typedBody.nodes ∧
      node.form = .reference name (.local localInstance.binding.binder.id) ∧
      SourceCompilationPlan.ordinaryOwnedRequirements? node = some owned ∧
      SourcePreparedQualifiedLocalReadBindings.BindingsReceipt caller localInstance.binding.binder
        {node with type := node.rawType, requirements := owned, coercions := []} substitution bindings := by
  have owner := discovered_owner discovered member
  have origin := localLambdaInstances_read_origin discovered localInstance member
  cases origin with
  | root node present name form matched =>
      obtain ⟨owned, substitution, bindings, spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.compiled_selected compiled selected present form owner qualified
      exact ⟨node, name, owned, substitution, bindings, present, form, spine, receipt⟩
  | contextual parentOrigin node present name form child matched cumulative =>
      obtain ⟨owned, substitution, bindings, spine, receipt⟩ :=
        SourcePreparedQualifiedLocalReadBindings.compiled_selected compiled selected present form owner qualified
      exact ⟨node, name, owned, substitution, bindings, present, form, spine, receipt⟩

/-- Every original template of an actual discovered instance is scoped only
by that instance's complete inner binder. -/
theorem compiled_instance_template_scoped (compiled : SourceCoreCompiler.Compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations)
    {contextFuel : Option Nat} {instances : List LocalLambdaInstance}
    (discovered : localLambdaInstances caller.function.typedBody contextFuel = .ok instances)
    {localInstance : LocalLambdaInstance} (member : localInstance ∈ instances)
    {template : LocalSchemeRequirement} (owned : template ∈ localInstance.binding.binder.schemeRequirements)
    {metavariable : TypeVarId}
    (occurs : metavariable ∈ TypedTraitResolution.predicateVariables template.predicate) :
    metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  have qualified : localInstance.binding.binder.schemeRequirements ≠ [] := by
    intro empty
    rw [empty] at owned
    exact List.not_mem_nil owned
  obtain ⟨_node, _name, _owned, _substitution, _bindings, _present, _form, _spine, receipt⟩ :=
    compiled_instance compiled selected discovered member qualified
  exact receipt.template_scoped owned occurs

/-- Successful checked compilation supplies the actual instance discovery
and the same-owner template scoping for every selected source row. -/
theorem compileChecked_instance_templates
    {program : CheckedProgram} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compileChecked program seeds options = .ok compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances caller.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∀ template ∈ localInstance.binding.binder.schemeRequirements,
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables template.predicate,
          metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  obtain ⟨instances, discovered, _origins⟩ :=
    SourceCompiledLocalReadOrigins.compileChecked_local_instances accepted selected
  exact ⟨instances, discovered, fun _ member _ owned _ occurs =>
    compiled_instance_template_scoped compiled selected discovered member owned occurs⟩

/-- The public raw-source compiler provides the same receipt without a
separate discovery, owner equality, or source typing assumption. -/
theorem compile_instance_templates
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : SourceSpecialization.SpecializedFunction}
    (selected : caller ∈ compiled.plan.specializations) :
    ∃ instances, localLambdaInstances caller.function.typedBody = .ok instances ∧
      ∀ localInstance ∈ instances, ∀ template ∈ localInstance.binding.binder.schemeRequirements,
        ∀ metavariable ∈ TypedTraitResolution.predicateVariables template.predicate,
          metavariable ∈ localInstance.binding.binder.scheme.quantified := by
  obtain ⟨instances, discovered, _origins⟩ :=
    SourceCompiledLocalReadOrigins.compile_local_instances accepted selected
  exact ⟨instances, discovered, fun _ member _ owned _ occurs =>
    compiled_instance_template_scoped compiled selected discovered member owned occurs⟩

end Solcore.SourceSemantics.SourcePreparedQualifiedLocalReadOwner
