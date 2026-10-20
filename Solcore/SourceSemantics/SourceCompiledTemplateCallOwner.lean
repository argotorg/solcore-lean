import Solcore.SourceSemantics.SourcePreparedOpenCallOwner

/-! Raw selected compilation closes the plan and graph premises for real open
template emitters, yielding an actual contextual instance of the same row. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
open Frontend SourceInference TypeSystem SourceSpecializationWorklist
open SourceCompiledLocalFinalization SourcePreparedOpenCallEdges
open CoreLowering.CallableCoercionPreparationSteps (Specialized)

private theorem member_filter {entries : List Specialized} {row : Specialized}
    (unique : (entries.map (·.key)).Nodup) (member : row ∈ entries) :
    entries.filter (fun other => decide (other.key = row.key)) = [row] := by
  induction entries with
  | nil => cases member
  | cons first rest ih =>
      obtain ⟨absent, unique⟩ := List.nodup_cons.mp unique
      rcases List.mem_cons.mp member with rfl | member
      · have empty : rest.filter (fun other => decide (other.key = row.key)) = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro other present matched
          exact absent (List.mem_map.mpr ⟨other, present, of_decide_eq_true matched⟩)
        simp only [List.filter_cons, decide_true, if_true, empty]
      · have different : first.key ≠ row.key := by
          intro same
          exact absent (List.mem_map.mpr ⟨row, member, same.symm⟩)
        simpa only [List.filter_cons, decide_eq_false different, Bool.false_eq_true, if_false] using ih unique member

/-- Actual worklist uniqueness supplies exact selection for every source row,
not only the named root vector. -/
theorem selected_exact {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : Specialized} (member : row ∈ compiled.plan.specializations) :
    SourceCompilationPlan.exactSpecialization compiled.plan row.key = .ok row := by
  have checked := SourceCoreCompiler.compile_checked_source accepted
  have lowered : SourceCoreCompiler.compileChecked compiled.program seeds options = .ok compiled := by
    simpa only [SourceCoreCompiler.compile, checked, Except.mapError, bind, Except.bind] using accepted
  obtain ⟨requests, ran⟩ := SourceCompiledLocalReadOrigins.compileChecked_worklist lowered
  have unique := run_complete_specializationKeys_nodup _ _ _ _ ran
  have found := member_filter unique member
  simp only [SourceCompilationPlan.exactSpecialization, found]

/-- Parameter substitution preserves the original checker's unique occurrence
identities; no body-typing proof is required. -/
theorem selected_unique {compiled : SourceCoreCompiler.Compiled} {row : Specialized} {fuel : Nat}
    (receipt : Selected compiled row fuel) : NodeOccurrencesUnique row.function.typedBody := by
  have unique := receipt.body.resources.graph_closed.wellFormed.nodeOccurrencesUnique
  rw [receipt.source]
  change (nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource)).Nodup
  have occurrences : nodeOccurrenceIds (SourceSpecialization.applyTypedSource row.parameterSubstitution receipt.body.finalized.typedSource) =
      nodeOccurrenceIds receipt.body.finalized.typedSource := by
    simp only [nodeOccurrenceIds, SourceSpecialization.applyTypedSource, List.map_map]
    congr 1
    funext node
    cases node <;> rfl
  rw [occurrences]
  exact unique

structure PreparedContextual (compiled : SourceCoreCompiler.Compiled) (caller : Specialized)
    (node : ExpressionNode) (instantiation : DeclarationInstantiation) where
  prepared : Plan
  accepted : SourceCompilationPlan.prepareExecutablePlanEvidence compiled.program compiled.plan = .ok prepared
  edge : EdgeAt caller node instantiation prepared
  contextual : SourcePreparedOpenCallOwner.Contextual compiled.program caller.key caller.function.typedBody node edge.edge
  bodyNodes : List Node
  bodyAccepted : localLambdaBodyNodes caller.function.typedBody contextual.localInstance = .ok bodyNodes
  nodeInBody : .expression node ∈ bodyNodes
  templates : LocalTemplateUses (localLambdaBindings caller.function.typedBody) contextual.localInstance bodyNodes

/-- Actual public compilation and an actual original open call provide the
complete discovered owner, substitution, and original-node correspondence.
There is no contextual-origin, ownership, or plan-uniqueness assumption. -/
theorem open_call_owner {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {node : ExpressionNode} (present : .expression node ∈ caller.function.typedBody.nodes)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (form : node.form = .call callee arguments (.declaration instantiation))
    (cataloged : instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id))
    (opened : InstantiationClosed instantiation = false) :
    Nonempty (PreparedContextual compiled caller node instantiation) := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  have catalog := SignatureCatalogWellFormed.ofCheckProgram (SourceCoreCompiler.compile_checked_source accepted)
  obtain ⟨prepared, preparedAccepted, growth, _origins, covered⟩ :=
    SourcePreparedFinalCallEdgeOrigins.compiled_selected compiled
  obtain ⟨edge, origin⟩ := covered caller member node present callee arguments instantiation form opened
  have source := SourcePreparedCatalogedCallOrigin.source_origin catalog growth
    (selected_exact accepted member) origin edge.callerEq
    (edge.declarationEq.symm ▸ cataloged)
  obtain ⟨contextual⟩ := SourcePreparedOpenCallOwner.contextual_of_open
    (selected_unique selected) present form opened source edge.occurrenceEq
  obtain ⟨bodyNodes, bodyAccepted, nodeInBody, templates⟩ :=
    contextual.body (selected_unique selected) present
  exact ⟨⟨prepared, preparedAccepted, edge, contextual, bodyNodes, bodyAccepted, nodeInBody, templates⟩⟩

/-- Every finalized template has a cataloged emitter. If that original call
is open, the same successful compilation also supplies its actual discovered
local instance. The closed alternative remains explicit for predicate joining. -/
theorem template_owner {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {caller : Specialized} (member : caller ∈ compiled.plan.specializations)
    {id : RequirementId} (template : id ∈ sourceLocalSchemeTemplateIds caller.function.typedBody) :
    ∃ node, .expression node ∈ caller.function.typedBody.nodes ∧
      ∃ callee arguments instantiation,
        node.form = .call callee arguments (.declaration instantiation) ∧
        id ∈ node.requirements ∧
        instantiation.declaration ∈ compiled.program.signatures.functions.map (·.id) ∧
        (InstantiationClosed instantiation = true ∨
          Nonempty (PreparedContextual compiled caller node instantiation)) := by
  obtain ⟨node, present, callee, arguments, instantiation, form, issued, cataloged⟩ :=
    SourceCompiledCatalogedCallOrigins.compile_template_emitters accepted member id template
  refine ⟨node, present, callee, arguments, instantiation, form, issued, cataloged, ?_⟩
  cases closed : InstantiationClosed instantiation with
  | true => exact .inl rfl
  | false => exact .inr (open_call_owner accepted member present form cataloged closed)

end Solcore.SourceSemantics.SourceCompiledTemplateCallOwner
