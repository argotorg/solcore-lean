import Solcore.Frontend.SourceInference.DirectCallPredicateInference
import Solcore.SourceSemantics.SourceCompiledTemplateCallOrigins
import Solcore.SourceSemantics.SourceCompiledSelectedFinalization

/-! Actual direct-call issuance is paired with the same raw ledger predicate,
then transported through the selected finalizer and rigid specialization. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
open Frontend SourceInference TypeSystem Detail SourceInferenceSoundness
open SourceCompiledLocalFinalization DirectCallPredicateEvents

variable {catalog : List Resolved.DeclarationId}

theorem solved_call {nodes : List Node} {requirement : Requirement}
    (emitter : HasCall catalog nodes requirement) (substitution : Substitution) :
    HasCall catalog (nodes.map (Node.applySubstitution substitution))
      { requirement with predicate := TypedTraitResolution.applySubstitution substitution requirement.predicate } := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := emitter
  refine ⟨node.applySubstitution substitution,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, instantiation.applySubstitution substitution, ?_, issued, cataloged,
    List.mem_map.mpr ⟨requirement.predicate, predicate, rfl⟩⟩
  change node.form.applySubstitution substitution = _
  rw [form]
  rfl

theorem specialized_call {source : TypedSource} {requirement : Requirement}
    (emitter : HasCall catalog source.nodes requirement) (substitution : ParameterSubstitution) :
    HasCall catalog (SourceSpecialization.applyTypedSource substitution source).nodes
      { requirement with predicate := ProgramPredicate.applyParameters substitution requirement.predicate } := by
  obtain ⟨node, member, callee, arguments, instantiation, form, issued, cataloged, predicate⟩ := emitter
  refine ⟨SourceSpecialization.applyExpressionNode substitution node,
    List.mem_map.mpr ⟨.expression node, member, rfl⟩,
    callee, arguments, SourceSpecialization.applyInstantiation substitution instantiation, ?_, issued, cataloged,
    List.mem_map.mpr ⟨requirement.predicate, predicate, rfl⟩⟩
  change SourceSpecialization.applyExpressionForm substitution node.form = _
  rw [form]
  rfl

private theorem solved_row_of_requirement_mem
    {inferenceContext : SourceInference.Context} {state : State}
    {requirements : List Requirement} {solved : List SolvedRequirement}
    (corresponds : Forall₂ (fun requirement row =>
      row.id = requirement.id ∧
        row.predicate = Detail.applyPredicate state requirement.predicate ∧
        Detail.solveRequirementEvidence inferenceContext state requirement = .ok row.evidence)
      requirements solved)
    {requirement : Requirement} (member : requirement ∈ requirements) :
    ∃ row, row ∈ solved ∧ row.id = requirement.id ∧
      row.predicate = Detail.applyPredicate state requirement.predicate := by
  induction corresponds with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, List.mem_cons_self, head.1, head.2.1⟩
    · obtain ⟨row, present, same, predicate⟩ := ih member
      exact ⟨row, List.mem_cons_of_mem _ present, same, predicate⟩

namespace BodyReceipt
variable {environment : ProgramEnvironment} {signatures : ProgramSignatures}
  {signature : ProgramFunctionSignature} {fuel : Nat} {checked : CheckedFunction}

theorem direct_origins (receipt : BodyReceipt environment signatures signature fuel checked) :
    Origins (signatures.functions.map (·.id)) receipt.returned :=
  Progress.unify receipt.unified (initializedStatements_origins receipt.inferred)

/-- Both the ledger row and the call instantiation come from the same actual
inference. The node's extra coercion IDs are never used to infer its predicate. -/
theorem raw_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    ∃ requirement ∈ receipt.returned.requirements, requirement.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.returned.nodes requirement :=
  direct_origins receipt id
    (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)

theorem finalized_direct_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ receipt.returned.directCallRequirements) :
    ∃ solved ∈ receipt.finalized.solvedRequirements, solved.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes
        { id, predicate := solved.predicate } := by
  obtain ⟨requirement, present, same, call⟩ := direct_origins receipt id member
  have solverMember : requirement ∈ receipt.resources.finalState.requirements := by
    rw [receipt.resources.requirements_eq]
    exact present
  obtain ⟨solved, solvedMember, solvedId, predicate⟩ :=
    solved_row_of_requirement_mem (solveRequirements_corresponds receipt.resources.solve_success) solverMember
  refine ⟨solved, solvedMember, solvedId.trans same, ?_⟩
  have predicateEq : solved.predicate =
      TypedTraitResolution.applySubstitution receipt.finalized.substitution requirement.predicate := by
    rw [predicate, receipt.resources.substitution_eq]
    rfl
  rw [receipt.resources.source_eq, predicateEq, ← same]
  exact solved_call call receipt.finalized.substitution

theorem finalized_template_emitter
    (receipt : BodyReceipt environment signatures signature fuel checked)
    {id : RequirementId} (member : id ∈ sourceLocalSchemeTemplateIds receipt.finalized.typedSource) :
    ∃ solved ∈ receipt.finalized.solvedRequirements, solved.id = id ∧
      HasCall (signatures.functions.map (·.id)) receipt.finalized.typedSource.nodes
        { id, predicate := solved.predicate } :=
  finalized_direct_emitter receipt
    (SourceCompiledTemplateCallOrigins.BodyReceipt.finalized_template_direct receipt member)

end BodyReceipt

theorem selected_template_emitter
    {compiled : SourceCoreCompiler.Compiled} {row : SourceSpecialization.SpecializedFunction} {fuel : Nat}
    (selected : Selected compiled row fuel) {id : RequirementId}
    (member : id ∈ sourceLocalSchemeTemplateIds row.function.typedBody) :
    ∃ solved ∈ row.function.solvedRequirements, solved.id = id ∧
      HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes
        { id, predicate := solved.predicate } := by
  rw [selected.source] at member
  have original : id ∈ sourceLocalSchemeTemplateIds selected.body.finalized.typedSource := by
    change id ∈ sourceLocalSchemeTemplateIds
      (StructuralSubstitution.applyTypedSource row.parameterSubstitution selected.body.finalized.typedSource) at member
    simpa only [StructuralSubstitution.sourceLocalSchemeTemplateIds_applyTypedSource] using member
  obtain ⟨solved, present, same, call⟩ := BodyReceipt.finalized_template_emitter selected.body original
  refine ⟨SourceSpecialization.applySolvedRequirement row.parameterSubstitution solved, ?_, same, ?_⟩
  · rw [selected.solved]
    exact List.mem_map.mpr ⟨solved, present, rfl⟩
  · rw [selected.source]
    exact specialized_call call row.parameterSubstitution

theorem receipt_ready_origins
    {fuel : Nat} {context : SourceInference.Context} {source : Syntax.Statement}
    {initial : State} {result : StatementResult}
    (receipt : LocalLetRequirementTiming.Receipt fuel context source initial result)
    (origins : Origins (context.signatures.functions.map (·.id)) initial) :
    Origins (context.signatures.functions.map (·.id)) receipt.ready :=
  inferExprFuel_origins_progress receipt.child origins

/-- Raw compilation supplies the actual selected body and all issuance facts. -/
theorem compile_template_emitters
    {raw : Workspace.RawWorkspace} {seeds : List SourceCoreCompiler.Seed}
    {options : SourceCoreCompiler.Options} {compiled : SourceCoreCompiler.Compiled}
    (accepted : SourceCoreCompiler.compile raw seeds options = .ok compiled)
    {row : SourceSpecialization.SpecializedFunction} (member : row ∈ compiled.plan.specializations) :
    ∀ id ∈ sourceLocalSchemeTemplateIds row.function.typedBody,
      ∃ solved ∈ row.function.solvedRequirements, solved.id = id ∧
        HasCall (compiled.program.signatures.functions.map (·.id)) row.function.typedBody.nodes
          { id, predicate := solved.predicate } := by
  obtain ⟨selected⟩ := SourceCompiledLocalFinalization.of_compile accepted member
  exact fun _ present => selected_template_emitter selected present

end Solcore.SourceSemantics.SourceCompiledDirectCallPredicateOrigins
