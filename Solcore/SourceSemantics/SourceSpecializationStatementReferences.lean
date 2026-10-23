import Lean
import Solcore.Frontend.SourceSpecialization

/-! The actual statement scheduler and canonical references contain the same
children. Loop bodies and post items may have different list order. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.Frontend.SourceSpecialization
open SourceInference

open Lean Meta Elab Tactic in
/-- Resolve only the existing private definitions and proved collector lemmas.
The resulting simplification proof is checked normally by the kernel. -/
private def simplifyActualScheduler : TacticM Unit := do
  let wanted := #[
    `Solcore.Frontend.SourceSpecialization.statementChildTasks,
    `Solcore.Frontend.SourceSpecialization.expressionTasks,
    `Solcore.Frontend.SourceSpecialization.statementTasks,
    `Solcore.Frontend.SourceSpecialization.assignmentTasks,
    `Solcore.Frontend.SourceSpecialization.projectionTasks_nodes,
    `Solcore.Frontend.SourceSpecialization.forItemTasks_nodes]
  let mut names : Array (TSyntax `ident) := #[]
  for original in wanted do
    let mut found : Option Name := none
    for (name, _) in (← getEnv).constants.toList do
      if privateToUserName? name == some original then
        if found.isSome then throwError "ambiguous scheduler declaration: {original}"
        found := some name
    let some name := found | throwError "missing scheduler declaration: {original}"
    names := names.push (mkIdent name)
  evalTactic (← `(tactic| simp only [statementChildNodeIds, $[$names:ident],*,
    StatementForm.references, AssignmentResolution.references, PlaceResolution.references,
    MatchResolution.references, List.map_map, List.map_flatMap, List.map_append,
    Function.comp_def] at *))

/-- Every canonical statement reference is scheduled by the same executable
specialization traversal, regardless of the loop-post ordering. -/
theorem statementChildNodeIds_of_reference {source : TypedSource} {node : StatementNode}
    {child : NodeId} (member : child ∈ node.form.references) :
    child ∈ statementChildNodeIds source node := by
  cases node with
  | mk id span type form =>
    cases form <;> run_tac simplifyActualScheduler
    all_goals simp_all [or_left_comm, or_comm, TypedMatchCase.references]

theorem statementChildNodeIds_mem_iff {source : TypedSource} {node : StatementNode}
    {child : NodeId} : child ∈ statementChildNodeIds source node ↔ child ∈ node.form.references :=
  ⟨statementChildNodeIds_references, statementChildNodeIds_of_reference⟩

end Solcore.Frontend.SourceSpecialization
