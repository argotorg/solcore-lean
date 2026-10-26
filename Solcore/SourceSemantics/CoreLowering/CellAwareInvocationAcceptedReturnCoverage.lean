import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedFlow

/-! Statement coverage of a body whose first statement returns a value. The
compiler reads that statement before choosing a branch, so every accepted tree
of the body is its `returning` branch, which the statement closure covers. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedReturnCoverage
open Core Frontend SourceInference
open AcceptedNamedBodyFlow (Tree)
open CellAwareInvocationAcceptedFlow (Covered)

private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨_, _, same⟩ := CompatibleEncoding.bind_ok accepted
      cases same
      rfl

variable {whole : SourceCoreUnifiedCompilation.Compiled} {bodyRelation : ActualBodyInvocation.BodyRelation}

/-- Every accepted tree of statements whose first statement returns a value is
covered, for every Source view, result type and match or generalized input. -/
theorem returning (index : ActualBodyInvocation.Index whole bodyRelation)
    {semantic : TypedSource} {expected : TypeSystem.Ty}
    {admitted : SourceCoreCompatibleDataMatches.Context → Prop} {generalized : Prop}
    {mode : Bool} {escaped : Word} {fuel : Nat} {scope : SourceCoreLocalCell.Scope}
    {statements : List StatementId} {code : Expr}
    (tree : Tree index.policy index.compilerSource index.result index.reasonAt mode escaped fuel scope
      statements code)
    {id : StatementId} {rest : List StatementId} {node : StatementNode} {expression : ExpressionId}
    (same : statements = id :: rest)
    (found : index.compilerSource.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression)) :
    Covered semantic expected admitted generalized tree := by
  subst same
  have sameNode : ∀ {other : StatementNode} {stored : Ty},
      index.policy.readStatement index.compilerSource id = .ok (other, stored) → other = node := by
    intro other stored read
    rw [index.statement_reader] at read
    exact Option.some.inj ((read_found read).symm.trans found)
  cases tree with
  | boundary read outside =>
    rw [sameNode read, form] at outside
    simp [AcceptedNamedBodyFlow.expanded] at outside
  | _ => first
    | trivial
    | (obtain rfl := sameNode (by assumption)
       simp_all)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedReturnCoverage
