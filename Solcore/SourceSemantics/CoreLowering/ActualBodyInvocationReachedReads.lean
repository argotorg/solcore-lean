import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocationReads

/-! Actual body roots supply lookup correspondence only where the compiler
descends. The root receipt and each child edge retain the same invocation. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference CallableLambdaBodyReachability
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

def Index.Reached {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    (id : NodeId) : Prop :=
  Reaches index.compilerSource (index.statements.map NodeId.statement) id

theorem Index.body_root {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : StatementId} (member : id ∈ index.statements) : index.Reached (.statement id) :=
  .root (List.mem_map.mpr ⟨id, member, rfl⟩)

/-- This carries the actual full compiler receipt and the roots it compiled.
No independently chosen statement list enters the reached-body interface. -/
theorem Index.body_root_receipt (index : Index compiled ReachedView) :
    Nonempty (AcceptedNamedBodyFlow.Body index.policy index.fuel index.compilerSource index.scope
      index.statements index.result index.reasonAt index.fellThrough index.escaped index.body) ∧
    (∀ id ∈ index.statements, index.Reached (.statement id)) :=
  ⟨index.body_receipt, fun _ member => index.body_root member⟩

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

theorem Index.statement_read_reached (index : Index compiled ReachedView) {id : StatementId}
    (reached : index.Reached (.statement id)) {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.source.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  exact (index.reached_view.statement (.inr reached)).trans (read_found accepted)

theorem Index.expression_read_reached (index : Index compiled ReachedView) {id : ExpressionId}
    (reached : index.Reached (.expression id)) {node : ExpressionNode}
    (found : index.compilerSource.lookupExpression? id = some node) :
    ∃ original, index.source.lookupExpression? id = some original ∧
      original.id = node.id ∧ original.form = node.form :=
  index.reached_view.expression (.inr reached) found

theorem Index.statement_child {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    {child : NodeId} (edge : child ∈ node.form.references) : index.Reached child := by
  rw [index.statement_reader] at accepted
  exact .statement reached (read_found accepted) edge

theorem Index.expression_child {bodyRelation : BodyRelation} (index : Index compiled bodyRelation)
    {id : ExpressionId} (reached : index.Reached (.expression id))
    {node : ExpressionNode} (found : index.compilerSource.lookupExpression? id = some node)
    {child : NodeId} (edge : child ∈ node.form.references) : index.Reached child :=
  .expression reached found edge

theorem Index.return_head_reached (index : Index compiled ReachedView)
    {invocation : Staging.Recursive.Scope} (source : invocation.source = index.source)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId} (rest : List StatementId)
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : Head invocation expression (id :: rest) :=
  .returning rest (source ▸ lookupStatement?_sound (index.statement_read_reached reached accepted)) form

theorem Index.tail_head_reached (index : Index compiled ReachedView)
    {invocation : Staging.Recursive.Scope} (source : invocation.source = index.source)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression false) : Head invocation expression [id] :=
  .tail (source ▸ lookupStatement?_sound (index.statement_read_reached reached accepted)) form

theorem Index.return_child (index : Index compiled ReachedView)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : index.Reached (.expression expression) := by
  apply index.statement_child reached accepted
  simp [form, StatementForm.references]

theorem Index.tail_child (index : Index compiled ReachedView)
    {id : StatementId} (reached : index.Reached (.statement id))
    {node : StatementNode} {type : Ty} {expression : ExpressionId} {discard : Bool}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression discard) : index.Reached (.expression expression) := by
  apply index.statement_child reached accepted
  simp [form, StatementForm.references]

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
