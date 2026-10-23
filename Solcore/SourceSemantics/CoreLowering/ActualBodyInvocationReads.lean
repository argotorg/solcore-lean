import Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-! The real named or contextual compiler statement reader retains the Source
statement selected by the same invocation. Terminal heads come from that read. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
open Core Frontend SourceInference
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

theorem Index.statement_reader {bodyRelation : BodyRelation} (index : Index compiled bodyRelation) : index.policy.readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  cases index with
  | named => rfl
  | contextual material _ => exact GeneralizedLocalAcceptedBodyCompiler.statement_reader material

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

theorem Index.statement_read (index : Index compiled) {id : StatementId}
    {node : StatementNode} {type : Ty}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type)) :
    index.source.lookupStatement? id = some node := by
  rw [index.statement_reader] at accepted
  exact index.source_view.statement (read_found accepted)

theorem Index.return_head (index : Index compiled) {invocation : Staging.Recursive.Scope}
    (source : invocation.source = index.source) {id : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId} (rest : List StatementId)
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .returnStmt (some expression)) : Head invocation expression (id :: rest) := by
  exact .returning rest (source ▸ lookupStatement?_sound (index.statement_read accepted)) form

theorem Index.tail_head (index : Index compiled) {invocation : Staging.Recursive.Scope}
    (source : invocation.source = index.source) {id : StatementId} {node : StatementNode}
    {type : Ty} {expression : ExpressionId}
    (accepted : index.policy.readStatement index.compilerSource id = .ok (node, type))
    (form : node.form = .expression expression false) : Head invocation expression [id] := by
  exact .tail (source ▸ lookupStatement?_sound (index.statement_read accepted)) form

end Solcore.SourceSemantics.CoreLowering.ActualBodyInvocation
