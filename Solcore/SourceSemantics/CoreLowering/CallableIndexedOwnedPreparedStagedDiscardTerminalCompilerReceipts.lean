import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds

/-! The accepted semicolon-discard branch retains its actual head expression
action and terminal tail receipt. Both compiler fuel decreases are extracted
from those same accepted actions. The original Source statement view retains
only the statement occurrences and forms; raw expression typing remains an
independent original Source obligation. No execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

/-- One true semicolon discard followed by an actual terminal Source tail. -/
structure Shape (source : TypedSource) (statement : StatementId)
    (firstExpression terminalExpression : ExpressionId) (rest : List StatementId) where
  node : StatementNode
  found : source.lookupStatement? statement = some node
  form : node.form = .expression firstExpression true
  terminal : Terminal source terminalExpression rest

/-- Static compiler evidence for the two expression actions actually used. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope) (statement : StatementId)
    (firstExpression terminalExpression : ExpressionId) (rest : List StatementId)
    (result : Ty) (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  shape : Shape source statement firstExpression terminalExpression rest
  childFuel : Nat
  predecessor : fuel = childFuel + 1
  first : SourceCoreBasic.LoweredExpr
  firstGenerated : policy.lowerExpression childFuel source scope firstExpression reasonAt = .ok first
  tailCode : Expr
  tail : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt policy childFuel source scope
    terminalExpression rest result reasonAt fellThrough escaped tailCode
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
    (statement :: rest) result reasonAt fellThrough escaped = .ok code
  emitted : code = CompatibleStatements.finish result
    (LocalSequence.discard (LocalLoop.controlType result) first.expression
      (LocalLoop.returnValue result tail.child.expression)) fellThrough escaped

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
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

private theorem finish_injective {type : Ty} {left right : Expr}
    {leftFellThrough leftEscaped rightFellThrough rightEscaped : Word}
    (same : CompatibleStatements.finish type left leftFellThrough leftEscaped =
      CompatibleStatements.finish type right rightFellThrough rightEscaped) : left = right := by
  unfold CompatibleStatements.finish LocalControl.finish LocalLoop.toControl LanguageResult.bind at same
  exact (Expr.caseE.inj (Expr.caseE.inj same).1).1

private theorem discard_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {rest : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {escaped : Word} {flow : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression true)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      (id :: rest) result reasonAt true escaped = .ok flow) :
    ∃ childFuel first tailFlow, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok first ∧
      SourceCoreLoops.lowerFlowStatementsWithPolicy policy childFuel source scope rest
        result reasonAt true escaped = .ok tailFlow ∧
      flow = LocalSequence.discard (LocalLoop.controlType result) first.expression tailFlow := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
    have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
    subst actual
    simp only [form] at accepted
    obtain ⟨first, generated, accepted⟩ := bind_ok accepted
    simp only [Bool.not_true, Bool.false_and, ↓reduceIte] at accepted
    obtain ⟨verified, _storedUnit, accepted⟩ := bind_ok accepted
    cases verified
    obtain ⟨tailFlow, tailGenerated, returned⟩ := bind_ok accepted
    cases returned
    exact ⟨fuel, first, tailFlow, rfl, generated, tailGenerated, rfl⟩

/-- The whole accepted action constructs both used-child receipts internally.
The head expression's native type is unrestricted; only the stored statement
projection is checked as Unit by the actual semicolon branch. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {firstExpression terminalExpression : ExpressionId} {rest : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (shape : Shape source statement firstExpression terminalExpression rest)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope
      (statement :: rest) result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Receipt policy fuel source scope statement firstExpression terminalExpression rest
      result reasonAt fellThrough escaped code) := by
  have whole := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  have footer : code = CompatibleStatements.finish result flow fellThrough escaped :=
    Except.ok.inj returned.symm
  obtain ⟨childFuel, first, tailFlow, predecessor, firstGenerated, tailGenerated, flowEq⟩ :=
    discard_flow readPolicy shape.found shape.form generated
  have tailAccepted : SourceCoreLoops.lowerStatementsWithPolicy policy childFuel source scope rest
      result reasonAt fellThrough escaped = .ok (CompatibleStatements.finish result tailFlow fellThrough escaped) := by
    unfold SourceCoreLoops.lowerStatementsWithPolicy
    rw [tailGenerated]
    rfl
  obtain ⟨tail⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    readPolicy shape.terminal tailAccepted
  have tailEq : tailFlow = LocalLoop.returnValue result tail.child.expression :=
    finish_injective tail.emitted
  refine ⟨⟨shape, childFuel, predecessor, first, firstGenerated,
    CompatibleStatements.finish result tailFlow fellThrough escaped, tail, whole, ?_⟩⟩
  simpa only [flowEq, tailEq] using footer

/-- Full statement-node transport supplies the real original discard and tail
occurrences. It does not transport expression typing or output coercions. -/
theorem Receipt.source_head {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {firstExpression terminalExpression : ExpressionId} {rest : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope statement firstExpression terminalExpression rest
      result reasonAt fellThrough escaped code)
    {invocation : Staging.Recursive.Scope}
    (view : LambdaMetadataViews.MetadataView invocation.source source) :
    ContainsStatement invocation.source statement receipt.shape.node ∧
      receipt.shape.node.form = .expression firstExpression true ∧
      CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation terminalExpression rest := by
  exact ⟨lookupStatement?_sound (view.statement receipt.shape.found), receipt.shape.form,
    CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head receipt.tail view⟩

/-- A fixed factory certificate contains only an authentic accepted action. -/
def certificate (policy : SourceCoreLoops.Policy) (reasonAt : ExpressionId → Word)
    (fellThrough escaped : Word) : FunctionCode.BodyCertificate :=
  fun source scope statements result code =>
    ∃ fuel statement firstExpression terminalExpression rest,
      statements = statement :: rest ∧ Nonempty (Receipt policy fuel source scope statement
        firstExpression terminalExpression rest result reasonAt fellThrough escaped code)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts
