import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts

/-! Accepted compilation of any finite semicolon-discard prefix followed by
one supported terminal statement. Each recursive tail retains its literal
accepted compiler action, its predecessor fuel and the ordered used child.
The receipt contains no execution law or completed body outcome. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal)

/-- The original reached statement grammar; a return may have an unexecuted suffix. -/
inductive Shape (source : TypedSource) : List StatementId → Prop where
  | terminal {expression statements} (head : Terminal source expression statements) :
      Shape source statements
  | discard {id node expression rest}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression true)
      (tail : Shape source rest) : Shape source (id :: rest)

/-- The exact emitted flow and every actual expression action, in source order. -/
inductive FlowReceipt (policy : SourceCoreLoops.Policy) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (result : Ty) (reasonAt : ExpressionId → Word)
    (fellThrough escaped : Word) : Nat → List StatementId → Expr → Type where
  | terminal {fuel expression statements code}
      (receipt : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Receipt policy fuel
        source scope expression statements result reasonAt fellThrough escaped code)
      (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
        statements result reasonAt true escaped =
          .ok (LocalLoop.returnValue result receipt.child.expression)) :
      FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements
        (LocalLoop.returnValue result receipt.child.expression)
  | discard {fuel id node expression rest flow}
      (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression true)
      (first : SourceCoreBasic.LoweredExpr)
      (firstGenerated : policy.lowerExpression fuel source scope expression reasonAt = .ok first)
      (tail : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel rest flow)
      (generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy (fuel + 1) source scope
        (id :: rest) result reasonAt true escaped =
          .ok (LocalSequence.discard (LocalLoop.controlType result) first.expression flow)) :
      FlowReceipt policy source scope result reasonAt fellThrough escaped (fuel + 1) (id :: rest)
        (LocalSequence.discard (LocalLoop.controlType result) first.expression flow)

/-- The whole body retains its original finish footer exactly once. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  flow : Expr
  tree : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    result reasonAt fellThrough escaped = .ok code
  emitted : code = CompatibleStatements.finish result flow fellThrough escaped

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

/-- Branch inversion constructs the recursive receipt from the same accepted action. -/
theorem of_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (shape : Shape source statements) {fuel : Nat} {flow : Expr}
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      statements result reasonAt true escaped = .ok flow) :
    Nonempty (FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow) := by
  induction shape generalizing fuel flow with
  | @terminal expression actualStatements head =>
    have whole : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope actualStatements
        result reasonAt fellThrough escaped =
          .ok (CompatibleStatements.finish result flow fellThrough escaped) := by
      unfold SourceCoreLoops.lowerStatementsWithPolicy
      rw [accepted]
      rfl
    obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
      readPolicy head whole
    have flowEq : flow = LocalLoop.returnValue result receipt.child.expression :=
      finish_injective receipt.emitted
    rw [flowEq] at accepted ⊢
    exact ⟨.terminal receipt accepted⟩
  | discard found form tail ih =>
    obtain ⟨childFuel, first, tailFlow, predecessor, firstGenerated, tailGenerated, flowEq⟩ :=
      discard_flow readPolicy found form accepted
    obtain ⟨tailReceipt⟩ := ih tailGenerated
    subst fuel
    subst flow
    exact ⟨.discard found form first firstGenerated tailReceipt accepted⟩

/-- Accepted whole-body compilation supplies both recursive children and footer. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {statements : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (shape : Shape source statements)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Receipt policy fuel source scope statements result reasonAt fellThrough escaped code) := by
  have whole := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  obtain ⟨tree⟩ := of_flow readPolicy shape generated
  exact ⟨⟨flow, tree, whole, Except.ok.inj returned.symm⟩⟩

/-- Literal membership preserves ordered and repeated children without choosing a substitute. -/
def FlowReceipt.Children {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (tree : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow)
    (expression : ExpressionId) (child : SourceCoreBasic.LoweredExpr) : Prop :=
  match tree with
  | @FlowReceipt.terminal _ _ _ _ _ _ _ _ terminalExpression _ _ receipt _ =>
      expression = terminalExpression ∧ child = receipt.child
  | @FlowReceipt.discard _ _ _ _ _ _ _ _ _ _ firstExpression _ _ _ _ first _ tail _ =>
      (expression = firstExpression ∧ child = first) ∨ tail.Children expression child

/-- The fixed certificate records only actual compiler receipts. -/
def certificate (policy : SourceCoreLoops.Policy) (reasonAt : ExpressionId → Word)
    (fellThrough escaped : Word) : FunctionCode.BodyCertificate :=
  fun source scope statements result code =>
    ∃ fuel, Nonempty (Receipt policy fuel source scope statements result reasonAt fellThrough escaped code)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
