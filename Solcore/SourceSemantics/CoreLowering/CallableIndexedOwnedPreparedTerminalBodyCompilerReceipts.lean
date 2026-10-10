import Solcore.SourceSemantics.CoreLowering.FunctionCodeCertificates
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedStagedTerminalStatements

/-! Accepted terminal body compilation retains the exact used expression
action and original footer. This first bridge stays at the same Source as the
compiler. It supplies no expression execution or completed body law. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
open Core Frontend SourceInference
open CompatibleEncoding (bind_ok)

inductive Terminal (source : TypedSource) (expression : ExpressionId) : List StatementId → Prop where
  | returning {id node} (rest : List StatementId)
      (found : source.lookupStatement? id = some node)
      (form : node.form = .returnStmt (some expression)) : Terminal source expression (id :: rest)
  | tail {id node} (found : source.lookupStatement? id = some node)
      (form : node.form = .expression expression false) : Terminal source expression [id]

/-- Static fields extracted from the actual accepted terminal branch. -/
structure Receipt (policy : SourceCoreLoops.Policy) (fuel : Nat)
    (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (expression : ExpressionId) (statements : List StatementId) (result : Ty)
    (reasonAt : ExpressionId → Word) (fellThrough escaped : Word) (code : Expr) where
  childFuel : Nat
  child : SourceCoreBasic.LoweredExpr
  predecessor : fuel = childFuel + 1
  generated : policy.lowerExpression childFuel source scope expression reasonAt = .ok child
  sameType : child.type = result
  terminal : Terminal source expression statements
  accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
    result reasonAt fellThrough escaped = .ok code
  emitted : code = CompatibleStatements.finish result
    (LocalLoop.returnValue result child.expression) fellThrough escaped

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

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem return_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {rest : List StatementId} {result : Ty}
    {reasonAt : ExpressionId → Word} {mode : Bool} {escaped : Word} {flow : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .returnStmt (some expression))
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      (id :: rest) result reasonAt mode escaped = .ok flow) :
    ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
    have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
    subst actual
    simp only [form] at accepted
    obtain ⟨checked, _, accepted⟩ := bind_ok accepted
    cases checked
    obtain ⟨child, generated, accepted⟩ := bind_ok accepted
    obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
    cases checked
    have same := ensure_same checkedType
    subst result
    cases accepted
    exact ⟨fuel, child, rfl, generated, rfl, rfl⟩

private theorem tail_flow {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id : StatementId} {node : StatementNode}
    {expression : ExpressionId} {result : Ty} {reasonAt : ExpressionId → Word}
    {escaped : Word} {flow : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .expression expression false)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope
      [id] result reasonAt true escaped = .ok flow) :
    ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
    have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
    subst actual
    simp only [form] at accepted
    obtain ⟨child, generated, accepted⟩ := bind_ok accepted
    simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
    obtain ⟨checked, _, accepted⟩ := bind_ok accepted
    cases checked
    obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
    cases checked
    have same := ensure_same checkedType
    subst result
    cases accepted
    exact ⟨fuel, child, rfl, generated, rfl, rfl⟩

/-- The source lookup and actual compiler output construct the receipt. -/
theorem of_accepted {policy : SourceCoreLoops.Policy}
    {checked : SourceCoreCompatibleCatalog.Checked} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement checked)
    (terminal : Terminal source expression statements)
    (accepted : SourceCoreLoops.lowerStatementsWithPolicy policy fuel source scope statements
      result reasonAt fellThrough escaped = .ok code) :
    Nonempty (Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code) := by
  have whole := accepted
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  have footer : code = CompatibleStatements.finish result flow fellThrough escaped :=
    Except.ok.inj returned.symm
  have used : ∃ childFuel child, fuel = childFuel + 1 ∧
      policy.lowerExpression childFuel source scope expression reasonAt = .ok child ∧
      child.type = result ∧ flow = LocalLoop.returnValue result child.expression := by
    cases terminal with
    | returning rest found form => exact return_flow readPolicy found form generated
    | tail found form => exact tail_flow readPolicy found form generated
  obtain ⟨childFuel, child, predecessor, childGenerated, sameType, flowEq⟩ := used
  exact ⟨⟨childFuel, child, predecessor, childGenerated, sameType, terminal, whole, flowEq ▸ footer⟩⟩

/-- The exact original source relation supplies the genuine staged Head. -/
theorem Receipt.head {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code)
    (invocation : Staging.Recursive.Scope) (sameSource : invocation.source = source) :
    CallableIndexedOwnedAdmittedStagedTerminalStatements.Head invocation expression statements := by
  cases sameSource
  cases receipt.terminal with
  | returning rest found form => exact .returning rest (lookupStatement?_sound found) form
  | tail found form => exact .tail (lookupStatement?_sound found) form

/-- Enclosing native checking supplies typing of the same used child. -/
theorem Receipt.native_child {policy : SourceCoreLoops.Policy} {fuel : Nat} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {expression : ExpressionId} {statements : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope expression statements result reasonAt fellThrough escaped code)
    {context : Core.Context} {nativeType : Ty} {definitions : DataEnvironment}
    (typed : HasType context code nativeType definitions) :
    ∃ childType, HasType context receipt.child.expression childType definitions := by
  rw [receipt.emitted] at typed
  obtain ⟨flowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow typed
  cases flowTyped with
  | caseE computation failure next => exact ⟨_, computation⟩

/-- A chosen static body certificate stores only accepted compiler receipts. -/
def certificate (policy : SourceCoreLoops.Policy) (reasonAt : ExpressionId → Word)
    (fellThrough escaped : Word) : FunctionCode.BodyCertificate :=
  fun source scope statements result code =>
    ∃ fuel expression, Nonempty (Receipt policy fuel source scope expression statements result
      reasonAt fellThrough escaped code)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
