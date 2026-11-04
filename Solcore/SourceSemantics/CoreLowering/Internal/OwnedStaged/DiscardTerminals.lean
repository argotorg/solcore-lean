import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.LambdaViewTrees

/-!
# Staged bounds: discard terminals

Compiler receipts of discard terminals and sequences, their flow and body bounds, and the Source typing and inversion of these bodies.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
/-! An actual semicolon discard before a supported terminal statement retains
two original Source children. Lookup uniqueness selects the expression trace;
full original body typing supplies its raw type and the remaining terminal
child at the same parameter context. No body execution law is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
open Frontend SourceInference
open Staging.Recursive
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

/-- A failed prefix returns its exact nested Failure. A successful prefix
retains the actual middle heap and the original remaining statement trace. -/
theorem child_and_tail {program : Program} {registry : Registry} {invocation : Scope}
    {context finalContext : SourceSemantics.Context} {environment : Dynamic.Environment}
    {before after : Dynamic.Heap} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {size : Nat} {outcome : BodyOutcome}
    (unique : NodeOccurrencesUnique invocation.source)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (trace : Size.Statements program registry size invocation context environment before
      (id :: rest) finalContext outcome after) :
    (∃ childSize failure,
      size = Size.stepSize [childSize] ∧ finalContext = context ∧ outcome = .fault failure ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.fault failure) after) ∨
    (∃ childSize tailSize value middle,
      size = Size.stepSize [childSize, tailSize] ∧
      Size.Expression program registry childSize invocation context environment before
        expression (.value value) middle ∧
      Size.Statements program registry tailSize invocation context environment middle
        rest finalContext outcome after) := by
  have shape := @statement_shape _ _ _ _ unique contains form
  cases trace with
  | breaking actual same | continuing actual same
  | blockBreaking actual same _ | blockContinuing actual same _
  | ifBreaking actual same _ _ | ifContinuing actual same _ _
  | matchBreaking actual same _ | matchContinuing actual same _
  | forInitializerFault actual same _ | forReturned actual same _ _ | forFault actual same _ _
  | forFallthrough actual same _ _ _
  | matchReturned actual same _ | matchFault actual same _ | matchFallthrough actual same _ _
  | blockReturned actual same _ | blockFault actual same _ | blockFallthrough actual same _ _
  | whileReturned actual same _ | whileFault actual same _ | whileFallthrough actual same _ _
  | ifConditionFault actual same _ | ifReturned actual same _ _ | ifFault actual same _ _
  | ifFallthrough actual same _ _ _ =>
    have impossible := (shape actual).symm.trans same
    cases impossible
  | returnUnit actual same =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | returnValue actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | returnFault actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | tail actual same child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | discard actual same child remaining =>
    have equal := (shape actual).symm.trans same
    cases equal
    exact .inr ⟨_, _, _, _, rfl, child, remaining⟩
  | expressionFault actual same child =>
    have equal := (shape actual).symm.trans same
    cases equal
    exact .inl ⟨_, _, rfl, rfl, rfl, child⟩
  | letGeneralized actual same _ _ _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | letUninitialized actual same monomorphic extension allocation remaining =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | letInitialized actual same child monomorphic extension allocation remaining =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | letFault actual same monomorphic child =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | bitNotProjected actual same _ _ _ _ _
  | bitNotProjectedRootFault actual same _ _
  | bitNotProjectedKeysFault actual same _ _ _
  | bitNotProjectedGetterFault actual same _ _ _
  | bitNotBare actual same _ _ _ | bitNotBareFault actual same _ _
  | assignProjected actual same _ _ _ _ _ _
  | assignProjectedRootFault actual same _ _
  | assignProjectedKeysFault actual same _ _ _
  | assignProjectedGetterFault actual same _ _ _
  | assignProjectedRhsFault actual same _ _ _ _
  | assignProjectedWriteFault actual same _ _ _ _ _
  | assignBare actual same _ _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareOperands actual same _ _ _ _ _ _ _ | assignBareFault actual same _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareUnbound actual same _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible
  | assignBareDangling actual same _ _ _ =>
    have impossible := shape actual
    rw [same] at impossible
    cases impossible

private theorem discard_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, final = context ∧
      facts = { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      ExpressionHasType source context expression type := by
  have shape := @statement_shape _ _ _ _ unique contains form
  clear contains form
  cases typed <;> have actualForm := shape (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- Both children use the original raw parameter context. The discard has no
lexical effect, and its ordinary control summary preserves tail completeness. -/
theorem children_typed {invocation : Scope} {context final : SourceSemantics.Context}
    {id next : StatementId} {rest : List StatementId} {node : StatementNode}
    {expression terminal : ExpressionId} {expected : TypeSystem.Ty} {facts : BodyFacts}
    (unique : NodeOccurrencesUnique invocation.source)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (head : Head invocation terminal (next :: rest))
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context (id :: next :: rest) final facts)
    (completes : BodyCompletes expected facts) :
    ∃ firstNode terminalNode,
      invocation.source.lookupExpression? expression = some firstNode ∧
      ExpressionHasType invocation.source context expression firstNode.type ∧
      invocation.source.lookupExpression? terminal = some terminalNode ∧
      terminalNode.type = expected ∧
      ExpressionHasType invocation.source context terminal terminalNode.type := by
  cases typed with
  | @cons _ _ _ _ _ _ _ _ tailFacts first remaining =>
    obtain ⟨firstType, rfl, rfl, firstTyped⟩ := discard_typed unique contains form first
    have tailCompletes : BodyCompletes expected tailFacts := by
      simpa [BodyFacts.cons] using completes
    obtain ⟨terminalNode, terminalFound, resultType, terminalTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head remaining tailCompletes
    obtain ⟨firstNode, firstContains, firstTypeEq⟩ := firstTyped.stored_type
    exact ⟨firstNode, terminalNode, lookupExpression?_complete unique firstContains,
      firstTypeEq ▸ firstTyped, terminalFound, resultType, terminalTyped⟩

/-- The original closure frame and the actual parameter extension supply the
full typing derivation before either expression child is selected. -/
theorem at_parameters {program : Program} {function : Dynamic.Closure}
    {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
    {invocation : Scope} {id next : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression terminal : ExpressionId}
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source)
    (body : function.body = id :: next :: rest)
    (contains : ContainsStatement invocation.source id node)
    (form : node.form = .expression expression true)
    (head : Head invocation terminal (next :: rest)) :
    ∃ firstNode terminalNode,
      invocation.source.lookupExpression? expression = some firstNode ∧
      ExpressionHasType invocation.source context expression firstNode.type ∧
      invocation.source.lookupExpression? terminal = some terminalNode ∧
      terminalNode.type = function.resultType ∧
      ExpressionHasType invocation.source context terminal terminalNode.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [body, ← source] at typed
  exact children_typed unique contains form head typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
/-! A real semicolon discard and an original terminal tail compose two
authentic Source Roots. Every expression and called-body law is supplied
internally by the checked selected caller family. The intermediate state is
the head producer's actual reached state. This flow adapter leaves the same
accepted statement/compiler and mixed invoked-body factory joins explicit. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedAdmittedStagedTerminalStatements (Head control ResultRepresents)
open GenericExpressionMeaning (agree_prefix rename_prefix)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
private theorem internal_preserves_below {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (budget : Nat) :
    PreservesBelow bridge context model stages invocation (Point scope expression lowered) callFaults budget := by
  intro childSize _strict
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport) root childSize

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport in
private theorem internal_reflects_below
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {context invocation scope expression lowered}
    (root : RootAt compiled context invocation scope expression lowered semanticFaults)
    (budget : Nat) :
    ReflectsBelow bridge context model stages invocation (Point scope expression lowered) callFaults budget := by
  intro childSize _strict
  exact CallableIndexedOwnedPreparedStagedSelectedCallerFromRecursiveBodies.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport) stageEq root childSize

section Flow
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {firstExpression terminalExpression : ExpressionId}
  {firstCode terminalCode : SourceCoreBasic.LoweredExpr}
  (firstRoot : RootAt compiled context invocation scope firstExpression firstCode semanticFaults)
  (terminalRoot : RootAt compiled context invocation scope terminalExpression terminalCode semanticFaults)
  {statement : StatementId} {rest : List StatementId} {statementNode : StatementNode}
  (contains : ContainsStatement invocation.source statement statementNode)
  (form : statementNode.form = .expression firstExpression true)
  (terminal : Head invocation terminalExpression rest)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport
  firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Original statement inversion selects both genuine children. Successful
head effects feed the tail at its reached Admission and the inserted native
temporary binder. The public theorem accepts no child execution law. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: rest) finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
          (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := internal_preserves_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport firstRoot size
  have terminalBelow := internal_preserves_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport terminalRoot size
  rcases CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.child_and_tail
      firstRoot.support.unique contains form trace with
    ⟨firstSize, failure, sameSize, rfl, rfl, firstTrace⟩ |
    ⟨firstSize, tailSize, sourceValue, middle, sameSize, firstTrace, tailTrace⟩
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | fault matched =>
        refine ⟨rfl, .fault failure, rfl, _, finalStore, finalMap, finalWorld, ?_, .fault matched,
          finalHeaps, maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
        rw [LoopRenaming.discard]
        exact LocalSequence.discard_failure _ evaluated
  · have firstStrict : firstSize < size := by
      rw [sameSize]
      exact Staging.Recursive.Size.child_lt_stepSize (by simp)
    obtain ⟨value, middleStore, middleMap, middleWorld, first, represented, middleHeaps,
        firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
      firstBelow firstSize firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
        environments heaps locals agrees actualTyped initial admitted firstTrace
    cases represented with
    | @value sourceValue coreValue payload =>
        obtain ⟨terminalSize, outcome, sameTailSize, rfl, rfl, terminalTrace⟩ :=
          CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.child_of_body
            terminalRoot.support.unique terminal tailTrace
        have tailWithin : Staging.Recursive.Size.stepSize [terminalSize] ≤ size := by
          rw [← sameTailSize, sameSize]
          exact Nat.le_of_lt (Staging.Recursive.Size.child_lt_stepSize (by simp))
        obtain ⟨_tailTrace, value, finalStore, finalMap, finalWorld, second, represented, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post⟩ :=
          CallableIndexedOwnedAdmittedStagedTerminalStatements.preserves bridge terminal
            ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
            (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
            (agree_prefix agrees coreValue)
            (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
            middleState firstPost.at_value.2 size terminalBelow terminalTrace tailWithin
        refine ⟨rfl, outcome, rfl, value, finalStore, finalMap, finalWorld, ?_, represented, finalHeaps,
          firstMaps.trans maps, firstWorlds.trans worlds, firstFrame.trans frame,
          firstMetadata.trans metadata, reached, callerProtocol.trans firstRelated related, post⟩
        rw [LoopRenaming.discard]
        rw [rename_prefix] at second
        exact LocalSequence.discard_success _ first second

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport
  firstRoot contains form terminal environments heaps locals agrees actualTyped admitted in
/-- Native inversion supplies strict executed children. Reflection rebuilds
the original discard and terminal Source traces with independent grades,
retaining the same stores, record relations and exact nested Failure. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType terminalCode.type) firstCode.expression
        (LocalLoop.returnValue terminalCode.type terminalCode.expression)).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: rest) context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld terminalRoot.support.node.type terminalCode.type
        callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        PostAdmission bridge context terminalRoot.support.node.type outcome reached := by
  have firstBelow := internal_reflects_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport stageEq firstRoot size
  have terminalBelow := internal_reflects_below bridge receiver stagePrepared profile observations extension
    semantic closureTerminals namedTerminals closureSupport namedSupport stageEq terminalRoot size
  have original := completed
  rw [LoopRenaming.discard] at original
  change EvaluationSize size actual store
    (LanguageResult.bind (LocalLoop.controlType terminalCode.type) (firstCode.expression.rename ξ)
      (((LocalLoop.returnValue terminalCode.type terminalCode.expression).rename ξ).weakenAt 0))
    value finalStore at original
  cases CallableIndirectCallBounds.bind_completed original (Nat.le_refl _) with
  | failed first strict =>
      obtain ⟨firstSize, outcome, after, finalMap, finalWorld, firstTrace, represented, finalHeaps,
          maps, worlds, frame, metadata, reached, related, post⟩ :=
        firstBelow _ strict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | fault matched =>
          exact ⟨_, .fault _, after, finalMap, finalWorld,
            .expressionFault contains form firstTrace, .fault matched, finalHeaps,
            maps, worlds, frame, metadata, reached, related, post.at_fault_type⟩
  | continued first remaining firstStrict remainingStrict =>
      obtain ⟨firstSize, outcome, middle, middleMap, middleWorld, firstTrace, represented, middleHeaps,
          firstMaps, firstWorlds, firstFrame, firstMetadata, middleState, firstRelated, firstPost⟩ :=
        firstBelow _ firstStrict ⟨rfl, rfl, rfl⟩ firstRoot.support.found firstRoot.support.typed
          environments heaps locals agrees actualTyped initial admitted first
      cases represented with
      | @value sourceValue coreValue payload =>
          have shifted := remaining
          rw [← rename_prefix] at shifted
          obtain ⟨tailSize, outcome, after, finalMap, finalWorld, tailTrace, represented, finalHeaps,
              maps, worlds, frame, metadata, reached, related, post⟩ :=
            CallableIndexedOwnedAdmittedStagedTerminalStatements.reflects bridge terminal
              ⟨rfl, rfl, rfl⟩ terminalRoot.support.found terminalRoot.support.typed
              (environments.extend firstMaps firstWorlds) middleHeaps (locals.mono firstMetadata)
              (agree_prefix agrees _)
              (.cons ((model).runtime_hasType payload) (actualTyped.weaken firstWorlds))
              middleState firstPost.at_value.2 size terminalBelow shifted (Nat.le_of_lt remainingStrict)
          exact ⟨_, outcome, after, finalMap, finalWorld, .discard contains form firstTrace tailTrace,
            represented, finalHeaps, firstMaps.trans maps, firstWorlds.trans worlds,
            firstFrame.trans frame, firstMetadata.trans metadata, reached,
            callerProtocol.trans firstRelated related, post⟩
end Flow
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
/-! The same accepted discard receipt issues both original expression Roots.
Original closure-frame typing supplies the real nodes; the actual expression
callback and reached view transport supply both accepted compiler actions.
Static call authority is indexed by these exact internally issued proofs.
Preservation and reflection then invoke the constructive flow family once.
The whole-body finish footer and a mixed invoked-body family remain separate.
No expression/body execution callback or desired result is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (RootAt NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor Certificate)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control ResultRepresents)

/-- Both raw nodes are authentic original lookups. The discard head is not
required to have Unit raw type; the terminal node retains the function result. -/
structure OriginalChildren (source : TypedSource) (context : SourceSemantics.Context)
    (firstExpression terminalExpression : ExpressionId) (result : TypeSystem.Ty) where
  first : ExpressionNode
  firstFound : source.lookupExpression? firstExpression = some first
  firstTyped : ExpressionHasType source context firstExpression first.type
  terminal : ExpressionNode
  terminalFound : source.lookupExpression? terminalExpression = some terminal
  terminalResult : terminal.type = result
  terminalTyped : ExpressionHasType source context terminalExpression terminal.type

section Static
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {function : Dynamic.Closure} {context : SourceSemantics.Context} {types : List TypeSystem.Ty}
  {invocation : Staging.Recursive.Scope} {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {semanticFaults : FunctionCalls.FaultRep}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}

/-- Only actual compiler, original typing and reached-call authority is stored.
The accepted receipt is a fixed index, so both child actions belong to it. -/
structure Static
    (receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
      (next :: rest) result reasonAt fellThrough escaped code) where
  edited : LocalView invocation.source view changed
  avoids : Avoids invocation.source roots changed
  sourceProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source scope reasonAt
  viewProfile : PolicyFor policy compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    view scope reasonAt
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy native active
  expressionCallback : statementPolicy.lowerExpression = fun childFuel source current id token =>
    SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min childFuel bodyFuel)
      compilation source current id token
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function
  parameters : MonoBindersExtend function.source.owner function.context function.parameters types context
  sameSource : invocation.source = function.source
  body : function.body = statement :: next :: rest
  firstSyntax : Syntax view firstExpression
  terminalSyntax : Syntax view terminalExpression
  firstReached : Reaches invocation.source roots (.expression firstExpression)
  terminalReached : Reaches invocation.source roots (.expression terminalExpression)
  conditions : OriginalConditions compiled policy compilation readFuel context invocation
    reasonAt scope semanticFaults

/-- Option.get selects the actual stored nodes; frame-derived existence is used
only to prove that each lookup succeeds and that its raw properties hold. -/
def Static.originalChildren
    {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
      (next :: rest) result reasonAt fellThrough escaped code}
    (packet : Static (compiled := compiled) (function := function) (context := context)
      (types := types) (invocation := invocation) (changed := changed) (roots := roots)
      (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
      (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
      (native := native) (active := active) receipt) :
    OriginalChildren invocation.source context firstExpression terminalExpression function.resultType := by
  have head := receipt.source_head packet.edited.metadata
  have raw := CallableIndexedOwnedPreparedStagedDiscardSourceBodyInversion.at_parameters
    packet.frame packet.parameters packet.sameSource packet.body head.1 head.2.1 head.2.2
  have firstAvailable : (invocation.source.lookupExpression? firstExpression).isSome := by
    obtain ⟨first, terminal, firstFound, _⟩ := raw
    exact Option.isSome_of_eq_some firstFound
  have terminalAvailable : (invocation.source.lookupExpression? terminalExpression).isSome := by
    obtain ⟨first, terminal, firstFound, firstTyped, terminalFound, _⟩ := raw
    exact Option.isSome_of_eq_some terminalFound
  let first := (invocation.source.lookupExpression? firstExpression).get firstAvailable
  let terminal := (invocation.source.lookupExpression? terminalExpression).get terminalAvailable
  have firstFound : invocation.source.lookupExpression? firstExpression = some first :=
    Option.eq_some_of_isSome firstAvailable
  have terminalFound : invocation.source.lookupExpression? terminalExpression = some terminal :=
    Option.eq_some_of_isSome terminalAvailable
  have properties : ExpressionHasType invocation.source context firstExpression first.type ∧
      terminal.type = function.resultType ∧
      ExpressionHasType invocation.source context terminalExpression terminal.type := by
    obtain ⟨originalFirst, originalTerminal, foundFirst, typedFirst, foundTerminal,
      sameResult, typedTerminal⟩ := raw
    have firstEq : originalFirst = first := Option.some.inj (foundFirst.symm.trans firstFound)
    have terminalEq : originalTerminal = terminal := Option.some.inj (foundTerminal.symm.trans terminalFound)
    simpa only [firstEq, terminalEq] using And.intro typedFirst (And.intro sameResult typedTerminal)
  exact ⟨first, firstFound, properties.1, terminal, terminalFound, properties.2.1, properties.2.2⟩

variable {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)

private def first_authority :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority packet.conditions
    ⟨packet.originalChildren.first, packet.originalChildren.firstFound, rfl,
      packet.originalChildren.firstTyped⟩
private def terminal_authority :=
  CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories.original_authority packet.conditions
    ⟨packet.originalChildren.terminal, packet.originalChildren.terminalFound,
      packet.originalChildren.terminalResult, packet.originalChildren.terminalTyped⟩

include packet in
private theorem first_action : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
    (min receipt.childFuel bodyFuel) compilation view scope firstExpression reasonAt = .ok receipt.first := by
  simpa only [packet.expressionCallback] using receipt.firstGenerated
include packet in
private theorem terminal_action : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody
    (min receipt.tail.childFuel bodyFuel) compilation view scope terminalExpression reasonAt = .ok receipt.tail.child := by
  simpa only [packet.expressionCallback] using receipt.tail.generated

include packet in
/-- This proof is issued by the real recursive extractor from the same first
accepted action, after genuine view transport and original raw typing. -/
theorem first_certificate : Certificate policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope firstExpression receipt.first :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    packet.firstSyntax packet.firstReached (first_authority packet) (first_action packet)
include packet in
/-- The tail certificate is indexed by the terminal child actually retained in
the same accepted whole action, with its own authentic compiler budget. -/
theorem terminal_certificate : Certificate policy lowerBody compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    invocation.source context reasonAt scope terminalExpression receipt.tail.child :=
  CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.issued_certificate
    packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
    packet.terminalSyntax packet.terminalReached (terminal_authority packet) (terminal_action packet)

/-- Both call ports belong to these exact proofs. They contain static callsite
and selected-body authority, never a caller or body execution law. -/
structure Ready : Prop where
  first : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) (first_certificate packet)
  terminal : CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.CallsReady
    (compiled := compiled) (invocation := invocation) (terminal_certificate packet)

/-- Both real original Roots are manufactured internally. The tail's original
raw result is retained explicitly, independently of its native projected type. -/
def rootPair (ready : Ready packet) :
    RootAt compiled context invocation scope firstExpression receipt.first semanticFaults ×
    { terminalRoot : RootAt compiled context invocation scope terminalExpression receipt.tail.child semanticFaults //
      terminalRoot.rawType = function.resultType } :=
  ⟨CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action
      packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
      packet.firstSyntax packet.firstReached (first_authority packet) (first_action packet) ready.first,
    CallableIndexedOwnedPreparedStagedSelectedBodyCompilerRoots.rootAt_of_view_action
      packet.edited packet.avoids packet.sourceProfile packet.viewProfile packet.callables
      packet.terminalSyntax packet.terminalReached (terminal_authority packet) (terminal_action packet) ready.terminal,
    rfl⟩
end Static

universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section Bounds
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {function : Dynamic.Closure} {types : List TypeSystem.Ty}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
  (ready : Ready packet)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- The receipt's exact head/tail actions, original frame and static call ports
construct both expression meanings before the original flow is preserved. -/
theorem preserves {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: next :: rest)
      finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧ ∃ value finalStore finalMap finalWorld,
      Evaluates actual store
        ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
          (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ) value finalStore ∧
      ResultRepresents model finalMap finalWorld function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context function.resultType outcome reached := by
  let pair := rootPair packet ready
  have originalHead := receipt.source_head packet.edited.metadata
  have rawType : pair.2.val.support.node.type = function.resultType :=
    pair.2.val.support.rawResult.trans pair.2.property
  have produced := CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (profile := profile)
    (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (firstRoot := pair.1) (terminalRoot := pair.2.val)
    (contains := originalHead.1) (form := originalHead.2.1) (terminal := originalHead.2.2)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) trace
  simpa only [rawType, receipt.tail.sameType] using produced

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- Native inversion uses the same receipt and independently issued children.
The returned original grades and reached state come from the flow family. -/
theorem reflects (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
        (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: next :: rest) context (control outcome) after ∧
      ResultRepresents model finalMap finalWorld function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context function.resultType outcome reached := by
  let pair := rootPair packet ready
  have originalHead := receipt.source_head packet.edited.metadata
  have rawType : pair.2.val.support.node.type = function.resultType :=
    pair.2.val.support.rawResult.trans pair.2.property
  have expanded : EvaluationSize size actual store
      ((LocalSequence.discard (LocalLoop.controlType receipt.tail.child.type) receipt.first.expression
        (LocalLoop.returnValue receipt.tail.child.type receipt.tail.child.expression)).rename ξ) value finalStore := by
    simpa only [receipt.tail.sameType] using completed
  have produced := CallableIndexedOwnedPreparedStagedDiscardTerminalFlowBounds.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared) (profile := profile)
    (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (firstRoot := pair.1) (terminalRoot := pair.2.val)
    (contains := originalHead.1) (form := originalHead.2.1) (terminal := originalHead.2.2)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) stageEq expanded
  simpa only [rawType, receipt.tail.sameType] using produced
end Bounds
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds
/-! The same accepted discard receipt supplies the literal whole-body footer.
The checked compiler-flow family constructs both child meanings internally;
the existing finish and prefix lemmas preserve its exact returned value or
staged failure and reached caller state. Native reflection uses the actual
strict flow child and determinism. No body execution law or desired result
is an input. Mixed called-body support remains a separate grammar extension. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds (TerminalFor)
open CallableIndexedOwnedPreparedStagedTerminalNamedGlobalDispatch (Terminal)
open CallableIndexedOwnedPreparedStagedSelectedBodyStaticSupport (NamedSupport ClosureSupportFor)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts (Receipt)
open CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds (Static Ready)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedTerminalBodyMeaning (fallback)

/-- The actual accepted statement action fixes the flow and footer together. -/
theorem emitted_rename {policy : SourceCoreLoops.Policy} {fuel : Nat}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {statement : StatementId}
    {firstExpression terminalExpression : ExpressionId} {rest : List StatementId}
    {result : Ty} {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
    (receipt : Receipt policy fuel source scope statement firstExpression terminalExpression rest
      result reasonAt fellThrough escaped code) (ξ : Renaming) :
    code.rename ξ = CallableIndexedOwnedAdmittedStagedTerminalBody.code result
      ((LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
        (LocalLoop.returnValue result receipt.tail.child.expression)).rename ξ)
      escaped ((fallback result fellThrough).rename ξ) := by
  have footer := congrArg (fun generated : Expr => generated.rename ξ) receipt.emitted
  exact footer.trans (by
    simpa only [CompatibleStatements.finish,
      CallableIndexedOwnedAdmittedStagedTerminalBody.code, fallback] using
      (CallableIndexedOwnedAdmittedStagedTerminalBody.code_rename result
        (LocalSequence.discard (LocalLoop.controlType result) receipt.first.expression
          (LocalLoop.returnValue result receipt.tail.child.expression))
        escaped (fallback result fellThrough) ξ))

universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closureTerminals : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), TerminalFor association stages)
  (namedTerminals : ∀ header, header ∈ headers → Terminal header)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore),
    ClosureSupportFor association stages (closureTerminals association))
  (namedSupport : ∀ header (member : header ∈ headers),
    CallableIndexedOwnedPreparedStagedNamedBodySupport.LegacySupport headers keys bodyRegistry
      header stages (namedTerminals header member) semanticFaults)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section Bounds
variable {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {scope : SourceCoreLocalCell.Scope} {statement next : StatementId} {rest : List StatementId}
  {firstExpression terminalExpression : ExpressionId} {result : Ty}
  {reasonAt : ExpressionId → Word} {fellThrough escaped : Word} {code : Expr}
  {statementPolicy : SourceCoreLoops.Policy} {fuel : Nat} {view : TypedSource}
  {function : Dynamic.Closure} {types : List TypeSystem.Ty}
  {changed : List ExpressionId} {roots : List NodeId}
  {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
  {compilation : SourceCoreFunctions.Context} {readFuel bodyFuel : Nat}
  {native : Option SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
  {receipt : Receipt statementPolicy fuel view scope statement firstExpression terminalExpression
    (next :: rest) result reasonAt fellThrough escaped code}
  (packet : Static (compiled := compiled) (function := function) (context := context)
    (types := types) (invocation := invocation) (changed := changed) (roots := roots)
    (policy := policy) (lowerBody := lowerBody) (compilation := compilation)
    (readFuel := readFuel) (bodyFuel := bodyFuel) (semanticFaults := semanticFaults)
    (native := native) (active := active) receipt)
  (ready : Ready packet)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
  {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents
    (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (heaps : GenericHeap.HeapRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- The complete Source trace constructs its actual BodyResult and the whole
native code from the same internally issued head and terminal certificates. -/
theorem preserves_body {size : Nat} {finalContext : SourceSemantics.Context}
    {bodyOutcome : Staging.Recursive.BodyOutcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram)
      stages size invocation context environment before (statement :: next :: rest)
      finalContext bodyOutcome after) :
    finalContext = context ∧ ∃ outcome,
      bodyOutcome = control outcome ∧
      Staging.Recursive.BodyResult function.resultType bodyOutcome outcome ∧
      ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (code.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context function.resultType outcome reached := by
  obtain ⟨sameContext, outcome, sameBody, value, finalStore, finalMap, finalWorld,
      evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.preserves
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (packet := packet) (ready := ready)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) trace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback result fellThrough).rename ξ) represented evaluated escaped
  have evaluatedBody : Evaluates actual store (code.rename ξ) wholeValue finalStore := by
    rw [emitted_rename receipt ξ]
    exact whole
  have bodyResult : Staging.Recursive.BodyResult function.resultType bodyOutcome outcome := by
    rw [sameBody]
    exact CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _
  exact ⟨sameContext, outcome, sameBody, bodyResult, wholeValue, finalStore, finalMap, finalWorld,
    evaluatedBody, resultRep, finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩

include bridge receiver stagePrepared observations extension semantic
  closureTerminals namedTerminals closureSupport namedSupport packet ready
  environments heaps locals agrees actualTyped admitted in
/-- Footer inversion obtains a real strict flow child. Its constructive
reflection and deterministic footer retain the original completed endpoint. -/
theorem reflects_body (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Statements (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before (statement :: next :: rest) context (control outcome) after ∧
      Staging.Recursive.BodyResult function.resultType (control outcome) outcome ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        function.resultType result callFaults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          bridge context function.resultType outcome reached := by
  have original := completed
  rw [emitted_rename receipt ξ] at original
  obtain ⟨flowSize, flowValue, flowStore, flowTrace, _strict⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.flow_prefix original (Nat.le_refl size)
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented,
      finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.reflects
    (bridge := bridge) (receiver := receiver) (stagePrepared := stagePrepared)
    (profile := profile) (observations := observations) (extension := extension) (semantic := semantic)
    (closureTerminals := closureTerminals) (namedTerminals := namedTerminals)
    (closureSupport := closureSupport) (namedSupport := namedSupport)
    (packet := packet) (ready := ready)
    (environments := environments) (heaps := heaps) (locals := locals) (agrees := agrees)
    (actualTyped := actualTyped) (initial := initial) (admitted := admitted) stageEq flowTrace
  obtain ⟨wholeValue, whole, resultRep⟩ :=
    CallableIndexedOwnedAdmittedStagedTerminalBody.terminal_evaluates
      (fallback := (fallback result fellThrough).rename ξ) represented flowTrace.sound escaped
  obtain ⟨same, stores⟩ := evaluation_deterministic original.sound whole
  cases same
  subst stores
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace,
    CallableIndexedOwnedAdmittedStagedTerminalBody.body_result _ _, resultRep,
    finalHeaps, maps, worlds, frame, metadata, reached, related, post⟩
end Bounds
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping
/-! Original full body typing is threaded through every accepted semicolon
 discard prefix. Discards retain the same raw context and tail completeness;
 the actual terminal selects the declared raw result. Statement metadata is
 transported literally, and no expression type is transported through a view.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping
open Core Frontend SourceInference
open CallableIndexedOwnedPreparedStagedDiscardSequenceCompilerReceipts (FlowReceipt)

private theorem statement_shape {source : TypedSource} {id : StatementId}
    {node : StatementNode} {form : StatementForm}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (same : node.form = form) :
    ∀ {other}, ContainsStatement source id other → other.form = form := by
  intro other present
  have nodeEq : other = node := Option.some.inj
    ((lookupStatement?_complete unique present).symm.trans (lookupStatement?_complete unique contains))
  cases nodeEq
  exact same

private theorem discard_typed {source : TypedSource} {control : ControlContext}
    {context final : SourceSemantics.Context} {id : StatementId} {facts : StatementFacts}
    {node : StatementNode} {expression : ExpressionId}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true)
    (typed : StatementHasType source control context id final facts) :
    ∃ type, final = context ∧
      facts = { type := .unit, hasValue := false, sawReturn := false, control := .ordinary .unit } ∧
      ExpressionHasType source context expression type := by
  have shape := @statement_shape _ _ _ _ unique contains form
  clear contains form
  cases typed <;> have actualForm := shape (by assumption) <;> simp_all
  exact ⟨_, by assumption⟩

/-- The actual typing cons supplies the tail at the same original context.
No target result equality or tail typing is assumed separately. -/
theorem discard_tail_typed {source : TypedSource}
    {context final : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    {node : StatementNode} {expression : ExpressionId} {expected : TypeSystem.Ty}
    {facts : BodyFacts}
    (unique : NodeOccurrencesUnique source) (contains : ContainsStatement source id node)
    (form : node.form = .expression expression true) (nonempty : rest ≠ [])
    (typed : StatementsHaveType source { returnType := expected } context (id :: rest) final facts)
    (completes : BodyCompletes expected facts) :
    ∃ firstType tailFacts,
      ExpressionHasType source context expression firstType ∧
      StatementsHaveType source { returnType := expected } context rest final tailFacts ∧
      BodyCompletes expected tailFacts := by
  cases typed with
  | singleton first => exact False.elim (nonempty rfl)
  | @cons _ _ _ _ _ _ _ _ tailFacts first remaining =>
    obtain ⟨firstType, rfl, rfl, firstTyped⟩ := discard_typed unique contains form first
    have tailCompletes : BodyCompletes expected tailFacts := by
      simpa [BodyFacts.cons] using completes
    exact ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩

/-- Every recursive tail has a reached terminal statement, so it is nonempty. -/
theorem nonempty {policy : SourceCoreLoops.Policy} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy source scope result reasonAt fellThrough escaped fuel statements flow) :
    statements ≠ [] := by
  cases receipt with
  | terminal terminal generated => cases terminal.terminal <;> simp
  | discard found form first generated tail accepted => simp

private theorem reaches_mono {source : TypedSource} {left right : List NodeId} {id : NodeId}
    (subset : ∀ node, node ∈ left → node ∈ right)
    (reached : CallableLambdaBodyReachability.Reaches source left id) :
    CallableLambdaBodyReachability.Reaches source right id := by
  induction reached with
  | root member => exact .root (subset _ member)
  | expression parent found edge ih => exact .expression ih found edge
  | statement parent found edge ih => exact .statement ih found edge

/-- Original statement references authenticate every actual compiled child,
including ordered duplicate occurrences. This uses no expression type equality. -/
theorem children_reached {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {result : Ty}
    {reasonAt : ExpressionId → Word} {fellThrough escaped : Word}
    {fuel : Nat} {statements : List StatementId} {flow : Expr}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView source view) :
    ∀ expression child, receipt.Children expression child →
      CallableLambdaBodyReachability.Reaches source (statements.map NodeId.statement)
        (.expression expression) := by
  induction receipt with
  | terminal terminal generated =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩
    cases terminal.terminal with
    | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
    | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | discard found form first generated tail accepted ih =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
    · exact reaches_mono (by
        intro node member
        exact List.mem_cons_of_mem _ member) (ih expression child tailUsed)

/-- Every actual compiler child has its own stored original node and raw type.
The terminal result follows from complete body typing, not native projection. -/
theorem children_typed {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    {invocation : Staging.Recursive.Scope} {context final : SourceSemantics.Context}
    {expected : TypeSystem.Ty} {facts : BodyFacts}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (unique : NodeOccurrencesUnique invocation.source)
    (typed : StatementsHaveType invocation.source { returnType := expected }
      context statements final facts)
    (completes : BodyCompletes expected facts) :
    ∀ expression child, receipt.Children expression child →
      ∃ node, invocation.source.lookupExpression? expression = some node ∧
        ExpressionHasType invocation.source context expression node.type := by
  induction receipt generalizing final facts with
  | terminal terminal generated =>
    intro expression child used
    rcases used with ⟨rfl, rfl⟩
    obtain ⟨node, found, sameType, childTyped⟩ :=
      CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique
        (CallableIndexedOwnedPreparedStagedTerminalMetadataBodyBounds.source_head terminal metadata)
        typed completes
    exact ⟨node, found, childTyped⟩
  | discard found form first generated tail accepted ih =>
    obtain ⟨firstType, tailFacts, firstTyped, remaining, tailCompletes⟩ :=
      discard_tail_typed unique (lookupStatement?_sound (metadata.statement found))
        form (nonempty tail) typed completes
    intro expression child used
    rcases used with ⟨rfl, rfl⟩ | tailUsed
    · obtain ⟨node, contains, sameType⟩ := firstTyped.stored_type
      exact ⟨node, lookupExpression?_complete unique contains, sameType ▸ firstTyped⟩
    · exact ih remaining tailCompletes expression child tailUsed

/-- The actual closure frame and parameter extension manufacture complete
original typing before selecting any of the ordered compiler children. -/
theorem at_parameters {policy : SourceCoreLoops.Policy} {view : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {result : Ty} {reasonAt : ExpressionId → Word}
    {fellThrough escaped : Word} {fuel : Nat} {statements : List StatementId} {flow : Expr}
    {program : Program} {function : Dynamic.Closure} {context : SourceSemantics.Context}
    {types : List TypeSystem.Ty} {invocation : Staging.Recursive.Scope}
    (receipt : FlowReceipt policy view scope result reasonAt fellThrough escaped fuel statements flow)
    (metadata : LambdaMetadataViews.MetadataView invocation.source view)
    (frame : Dynamic.ClosureFrame program function)
    (extended : MonoBindersExtend function.source.owner function.context function.parameters types context)
    (source : invocation.source = function.source) (body : function.body = statements) :
    ∀ expression child, receipt.Children expression child →
      ∃ node, invocation.source.lookupExpression? expression = some node ∧
        ExpressionHasType invocation.source context expression node.type := by
  obtain ⟨final, facts, typed, completes⟩ :=
    CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame extended
  have unique : NodeOccurrencesUnique invocation.source := by
    rw [source]
    exact frame.code.graph.nodeOccurrencesUnique
  rw [body, ← source] at typed
  exact children_typed receipt metadata unique typed completes

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceSourceBodyTyping
end
