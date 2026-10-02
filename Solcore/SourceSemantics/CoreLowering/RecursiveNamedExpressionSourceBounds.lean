import Solcore.SourceSemantics.CoreLowering.RecursiveNamedBoundedContracts
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts

/-! Original source children for ordinary composition heads. Each size refers
 to the retained source derivation. Native branch bounds are extracted from
 their original completion, independently of the source cost. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives RecursiveNamedCallBounds

private theorem node_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem evaluation_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (evaluation : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before id value after) :
    ∃ child, SourceExecutionSize.ExpressionFormEvaluates program child context evidence source environment before
      node.form node.requirements node.coercions value after ∧ child < size := by
  cases evaluation with
  | intro found raw coercions =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact ⟨_, raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

theorem fault_raw_sized
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault} {size : Nat}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (fault : SourceExecutionSize.ExpressionFaults program size context evidence source environment before id reason after) :
    ∃ child, SourceExecutionSize.ExpressionFormFaults program child context evidence source environment before
      node.form node.requirements node.coercions reason after ∧ child < size := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw =>
    exact ⟨_, node_unique unique found contains ▸ raw, SourceExecutionSize.child_lt_stepSize (by simp)⟩
  | coercion found _ failed =>
    have same := node_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := node_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

theorem group_inv (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child, ExpressionOutcome program child context evidence source environment before inner outcome after ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with
    | group _ child => exact ⟨_, .value child, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with
    | group _ child => exact ⟨_, .fault child, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩

theorem pair_inv (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child sequence, ProtectedDataExpressionSequence.TraceAt program child context evidence source environment before
      [left, right] sequence after ∧ CompatibleExpressionProducts.PacksOutcome sequence outcome ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with
    | tuple _ children pack => exact ⟨_, _, .values children, .values pack,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with
    | tuple _ children => exact ⟨_, _, .fault children, .fault _,
        Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩

inductive UnaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {childSize input output after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before operand input after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output)
      (childSizeSmaller : childSize < size) : UnaryTrace program size context evidence source environment before operand operator (.value output) after
  | fault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before operand reason after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context evidence source environment before operand operator (.fault reason) after
  | invalid {childSize input reason middle after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before operand input middle)
      (fault : Dynamic.UnaryOperationFaults program context evidence middle operator [] input reason after)
      (childSizeSmaller : childSize < size) :
      UnaryTrace program size context evidence source environment before operand operator (.fault reason) after

theorem unary_inv {operator : Syntax.UnaryOp} {operand : ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    UnaryTrace program size context evidence source environment before operand operator outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unary layout child applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => refine .value child applied ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      | method _ selected _ => cases selected
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unaryOperand _ child => refine .fault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | unaryApply layout child failed =>
      have empty := no_owned layout
      subst empty
      refine .invalid child failed.sound ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive BinaryTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | leftFault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before left reason after)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after
  | leftInvalid {childSize input after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before left input after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault (.invalidBinaryOperands operator)) after
  | short {childSize input output after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before left input after)
      (circuit : Dynamic.ShortCircuits operator input output)
      (childSizeSmaller : childSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.value output) after
  | rightFault {firstSize secondSize input reason middle after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left input middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : SourceExecutionSize.ExpressionFaults program secondSize context evidence source environment middle right reason after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after
  | value {firstSize secondSize a b output middle after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : SourceExecutionSize.ExpressionEvaluates program secondSize context evidence source environment middle right b after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.value output) after
  | invalid {firstSize secondSize a b reason middle operated after}
      (first : SourceExecutionSize.ExpressionEvaluates program firstSize context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : SourceExecutionSize.ExpressionEvaluates program secondSize context evidence source environment middle right b operated)
      (failed : Dynamic.BinaryOperationFaults program context evidence operated operator [] a b reason after)
      (firstSizeSmaller : firstSize < size)
      (secondSizeSmaller : secondSize < size) :
      BinaryTrace program size context evidence source environment before left right operator (.fault reason) after

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    BinaryTrace program size context evidence source environment before left right operator outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryShortCircuit _ child circuit _ => refine .short child circuit ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryEvaluateRight layout first continues second applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => refine .value first continues second applied ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
      | method _ selected _ => cases selected
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryLeft _ child => refine .leftFault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryLeftOperand _ child invalid => refine .leftInvalid child invalid ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryRight _ first continues second => refine .rightFault first continues second ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | binaryApply layout first continues second failed =>
      have empty := no_owned layout
      subst empty
      refine .invalid first continues second failed.sound ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

inductive ConditionalTrace (program : Program) (size : Nat) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {childSize reason after}
      (child : SourceExecutionSize.ExpressionFaults program childSize context evidence source environment before condition reason after)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId (.fault reason) after
  | branch {childSize branchSize flag middle outcome after}
      (conditionTrace : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before condition (.bool flag) middle)
      (branchTrace : ExpressionOutcome program branchSize context evidence source environment middle
        (if flag then thenId else elseId) outcome after)
      (childSizeSmaller : childSize < size)
      (branchSizeSmaller : branchSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId outcome after
  | invalid {childSize value actual after}
      (child : SourceExecutionSize.ExpressionEvaluates program childSize context evidence source environment before condition value after)
      (invalid : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual)
      (childSizeSmaller : childSize < size) :
      ConditionalTrace program size context evidence source environment before condition thenId elseId (.fault (.typeMismatch .bool actual)) after

theorem conditional_inv {condition thenId elseId : ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ConditionalTrace program size context evidence source environment before condition thenId elseId outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalTrue _ first second => refine .branch first (.value second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalFalse _ first second => refine .branch first (.value second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalCondition _ child => refine .fault child ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalTrueBranch _ first second => refine .branch first (.fault second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalFalseBranch _ first second => refine .branch first (.fault second) ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | conditionalType _ child invalid runtimeType => refine .invalid child invalid runtimeType ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller

/-- The chosen right branch retains its original native child witness. -/
theorem right_evaluated {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {operator : Syntax.BinaryOp}
    {operand result : TypeSystem.Ty} {mode : Mode} {a : Dynamic.Value} {x : Value}
    {actual : Environment} {store finalStore : Store} {right : Expr} {value : Value}
    (profile : BinaryProfile operator operand result mode)
    (represented : ValueRep checked registry functions mapping world operand a x (mode.operandType operator))
    (continues : Dynamic.EvaluatesRightOperand operator a)
    (original : EvaluationSize size (x :: actual) store (mode.tail operator right) value finalStore) :
    ∃ child rightValue rightStore, EvaluationSize child (x :: actual) store
      (right.weakenAt 0) rightValue rightStore ∧ child < size := by
  cases profile with
  | word strict => cases strict <;> cases original <;> refine ⟨_, _, _, by assumption, ?_⟩ <;> omega
  | integer strict => cases strict <;> cases original <;> refine ⟨_, _, _, by assumption, ?_⟩ <;> omega
  | logicalAnd =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | andTrue =>
      cases original with
      | ifTrue condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
        exact ⟨_, _, _, right, by omega⟩
      | ifFalse condition right =>
        have same := (evaluation_deterministic condition.sound (Evaluates.var rfl)).1
        cases same
  | logicalOr =>
    obtain ⟨boolean, rfl, rfl⟩ := bool_fields represented
    cases continues with
    | strict strict => cases strict
    | orFalse =>
      cases original with
      | ifFalse condition right =>
        obtain ⟨_, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
        exact ⟨_, _, _, right, by omega⟩
      | ifTrue condition right =>
        have same := (evaluation_deterministic condition.sound (Evaluates.var rfl)).1
        cases same

theorem choose_branch_evaluated {actual : Environment} {store finalStore : Store}
    {flag : Bool} {thenCode elseCode : Expr} {value : Value}
    (original : EvaluationSize size (.bool flag :: actual) store
      (.ifE (.var 0) (thenCode.weakenAt 0) (elseCode.weakenAt 0)) value finalStore) :
    ∃ child, EvaluationSize child (.bool flag :: actual) store
      ((if flag then thenCode else elseCode).weakenAt 0) value finalStore ∧ child < size := by
  cases original with
  | ifTrue condition branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
    cases same
    exact ⟨_, branch, by omega⟩
  | ifFalse condition branch =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic condition.sound (Evaluates.var rfl)
    cases same
    exact ⟨_, branch, by omega⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
