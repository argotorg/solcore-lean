import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveOperations

/-! Independent source decomposition for empty-evidence primitive nodes.
Faulting operands and invalid operations are distinguished before the scalar
representation proof excludes the invalid-operation alternatives. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
open Core Frontend SourceInference
abbrev Metadata := CompatibleExpressionReads.Metadata

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

theorem evaluation_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {value : Dynamic.Value}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (evaluation : Dynamic.ExpressionEvaluates program context evidence source environment before id value after) :
    Dynamic.ExpressionFormEvaluates program context evidence source environment before node.form node.requirements node.coercions value after := by
  cases evaluation with
  | intro found raw coercions =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at coercions
    cases coercions
    exact raw
  | generalizedLocal found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

theorem fault_raw
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before after : Dynamic.Heap} {reason : Dynamic.SemanticFault}
    (unique : NodeOccurrencesUnique source) (contains : ContainsExpression source id node)
    (notLocal : ∀ name binder, node.form ≠ .reference name (.local binder)) (empty : node.coercions = [])
    (fault : Dynamic.ExpressionFaults program context evidence source environment before id reason after) :
    Dynamic.ExpressionFormFaults program context evidence source environment before node.form node.requirements node.coercions reason after := by
  cases fault with
  | missing absent => exact False.elim (Dynamic.ExpressionAbsentIn.excludes_contains absent contains)
  | form found raw => exact contains_unique unique found contains ▸ raw
  | coercion found _ failed =>
    have same := contains_unique unique found contains
    subst same
    rw [empty] at failed
    cases failed
  | generalizedLocalRequirement found form _ _ _ _ _ _ _ | generalizedLocalCoercion found form _ _ _ _ _ _ _ =>
    have same := contains_unique unique found contains
    subst same
    exact False.elim (notLocal _ _ form)

theorem no_owned {owned : List RequirementId}
    (layout : Dynamic.OrdinaryRequirementLayout [] [] owned) : owned = [] := by
  simpa [Dynamic.OrdinaryRequirementLayout, coercionRequirementIds] using layout.symm

inductive UnaryTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (operand : ExpressionId) (operator : Syntax.UnaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {input output after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before operand input after)
      (applies : Dynamic.UnaryPrimitiveApplies operator input output) : UnaryTrace program context evidence source environment before operand operator (.value output) after
  | fault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before operand reason after) :
      UnaryTrace program context evidence source environment before operand operator (.fault reason) after
  | invalid {input reason middle after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before operand input middle)
      (fault : Dynamic.UnaryOperationFaults program context evidence middle operator [] input reason after) :
      UnaryTrace program context evidence source environment before operand operator (.fault reason) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {operator : Syntax.UnaryOp} {operand : ExpressionId}

theorem unary_inv (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    UnaryTrace program context evidence source environment before operand operator outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unary layout child applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => exact .value child applied
      | method _ selected _ => cases selected
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | unaryOperand _ child => exact .fault child
    | unaryApply layout child failed =>
      have empty := no_owned layout
      subst empty
      exact .invalid child failed

theorem unary_intro (metadata : Metadata checked source id node type)
    (form : node.form = .unary operator operand)
    (trace : UnaryTrace program context evidence source environment before operand operator outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value child applied =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .unary (owned := []) rfl child (.primitive applied)
    · rw [metadata.coercions]; exact .nil
  | fault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .unaryOperand (owned := []) rfl child
  | invalid child failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .unaryApply (owned := []) rfl child failed

theorem unary_fault_excluded {input output : Dynamic.Value} {reason : Dynamic.SemanticFault}
    (applied : Dynamic.UnaryPrimitiveApplies operator input output)
    (fault : Dynamic.UnaryOperationFaults program context evidence before operator [] input reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | requirement failed => cases failed
  | method _ selected _ => cases selected


inductive BinaryTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (left right : ExpressionId) (operator : Syntax.BinaryOp) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | leftFault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before left reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after
  | leftInvalid {input after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before left input after)
      (invalid : Dynamic.BinaryLeftOperandInvalid operator input) :
      BinaryTrace program context evidence source environment before left right operator (.fault (.invalidBinaryOperands operator)) after
  | short {input output after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before left input after)
      (circuit : Dynamic.ShortCircuits operator input output) :
      BinaryTrace program context evidence source environment before left right operator (.value output) after
  | rightFault {input reason middle after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left input middle)
      (continues : Dynamic.EvaluatesRightOperand operator input)
      (second : Dynamic.ExpressionFaults program context evidence source environment middle right reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after
  | value {a b output middle after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Dynamic.ExpressionEvaluates program context evidence source environment middle right b after)
      (applies : Dynamic.BinaryPrimitiveApplies operator a b output) :
      BinaryTrace program context evidence source environment before left right operator (.value output) after
  | invalid {a b reason middle operated after}
      (first : Dynamic.ExpressionEvaluates program context evidence source environment before left a middle)
      (continues : Dynamic.EvaluatesRightOperand operator a)
      (second : Dynamic.ExpressionEvaluates program context evidence source environment middle right b operated)
      (failed : Dynamic.BinaryOperationFaults program context evidence operated operator [] a b reason after) :
      BinaryTrace program context evidence source environment before left right operator (.fault reason) after

theorem binary_inv {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type)
    (form : node.form = .binary left operator right) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    BinaryTrace program context evidence source environment before left right operator outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryShortCircuit _ child circuit _ => exact .short child circuit
    | binaryEvaluateRight layout first continues second applies =>
      have empty := no_owned layout
      subst empty
      cases applies with
      | primitive applied => exact .value first continues second applied
      | method _ selected _ => cases selected
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | binaryLeft _ child => exact .leftFault child
    | binaryLeftOperand _ child invalid => exact .leftInvalid child invalid
    | binaryRight _ first continues second => exact .rightFault first continues second
    | binaryApply layout first continues second failed =>
      have empty := no_owned layout
      subst empty
      exact .invalid first continues second failed

theorem binary_intro {operator : Syntax.BinaryOp} {left right : ExpressionId}
    (metadata : Metadata checked source id node type) (form : node.form = .binary left operator right)
    (trace : BinaryTrace program context evidence source environment before left right operator outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | short child circuit =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .binaryShortCircuit (owned := []) rfl child circuit rfl
    · rw [metadata.coercions]; exact .nil
  | value first continues second applied =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]
      exact .binaryEvaluateRight (owned := []) rfl first continues second (.primitive applied)
    · rw [metadata.coercions]; exact .nil
  | leftFault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryLeft (owned := []) rfl child
  | leftInvalid child invalid =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryLeftOperand (owned := []) rfl child invalid
  | rightFault first continues second =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryRight (owned := []) rfl first continues second
  | invalid first continues second failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .binaryApply (owned := []) rfl first continues second failed

theorem binary_fault_excluded {operator : Syntax.BinaryOp} {left right output : Dynamic.Value} {reason : Dynamic.SemanticFault}
    (applied : Dynamic.BinaryPrimitiveApplies operator left right output)
    (fault : Dynamic.BinaryOperationFaults program context evidence before operator [] left right reason after) : False := by
  cases fault with
  | primitive invalid => exact invalid.excludes_application ⟨output, applied⟩
  | requirement failed => cases failed
  | method _ selected _ => cases selected

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitives
