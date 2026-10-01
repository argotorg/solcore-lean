import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductTree

/-! Independent source composition/inversion for empty-coercion groups and
binary tuples. Evaluation order and the faulting prefix remain explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
open Core Frontend SourceInference

private theorem contains_unique {source : TypedSource} {id : ExpressionId} {left right : ExpressionNode}
    (unique : NodeOccurrencesUnique source) (first : ContainsExpression source id left)
    (second : ContainsExpression source id right) : left = right :=
  Option.some.inj ((lookupExpression?_complete unique first).symm.trans (lookupExpression?_complete unique second))

private theorem evaluation_raw
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

private theorem fault_raw
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

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome}

theorem group_inv (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with | group _ child => exact .value child
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with | group _ child => exact .fault child

theorem group_intro (metadata : Metadata checked source id node type) {inner : ExpressionId}
    (form : node.form = .group inner)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before inner outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value evaluated =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .group rfl evaluated
    · rw [metadata.coercions]; exact .nil
  | fault failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .group rfl failed

inductive PacksOutcome : DataExpressionSequence.Outcome → Dynamic.ExpressionOutcome → Prop where
  | values {values packed} (pack : Dynamic.ValuesPack values packed) : PacksOutcome (.ok values) (.value packed)
  | fault (reason : Dynamic.SemanticFault) : PacksOutcome (.error reason) (.fault reason)

theorem PacksOutcome.functional {input left right} (first : PacksOutcome input left) (second : PacksOutcome input right) : left = right := by
  cases first with
  | values first => cases second with | values second => exact congrArg _ (first.functional second)
  | fault => cases second; rfl

theorem pair_inv (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ sequence, DataExpressionSequence.Trace program context evidence source environment before [left, right] sequence after ∧
      PacksOutcome sequence outcome := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form] at raw
    cases raw with | tuple _ children pack => exact ⟨_, .values children, .values pack⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form] at raw
    cases raw with | tuple _ children => exact ⟨_, .fault children, .fault _⟩

theorem pair_intro (metadata : Metadata checked source id node type) {left right : ExpressionId}
    (form : node.form = .tuple [left, right]) {sequence : DataExpressionSequence.Outcome}
    (trace : DataExpressionSequence.Trace program context evidence source environment before [left, right] sequence after)
    (packed : PacksOutcome sequence outcome) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases packed with
  | values pack =>
    cases trace with
    | values evaluated =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]; exact .tuple rfl evaluated pack
      · rw [metadata.coercions]; exact .nil
  | fault reason =>
    cases trace with
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .tuple rfl failed

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProducts
