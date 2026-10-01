import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionPrimitiveSource

/-! Independent source conditional traces retain the type-error alternative
until the compatible Bool representation excludes it. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
open Core Frontend SourceInference CompatibleExpressionPrimitives

inductive ConditionalTrace (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (environment : Dynamic.Environment)
    (before : Dynamic.Heap) (condition thenId elseId : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | fault {reason after}
      (child : Dynamic.ExpressionFaults program context evidence source environment before condition reason after) :
      ConditionalTrace program context evidence source environment before condition thenId elseId (.fault reason) after
  | branch {flag middle outcome after}
      (conditionTrace : Dynamic.ExpressionEvaluates program context evidence source environment before condition (.bool flag) middle)
      (branchTrace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment middle
        (if flag then thenId else elseId) outcome after) :
      ConditionalTrace program context evidence source environment before condition thenId elseId outcome after
  | invalid {value actual after}
      (child : Dynamic.ExpressionEvaluates program context evidence source environment before condition value after)
      (invalid : ¬ Dynamic.BooleanValue value) (runtimeType : Dynamic.ValueRuntimeType value actual) :
      ConditionalTrace program context evidence source environment before condition thenId elseId (.fault (.typeMismatch .bool actual)) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {condition thenId elseId : ExpressionId}

theorem conditional_inv (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ConditionalTrace program context evidence source environment before condition thenId elseId outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalTrue _ first second => exact .branch first (.value second)
    | conditionalFalse _ first second => exact .branch first (.value second)
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | conditionalCondition _ child => exact .fault child
    | conditionalTrueBranch _ first second => exact .branch first (.fault second)
    | conditionalFalseBranch _ first second => exact .branch first (.fault second)
    | conditionalType _ child invalid runtimeType => exact .invalid child invalid runtimeType

theorem conditional_intro (metadata : Metadata checked source id node type)
    (form : node.form = .conditional condition thenId elseId)
    (trace : ConditionalTrace program context evidence source environment before condition thenId elseId outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | fault child =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .conditionalCondition rfl child
  | @branch flag middle outcome after conditionTrace branchTrace =>
    cases flag
    all_goals cases branchTrace with
      | value branch =>
        apply Dynamic.ExpressionEvaluatesOutcome.value
        apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
        · rw [form, metadata.requirements, metadata.coercions]
          first | exact .conditionalTrue rfl conditionTrace branch | exact .conditionalFalse rfl conditionTrace branch
        · rw [metadata.coercions]; exact .nil
      | fault branch =>
        apply Dynamic.ExpressionEvaluatesOutcome.fault
        apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
        rw [form, metadata.requirements, metadata.coercions]
        first | exact .conditionalTrueBranch rfl conditionTrace branch | exact .conditionalFalseBranch rfl conditionTrace branch
  | invalid child invalid runtimeType =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .conditionalType rfl child invalid runtimeType

theorem conditional_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .conditional condition thenId elseId) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ conditionNode thenNode elseNode,
      source.lookupExpression? condition = some conditionNode ∧ source.lookupExpression? thenId = some thenNode ∧
      source.lookupExpression? elseId = some elseNode ∧ conditionNode.type = .bool ∧
      thenNode.type = node.type ∧ elseNode.type = node.type ∧
      ExpressionHasType source context condition conditionNode.type ∧
      ExpressionHasType source context thenId thenNode.type ∧ ExpressionHasType source context elseId elseNode.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | conditional conditionTyped thenTyped elseTyped =>
      obtain ⟨conditionNode, conditionContains, conditionType⟩ := conditionTyped.stored_type
      obtain ⟨thenNode, thenContains, thenType⟩ := thenTyped.stored_type
      obtain ⟨elseNode, elseContains, elseType⟩ := elseTyped.stored_type
      exact ⟨conditionNode, thenNode, elseNode, lookupExpression?_complete unique conditionContains,
        lookupExpression?_complete unique thenContains, lookupExpression?_complete unique elseContains,
        conditionType, thenType, elseType,
        conditionType ▸ conditionTyped, thenType ▸ thenTyped, elseType ▸ elseTyped⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionals
