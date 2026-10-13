import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission

/-! An accepted ordinary index action retains its original mapping layout,
comparator and both child actions in base-then-key order. The raw key type is
kept separately from the projected runtime layout. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedIndexExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)

def Operands (source : TypedSource) (base key : ExpressionId) : Prop :=
  ∃ baseNode keyNode, source.lookupExpression? base = some baseNode ∧
    source.lookupExpression? key = some keyNode ∧ CompatibleExpressionIndices.SourceScalar keyNode.type

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id base key : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "current" => context compiled.indexed named

structure Receipt (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id base key : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : Type where
  node : ExpressionNode
  baseNode : ExpressionNode
  keyNode : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .index base key
  baseFound : source.lookupExpression? base = some baseNode
  keyFound : source.lookupExpression? key = some keyNode
  scalar : CompatibleExpressionIndices.SourceScalar keyNode.type
  layout : Core.OrderedMapping.Layout
  comparison : SourceCoreCompatibleDataEquality.Prepared compiled.compatible.checked
  first : SourceCoreBasic.LoweredExpr
  second : SourceCoreBasic.LoweredExpr
  output : lowered = ⟨layout.valueType, SourceCoreCompatibleDataExpressions.index layout
    comparison.expression first.expression second.expression (reasonAt id)⟩
  header : CompatibleExpressionIndices.Header values source id base node baseNode layout comparison first second
  firstAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
    fuel current source scope base reasonAt = .ok first
  secondAccepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
    fuel current source scope key reasonAt = .ok second

/-- The original index form never enters local reference normalization. -/
theorem read_policy {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .index base key) :
    root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [root.compilerPolicy.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Raw original metadata closes the contextual initializer and evidence branches. -/
theorem special_none {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .index base key)
    (clean : CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest compiled.indexed named node)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) :
    (match root.selected.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current child budget source scope id reasonAt) = .ok none := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals
      (context compiled.indexed named).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  have requirements : node.requirements = [] := by simpa only [form] using clean.2.2.1
  have ordinary := clean.2.1
  rw [(lookupExpression?_sound found).2] at ordinary
  have noEvidence := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.evidence_none
    compiled.indexed.base.sourceProgram
    ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
    named.specialized current child budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
    found (form ▸ .index base key) (.inl requirements) clean.1
    (by intro callee ids metadata impossible; rw [form] at impossible; cases impossible)
    (by intro callee ids instantiation impossible; rw [form] at impossible; cases impossible)
  rw [root.selected.special_eq, root.selected.special_body]
  simp only [same, bind, Except.bind, found, pure, Except.pure, ordinary,
    Option.filter_none, noEvidence, form]

/-- Only the actual callback at the accepted step is used. No grammar, child
correctness, or universal special-handler premise is supplied. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none) (form : head.node.form = .index base key)
    {baseNode keyNode : ExpressionNode}
    (baseFound : source.lookupExpression? base = some baseNode)
    (keyFound : source.lookupExpression? key = some keyNode)
    (scalar : CompatibleExpressionIndices.SourceScalar keyNode.type) :
    Nonempty (Receipt root source scope reasonAt fuel id base key lowered) := by
  have accepted := head.accepted
  have bypass := head.selected
  rw [plain] at bypass
  have read := read_policy root head.found form
  have leaf : root.selected.policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values :=
    root.compilerPolicy.leafLowerer
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [head.owner, ne_eq, not_true_eq_false, ↓reduceIte, head.found,
    bind, Except.bind, pure, Except.pure] at accepted
  cases hook : root.selected.policy.lowerSpecial? <;>
    simp only [specialAction, hook] at accepted bypass
  all_goals try rw [bypass] at accepted
  all_goals
    simp only [form, read, bind, Except.bind, pure, Except.pure] at accepted
    cases actualRead : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id with
    | error error => simp [actualRead] at accepted
    | ok pair =>
      rcases pair with ⟨actualNode, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read actualRead
      have same := Option.some.inj (metadata.found.symm.trans head.found)
      subst actualNode
      simp only [actualRead, form, leaf] at accepted
      unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
      have actualRead' : SourceCoreCompatibleDataExpressions.readExpression (values).checked source id = .ok (head.node, type) := actualRead
      simp only [actualRead', bind, Except.bind, form] at accepted
      obtain ⟨layout, comparison, first, second, output, header, firstAccepted, secondAccepted⟩ :=
        CompatibleExpressionIndices.index_of_lower head.found baseFound form accepted
      exact ⟨⟨head.node, baseNode, keyNode, head.found, form, baseFound, keyFound, scalar,
        layout, comparison, first, second, output, header,
        by simpa only [Nat.min_self] using firstAccepted,
        by simpa only [Nat.min_self] using secondAccepted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedIndexExpressionReceipt
