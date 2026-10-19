import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates

/-! Accepted proxy leaves retain the original raw type and exact emitted
metadata header. Extraction follows the actual compiler callback and has no
child action or execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProxyExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {inner : TypeSystem.Ty} {lowered : SourceCoreBasic.LoweredExpr}

local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "current" => context compiled.indexed named

theorem read_policy {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner) :
    root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (current).plan compiled.indexed.base.locals (current).owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [root.compilerPolicy.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Raw original metadata closes the contextual initializer and evidence branches. -/
theorem special_none {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .proxy inner)
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
    found (form ▸ .proxy inner) (.inl requirements) clean.1
    (by intro callee ids metadata impossible; rw [form] at impossible; cases impossible)
    (by intro callee ids instantiation impossible; rw [form] at impossible; cases impossible)
  rw [root.selected.special_eq, root.selected.special_body]
  simp only [same, bind, Except.bind, found, pure, Except.pure, ordinary,
    Option.filter_none, noEvidence, form]

/-- Only the selected ordinary action is unfolded. The exact proxy header
comes from the successful leaf preparation, without recovering raw metadata
from its erased nominal representation. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none) (form : head.node.form = .proxy inner) :
    CompatibleExpressionProxies.Certificate values source scope id lowered := by
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
    simp only [form, read] at accepted
    cases actualRead : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id with
    | error error => simp [actualRead] at accepted
    | ok pair =>
      rcases pair with ⟨actualNode, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read actualRead
      have same := Option.some.inj (metadata.found.symm.trans head.found)
      subst actualNode
      simp only [actualRead, form, leaf] at accepted
      unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
      have actualRead' : SourceCoreCompatibleDataExpressions.readExpression (values).checked source id =
          .ok (head.node, type) := actualRead
      simp only [actualRead', bind, Except.bind, form] at accepted
      obtain ⟨owner, header, rfl, receipt⟩ := CompatibleExpressionProxies.proxy_of_lower head.found form accepted
      exact .proxy receipt

end Solcore.SourceSemantics.CoreLowering.AcceptedProxyExpressionReceipt
