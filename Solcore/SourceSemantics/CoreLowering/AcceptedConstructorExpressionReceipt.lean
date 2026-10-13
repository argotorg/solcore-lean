import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorExtraction
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission

/-! Accepted constructor actions retain the original constructor metadata,
complete raw substitution range and every ordered payload action. Native
layout projection never establishes the independent raw range condition. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedConstructorExpressionReceipt
open Core Frontend SourceInference DataPatternValues
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
  {fuel : Nat} {id : ExpressionId} {instantiation : DataConstructorInstantiation}
  {ids : List ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

local notation "values" => SourceCoreCompatibleValues.Context.initial compiled.compatible.checked
local notation "current" => context compiled.indexed named
local notation "child" => (fun budget childSource childScope childId childReasonAt =>
  SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody budget
    current childSource childScope childId childReasonAt)

structure Receipt (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id : ExpressionId)
    (instantiation : DataConstructorInstantiation) (ids : List ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : Type where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .constructor instantiation ids
  range : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution
  tag : ConstructorId
  metadataId : Word
  codes : List SourceCoreBasic.LoweredExpr
  output : lowered = ⟨.namedData tag.owner, SourceCoreCompatibleDataExpressions.construct
    tag metadataId (SourceCoreCalls.packArguments codes).expression⟩
  header : CompatibleExpressionConstructors.Header values source id node instantiation tag metadataId codes
  count : ids.length = instantiation.payloadTypes.length
  arguments : ListRel (CompatibleExpressionConstructors.Argument values child fuel source scope reasonAt)
    (ids.zip instantiation.payloadTypes) codes

theorem Receipt.generated
    (receipt : Receipt root source scope reasonAt fuel id instantiation ids lowered) :
    ids.mapM (fun argument => child fuel source scope argument reasonAt) = .ok receipt.codes := by
  have count := receipt.count
  have accepted := receipt.arguments
  generalize typesEq : instantiation.payloadTypes = types at count accepted
  generalize codesEq : receipt.codes = codes at accepted ⊢
  clear typesEq codesEq receipt
  induction ids generalizing types codes with
  | nil =>
    cases types with
    | nil => cases accepted; rfl
    | cons => cases count
  | cons id ids ih =>
    cases types with
    | nil => cases count
    | cons type types =>
      cases accepted with
      | cons first rest =>
        have tail := ih types (Nat.succ.inj count) _ rest
        simp only [List.mapM_cons, first.generated, tail, bind, Except.bind, pure, Except.pure]

/-- Constructor nodes retain their original contextual reader. -/
theorem read_policy {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids) :
    root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (context compiled.indexed named).plan compiled.indexed.base.locals (context compiled.indexed named).owner
      none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [root.compilerPolicy.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Raw original metadata determines genuine initializer and evidence delegation. -/
theorem special_none {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : node.form = .constructor instantiation ids)
    (clean : CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest compiled.indexed named node)
    (recursive : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) :
    (match root.selected.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current recursive budget source scope id reasonAt) = .ok none := by
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
    named.specialized current recursive budget scope reasonAt
    (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
    found (form ▸ .constructor instantiation ids) (.inl requirements) clean.1
    (by intro callee args metadata impossible; rw [form] at impossible; cases impossible)
    (by intro callee args inst impossible; rw [form] at impossible; cases impossible)
  rw [root.selected.special_eq, root.selected.special_body]
  simp only [same, bind, Except.bind, found, pure, Except.pure, ordinary,
    Option.filter_none, noEvidence, form]

/-- Exact ordinary acceptance supplies the payload sequence; raw range is a
separate static premise over every retained replacement entry. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none) (form : head.node.form = .constructor instantiation ids)
    (range : CompatibleSourceInstantiationClosure.ClosedParameterRange instantiation.parameterSubstitution) :
    Nonempty (Receipt root source scope reasonAt fuel id instantiation ids lowered) := by
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
      obtain ⟨tag, metadataId, codes, output, header, count, arguments⟩ :=
        CompatibleExpressionConstructors.constructor_of_lower head.found form accepted
      refine ⟨⟨head.node, head.found, form, range, tag, metadataId, codes, output, header, count, ?_⟩⟩
      generalize inputsEq : ids.zip instantiation.payloadTypes = inputs at arguments ⊢
      clear output header inputsEq
      induction arguments with
      | nil => exact .nil
      | cons first rest ih =>
        exact .cons ⟨first.projected, by simpa only [Nat.min_self] using first.generated⟩ ih

end Solcore.SourceSemantics.CoreLowering.AcceptedConstructorExpressionReceipt
