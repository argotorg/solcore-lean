import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.NamedCollectors
import Solcore.SourceSemantics.CoreLowering.Internal.Accepted.NamedBodies
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProxyCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexExtraction
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorExtraction

/-!
# Accepted expression receipts

Receipts of accepted proxy, composite, ordinary, indirect, index and constructor expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedProxyExpressionReceipt
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedCompositeExpressionReceipt
/-! Composite receipts retain the actual compiler actions in source order.
Grouping keeps its exact child output; products retain the real packer and
conditionals retain both accepted branches and the Boolean condition check. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedCompositeExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)

inductive Form : ExpressionForm → Prop where
  | group (inner : ExpressionId) : Form (.group inner)
  | tuple (first : ExpressionId) (rest : List ExpressionId) : Form (.tuple (first :: rest))
  | conditional (test yes no : ExpressionId) : Form (.conditional test yes no)

def operands : ExpressionForm → List ExpressionId
  | .group inner => [inner]
  | .tuple ids => ids
  | .conditional test yes no => [test, yes, no]
  | _ => []

def Output (form : ExpressionForm) (codes : List SourceCoreBasic.LoweredExpr)
    (lowered : SourceCoreBasic.LoweredExpr) : Prop :=
  match form, codes with
  | .group _, [child] => lowered = child
  | .tuple _, _ => lowered = SourceCoreCalls.packArguments codes
  | .conditional _ _ _, [test, yes, no] =>
      test.type = .bool ∧ yes.type = no.type ∧
      lowered = ⟨yes.type, LocalControl.choose yes.type test.expression yes.expression no.expression⟩
  | _, _ => False

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

local notation "current" => context compiled.indexed named

structure Receipt (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : Type where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : Form node.form
  codes : List SourceCoreBasic.LoweredExpr
  generated : (operands node.form).mapM (fun child =>
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      fuel current source scope child reasonAt) = .ok codes
  output : Output node.form codes lowered

/-- These forms read the original source without local-reference normalization. -/
theorem read_policy {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : Form node.form) :
    root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (current).plan compiled.indexed.base.locals (current).owner none source id = .ok source := by
    generalize eq : node.form = actual at form
    cases form <;> simp [SourceCoreGeneralFunctions.contextualSource, found, eq]
  rw [root.compilerPolicy.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Original finite metadata excludes contextual initializers and evidence hooks. -/
theorem special_none {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : Form node.form)
    (clean : CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest compiled.indexed named node)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) :
    (match root.selected.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current child budget source scope id reasonAt) = .ok none := by
  generalize eq : node.form = actual at form
  cases form
  all_goals
    have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
        (current).plan compiled.indexed.base.locals (current).owner none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, eq]
    have requirements : node.requirements = [] := by simpa only [eq] using clean.2.2.1
    have ordinary := clean.2.1
    rw [(lookupExpression?_sound found).2] at ordinary
    have noEvidence := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.evidence_none
      compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found (by rw [eq]; first | exact .group _ | exact .tuple _ | exact .conditional _ _ _) (.inl requirements) clean.1
      (by intro callee ids metadata impossible; rw [eq] at impossible; cases impossible)
      (by intro callee ids instantiation impossible; rw [eq] at impossible; cases impossible)
    rw [root.selected.special_eq, root.selected.special_body]
    simp only [same, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, eq]

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensure_type {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  by_cases same : expected = actual
  · exact same
  · simp [SourceCoreBasic.ensureType, same] at accepted

open CompatibleExpressionPrimitives
open CompatibleExpressionConditionals

private theorem tuple_leaf_receipt {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {id : ExpressionId}
    {node : ExpressionNode} {type : Ty} {ids : List ExpressionId} {fuel : Nat}
    {reasonAt : ExpressionId → Word} {child : SourceCoreFunctions.ExpressionLowerer}
    {lowered : SourceCoreBasic.LoweredExpr}
    (read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id = .ok (node, type))
    (form : node.form = .tuple ids)
    (accepted : SourceCoreCompatibleDataExpressions.leafLowerer values child fuel source scope id reasonAt = .ok lowered) :
    ∃ codes, ids.mapM (fun element => child fuel source scope element reasonAt) = .ok codes ∧
      lowered = SourceCoreCalls.packArguments codes ∧
      Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type := by
  unfold SourceCoreCompatibleDataExpressions.leafLowerer at accepted
  simp only [read, form, bind, Except.bind, pure, Except.pure] at accepted
  obtain ⟨codes, children, accepted⟩ := bind_ok accepted
  obtain ⟨output, checked, accepted⟩ := bind_ok accepted
  cases output
  have same := ensure_type checked
  subst type
  cases accepted
  exact ⟨codes, children, rfl, CompatibleExpressionReads.metadata_of_read read⟩

/-- Every tuple arity uses the actual production mapM, including the separate
binary branch. The returned vector is source ordered and keeps repeated IDs. -/
private theorem tuple_of_actual {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreBasic.Scope} {id : ExpressionId} {node : ExpressionNode}
    {ids : List ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (form : node.form = .tuple ids)
    (special : specialAction policy body fuel compilation source scope id reasonAt = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (leaf : policy.leafLowerer = SourceCoreCompatibleDataExpressions.leafLowerer values)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) compilation source scope id reasonAt = .ok lowered) :
    ∃ codes, ids.mapM (fun element => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel compilation source scope element reasonAt) = .ok codes ∧
      lowered = SourceCoreCalls.packArguments codes ∧
      Metadata values.checked source id node (SourceCoreCalls.packArguments codes).type := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special
    cases hook : policy.lowerSpecial? <;> simp only [specialAction, CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child, hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error => simp [readPolicy, read, form] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [readPolicy, read, form] at accepted
        cases ids with
        | nil =>
          simp only [leaf] at accepted
          simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using tuple_leaf_receipt read form accepted
        | cons first rest =>
          cases rest with
          | nil =>
            simp only [leaf] at accepted
            simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using tuple_leaf_receipt read form accepted
          | cons second rest =>
            cases rest with
            | cons next rest =>
              simp only [leaf] at accepted
              simpa only [Nat.min_eq_right (Nat.le_succ fuel)] using tuple_leaf_receipt read form accepted
            | nil =>
              obtain ⟨firstCode, firstAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨secondCode, secondAccepted, accepted⟩ := bind_ok accepted
              obtain ⟨output, checked, accepted⟩ := bind_ok accepted
              cases output
              have same := ensure_type checked
              subst type
              cases accepted
              refine ⟨[firstCode, secondCode], ?_, rfl, metadata⟩
              simp only [List.mapM_cons, List.mapM_nil, firstAccepted, secondAccepted, bind, Except.bind, pure, Except.pure]
  · simp [owner, bind, Except.bind] at accepted


theorem ordinary_step_of_actual
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {context : SourceCoreFunctions.Context} {values : SourceCoreCompatibleValues.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (found : source.lookupExpression? id = some node) (compound : Compound node.form)
    (special : specialAction policy body fuel context source scope id reasonAt = .ok none)
    (readPolicy : policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1) context source scope id reasonAt = .ok lowered) :
    Step policy body fuel context values source scope reasonAt id node lowered := by
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found,
      bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special
    cases hook : policy.lowerSpecial? <;> simp only [specialAction, CallableIndexedOwnedPreparedStagedDirectCallCertificates.Child, hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      generalize form : node.form = shape at compound
      cases compound <;> simp only [form, readPolicy, bind, Except.bind, pure, Except.pure] at accepted
    all_goals
      cases read : SourceCoreCompatibleDataExpressions.readExpression values.checked source id with
      | error error => simp [read] at accepted
      | ok pair =>
        obtain ⟨other, type⟩ := pair
        have metadata := CompatibleExpressionReads.metadata_of_read read
        have same := Option.some.inj (metadata.found.symm.trans found)
        subst other
        simp only [read, form] at accepted
        first
        | obtain ⟨child, generated, afterChild⟩ := bind_ok accepted
          obtain ⟨output, operandChecked, afterOperand⟩ := bind_ok afterChild
          cases output
          obtain ⟨output, resultChecked, outputEq⟩ := bind_ok afterOperand
          cases output
          have operandType := ensure_type operandChecked
          have resultType := ensure_type resultChecked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .unary form metadata generated operandType
        | obtain ⟨first, generated, afterFirst⟩ := bind_ok accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_ok afterFirst
          split at afterSecond <;>
            obtain ⟨output, firstChecked, afterChecked⟩ := bind_ok afterSecond <;> cases output <;>
            obtain ⟨output, secondChecked, afterSecondChecked⟩ := bind_ok afterChecked <;> cases output <;>
            obtain ⟨output, resultChecked, outputEq⟩ := bind_ok afterSecondChecked <;> cases output
          all_goals
            rename_i branch
            have firstType := ensure_type firstChecked
            have secondType := ensure_type secondChecked
            have resultType := ensure_type resultChecked
            subst type
            simp only [pure, Except.pure, Except.ok.injEq] at outputEq
            subst lowered
            simpa only [selectedMode, branch, ↓reduceIte, Mode.binary, Mode.resultType] using (Step.binary form (by simpa only [selectedMode, branch, ↓reduceIte, Mode.resultType] using metadata)
              generated secondGenerated (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using firstType)
              (by simpa only [selectedMode, branch, ↓reduceIte, Mode.operandType] using secondType))
        | obtain ⟨child, generated, afterChild⟩ := bind_ok accepted
          obtain ⟨output, checked, outputEq⟩ := bind_ok afterChild
          cases output
          have same := ensure_type checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .group form metadata generated
        | obtain ⟨first, generated, afterFirst⟩ := bind_ok accepted
          obtain ⟨second, secondGenerated, afterSecond⟩ := bind_ok afterFirst
          obtain ⟨output, checked, outputEq⟩ := bind_ok afterSecond
          cases output
          have same := ensure_type checked
          subst type
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .pair form metadata generated secondGenerated
        | obtain ⟨condition, conditionGenerated, afterCondition⟩ := bind_ok accepted
          obtain ⟨output, conditionChecked, afterChecked⟩ := bind_ok afterCondition
          cases output
          obtain ⟨thenCode, thenGenerated, afterThen⟩ := bind_ok afterChecked
          obtain ⟨elseCode, elseGenerated, afterElse⟩ := bind_ok afterThen
          obtain ⟨output, thenChecked, afterThenChecked⟩ := bind_ok afterElse
          cases output
          obtain ⟨output, elseChecked, outputEq⟩ := bind_ok afterThenChecked
          cases output
          have conditionType := ensure_type conditionChecked
          have thenType := ensure_type thenChecked
          have elseType := ensure_type elseChecked
          rcases condition with ⟨conditionType', conditionExpr⟩
          rcases thenCode with ⟨thenType', thenExpr⟩
          rcases elseCode with ⟨elseType', elseExpr⟩
          dsimp only at conditionType thenType elseType
          subst conditionType' thenType' elseType'
          simp only [pure, Except.pure, Except.ok.injEq] at outputEq
          subst lowered
          exact .conditional form metadata conditionGenerated thenGenerated elseGenerated
  · simp [owner, bind, Except.bind] at accepted

/-- The original head supplies every action; no child grammar is a premise. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none) (shape : Form head.node.form) :
    Nonempty (Receipt root source scope reasonAt fuel id lowered) := by
  have bypass := head.selected
  rw [plain] at bypass
  have read := read_policy root head.found shape
  generalize form : head.node.form = actual at shape
  cases shape with
  | tuple first rest =>
    obtain ⟨codes, generated, output, _metadata⟩ := tuple_of_actual head.found form bypass read
      root.compilerPolicy.leafLowerer head.accepted
    exact ⟨⟨head.node, head.found, form ▸ .tuple first rest, codes,
      by simpa only [form, operands] using generated,
      by simpa only [form, Output] using output⟩⟩
  | group inner =>
    have step := ordinary_step_of_actual (values := .initial compiled.compatible.checked) head.found (form ▸ Compound.group inner) bypass read head.accepted
    cases step with
    | group actual metadata generated =>
      have same := ExpressionForm.group.inj (form.symm.trans actual)
      subst same
      refine ⟨⟨head.node, head.found, form ▸ .group inner, [lowered], ?_, ?_⟩⟩
      · simp only [form, operands, List.mapM_cons, List.mapM_nil, generated, bind, Except.bind, pure, Except.pure]
      · simp only [form, Output]
    | unary actual _ _ _ | binary actual _ _ _ _ _ | pair actual _ _ _ | conditional actual _ _ _ _ =>
      simp only [form] at actual
      cases actual
  | conditional test yes no =>
    have step := ordinary_step_of_actual (values := .initial compiled.compatible.checked) head.found (form ▸ Compound.conditional test yes no) bypass read head.accepted
    cases step with
    | @conditional _ _ _ testCode yesCode noCode type actual metadata testAccepted yesAccepted noAccepted =>
      have same := ExpressionForm.conditional.inj (form.symm.trans actual)
      rcases same with ⟨rfl, rfl, rfl⟩
      refine ⟨⟨head.node, head.found, form ▸ .conditional test yes no,
        [⟨.bool, testCode⟩, ⟨type, yesCode⟩, ⟨type, noCode⟩], ?_, ?_⟩⟩
      · simp only [form, operands, List.mapM_cons, List.mapM_nil, testAccepted, yesAccepted, noAccepted, bind, Except.bind, pure, Except.pure]
      · simp only [form, Output, and_self]
    | unary actual _ _ _ | binary actual _ _ _ _ _ | group actual _ _ | pair actual _ _ _ =>
      simp only [form] at actual
      cases actual

end Solcore.SourceSemantics.CoreLowering.AcceptedCompositeExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedOrdinaryExpressionReceipt
/-! Ordinary compiler receipts keep the authentic primitive checks and builtin
inventory, descriptor, complete ordered argument actions and emitted code. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedOrdinaryExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)
abbrev OperatorForm := AcceptedContextualOperatorReceipt.Form

def BuiltinForm (form : ExpressionForm) : Prop :=
  ∃ callee ids function, form = .call callee ids (.builtinFunction function)

def operands : ExpressionForm → List ExpressionId
  | .unary _ operand => [operand]
  | .binary left _ right => [left, right]
  | .call _ ids (.builtinFunction _) => ids
  | _ => []

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

local notation "current" => context compiled.indexed named

structure OperatorReceipt (source : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) (fuel : Nat) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : Type where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : OperatorForm node.form
  codes : List SourceCoreBasic.LoweredExpr
  generated : (operands node.form).mapM (fun child =>
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      fuel current source scope child reasonAt) = .ok codes
  compiled : CompatibleExpressionConditionals.Step root.selected.policy root.selected.lowerBody
    fuel current (.initial compiled.compatible.checked) source scope reasonAt id node lowered

theorem read_policy {node : ExpressionNode}
    (found : source.lookupExpression? id = some node)
    (form : OperatorForm node.form ∨ BuiltinForm node.form) :
    root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
      (current).plan compiled.indexed.base.locals (current).owner none source id = .ok source := by
    rcases form with (⟨operator, operand, eq⟩ | ⟨operator, left, right, eq⟩) | ⟨callee, ids, function, eq⟩
    all_goals simp [SourceCoreGeneralFunctions.contextualSource, found, eq]
  rw [root.compilerPolicy.readExpression]
  simp only [same, bind, Except.bind]
  rfl

theorem operator_of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none) (shape : OperatorForm head.node.form) :
    Nonempty (OperatorReceipt root source scope reasonAt fuel id lowered) := by
  have bypass := head.selected
  rw [plain] at bypass
  have read := read_policy root head.found (.inl shape)
  have compound : CompatibleExpressionConditionals.Compound head.node.form := by
    rcases shape with ⟨operator, operand, form⟩ | ⟨operator, left, right, form⟩
    · exact form ▸ .unary operator operand
    · exact form ▸ .binary operator left right
  have step := AcceptedCompositeExpressionReceipt.ordinary_step_of_actual
    (values := .initial compiled.compatible.checked) head.found compound bypass read head.accepted
  have retained := step
  cases step with
  | @unary operator operand child form metadata generated operandType =>
    refine ⟨⟨head.node, head.found, .inl ⟨operator, operand, form⟩, [child], ?_, retained⟩⟩
    simp only [form, operands, List.mapM_cons, List.mapM_nil, generated, bind, Except.bind, pure, Except.pure]
  | @binary operator left right first second form metadata generated secondGenerated leftType rightType =>
    refine ⟨⟨head.node, head.found, .inr ⟨operator, left, right, form⟩, [first, second], ?_, retained⟩⟩
    simp only [form, operands, List.mapM_cons, List.mapM_nil, generated, secondGenerated, bind, Except.bind, pure, Except.pure]
  | group form _ _ | pair form _ _ _ | conditional form _ _ _ _ =>
    rcases shape with ⟨operator, operand, original⟩ | ⟨operator, left, right, original⟩
    all_goals simp [original] at form

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem descriptor_exists
    {native : SourceCoreGeneralFunctions.CallableContext} {active : TypeSystem.Substitution}
    {compilation : SourceCoreFunctions.Context} {source : TypedSource} {node : ExpressionNode}
    {callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {type : Ty} {calleeCode arguments expression : Expr}
    (form : node.form = .call callee ids (.builtinFunction function))
    (emitted : (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      compilation source node type calleeCode arguments = .ok expression) :
    Nonempty (SourceCoreCallableContracts.Descriptor native.table (.builtin function)) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form] at emitted
  cases selected : SourceCoreCallableContracts.descriptor native.table (.builtin function) with
  | error failure => simp [selected, Except.mapError, bind, Except.bind] at emitted
  | ok descriptor => exact ⟨descriptor⟩

/-- Authentic lowering determines the literal contracted builtin wrapper.
The source reader and callable policy are static equations from the producer. -/
private theorem builtin_of_actual
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (special : specialAction policy body fuel compilation source scope id reasonAt = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt policy body fuel compilation values source scope id callee ids function reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special
    cases hook : policy.lowerSpecial? <;> simp only [specialAction, hook] at accepted bypass
    all_goals try rw [bypass] at accepted
    all_goals
      simp only [form] at accepted
      obtain ⟨pair, read, _remaining⟩ := bind_ok accepted
      rcases pair with ⟨other, type⟩
      have metadata := CompatibleExpressionReads.metadata_of_read (readPolicy.symm ▸ read)
      have same := Option.some.inj (metadata.found.symm.trans found)
      subst other
      obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, validated,
        calleeRead, reference, generated, parameter, result, emitted, rfl⟩ :=
        BuiltinCalls.call_of_accepted owner found read form special original
      obtain ⟨descriptor⟩ := descriptor_exists form (callables ▸ emitted)
      cases reference with
      | @intro index identity calleeExpression _ calleeSourceType inventory identitySelected decorated =>
        rw [callables, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
          (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
        cases decorated
        rw [callables, BuiltinCalls.Typed.builtin_call native active compilation source node callee ids function
          type _ _ descriptor form] at emitted
        cases emitted
        subst type
        exact ⟨{
          node := node
          metadata := metadata
          form := form
          accepted := original
          validated := validated
          native := native
          active := active
          callables := callables
          descriptor := descriptor
          index := index
          identity := identity
          inventory := inventory
          identitySelected := identitySelected
          calleeNode := calleeNode
          calleeReadType := calleeType
          calleeRead := calleeRead
          calleeType := calleeSourceType
          codes := codes
          generated := generated
          parameter := parameter
          result := rfl
          emitted := rfl }⟩
  · simp [owner, bind, Except.bind] at accepted

theorem builtin_of_head
    {callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    (head : Head root.selected.policy root.selected.lowerBody fuel current source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee ids (.builtinFunction function)) :
    Nonempty (CallableIndexedOwnedPreparedStagedBuiltinCallCertificates.Receipt root.selected.policy
      root.selected.lowerBody fuel current (.initial compiled.compatible.checked)
      source scope id callee ids function reasonAt lowered) := by
  exact builtin_of_actual compiled.indexed.ancestry.graph.inputs.callable [] root.callables
    head.found form (head.selected.trans (congrArg Except.ok plain))
    (read_policy root head.found (.inr ⟨callee, ids, function, form⟩)) head.accepted

theorem builtin_special_none {node : ExpressionNode}
    (found : source.lookupExpression? id = some node) (form : BuiltinForm node.form)
    (clean : CallableIndexedOwnedPreparedNamedSyntaxAdmission.MetadataTest compiled.indexed named node)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) :
    (match root.selected.policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current child budget source scope id reasonAt) = .ok none := by
  obtain ⟨callee, ids, function, eq⟩ := form
  all_goals
    have same : SourceCoreGeneralFunctions.contextualSource compiled.indexed.base.sourceProgram
        (current).plan compiled.indexed.base.locals (current).owner none source id = .ok source := by
      simp [SourceCoreGeneralFunctions.contextualSource, found, eq]
    have requirements : node.requirements = [] := by simpa only [eq] using clean.2.2.1
    have ordinary := clean.2.1
    rw [(lookupExpression?_sound found).2] at ordinary
    have noEvidence := CallableIndexedOwnedPreparedStagedGeneralCallerPolicyProfiles.evidence_none
      compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []).expressions.projectType
      named.specialized current child budget scope reasonAt
      (SourceCoreGeneralFunctions.callablePolicy compiled.indexed.base.callableContext [])
      found (by rw [eq]; exact .builtin _ _ _) (.inl requirements) clean.1
      (by intro callee ids metadata impossible; rw [eq] at impossible; cases impossible)
      (by intro callee ids instantiation impossible; rw [eq] at impossible; cases impossible)
    rw [root.selected.special_eq, root.selected.special_body]
    simp only [same, bind, Except.bind, found, pure, Except.pure, ordinary,
      Option.filter_none, noEvidence, eq]

end Solcore.SourceSemantics.CoreLowering.AcceptedOrdinaryExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
/-! Ordinary indirect acceptance retains the actual callee and ordered argument
actions. Compatible reads and the original successful guard recover metadata;
the same contextual callback supplies genuine initializer exclusion. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open AcceptedNamedExpressionFlow (Head specialAction)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id callee : ExpressionId} {arguments : List ExpressionId}
  {metadata : IndirectCallResolution} {lowered : SourceCoreBasic.LoweredExpr}

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem initializer_none
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none := by
  have accepted := head.selected
  rw [plain] at accepted
  unfold specialAction at accepted
  rw [root.compilerPolicy.lowerSpecial] at accepted
  have sameSource := CallableIndexedOwnedIndirectCompilerPolicyInputs.contextualSource_indirect
    compiled.indexed.base.sourceProgram (context compiled.indexed named).plan
    compiled.indexed.base.locals (context compiled.indexed named).owner none head.found form
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special at accepted
  simp only [sameSource, bind, Except.bind, head.found, pure, Except.pure] at accepted
  cases selected : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) with
  | none => rfl
  | some binding =>
    simp only [selected, Option.filter_some, ne_eq, reduceCtorEq, not_false_eq_true, decide_true,
      ↓reduceIte] at accepted
    obtain ⟨actual, _binding, accepted⟩ := bind_ok accepted
    obtain ⟨result, _initializer, accepted⟩ := bind_ok accepted
    cases accepted

private theorem ordinary_metadata
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    ∃ type, root.selected.policy.readExpression source id = .ok (head.node, type) ∧
      CompatibleExpressionReads.Metadata compiled.compatible.checked source id head.node type ∧
      metadata.argumentCoercions = [] := by
  have sameSource := CallableIndexedOwnedIndirectCompilerPolicyInputs.contextualSource_indirect
    compiled.indexed.base.sourceProgram (context compiled.indexed named).plan
    compiled.indexed.base.locals (context compiled.indexed named).owner none head.found form
  have readPolicy : root.selected.policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked source id := by
    rw [root.compilerPolicy.readExpression]
    simp only [sameSource, bind, Except.bind]
    rfl
  have accepted := head.accepted
  have selected := head.selected
  rw [plain] at selected
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  simp only [head.owner, ne_eq, not_true_eq_false, ↓reduceIte, head.found,
    bind, Except.bind, pure, Except.pure] at accepted
  cases hook : root.selected.policy.lowerSpecial? <;>
    simp only [specialAction, hook] at selected accepted
  all_goals try rw [selected] at accepted
  all_goals
    simp only [form] at accepted
    obtain ⟨pair, read, accepted⟩ := bind_ok accepted
    obtain ⟨node, type⟩ := pair
    have actual := CompatibleExpressionReads.metadata_of_read (readPolicy ▸ read)
    have same := Option.some.inj (actual.found.symm.trans head.found)
    subst node
    simp only [form] at accepted
    by_cases empty : metadata.argumentCoercions.isEmpty = true
    · exact ⟨type, read, actual, List.isEmpty_iff.mp empty⟩
    · simp [empty] at accepted

/-- No grammar or universal hook premise is required. Both delegation fields
of the existing receipt are derived from this actual ordinary compiler action. -/
theorem of_head
    (head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered)
    (plain : head.special = none)
    (form : head.node.form = .call callee arguments (.indirect metadata)) :
    Nonempty (CallableIndirectCallCertificates.Receipt root.selected.policy root.selected.lowerBody
      fuel (context compiled.indexed named) source scope id callee arguments metadata reasonAt lowered) := by
  have ordinary := initializer_none root head plain form
  obtain ⟨type, read, actual, noArgumentCoercions⟩ := ordinary_metadata root head plain form
  have profile := CallableIndexedOwnedContextualCompilerPolicyProfiles.indirect_policy root
    (scope := scope) (reasonAt := reasonAt)
    head.found form actual.requirements actual.coercions noArgumentCoercions ordinary
  exact CallableIndirectCallCertificates.of_functions head.found form profile.special read form head.accepted

end Solcore.SourceSemantics.CoreLowering.AcceptedIndirectExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedIndexExpressionReceipt
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
    source.lookupExpression? key = some keyNode

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
    (keyFound : source.lookupExpression? key = some keyNode) :
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
      exact ⟨⟨head.node, baseNode, keyNode, head.found, form, baseFound, keyFound,
        layout, comparison, first, second, output, header,
        by simpa only [Nat.min_self] using firstAccepted,
        by simpa only [Nat.min_self] using secondAccepted⟩⟩

end Solcore.SourceSemantics.CoreLowering.AcceptedIndexExpressionReceipt
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.AcceptedConstructorExpressionReceipt
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
end
