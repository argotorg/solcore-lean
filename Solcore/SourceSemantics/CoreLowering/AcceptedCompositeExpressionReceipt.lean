import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionTupleCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNamedSyntaxAdmission

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


private theorem conditional_of_actual
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
    have step := conditional_of_actual (values := .initial compiled.compatible.checked) head.found (form ▸ Compound.group inner) bypass read head.accepted
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
    have step := conditional_of_actual (values := .initial compiled.compatible.checked) head.found (form ▸ Compound.conditional test yes no) bypass read head.accepted
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
