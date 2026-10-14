import Solcore.SourceSemantics.CoreLowering.AcceptedCompositeExpressionReceipt
import Solcore.SourceSemantics.CoreLowering.AcceptedContextualOperatorReceipt
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates

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
