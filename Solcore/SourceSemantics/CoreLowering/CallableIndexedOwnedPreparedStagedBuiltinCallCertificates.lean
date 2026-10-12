import Solcore.SourceSemantics.CoreLowering.BuiltinCallTypedCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionReadCertificates

/-! A direct builtin call keeps the actual builtin inventory entry, callable
descriptor and accepted ordered argument actions. The callable hooks are the
real retained compiler policy; no child execution or callable body law is an
input. The synthetic callee is metadata, rather than an evaluated child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates
open Core Frontend SourceInference

structure Receipt (policy : SourceCoreFunctions.Policy) (body : SourceCoreFunctions.BodyLowerer)
    (fuel : Nat) (compilation : SourceCoreFunctions.Context)
    (values : SourceCoreCompatibleValues.Context) (source : TypedSource)
    (scope : SourceCoreLocalCell.Scope) (id callee : ExpressionId)
    (ids : List ExpressionId) (function : BuiltinFunctionId)
    (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  metadata : CompatibleExpressionReads.Metadata values.checked source id node lowered.type
  form : node.form = .call callee ids (.builtinFunction function)
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
    compilation source scope id reasonAt = .ok lowered
  validated : SourceCoreElaboration.validateBuiltinFunctionCall source node callee ids function = .ok ()
  native : SourceCoreGeneralFunctions.CallableContext
  active : TypeSystem.Substitution
  callables : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active
  descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function)
  index : Nat
  identity : Word
  inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index)
  identitySelected : Word.ofNat? (compilation.globals.length + index + 1) = some identity
  calleeNode : ExpressionNode
  calleeReadType : Ty
  calleeRead : policy.readExpression source callee = .ok (calleeNode, calleeReadType)
  calleeType : calleeNode.type = function.type
  codes : List SourceCoreBasic.LoweredExpr
  generated : ids.mapM (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy body fuel
    compilation source scope child reasonAt) = .ok codes
  parameter : (SourceCoreCalls.packArguments codes).type = SourceCoreInteger.builtinParameter function
  result : lowered.type = SourceCoreInteger.builtinResult function
  emitted : lowered.expression = CallableContract.call [⟨descriptor.id, none, none⟩]
    native.diagnostics.unknown (SourceCoreInteger.builtinResult function)
    (BuiltinCalls.Protocol.contracted function identity descriptor.id)
    (SourceCoreCalls.packArguments codes).expression

/-- The complete lowered expression is the authenticated builtin wrapper. -/
theorem Receipt.output
    {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId}
    {ids : List ExpressionId} {function : BuiltinFunctionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Receipt policy body fuel compilation values source scope id callee ids function reasonAt lowered) :
    lowered = ⟨SourceCoreInteger.builtinResult function,
      CallableContract.call [⟨receipt.descriptor.id, none, none⟩] receipt.native.diagnostics.unknown
        (SourceCoreInteger.builtinResult function)
        (BuiltinCalls.Protocol.contracted function receipt.identity receipt.descriptor.id)
        (SourceCoreCalls.packArguments receipt.codes).expression⟩ := by
  cases lowered
  simp only [SourceCoreBasic.LoweredExpr.mk.injEq]
  exact ⟨receipt.result, receipt.emitted⟩

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
theorem of_functions
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
    (special : ∀ child budget, (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation child budget source scope id reasonAt) = .ok none)
    (readPolicy : policy.readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression values.checked source id)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy body (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Nonempty (Receipt policy body fuel compilation values source scope id callee ids function reasonAt lowered) := by
  have original := accepted
  rw [SourceCoreFunctions.lowerExpressionWithPolicy] at accepted
  by_cases owner : id.occurrence.owner = source.owner
  · simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, bind, Except.bind, pure, Except.pure] at accepted
    have bypass := special (fun budget childSource childScope childId childReasonAt =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy body (min budget fuel)
        compilation childSource childScope childId childReasonAt) (fuel + 1)
    cases hook : policy.lowerSpecial? <;> simp only [hook] at accepted bypass
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
        BuiltinCalls.call_of_accepted owner found read form (special _ _) original
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

/-- The independent original typing fixes every argument's raw builtin type. -/
theorem source_types {source : TypedSource} {context : SourceSemantics.Context}
    {id callee : ExpressionId} {ids : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee ids (.builtinFunction function))
    (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    DirectBuiltinCalleeValid source callee function ∧
      ExpressionsHaveTypes source context ids function.parameterTypes ∧ node.type = function.returnType := by
  generalize reportedEq : node.type = reported at typed
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
    | builtinCall calleeValid argumentsTyped => exact ⟨calleeValid, argumentsTyped, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBuiltinCallCertificates
