import Solcore.SourceSemantics.CoreLowering.ActualCallablePolicy
import Solcore.SourceSemantics.CoreLowering.CompatibleBuiltinMeaning

/-! Static receipts from the actual builtin reference and direct-call branches.
The identity comes from the real global prefix and builtin inventory; callable
decoration and argument children retain their actual compiler equations. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls
open Core Frontend SourceInference

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem ensureType_ok {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

inductive Reference (callables : SourceCoreFunctions.CallablePolicy) (compilation : SourceCoreFunctions.Context)
    (source : TypedSource) (node : ExpressionNode) (name : String) (function : BuiltinFunctionId) :
    SourceCoreBasic.LoweredExpr → Prop where
  | intro {index : Nat} {identity : Word} {expression : Expr}
      (spelling : name = function.spelling) (sourceType : node.type = function.type)
      (inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index))
      (identitySelected : Word.ofNat? (compilation.globals.length + index + 1) = some identity)
      (decorated : callables.decorateCallable compilation source node (.builtin function)
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (LanguageResult.success (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function))) = .ok expression) :
      Reference callables compilation source node name function
        ⟨callables.functionType (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function), expression⟩

theorem reference_of_accepted
    {callables : SourceCoreFunctions.CallablePolicy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
    {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreFunctions.builtinReference callables compilation source node name function = .ok lowered) :
    Reference callables compilation source node name function lowered := by
  by_cases spelling : name = function.spelling
  · by_cases sourceType : node.type = function.type
    · cases inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) with
      | none => simp [SourceCoreFunctions.builtinReference, spelling, sourceType, inventory, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
      | some item =>
        have same : item.1 = function := by simpa using List.find?_some inventory
        obtain ⟨actual, index⟩ := item
        change actual = function at same
        subst actual
        cases selected : Word.ofNat? (compilation.globals.length + index + 1) with
        | none => simp [SourceCoreFunctions.builtinReference, spelling, sourceType, inventory, selected, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
        | some identity =>
          simp only [SourceCoreFunctions.builtinReference, spelling, sourceType, ne_eq,
            not_true_eq_false, decide_false, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
            inventory, selected, bind, Except.bind, pure, Except.pure] at accepted
          obtain ⟨expression, decorated, accepted⟩ := bind_ok accepted
          cases accepted
          exact .intro spelling sourceType inventory selected decorated
    · simp [SourceCoreFunctions.builtinReference, sourceType, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted
  · simp [SourceCoreFunctions.builtinReference, spelling, throw, throwThe, MonadExceptOf.throw, bind, Except.bind, pure, Except.pure] at accepted

/-- Successful production builtin-call lowering exposes the exact callee
receipt, ordered argument compilation and call hook. No child execution is
part of this certificate. The ordinary special-hook condition stays explicit. -/
theorem call_of_accepted
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (owner : id.occurrence.owner = source.owner)
    (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    ∃ calleeNode calleeType calleeCode codes expression,
      SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function = .ok () ∧
      policy.readExpression source callee = .ok (calleeNode, calleeType) ∧
      Reference policy.callables compilation source calleeNode function.spelling function calleeCode ∧
      arguments.mapM (fun argument => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel
        compilation source scope argument reasonAt) = .ok codes ∧
      (SourceCoreCalls.packArguments codes).type = SourceCoreInteger.builtinParameter function ∧
      type = SourceCoreInteger.builtinResult function ∧
      policy.callables.callCallable compilation source node type calleeCode.expression
        (SourceCoreCalls.packArguments codes).expression = .ok expression ∧
      lowered = ⟨type, expression⟩ := by
  cases hook : policy.lowerSpecial? <;> simp only [hook] at special
  all_goals
    unfold SourceCoreFunctions.lowerExpressionWithPolicy at accepted
    simp only [owner, ne_eq, not_true_eq_false, ↓reduceIte, found, hook, special, form, read,
      bind, Except.bind, pure, Except.pure] at accepted
    obtain ⟨validation, validated, accepted⟩ := bind_ok accepted
    have validatedRaw : SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function = .ok () := by
      cases actual : SourceCoreElaboration.validateBuiltinFunctionCall source node callee arguments function <;>
        simp_all [Except.mapError]
    obtain ⟨calleePair, calleeRead, accepted⟩ := bind_ok accepted
    obtain ⟨calleeNode, calleeType⟩ := calleePair
    obtain ⟨calleeCode, calleeAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨codes, argumentsAccepted, accepted⟩ := bind_ok accepted
    obtain ⟨packedCheck, packedChecked, accepted⟩ := bind_ok accepted
    have packedType := (ensureType_ok packedChecked).symm
    obtain ⟨resultCheck, resultChecked, accepted⟩ := bind_ok accepted
    have resultType := (ensureType_ok resultChecked).symm
    obtain ⟨expression, emitted, accepted⟩ := bind_ok accepted
    cases accepted
    exact ⟨calleeNode, calleeType, calleeCode, codes, expression, validatedRaw, calleeRead,
      reference_of_accepted calleeAccepted, argumentsAccepted, packedType, resultType, emitted, rfl⟩
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls
