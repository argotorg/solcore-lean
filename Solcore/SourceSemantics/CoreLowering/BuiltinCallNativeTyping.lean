import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructorNativeTyping
import Solcore.SourceSemantics.CoreLowering.BuiltinCallTypedCertificates

/-! Native typing follows the actual contracted builtin and ordered argument
packing. The scalar consumer extracts all child receipts from the real compiler
callback; native child typing is not a premise of that consumer. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping
open Core Frontend SourceInference DataPatternValues
open CompatibleExpressionScalarNativeTyping CompatibleExpressionConstructorNativeTyping

theorem result_wellFormed (function : BuiltinFunctionId) (definitions : DataEnvironment) :
    (SourceCoreInteger.builtinResult function).WellFormed definitions := by
  cases function <;> constructor

theorem contracted_native (function : BuiltinFunctionId) (identity contract : Word)
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType context (BuiltinCalls.Protocol.contracted function identity contract)
      (LanguageResult.resultType (CallableContract.functionType
        (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function))) definitions :=
  LanguageResult.success_hasType (CallableContract.wrap_hasType contract
    (TaggedFunction.identified_hasType identity (SourceCoreInteger.builtinClosure_hasType function)))

theorem call_native {definitions : DataEnvironment} {context : Core.Context}
    (function : BuiltinFunctionId) (identity contract unknown : Word)
    {arguments : SourceCoreBasic.LoweredExpr}
    (typed : NativeTyping definitions context arguments)
    (parameter : arguments.type = SourceCoreInteger.builtinParameter function) :
    NativeTyping definitions context
      ⟨SourceCoreInteger.builtinResult function,
        CallableContract.call [⟨contract, none, none⟩] unknown (SourceCoreInteger.builtinResult function)
          (BuiltinCalls.Protocol.contracted function identity contract) arguments.expression⟩ := by
  refine ⟨result_wellFormed function definitions, CallableContract.call_hasType [⟨contract, none, none⟩] unknown
    (result_wellFormed function definitions) (contracted_native function identity contract definitions context) ?_⟩
  simpa only [parameter] using typed.2

theorem Head.native {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {context : Core.Context}
    (head : BuiltinCalls.Typed.Head values source certificate scope id lowered)
    (children : ∀ child code, certificate scope child code → NativeTyping definitions context code) :
    NativeTyping definitions context lowered := by
  cases head with
  | @contracted callee arguments function node codes identity contract unknown metadata form sourceType sequence nativeTypes =>
    apply call_native function identity contract unknown (packed_native sequence children)
    rw [packed_type, nativeTypes, CompatibleBuiltinMeaning.argumentTypes_pack]

private theorem receipts_of_mapM {error : Type} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {certificate : GenericExpressionMeaning.Certificate}
    (compile : ExpressionId → Except error SourceCoreBasic.LoweredExpr)
    {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
    (accepted : ids.mapM compile = .ok codes)
    (extract : ∀ id, id ∈ ids → ∀ code, compile id = .ok code →
      ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) :
    ListRel (fun id code => ∃ node, source.lookupExpression? id = some node ∧ certificate scope id code) ids codes := by
  induction ids generalizing codes with
  | nil => simp at accepted; subst codes; exact .nil
  | cons id ids ih =>
    cases first : compile id with
    | error reason => simp [List.mapM_cons, first, bind, Except.bind] at accepted
    | ok code =>
      cases rest : ids.mapM compile with
      | error reason => simp [List.mapM_cons, first, rest, bind, Except.bind] at accepted
      | ok tail =>
        simp only [List.mapM_cons, first, rest, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
        subst codes
        exact .cons (extract id (by simp) code first)
          (ih rest (fun child member => extract child (List.mem_cons_of_mem id member)))

/-- The actual dispatcher checks the packed parameter type and authenticates
the builtin decoration and gate. Only real argument callbacks are consumed. -/
theorem of_functions {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {context : Core.Context}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (children : ∀ child, child ∈ arguments → ∀ code,
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope child reasonAt = .ok code →
      ∃ node, source.lookupExpression? child = some node ∧ NativeTyping definitions context code)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) : NativeTyping definitions context lowered := by
  obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
    argumentsAccepted, parameter, resultType, emitted, rfl⟩ :=
    BuiltinCalls.call_of_accepted owner found read form special accepted
  cases reference with
  | @intro index identity calleeExpression _ _ _ _ decorated =>
    rw [profile, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
      (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
    cases decorated
    rw [profile, BuiltinCalls.Typed.builtin_call native active compilation source node callee arguments function
      type _ _ descriptor form] at emitted
    cases emitted
    subst type
    have receipts := receipts_of_mapM (scope := scope)
      (certificate := fun _ _ code => NativeTyping definitions context code)
      (fun child => SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope child reasonAt)
      argumentsAccepted children
    obtain ⟨_, sequence⟩ := DataExpressionSequence.Tree.of_children
      (source := source) (scope := scope)
      (certificate := fun _ _ code => NativeTyping definitions context code) receipts
    exact call_native function identity descriptor.id native.diagnostics.unknown
      (packed_native sequence (fun _ _ typed => typed)) parameter

/-- Scalar source syntax and typing at the real argument callbacks close all
native child obligations under arbitrary administrative and ambient contexts. -/
theorem scalar_of_functions {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context}
    {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
    {scope : SourceCoreLocalCell.Scope} {id callee : ExpressionId} {arguments : List ExpressionId}
    {function : BuiltinFunctionId} {node : ExpressionNode} {type : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    {definitions : DataEnvironment} {sourceContext : SourceSemantics.Context}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (owner : id.occurrence.owner = source.owner) (found : source.lookupExpression? id = some node)
    (read : policy.readExpression source id = .ok (node, type))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (unique : NodeOccurrencesUnique source)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
    (ordinary : CompatibleExpressionConditionals.PolicyFor policy compilation readFuel values source scope reasonAt)
    (coercions : ∀ child node, CompatibleExpressionConditionals.Syntax source child →
      source.lookupExpression? child = some node → node.coercions = [])
    (argumentsTyped : ∀ child, child ∈ arguments → ∃ node,
      source.lookupExpression? child = some node ∧ CompatibleExpressionConditionals.Syntax source child ∧
        ExpressionHasType source sourceContext child node.type)
    (scopeWF : ScopeWellFormed values.checked.catalog.definitions scope)
    (administrative : Core.Context) (extension : values.checked.catalog.definitions.Extends definitions)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    NativeTyping definitions (SourceCoreLocalCell.coreContext scope ++ administrative) lowered := by
  apply of_functions native active profile descriptor owner found read form special _ accepted
  intro child member code generated
  obtain ⟨node, found, syntaxTree, typed⟩ := argumentsTyped child member
  exact ⟨node, found, conditionals_native_at scopeWF administrative extension
    (CompatibleExpressionConditionals.tree_of_functions unique declarations ordinary coercions syntaxTree found typed generated)⟩

end Solcore.SourceSemantics.CoreLowering.BuiltinCallNativeTyping
