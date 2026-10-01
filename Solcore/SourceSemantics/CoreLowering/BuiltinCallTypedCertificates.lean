import Solcore.SourceSemantics.CoreLowering.BuiltinCallMeaning

/-! Successful production lowering authenticates contracted builtin selection,
identity and the complete argument bundle. The remaining premises are static
source metadata and concrete argument receipts, with no child execution premise. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false
namespace Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
open Core Frontend SourceInference

private theorem descriptor_reconstructs {table : SourceCoreStageCodebook.Table}
    {origin : SourceCoreStageCodebook.Origin} (descriptor : SourceCoreCallableContracts.Descriptor table origin) :
    SourceCoreCallableContracts.descriptor table origin = .ok descriptor := by
  cases descriptor
  rename_i identity found
  unfold SourceCoreCallableContracts.descriptor
  split
  · rename_i absent
    rw [found] at absent
    contradiction
  · rename_i selected actual
    have same := Option.some.inj (actual.symm.trans found)
    subst selected
    rfl

theorem builtin_call (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (compilation : SourceCoreFunctions.Context) (source : TypedSource) (node : ExpressionNode)
    (callee : ExpressionId) (arguments : List ExpressionId) (function : BuiltinFunctionId)
    (result : Ty) (calleeCode argumentCode : Expr)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (form : node.form = .call callee arguments (.builtinFunction function)) :
    (SourceCoreGeneralFunctions.callablePolicy (some native) active).callCallable
      compilation source node result calleeCode argumentCode =
      .ok (CallableContract.call [⟨descriptor.id, none, none⟩] native.diagnostics.unknown result calleeCode argumentCode) := by
  simp only [SourceCoreGeneralFunctions.callablePolicy, form, descriptor_reconstructs descriptor,
    Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem argument_types {fuel : Nat} {values : ValuesContext} {source : TypedSource}
    {context : SourceSemantics.Context} {solved : List SolvedRequirement} {reasonAt : ExpressionId → Word}
    {scope : Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (children : DataExpressionSequence.Tree source
      (CompatibleExpressionGeneral.Tree fuel values source context solved reasonAt) scope ids types codes) :
    types.mapM values.checked.catalog.project = .ok (codes.map (·.type)) := by
  induction children with
  | nil => rfl
  | single found child => simp [child.projected found, Functor.map, Except.map, bind, Except.bind, pure, Except.pure]
  | cons found child _ ih => simp [List.mapM_cons, child.projected found, ih, Functor.map, Except.map, bind, Except.bind]

/-- The child extraction is a static compiler receipt. Concrete General trees
close their meaning independently through `Typed.preserves` and `Typed.reflects`.
The supplied source types are raw builtin types, as required by the validator. -/
theorem tree_of_functions
    {policy : SourceCoreFunctions.Policy} {lowerBody : SourceCoreFunctions.BodyLowerer}
    {fuel readFuel : Nat} {compilation : SourceCoreFunctions.Context} {values : ValuesContext}
    {source : TypedSource} {sourceContext : SourceSemantics.Context} {solved : List SolvedRequirement}
    {scope : Scope} {id callee : ExpressionId} {arguments : List ExpressionId} {function : BuiltinFunctionId}
    {node : ExpressionNode} {type : Ty} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (profile : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (descriptor : SourceCoreCallableContracts.Descriptor native.table (.builtin function))
    (metadata : CompatibleExpressionPrimitives.Metadata values.checked source id node (SourceCoreInteger.builtinResult function))
    (form : node.form = .call callee arguments (.builtinFunction function))
    (sourceType : node.type = function.returnType)
    (read : policy.readExpression source id = .ok (node, type))
    (special : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower compilation
          (fun budget childSource childScope childId childReasonAt =>
            SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (min budget fuel)
              compilation childSource childScope childId childReasonAt)
          (fuel + 1) source scope id reasonAt) = .ok none)
    (children : ∀ codes, arguments.mapM (fun argument =>
      SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody fuel compilation source scope argument reasonAt) = .ok codes →
      DataExpressionSequence.Tree source (CompatibleExpressionGeneral.Tree readFuel values source sourceContext solved reasonAt)
        scope arguments function.parameterTypes codes)
    (accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
      compilation source scope id reasonAt = .ok lowered) :
    Tree readFuel values source sourceContext solved reasonAt scope id lowered := by
  obtain ⟨calleeNode, calleeType, calleeCode, codes, expression, _, _, reference,
    argumentsAccepted, _, resultType, emitted, rfl⟩ :=
    call_of_accepted metadata.owner metadata.found read form special accepted
  cases reference with
  | @intro index identity calleeExpression _ _ _ _ decorated =>
    rw [profile, ActualCallablePolicy.builtin_decoration native active compilation source calleeNode function
      (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function) _ descriptor] at decorated
    cases decorated
    rw [profile, builtin_call native active compilation source node callee arguments function type _ _ descriptor form] at emitted
    cases emitted
    subst type
    have argumentTrees := children codes argumentsAccepted
    have projected := argument_types argumentTrees
    rw [CompatibleBuiltinMeaning.argumentTypes_project function] at projected
    have nativeTypes := (Except.ok.inj projected).symm
    exact .contracted metadata form sourceType argumentTrees nativeTypes
end Solcore.SourceSemantics.CoreLowering.BuiltinCalls.Typed
