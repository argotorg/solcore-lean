import Solcore.SourceSemantics.CoreLowering.CallableIndexedBuiltinValues

/-! A builtin value retains the actual accepted reference, source occurrence,
nonwrapping identity and descriptor from the compiled artifact. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
open Core Frontend SourceInference
open CallableIndexedBuiltinValues (Prepared)

structure Header {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (source : TypedSource) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  node : ExpressionNode
  name : String
  function : BuiltinFunctionId
  found : source.lookupExpression? id = some node
  form : node.form = .reference name (.builtinFunction function)
  requirements : node.requirements = []
  coercions : node.coercions = []
  sourceType : node.type = function.type
  index : Nat
  identity : Word
  inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index)
  number : Word.ofNat? (prepared.base.globals.length + index + 1) = some identity
  descriptor : SourceCoreCallableContracts.Descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function)
  nativeType : lowered.type = CallableContract.functionType
    (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
  emitted : lowered.expression = BuiltinCalls.Protocol.contracted function identity descriptor.id

theorem of_reference {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {source : TypedSource} {id : ExpressionId} {node : ExpressionNode} {name : String}
    {function : BuiltinFunctionId} {lowered : SourceCoreBasic.LoweredExpr}
    {compilation : SourceCoreFunctions.Context}
    (globals : compilation.globals = prepared.base.globals)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.builtinFunction function))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (accepted : SourceCoreFunctions.builtinReference
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext [])
      compilation source node name function = .ok lowered) : Nonempty (Header prepared source id lowered) := by
  rw [prepared.ancestry.graph.inputs.callableSelected] at accepted
  have reference := BuiltinCalls.reference_of_accepted accepted
  cases reference with
  | @intro index identity expression spelling sourceType inventory number decorated =>
    cases descriptorFound : SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function) with
    | error error =>
      simp [SourceCoreGeneralFunctions.callablePolicy, descriptorFound, bind, Except.bind, Except.mapError] at decorated
    | ok descriptor =>
      have emitted := ActualCallablePolicy.builtin_decoration prepared.ancestry.graph.inputs.callable [] compilation source node
        function (SourceCoreInteger.builtinParameter function) (SourceCoreInteger.builtinResult function)
        (TaggedFunction.identified identity (SourceCoreInteger.builtinClosure function)) descriptor
      have same := Except.ok.inj (emitted.symm.trans decorated)
      subst expression
      exact ⟨⟨node, name, function, found, form, requirements, coercions, sourceType,
        index, identity, inventory, by simpa only [globals] using number, descriptor, rfl, rfl⟩⟩

/-- Renaming a builtin reference keeps its closed builtin body and captures
exactly the current actual environment at evaluation. -/
theorem Header.rename {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
    {source : TypedSource} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : Header prepared source id lowered) (embedding : Nat → Nat) :
    lowered.expression.rename embedding = lowered.expression := by
  rw [receipt.emitted]
  have closed : ∀ (function : BuiltinFunctionId) (identity contract : Word),
      (BuiltinCalls.Protocol.contracted function identity contract).rename embedding =
        BuiltinCalls.Protocol.contracted function identity contract := by
    intro function identity contract
    cases function <;> rfl
  exact closed receipt.function receipt.identity receipt.descriptor.id

end Solcore.SourceSemantics.CoreLowering.CellAwareBuiltinValueCertificates
