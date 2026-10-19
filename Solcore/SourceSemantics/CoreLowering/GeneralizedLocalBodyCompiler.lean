import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalMaterializedAssociation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness

/-! A materialized instance retains its actual compiler callback. Terminal
body certificates are extracted from that accepted action, with the actual
metadata view and full Source parameter context kept explicit. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalMaterializedAssociation
open GeneralizedLocalLambdaCompilation (representation binder)
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Terminal Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)

def policy : SourceCoreLoops.Policy :=
  let actual := representation material.inputs material.packet.original.emission.prepared
  { actual.loopsWithSourceCells actual.expressions.sourceCells
      material.packet.original.emission.prepared.caller.function.solvedRequirements
      material.inputs.assignments material.inputs.diagnostics material.inputs.current.owner
      (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) with
    sourceCells := actual.expressions.sourceCells
    lowerBinder := binder material.inputs material.packet.original.emission.prepared }

theorem callback : material.code.lowerBody
    (FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation) =
    SourceCoreLoops.lowerStatementsWithPolicy (policy material) := by
  rw (occs := .pos [1]) [material.lowerBody]
  rfl

theorem expression_reader : (policy material).lowerExpression =
    FunctionCode.children material.code.policy material.code.lowerBody material.code.fuel material.code.compilation := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

theorem statement_reader : (policy material).readStatement =
    SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked := by
  unfold policy representation
  rw [material.indexed.represented]
  rfl

/-- The original accepted lambda body supplies its terminal receipt. Neither
recompilation of a different Source view nor a body execution law is required. -/
theorem terminal_receipt {expression : ExpressionId}
    (terminal : Terminal material.code.view expression function.body) :
    Nonempty (Receipt (policy material) material.code.fuel material.code.view
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      expression function.body material.code.receipt.resultCore material.code.reasonAt
      material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body) := by
  exact CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (statement_reader material) terminal
    (CallableIndexedLambdaSemanticInvocation.loops_accepted
      (values := .initial compiled.compatible.checked) material.code (policy material) (callback material))

/-- Complete Source lambda typing supplies the actual parameter context.
The real global layout fixes the native reference slot independently of types. -/
theorem entry_context {program : Program} (frame : Dynamic.ClosureFrame program function)
    (ownership : LocalIdentityOwnership function.source)
:
    Nonempty (CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code) := by
  obtain ⟨id, node, contains, form, raw, typing⟩ := frame.code.occurrence
  have kinds := CallableIndexedOwnedLocalIdentityFreshness.lowered_parameter_kinds
    (values := .initial compiled.compatible.checked) material.code ownership contains form
  have reference : material.code.referenceIndex =
      material.inputs.scope.length + 1 + compiled.indexed.base.globals.length := by
    unfold CallableIndexedLambdaValues.Code.referenceIndex
    rw [material.compilation]
    change material.inputs.scope.length + material.inputs.current.administrativePrefix + material.inputs.current.globals.length = _
    rw [material.indexed.administrativePrefix, material.indexed.globals]
  rw [form] at typing
  generalize rawEq : TypeSystem.Ty.function
    (TypeSystem.Ty.productMany (function.parameters.map (fun binder => binder.scheme.body))) function.resultType = rawType at typing
  generalize planEq : ExpressionRequirementPlan.ordinary [] = plan at typing
  cases typing with
  | lambda unique extended bodyTyped completes =>
    exact ⟨⟨_, _, extended, kinds, reference⟩⟩

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyCompiler
