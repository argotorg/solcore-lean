import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedMaterialization
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaSemanticInvocation
import Solcore.SourceSemantics.CoreLowering.AcceptedNamedBodyFlow
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLocalIdentityFreshness

/-! Materialization enters the same complete accepted lambda body. Its actual
Source frame supplies the parameter context without a finite body profile. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
open Core Frontend SourceInference GeneralHeap ReadOnly
open GeneralizedLocalAcceptedMaterialization
open GeneralizedLocalLambdaCompilation (representation binder)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} {viewRelation : TypedSource → TypedSource → Prop}
  (material : Materialization compiled mapping world function viewRelation)

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

/-- The same source closure and compiled view use the complete original body. -/
theorem lambda_fields : material.packet.parameters = function.parameters ∧
    material.packet.result = function.resultType ∧ material.packet.statements = function.body := by
  have found := material.code.found
  rw [material.codeId, material.view] at found
  have same := Option.some.inj (material.packet.found.symm.trans found)
  have form := material.code.form.trans material.code.sourceForm
  exact ExpressionForm.lambda.inj (material.packet.form.symm.trans
    ((congrArg ExpressionNode.form same).trans form))

/-- Readout materialization retains the same actual whole-body compiler call,
with its parameter scope and full unfiltered statement list. -/
theorem body_receipt : Nonempty (AcceptedNamedBodyFlow.Body (policy material)
    material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body) := by
  exact AcceptedNamedBodyFlow.body_of_accepted
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

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalAcceptedBodyCompiler
