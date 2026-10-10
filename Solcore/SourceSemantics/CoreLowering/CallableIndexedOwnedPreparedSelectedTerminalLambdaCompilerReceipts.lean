import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

/-! A literal selected lambda receipt retains the accepted body action and
its compiler recipe. A supported terminal form therefore constructs its
terminal compiler receipt internally, before any body evaluation is used. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedTerminalLambdaCompilerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode} {parameters : List TypedBinder} {result : TypeSystem.Ty}
  {statements : List StatementId} {reported : Ty} {childFuel : Nat}
  (certificate : CallableIndexedLambdaCertificates.Certificate root.selected.policy root.selected.lowerBody childFuel
    (context compiled.indexed named) (source named) scope id node parameters result statements reported rootReasonAt lowered)
  (actual : CallableIndexedOwnedPreparedNativeLambdaCompilerReceipts.Receipt root expressionSyntax certificate
    (sourceContext := sourceContext) (evidence := evidence))

/-- Only the supported actual terminal shape is a static input. The body
compiler equation, policy, parameter scope, used child and footer are obtained
from the same retained compiler receipt; no output equality is requested. -/
theorem of_receipt {expression : ExpressionId}
    (terminal : Terminal actual.site.code.view expression statements) :
    Nonempty (Receipt (bodyPolicy compilation actual.site.code) actual.site.code.fuel actual.site.code.view
      (actual.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression statements actual.site.code.receipt.resultCore actual.site.code.reasonAt
      actual.site.code.compilation.internalReason actual.site.code.compilation.internalReason
      actual.site.code.receipt.body) := by
  have accepted := actual.site.code.receipt.bodyCompiled
  rw [callback_of_recipe compilation actual.body.recipe] at accepted
  have parameterScope := FunctionCode.Parameters.scope
    (FunctionCode.Parameters.of_accepted actual.site.code.receipt.parametersCompiled)
  have sameScope : actual.site.code.receipt.bodyScope =
      actual.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope := by
    simpa only [List.map_reverse] using parameterScope
  rw [sameScope] at accepted
  exact CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    actual.shell.static.readPolicy terminal accepted

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedSelectedTerminalLambdaCompilerReceipts
