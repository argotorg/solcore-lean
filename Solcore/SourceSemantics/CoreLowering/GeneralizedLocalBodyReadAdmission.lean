import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyProfileReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaScopeDeclarations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalBodyTyping

/-! Actual closure typing, captured declarations and accepted compilation
supply the complete terminal read certificate at the real parameter context. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadAdmission
open Core Frontend SourceInference GeneralHeap
open GeneralizedLocalMaterializedAssociation
open CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts (Receipt)

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {mapping : LocationMap} {world : StoreTyping}
  {function : Dynamic.Closure} (material : Materialization compiled mapping world function)
  (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) material.code)
  {program : Program} (frame : Dynamic.ClosureFrame program function)
  {invocation : Staging.Recursive.Scope} (source : invocation.source = function.source)
  (receipt : Receipt (GeneralizedLocalBodyCompiler.policy material) material.code.fuel material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    material.bodyProfile.expression function.body material.code.receipt.resultCore material.code.reasonAt
    material.code.compilation.internalReason material.code.compilation.internalReason material.code.receipt.body)

include frame source in
theorem actual_read :
    CompatibleExpressionReads.LoweredRead compiled.indexed.fuel (.initial compiled.compatible.checked)
      material.code.view inputs.context material.code.reasonAt
      (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
      material.bodyProfile.expression receipt.child ∧
    (GeneralizedLocalBodyProfileReceipts.read_site material).node.type = function.resultType := by
  have declarations := CallableIndexedOwnedPreparedLambdaScopeDeclarations.at_parameters
    (values := .initial compiled.compatible.checked) material.code inputs frame material.capturedDeclarations
  have body := CallableIndexedOwnedLambdaSourceAdmission.body_typed_at_parameters frame inputs.extended
  obtain ⟨finalContext, facts, bodyTyped, completes⟩ := body
  have compilerSource := GeneralizedLocalBodyProfileReceipts.view_source material
  have unique : NodeOccurrencesUnique invocation.source := source ▸ material.unique
  have head := receipt.head invocation (source.trans compilerSource.symm)
  rw [← source] at bodyTyped
  obtain ⟨node, found, type, typed⟩ :=
    CallableIndexedOwnedPreparedStagedTerminalBodyTyping.child_typed unique head bodyTyped completes
  let site := GeneralizedLocalBodyProfileReceipts.read_site material
  have foundView : material.code.view.lookupExpression? material.bodyProfile.expression = some node := by
    rwa [source, ← compilerSource] at found
  have same := Option.some.inj (site.found.symm.trans foundView)
  have readTyped : ExpressionHasType material.code.view inputs.context material.bodyProfile.expression site.node.type := by
    rw [source, ← compilerSource] at typed
    exact same.symm ▸ typed
  have accepted := receipt.generated
  rw [GeneralizedLocalBodyCompiler.expression_reader] at accepted
  change SourceCoreFunctions.lowerExpressionWithPolicy material.code.policy material.code.lowerBody
    (min receipt.childFuel material.code.fuel) material.code.compilation material.code.view
    (material.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ material.inputs.scope)
    material.bodyProfile.expression material.code.reasonAt = .ok receipt.child at accepted
  refine ⟨GeneralizedLocalBodyReadCertificate.lowered_read material site
    (by simpa only [compilerSource] using material.unique) (by simpa only [compilerSource] using declarations) readTyped accepted, ?_⟩
  exact (congrArg ExpressionNode.type same).trans type

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalBodyReadAdmission
