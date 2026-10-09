import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLiteralReturnSiteShells

/-! The same selected lambda certificate supplies the actual singleton-return
child callback and finish expression. The original minimum compiler budget is
retained separately from any semantic read or execution index. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedLiteralReturnSiteShells

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
    {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- This receipt contains successful compiler equations and the exact emitted
finish wrapper. It contains no child evaluation or body execution law. -/
structure Receipt (expression : ExpressionId) where
  budget : Nat
  child : SourceCoreBasic.LoweredExpr
  accepted : (bodyPolicy produced.compilation produced.site.code).lowerExpression budget
    produced.site.code.view
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    expression produced.site.code.reasonAt = .ok child
  resultType : child.type = produced.site.code.receipt.resultCore
  emitted : produced.site.code.receipt.body =
    LocalControl.finish produced.site.code.receipt.resultCore
      (LocalLoop.toControl produced.site.code.receipt.resultCore
        (LocalLoop.returnValue produced.site.code.receipt.resultCore child.expression)
        produced.site.code.compilation.internalReason)
      (if produced.site.code.receipt.resultCore = .unit then LanguageResult.success .unit
       else LanguageResult.failure produced.site.code.receipt.resultCore
         (.word produced.site.code.compilation.internalReason))

/-- Inversion uses the original accepted body once, at its actual chosen Site. -/
theorem of_return {statement : StatementId} {node : StatementNode} {statementType : Ty}
    {expression : ExpressionId}
    (singleton : statements = [statement])
    (read : (bodyPolicy produced.compilation produced.site.code).readStatement produced.site.code.view statement =
      .ok (node, statementType))
    (form : node.form = .returnStmt (some expression)) :
    Nonempty (Receipt produced expression) := by
  have accepted := body_accepted produced
  conv at accepted => lhs; arg 5; rw [singleton]
  obtain ⟨budget, child, generated, sameType, emitted⟩ :=
    CallableIndexedLambdaScalarNativeTyping.scalar_body_receipt read (Or.inl form) accepted
  exact ⟨⟨budget, child, generated, sameType, emitted⟩⟩

variable {expression : ExpressionId} (receipt : Receipt produced expression)

/-- The real body callback keeps its own minimum fuel and selected policy. -/
theorem Receipt.functions_child :
    SourceCoreFunctions.lowerExpressionWithPolicy produced.site.code.policy produced.site.code.lowerBody
      (min receipt.budget produced.site.code.fuel) produced.site.code.compilation produced.site.code.view
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression produced.site.code.reasonAt = .ok receipt.child := by
  exact receipt.accepted

section Root
variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
    {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
    (root : CallableIndexedOwnedContextualCompilerPolicyProfiles.RootPolicyReceipt
      (compiled := compiled) caller.named diagnostics namedCode compilation
      rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Genuine callback identities place the same child action under its original
root. No compiler callback, Source row or selected Site is reconstructed. -/
theorem Receipt.at_root
    (policy : produced.site.code.policy = root.selected.policy)
    (body : produced.site.code.lowerBody = root.selected.lowerBody)
    (canonical : produced.site.code.view = source caller.named)
    (reason : produced.site.code.reasonAt = rootReasonAt) :
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (min receipt.budget produced.site.code.fuel) (context compiled.indexed caller.named) (source caller.named)
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression rootReasonAt = .ok receipt.child := by
  have actual := receipt.functions_child produced
  conv at actual => lhs; arg 1; rw [policy]
  conv at actual => lhs; arg 2; rw [body]
  conv at actual => lhs; arg 4; rw [produced.site.compilation]
  conv at actual => lhs; arg 5; rw [canonical]
  conv at actual => lhs; arg 8; rw [reason]
  exact actual

end Root
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSingletonReturnCompilerReceipts
