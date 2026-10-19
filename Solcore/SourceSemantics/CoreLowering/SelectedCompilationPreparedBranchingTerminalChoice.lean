import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticFacts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance

/-! The retained ordinary compiler recipe supplies the exact accepted terminal
child. This choice keeps the compiler callback and a singleton certificate;
it contains no expression or body execution premise. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaProvenance (OrdinaryAt)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedTerminalClosureUsedChildBounds (Point)

private theorem terminal_view {source view : TypedSource} {expression : ExpressionId}
    {statements : List StatementId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      source expression statements) :
    CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal view expression statements := by
  cases terminal with
  | returning rest found form => exact .returning rest (metadata.symm.statement found) form
  | tail found form => exact .tail (metadata.symm.statement found) form

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {stages : Staging.Recursive.Registry}

/-- Recapture keeps the original terminal statement and the compiler's actual
lowerer. The selected Source scope is retained unchanged in the packet. -/
theorem of_actual
    (code : Code compiled.indexed function scope administrative)
    (support : PreparedLambdaBodySupport.Support code)
    (provenance : PreparedLambdaBodySupport.PreparedAt code support)
    (expression : ExpressionId)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      function.source expression function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    ∃ packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages,
      packet.expression = expression ∧
      packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation ∧
      packet.reasonAt = code.reasonAt ∧ packet.child = child ∧
      packet.certificate = Point
        (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
        packet.expression packet.receipt.child ∧
      code.compilation.administrativePrefix = 1 := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := provenance.issued_recipe.body_recipe
  let callback := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have actualCallback : code.lowerBody callback = SourceCoreLoops.lowerStatementsWithPolicy policy := by
    rw [recipe]
    exact CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback
  have viewed : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      code.view expression function.body := terminal_view code.viewOfSource terminal
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    code policy actualCallback
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed support.caller.named compilation.own.assignments diagnostics callback) viewed accepted
  let packet : CallableIndexedOwnedPreparedStagedTerminalClosureParentBounds.Terminal code stages := {
    policy := policy
    fuel := code.fuel
    expression := expression
    reasonAt := code.reasonAt
    fellThrough := code.compilation.internalReason
    escaped := code.compilation.internalReason
    receipt := receipt
    certificate := Point
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      expression receipt.child
    certifies := by
      intro lowered generated
      exact ⟨rfl, rfl, Except.ok.inj (generated.symm.trans receipt.generated)⟩
    child := child
    selected := selected }
  refine ⟨packet, rfl, rfl, rfl, rfl, rfl, ?_⟩
  rw [support.compilation]
  rfl

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPreparedBranchingTerminalChoice
