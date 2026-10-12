import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks

/-! The actual retained callback compiles an empty body to its original
fallthrough footer. The independent BodyWith supplies the result projection. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Empty EmptySupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {stages : Staging.Recursive.Registry}

/-- Every field comes from this exact Code, original static body and selected scope. -/
theorem of_empty
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) expressionSyntax certificates code
      (Program.ofChecked compiled.sourceProgram) registry faults)
    (empty : function.body = []) (unit : function.resultType = .unit)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Σ packet : Empty code stages,
      EmptySupport code body.toContext stages packet faults) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have applied := congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    applied.trans (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
      compiled.indexed named compilation.own.assignments diagnostics expression)
  have generated : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason =
      .ok (LocalLoop.fallthrough code.receipt.resultCore) := by
    exact (congrArg (fun statements => SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel code.view
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      statements code.receipt.resultCore code.reasonAt true code.compilation.internalReason) empty).trans (by simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy])
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  rw [generated] at accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore
      (LocalLoop.fallthrough code.receipt.resultCore) code.compilation.internalReason
      code.compilation.internalReason := Except.ok.inj accepted.symm
  have nativeUnit : code.receipt.resultCore = .unit := by
    have projected := body.projection
    have atUnit := (congrArg compiled.compatible.checked.catalog.project unit).symm.trans projected
    exact Except.ok.inj atUnit.symm
  exact ⟨⟨⟨empty, unit, nativeUnit, emitted, child, selected⟩, ⟨body.frame⟩⟩⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyBodyCompilerReceipts
