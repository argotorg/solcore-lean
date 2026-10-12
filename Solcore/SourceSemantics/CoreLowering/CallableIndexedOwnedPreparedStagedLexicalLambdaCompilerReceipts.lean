import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks

/-! The original body callback determines one lexical flow, allocator and
finish footer at the authentic closure Code. This contains only compiler facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Lexical parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative) {stages : Staging.Recursive.Registry}

structure Choice where
  packet : Lexical code stages
  callback : packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  readPolicy : packet.policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    packet.policy.lowerBinder code.view scope binder =
      SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked code.view scope binder
  allocationPolicy : packet.policy.sourceCells = some
    (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt packet.allocationOwner packet.active packet.onError))

/-- The actual retained lowerer supplies all allocator and binder callbacks;
none is inferred from a native result type. -/
theorem choose (named : Named)
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (shape : CallableIndexedOwnedPreparedStagedLexicalTree.Shape function.source function.body)
    (child : Staging.Recursive.Scope) (selected : stages.Closure function child) :
    Nonempty (Choice code (stages := stages)) := by
  obtain ⟨diagnostics, namedCode, compilation, recipe⟩ := retained
  let expression := FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  let policy := loop_policy compiled.indexed named compilation.own.assignments diagnostics expression
  have callback : code.lowerBody expression = SourceCoreLoops.lowerStatementsWithPolicy policy :=
    (congrArg (fun lower : SourceCoreFunctions.BodyLowerer => lower expression) recipe).trans
      (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.body_lowerer
        compiled.indexed named compilation.own.assignments diagnostics expression)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := .initial compiled.compatible.checked) code policy callback
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, returned⟩ := bind_ok accepted
  refine ⟨{
    packet := {
      policy := policy
      fuel := code.fuel
      reasonAt := code.reasonAt
      fellThrough := code.compilation.internalReason
      escaped := code.compilation.internalReason
      allocationOwner := named.signature.key
      active := []
      onError := fun error => .sourceAllocation (reprStr error)
      flow := flow
      accepted := generated
      emitted := (Except.ok.inj returned).symm
      shape := shape
      child := child
      selected := selected }
    callback := rfl
    reason := rfl
    readPolicy := rfl
    binderPolicy := ?_
    allocationPolicy := rfl }⟩
  intro current binder mono
  change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
  simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
  rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaCompilerReceipts
