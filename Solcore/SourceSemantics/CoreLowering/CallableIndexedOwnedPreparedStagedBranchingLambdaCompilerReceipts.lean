import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks
import Solcore.SourceSemantics.CoreLowering.CompatibleAssignmentStatementCertificates

/-! The original body callback determines one branching flow, allocator and
finish footer at the authentic closure Code. This contains only compiler facts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CompatibleEncoding (bind_ok)
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Branching parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative) {stages : Staging.Recursive.Registry}

structure Choice where
  invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word
  invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Solcore.Syntax.ValueAssignOp → Word
  missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word
  packet : Branching code stages
  callback : packet.policy.lowerExpression = FunctionCode.children code.policy code.lowerBody code.fuel code.compilation
  reason : packet.reasonAt = code.reasonAt
  assignments : CompatibleAssignmentStatements.AssignmentPolicy packet.policy (.initial compiled.compatible.checked) invalidProjection invalidOperand missingDefault
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
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body)
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
    invalidProjection := fun site root => diagnostics.placeReason named.signature.key site root none
    invalidOperand := fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator)
    missingDefault := fun site root type => diagnostics.placeReason named.signature.key site root (some type)
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
    assignments := ?_
    readPolicy := rfl
    binderPolicy := ?_
    allocationPolicy := rfl }⟩
  · refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  · intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingLambdaCompilerReceipts
