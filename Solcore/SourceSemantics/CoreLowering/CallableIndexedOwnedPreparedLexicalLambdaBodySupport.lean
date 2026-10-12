import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion

/-! The actual lexical lambda callback builds a static body certificate.
Children retain their original typed nodes; application meaning is supplied
later by the recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

def Syntax : TypedSource → ExpressionId → Prop := fun _ _ => True

def Child : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ source context _ id _ => ∃ node,
    source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Every tree node is recovered from the accepted same-view compiler flow and
independent Source syntax at the real parameter context. -/
theorem of_lexical
    (retained : CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    (owner : code.compilation.owner = named.signature.key)
    (active : code.active = [])
    (onError : code.allocationError = fun error => .sourceAllocation (reprStr error))
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (syntaxTree : GenericLexicalStatements.Syntax function.source (Syntax function.source)
      inputs.context true function.body function.resultType) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) Syntax Child code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax function.source)
        body.context (.statements true function.body) function.resultType := by
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
  obtain ⟨flow, generated, returned⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
      code.compilation.internalReason code.compilation.internalReason := (Except.ok.inj returned).symm
  have native := CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native code
  rw [emitted] at native
  obtain ⟨nativeType, native⟩ := TypedLexicalWhile.Native.finished_flow native
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections code profile).2
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have generatedSource : SourceCoreLoops.lowerFlowStatementsWithPolicy policy code.fuel function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow := by
    simpa only [view] using generated
  have binderPolicy : ∀ current binder, binder.scheme.quantified = [] →
      policy.lowerBinder function.source current binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked function.source current binder := by
    intro current binder mono
    change SourceCoreGeneralFunctions.contextualBinder _ _ _ _ _ _ _ = _
    simp only [SourceCoreGeneralFunctions.contextualBinder, mono, List.isEmpty_nil, ↓reduceIte]
    rfl
  have allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length
      (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  let tree := CallableIndexedOwnedPreparedNativeLexicalCollectors.tree_of_typed_flow_with_residual
    (values := .initial compiled.compatible.checked) true
    (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
    binderPolicy allocationPolicy
    (certificates := Child 0 function.source)
    (fun context _closed _residual _signatures scope fuel id node lowered _declarations _syntax found typed _accepted nativeType _native =>
      ⟨node, found, typed⟩)
    syntaxTree runtime.variables_closed runtime.residual_variables_open signatures declarations projection generatedSource native
  let full : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (Syntax function.source) (Child 0 function.source)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := .body syntaxTree tree
  have sites : full.CatalogSites .reachable registry faults := .body (syntaxTree := syntaxTree) (body := tree)
  let actualTree : GenericImperativeMatch.Tree compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) code.view (Syntax code.view) (Child 0 code.view)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow := by
    simpa only [view] using full
  have actualSites : actualTree.CatalogSites .reachable registry faults := by
    simpa only [view] using sites
  refine ⟨{
    toContext := inputs, frame := frame, readFuel := 0, policy := policy, callback := callback
    flow := flow, generated := generated, projection := projection, emitted := emitted
    actualTree := actualTree, actualSites := actualSites, tree := full, sites := sites
    valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) code inputs frame sameLedger
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl, .body syntaxTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLexicalLambdaBodySupport
