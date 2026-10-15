import Solcore.SourceSemantics.CoreLowering.PreparedBranchingLegacyCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicUnaryAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIssuedAssignmentRecipes
import Solcore.SourceSemantics.CoreLowering.PreparedBranchingAssignmentDiagnostics
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedEmptyLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeBranchingCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingCatalogSites
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion

/-! The actual branching lambda callback builds a static body certificate.
Children retain their original typed nodes; application meaning is supplied
later by the recursive body family. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (loop_policy)

def Syntax : TypedSource → ExpressionId → Prop := fun _ _ => True

def Child : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  fun _ source => CallableIndexedOwnedPreparedStagedLexicalTree.TypedCertificate source
    (fun _ _ _ _ => True)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (code : Code compiled.indexed function scope administrative)
  {named : Named} {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Every tree node is recovered from the accepted same-view compiler flow and
independent Source syntax at the real parameter context. -/
theorem of_branching
    (retained : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named code)
    {index : Nat} (selected : compiled.indexed.base.functions[index]? = some named)
    (source : function.source = CallableIndexedNamedGeneration.source named)
    {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
    (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed
      completion.entry completion.result.context.registry completion.result.extension completion.result.diagnostics)
    (included : ∀ reason token,
      CallableIndexedOwnedPublicDecodedCallFaults.faults completion.result.diagnostics reason token → faults reason token)
    (sameCompilation : code.compilation = context compiled.indexed named)
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (sameLedger : function.context.solvedRequirements = code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (view : code.view = function.source)
    (owner : code.compilation.owner = named.signature.key)
    (active : code.active = [])
    (onError : code.allocationError = fun error => .sourceAllocation (reprStr error))
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh function.source)
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations function.source
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (shape : CallableIndexedOwnedPreparedStagedLegacyBranchingTree.Shape function.source true function.body)
    (syntaxTree : GenericImperativeMatch.Syntax function.source (Syntax function.source)
      inputs.context (.statements true function.body) function.resultType) :
    ∃ body : CallableIndexedLambdaStaticBodySupport.BodyWith
      (values := .initial compiled.compatible.checked) Syntax Child code
      (Program.ofChecked compiled.sourceProgram) registry faults,
      body.toContext = inputs ∧ GenericImperativeMatch.Syntax function.source (Syntax function.source)
        body.context (.statements true function.body) function.resultType := by
  obtain ⟨diagnostics, namedCode, compilation, _rootFuel, issued, recipe, _policyRecipe, _sameCompilation⟩ := retained
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
  have assignments : CompatibleAssignmentStatements.AssignmentPolicy policy
      (.initial compiled.compatible.checked)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root operator => if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site root (.value operator))
      (fun site root type => diagnostics.placeReason named.signature.key site root (some type)) := by
    refine ⟨rfl, rfl, ?_⟩
    change some _ = some _
    apply congrArg some
    funext expression fuel source scope site assignment operator rhs output next reasonAt
    cases operator <;> rfl
  have unaryPolicy : CompatibleBitNotStatements.Policy policy (.initial compiled.compatible.checked)
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root => compilation.own.assignments.reasonAt site root .bitNot)
      (fun site root type => diagnostics.placeReason named.signature.key site root (some type)) := rfl
  obtain ⟨first, assignmentPrepared⟩ :=
    CallableIndexedOwnedIssuedAssignmentRecipes.assignments_prepared selected compilation issued
  rw [← source] at assignmentPrepared
  have operands : ∀ {site assignment operator rhs},
      AssignmentDiagnosticOrigins.Occurs function.source site assignment operator rhs →
      (operator = .equal ∨ assignment.target.type = .word) →
      AssignmentOperandDiagnostics.OperandsLaw faults operator
        (if operator = .equal then Word.zero else compilation.own.assignments.reasonAt site assignment.target.root (.value operator)) := by
    intro site assignment operator rhs occurrence rawProfile
    exact PreparedBranchingAssignmentDiagnostics.operands assignmentPrepared
      (fun reason token represented => included reason token
        (CallableIndexedOwnedIssuedAssignmentRecipes.operands compilation issued receiver represented)) occurrence rawProfile
  have unary : ∀ {site assignment}, GenericAssignmentUnaryDiagnostics.UnaryOccurs function.source site assignment →
      assignment.target.type = .word → faults (.invalidUnaryOperand .bitNot)
        (compilation.own.assignments.reasonAt site assignment.target.root .bitNot) := by
    intro site assignment origin rawWord
    exact GenericAssignmentUnaryDiagnostics.prepared_unary_included assignmentPrepared
      (fun reason token represented => included reason token
        (CallableIndexedOwnedPublicUnaryAssignmentDiagnostics.compilation_unary compilation issued receiver represented))
      origin rawWord
  let baseMatch : SourceCoreCompatibleDataMatches.Context :=
    ⟨.initial compiled.compatible.checked, (context compiled.indexed named).solvedRequirements,
      some (allocator compiled.indexed named), none⟩
  have matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy
      (CompatibleMatchAmbientLowering.withDefinitions baseMatch compiled.indexed.layouts.definitions) := by
    apply CompatibleMatchAmbientLowering.PolicySuccess.extend (show policy.lowerMatch = some
      (SourceCoreCompatibleDataMatches.lowerWithReasons baseMatch) from rfl)
    exact ⟨_, CallableIndexedAmbient.definitions_exact compiled.indexed⟩
  have matchAllocator : (CompatibleMatchAmbientLowering.withDefinitions baseMatch
      compiled.indexed.layouts.definitions).sourceCells = some
      (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length
        (compiled.indexed.layouts.allocatorAt code.compilation.owner code.active code.allocationError)) := by
    rw [owner, active, onError]
    rfl
  have matchLedger : inputs.context.solvedRequirements = baseMatch.solvedRequirements := by
    exact (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).solvedRequirements.trans
      (sameLedger.trans (by rw [sameCompilation]))
  let collected : CallableIndexedOwnedPreparedBranchingCatalogSites.Collected
      (fun site root => diagnostics.placeReason named.signature.key site root none)
      (fun site root raw => diagnostics.placeReason named.signature.key site root (some raw)) (faults := faults) compiled.indexed.layouts code.compilation.owner code.active
      compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
      (.initial compiled.compatible.checked) function.source (Syntax function.source) (Child 0 function.source)
      compiled.indexed.layouts.definitions administrative inputs.context
      (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true function.body) function.resultType code.receipt.resultCore flow :=
    CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
      (CallableLambdaViewEdits.LocalView.refl function.source)
      (by intro id member; cases member)
      frame.code.graph.nodeOccurrencesUnique
      (show policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement compiled.compatible.checked from rfl)
      binderPolicy allocationPolicy assignments unaryPolicy operands unary
      matchPolicy rfl rfl matchAllocator hidden catalog matchLedger
      (certificates := fun _ _ _ _ => True)
      (by intros; exact True.intro)
      syntaxTree rfl shape.forget (Dynamic.RuntimeContextFields.refl _)
      runtime.variables_closed runtime.residual_variables_open signatures declarations
      (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection generatedSource native
  let full := collected.tree
  have sites : full.CatalogSites .reachable registry faults := PreparedBranchingLegacyCatalogSites.body (collected.sites registry) shape
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
    unique := frame.code.graph.nodeOccurrencesUnique }, rfl, syntaxTree⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
