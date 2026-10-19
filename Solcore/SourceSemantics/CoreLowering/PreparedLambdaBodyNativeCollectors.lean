import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport

/-! The original accepted lambda body supplies one exact prepared tree. Its
finite diagnostic interpretation is chosen only after the tree is retained. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyNativeCollectors
open Core Frontend SourceInference
open CallableIndexedLambdaValues CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableLambdaViewEdits CallableLambdaBodyReachability
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedNativeJointBodyCollectors (NativeExtractionInputs)
open CallableIndexedOwnedPreparedBranchingLambdaBodySupport (Syntax Child)
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

theorem at_site {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {captured : Dynamic.Environment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site compiled.indexed named parameters result statements sourceContext evidence captured scope administrative)
    (recipe : BodyRecipe namedCompilation site.code)
    (program : Program) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code)
    (frame : Dynamic.ClosureFrame program (CallableIndexedLambdaGeneration.closure named parameters result statements sourceContext evidence captured))
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    (sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements)
    (view : site.code.view = CallableIndexedNamedGeneration.source named)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
    (hidden : GenericImperativeMatch.MatchHiddenFresh (CallableIndexedNamedGeneration.source named))
    (catalog : SignatureCatalogWellFormed compiled.compatible.checked.signatures)
    (shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape (CallableIndexedNamedGeneration.source named) true statements)
    (syntaxTree : GenericImperativeMatch.PreparedSyntax (CallableIndexedNamedGeneration.source named)
      (Syntax (CallableIndexedNamedGeneration.source named)) inputs.context (.statements true statements) result)
    (projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore)
    (static : NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (onError := site.code.allocationError) (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := Syntax site.code.view) (certificates := Child 0 site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := invalidOperand) (invalidUnary := invalidUnary) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) true (bodyPolicy namedCompilation site.code) inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope))
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ∃ body : PreparedLambdaBodySupport.Body namedCompilation site.code program Syntax Child
        invalidOperand invalidUnary invalidProjection missingDefault,
      body.toContext = inputs := by
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked)
    site.code (bodyPolicy namedCompilation site.code) (callback_of_recipe namedCompilation recipe)
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : site.code.receipt.body = CompatibleStatements.finish site.code.receipt.resultCore flow
      site.code.compilation.internalReason site.code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨nativeFlowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow (emitted ▸ nativeTyped)
  have edited : LocalView (CallableIndexedNamedGeneration.source named) site.code.view [] := by
    rw [view]
    exact .refl _
  have binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      (bodyPolicy namedCompilation site.code).lowerBinder site.code.view scope binder =
        SourceCoreCompatibleDataExpressions.lowerBinder compiled.compatible.checked site.code.view scope binder :=
    static.binderPolicy
  let collect (faults : FunctionCalls.FaultRep)
      (operands : PreparedLambdaBodyStaticReceipts.OperandLaw (CallableIndexedNamedGeneration.source named) invalidOperand faults)
      (unary : PreparedLambdaBodyStaticReceipts.UnaryLaw (CallableIndexedNamedGeneration.source named) invalidUnary faults) :=
    CallableIndexedOwnedPreparedNativeBranchingCollectors.collected
      (initial := inputs.context) (roots := statements.map NodeId.statement)
      edited (by intro id member; cases member) unique static.readPolicy binderPolicy static.allocationPolicy
      static.assignments static.unaries operands unary
      static.matchPolicy static.matchValues static.matchDefinitions static.matchAllocator hidden catalog static.ledger
      (certificates := fun _ _ _ _ => True)
      (by intros; exact True.intro)
      syntaxTree rfl shape (Dynamic.RuntimeContextFields.refl _)
      static.closed static.residual static.sourceSignatures
      (by simpa only [view] using static.declarations)
      (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩)) projection generated flowTyped
  let chosen := collect (fun _ _ => True)
    (by
      unfold PreparedLambdaBodyStaticReceipts.OperandLaw
      intro site assignment operator rhs origin profile previous right invalid
      exact True.intro)
    (by
      unfold PreparedLambdaBodyStaticReceipts.UnaryLaw
      intro site assignment origin profile
      exact True.intro)
  let extraction : PreparedLambdaBodyStaticReceipts.PreparedExtraction compiled.indexed.layouts
      site.code.compilation.owner site.code.active compiled.indexed.ancestry.layout.frame
      compiled.indexed.base.globals.length site.code.allocationError (.initial compiled.compatible.checked)
      (CallableIndexedNamedGeneration.source named) invalidOperand invalidUnary invalidProjection missingDefault
      (Syntax (CallableIndexedNamedGeneration.source named)) (Child 0 (CallableIndexedNamedGeneration.source named))
      compiled.indexed.layouts.definitions administrative inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
      (.statements true statements) result site.code.receipt.resultCore flow := {
    tree := chosen.tree
    sites := by
      intro registry faults operands unary
      exact (collect faults operands unary).sites registry }
  exact ⟨{
    toContext := inputs, frame := frame, readFuel := 0, flow := flow,
    projection := projection, emitted := emitted,
    valid := CallableIndexedLambdaStaticBodySupport.context_valid
      (values := .initial compiled.compatible.checked) site.code inputs frame sameLedger,
    unique := unique, syntaxTree := syntaxTree, shape := shape, view := view,
    recipe := recipe, generated := generated, extraction := extraction }, rfl⟩

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyNativeCollectors
