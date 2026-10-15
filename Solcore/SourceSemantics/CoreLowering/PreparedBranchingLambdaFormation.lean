import Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaIssuance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedBranchingLambdaBodySupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation

/-! The actual branching lambda Site constructs its prepared body before capture.
Original Source typing and the accepted native compiler supply every static
child; projected diagnostics remain attached to the original issuer. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedPreparedBranchingLambdaBodySupport (Syntax Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (original : CallableIndexedOwnedContextualLambdaProducerReceipts.Produced (compiled := compiled)
    caller.named parameters result statements sourceContext evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)

/-- The selected physical formation also retains the actual complete named
caller dictionary, which later expression certificates use after recapture. -/
structure Formation (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation caller context evidence scope id lowered where
  callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller context evidence

 theorem of_produced
    (typing : EmittedDiagnosticTokenPlan.UnaryTyped (source caller.named) ∧
      AssignmentDiagnosticOrigins.OperandsTyped (source caller.named))
    (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) original.site.code)
    (frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
      (closure caller.named parameters result statements sourceContext evidence []))
    (sameLedger : sourceContext.solvedRequirements = original.site.code.compilation.solvedRequirements)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (canonical : original.site.code.view = source caller.named)
    (signatures : inputs.context.signatures = compiled.compatible.checked.signatures)
    (hidden : GenericImperativeMatch.MatchHiddenFresh (source caller.named))
    (entryDeclarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named)
      (original.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) inputs.context)
    (syntaxTree : GenericImperativeMatch.Syntax (source caller.named) (Syntax (source caller.named))
      inputs.context (.statements true statements) result)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons original.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
    (sourceType : original.site.code.sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout original.site.code.sourceNode.requirements
      original.site.code.sourceNode.coercions [])
    (coercions : original.site.code.sourceNode.coercions = [])
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence) :
    Nonempty (Formation caller sourceContext evidence scope id lowered) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, issuedAt, recipe, compilerPolicy, sameCompilation⟩ := original.issuedRecipe
  let produced : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, original.site, original.identifier, original.emitted,
      original.binderPolicy, recipe, original.compilerPolicy, original.issuedRecipe⟩
  obtain ⟨issuer, sameAssignments, samePlaces⟩ :=
    PreparedBranchingLambdaIssuance.of_compilation caller compilation issuedAt typing
  have owner : produced.site.code.compilation.owner = caller.named.signature.key := by
    rw [produced.site.compilation]
    rfl
  let issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled
      produced.site.code.compilation.owner (source caller.named) := {
    first := issuer.first
    assignments := issuer.assignments
    assignmentsPrepared := issuer.assignmentsPrepared
    typing := issuer.typing
    plan := issuer.plan
    root := issuer.root
    extra := issuer.extra
    diagnostics := issuer.diagnostics
    prepared := issuer.prepared
    collected := by simpa only [owner] using issuer.collected }
  have assignments : issued.assignments = produced.compilation.own.assignments := sameAssignments
  have places : CallableIndexedOwnedLiteralPlaceDiagnosticShells.PlaceReasonsEq
      issued.diagnostics.program produced.diagnostics := samePlaces
  have runtime := (CallableIndexedOwnedLambdaSourceAdmission.runtime_at_parameters frame inputs.extended).1
  have projection := (CallableIndexedOwnedContextualLambdaPackReceipts.Code.source_projections original.site.code profile).2
  have allocation : (bodyPolicy produced.compilation produced.site.code).sourceCells =
      some (SourceCoreCallableIndexedAllocationFrames.allocator compiled.indexed.ancestry.layout.frame
        compiled.indexed.base.globals.length (compiled.indexed.layouts.allocatorAt
          produced.site.code.compilation.owner produced.site.code.active produced.site.code.allocationError)) := by
    rw [produced.site.compilation, produced.site.active, produced.site.allocationError]
    rfl
  let static : CallableIndexedOwnedPreparedNativeJointBodyCollectors.NativeExtractionInputs
      (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
      (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
      (expressionSyntax := Syntax produced.site.code.view) (certificates := Child 0 produced.site.code.view)
      (reasonAt := produced.site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions)
      (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
      (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
      true (bodyPolicy produced.compilation produced.site.code) inputs.context
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) := {
    matchCompilation := CallableIndexedOwnedLiteralReturnSiteShells.ambientMatch produced
    matchPolicy := CallableIndexedOwnedLiteralReturnSiteShells.match_policy produced
    matchValues := rfl
    matchDefinitions := rfl
    matchAllocator := allocation
    matchChildStatic := GenericImperativeMatch.MatchChildStatic.of_hidden (canonical.symm ▸ hidden)
    readPolicy := rfl
    binderPolicy := fun current binder mono => CallableIndexedOwnedLiteralReturnSiteShells.binder_policy produced binder current mono
    allocationPolicy := allocation
    expressions := by
      intro context closed residual sourceSignatures current fuel candidate node child declaration approved found typed accepted nativeType native
      exact ⟨node, found, typed, True.intro⟩
    assignments := CallableIndexedOwnedLiteralPlaceDiagnosticShells.assignment_policy produced issued assignments places
    unaries := CallableIndexedOwnedLiteralPlaceDiagnosticShells.unary_policy produced issued assignments places
    closed := runtime.variables_closed
    residual := runtime.residual_variables_open
    sourceSignatures := signatures
    declarations := by simpa only [produced, canonical] using entryDeclarations
    ledger := (Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended).solvedRequirements.trans
      (sameLedger.trans (by rw [original.site.compilation]; rfl)) }
  have edited : CallableLambdaViewEdits.LocalView (source caller.named) produced.site.code.view [] := by
    rw [canonical]
    exact .refl _
  obtain ⟨body, _entry, _readFuel⟩ := CallableIndexedOwnedPreparedNativeJointBodyCollectors.at_site
    produced.compilation produced.site produced.recipe (Program.ofChecked compiled.sourceProgram) inputs frame
    Syntax Child 0 .reachable issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
    edited (by intro candidate member; cases member) frame.code.graph.nodeOccurrencesUnique sameLedger
    (by intro candidate reached allowed; exact True.intro)
    (by intro context current candidate child reached given; simpa only [produced, canonical] using given)
    syntaxTree (canonical.symm ▸ syntaxTree) projection static
    (CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native original.site.code)
  exact ⟨{
    parameters := parameters
    result := result
    statements := statements
    produced := produced
    expressionSyntax := Syntax
    certificates := Child
    issued := issued
    diagnosticPolicy := .reachable
    body := body
    bodyView := by intro candidate reached; change (source caller.named).lookupExpression? candidate = original.site.code.view.lookupExpression? candidate; rw [canonical]
    bodyReasons := bodyReasons
    declarations := declarations
    sourceType := sourceType
    ordinary := ordinary
    coercions := coercions
    callerReceipt := callerReceipt }⟩

end Solcore.SourceSemantics.CoreLowering.PreparedBranchingLambdaFormation
