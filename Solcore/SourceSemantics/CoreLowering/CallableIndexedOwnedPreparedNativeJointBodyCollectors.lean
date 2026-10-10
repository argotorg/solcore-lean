import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeImperativeCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts

/-! The literal body recipe and one same-view compiler extraction construct
one JointBody with actual local native occurrence witnesses. Ordered assignment
keys and present RHS use the real execute inversion. The canonical transport,
chosen flow and prepared structural eliminator are the original producer's
same-Code proofs. There is no expected child typing supplier or semantic body
callback. The static child factory still must manufacture the genuine finite
compiler certificate at each actual Source occurrence. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability CallableLambdaViewStaticTyping
open GenericImperativeMatch
open CallableIndexedOwnedContextualLambdaJointStaticReceipts

section Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Static policy belongs to this exact body lowerer. The single expression
factory receives the actual local native witness, including ordered keys and
present RHS. No expected child typing or expression execution is supplied. -/
structure NativeExtractionInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  matchChildStatic : MatchChildStatic matchCompilation source certificates definitions administrative
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  expressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures →
    ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
    source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
    ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType definitions → certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

/-- The real occurrence collector runs once at this actual accepted view flow. -/
theorem NativeExtractionInputs.extract {residualMode : Bool} {policy : SourceCoreLoops.Policy}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (inputs : NativeExtractionInputs (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := expressionSyntax) (certificates := certificates) (reasonAt := reasonAt)
      (definitions := definitions) (administrative := administrative) (invalidOperand := invalidOperand)
      (invalidUnary := invalidUnary) (invalidProjection := invalidProjection) (missingDefault := missingDefault)
      residualMode policy context scope)
    (diagnosticPolicy : AssignmentDiagnosticPolicy) (unique : NodeOccurrencesUnique source)
    {position : Position} {expected : TypeSystem.Ty} {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (syntaxTree : Syntax source expressionSyntax context position expected)
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : AssignmentDiagnosticOrigins.AcceptedFor true policy fuel source scope position type reasonAt selfReason code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Nonempty (CatalogCoupledExtractionFor diagnosticPolicy layouts owner active frame globals onError values source
      (trackedFactory diagnosticPolicy source invalidOperand) invalidUnary invalidProjection missingDefault expressionSyntax certificates
      definitions administrative inputs.matchCompilation.solvedRequirements context scope position expected type code) := by
  exact CallableIndexedOwnedPreparedNativeImperativeCollectors.extraction_of_typed_position_with_catalog_coupled residualMode diagnosticPolicy
    (trackedFactory diagnosticPolicy source invalidOperand) inputs.matchPolicy inputs.matchValues inputs.matchDefinitions
    inputs.matchAllocator inputs.matchChildStatic inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy
    inputs.expressions inputs.assignments inputs.unaries unique syntaxTree
    inputs.closed inputs.residual inputs.sourceSignatures inputs.declarations projection accepted nativeTyped

end Extraction

section Site
open CallableIndexedLambdaValues
open CallableIndexedLambdaGeneration
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

/-- One actual native-aware collector supplies the original joint constructor.
The real Site, compiler callback, body, lexical context, flow, prepared tree and
view transport remain exact. No arbitrary body equality or execution is input. -/
theorem at_site {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {captured : Dynamic.Environment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (site : Site compiled.indexed named parameters result statements sourceContext evidence captured scope administrative)
    (recipe : BodyRecipe namedCompilation site.code)
    (program : Program) (inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code)
    (frame : Dynamic.ClosureFrame program (CallableIndexedLambdaGeneration.closure named parameters result statements sourceContext evidence captured))
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (readFuel : Nat) (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    {changed : List ExpressionId}
    (edited : LocalView (CallableIndexedNamedGeneration.source named) site.code.view changed)
    (avoids : Avoids (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) changed)
    (unique : NodeOccurrencesUnique (CallableIndexedNamedGeneration.source named))
    (sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements)
    (syntaxTransport : ∀ id, Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      expressionSyntax site.code.view id → expressionSyntax (CallableIndexedNamedGeneration.source named) id)
    (expressions : ∀ context scope id lowered,
      Reaches (CallableIndexedNamedGeneration.source named) (statements.map NodeId.statement) (.expression id) →
      certificates readFuel site.code.view context scope id lowered →
      certificates readFuel (CallableIndexedNamedGeneration.source named) context scope id lowered)
    (syntaxTree : Syntax (CallableIndexedNamedGeneration.source named)
      (expressionSyntax (CallableIndexedNamedGeneration.source named)) inputs.context (.statements true statements) result)
    (viewSyntax : Syntax site.code.view (expressionSyntax site.code.view) inputs.context (.statements true statements) result)
    (projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore)
    {residualMode : Bool}
    (static : NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
      (onError := site.code.allocationError) (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view) (certificates := certificates readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := invalidOperand) (invalidUnary := invalidUnary) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) residualMode (bodyPolicy namedCompilation site.code) inputs.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope))
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
      site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions) :
    ∃ body : JointBody namedCompilation site.code program expressionSyntax certificates diagnosticPolicy
        invalidOperand invalidUnary invalidProjection missingDefault,
      body.toBody.toContext = inputs ∧ body.readFuel = readFuel := by
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted (values := .initial compiled.compatible.checked) site.code (bodyPolicy namedCompilation site.code)
    (callback_of_recipe namedCompilation recipe)
  unfold SourceCoreLoops.lowerStatementsWithPolicy at accepted
  obtain ⟨flow, generated, accepted⟩ := CompatibleEncoding.bind_ok accepted
  have emitted : site.code.receipt.body = CompatibleStatements.finish site.code.receipt.resultCore flow
      site.code.compilation.internalReason site.code.compilation.internalReason := Except.ok.inj accepted.symm
  obtain ⟨nativeFlowType, flowTyped⟩ := TypedLexicalWhile.Native.finished_flow (emitted ▸ nativeTyped)
  obtain ⟨actual⟩ := static.extract diagnosticPolicy (edited.metadata.unique unique) viewSyntax projection generated flowTyped
  have reverse : LocalView site.code.view (CallableIndexedNamedGeneration.source named) changed :=
    ⟨edited.metadata.symm, fun id fresh => (edited.unchanged id fresh).symm⟩
  obtain ⟨canonical, prepared⟩ := transport_prepared reverse (avoids.view edited.metadata)
    (edited.metadata.unique unique)
    (fun id reached receipt => syntaxTransport id (reached.metadata edited.metadata.symm) receipt)
    (fun context scope id lowered reached receipt => expressions context scope id lowered
      (reached.metadata edited.metadata.symm) receipt)
    (targetFactory := trackedFactory diagnosticPolicy (CallableIndexedNamedGeneration.source named) invalidOperand)
    (actual.eliminate static.ledger) (fun id member => .root (List.mem_map.mpr ⟨id, member, rfl⟩))
  have actualLedger : static.matchCompilation.solvedRequirements = inputs.context.solvedRequirements := static.ledger.symm
  exact ⟨{
    toBody := {
      toContext := inputs, frame := frame, readFuel := readFuel, flow := flow,
      projection := projection, emitted := emitted, tree := canonical,
      valid := CallableIndexedLambdaStaticBodySupport.context_valid (values := .initial compiled.compatible.checked) site.code inputs frame sameLedger,
      unique := unique, syntaxTree := syntaxTree },
    recipe := recipe, generated := generated,
    actual := actualLedger ▸ actual,
    prepared := prepared }, rfl, rfl⟩

end Site

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
