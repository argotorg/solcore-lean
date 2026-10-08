import Solcore.SourceSemantics.CoreLowering.CallableLambdaViewMatchRuntimeCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedTypedLambdaStaticBody
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchCertificates

/-! The actual contextual body recipe and one view extraction supply the same
canonical flow and its prepared structural payload. Source syntax and static
child/compiler evidence remain independent genuine receipts. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
open Core Frontend SourceInference
open CallableLambdaViewEdits CallableLambdaBodyReachability CallableLambdaViewStaticTyping
open GenericImperativeMatch

/-- This constructible static factory retains owning occurrences. Its legacy
error package remains residual and is unused by the prepared structural route. -/
def trackedFactory (diagnosticPolicy : AssignmentDiagnosticPolicy) (source : TypedSource)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word) :
    AssignmentDiagnosticOrigins.Factory true diagnosticPolicy source invalidOperand :=
  ⟨fun head registry faults => head.ErrorsFor diagnosticPolicy registry faults,
   fun _ _ _ _ _ _ given => given⟩

section Transport
variable {source view : TypedSource} {roots : List NodeId} {changed : List ExpressionId}
  (edited : LocalView source view changed) (avoids : Avoids source roots changed)
  {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {definitions : DataEnvironment} {administrative : Core.Context}
  {beforeSyntax afterSyntax : ExpressionId → Prop}
  {before after : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  (unique : NodeOccurrencesUnique source)
  (syntaxTransport : ∀ id, Reaches source roots (.expression id) → beforeSyntax id → afterSyntax id)
  (expressions : ∀ context scope id lowered, Reaches source roots (.expression id) →
    before context scope id lowered → after context scope id lowered)
  {tracked : Bool} {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  {factory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy source invalidOperand}
  {targetFactory : AssignmentDiagnosticOrigins.Factory tracked diagnosticPolicy view invalidOperand}
include edited avoids unique expressions

/-- The mapped post tree and its plan are chosen together by the shared core. -/
theorem header_prepared {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {items : List ForItemForm} {type : Ty} {code : Expr}
    {tree : GenericForHeader.Tree layouts owner active frame globals onError values source before definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code}
    (receipt : Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (reached : Within source roots (items.flatMap ForItemForm.references)) :
    ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values view after definitions administrative
      type (TypedForHeader.Fallthrough type) context scope items code,
      Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree := by
  obtain ⟨plan, coupled, tokens⟩ := receipt
  exact CallableLambdaViewMatchRuntimeCertificates.header_payload_with edited avoids expressions
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
    (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
    (fun tree => CallableLambdaViewPreparedStaticTransport.Header.PreparedPacket (factory := targetFactory)
      (invalidProjection := invalidProjection) (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    CallableLambdaViewPreparedStaticTransport.Header.prepared_algebra
    (fun head reached receipt => CallableLambdaViewMatchRuntimeCertificates.assignment_payload edited avoids
      expressions unique receipt reached)
    (fun head receipt => CallableLambdaViewMatchRuntimeCertificates.unary_payload edited receipt)
    (GenericForHeader.Structural.of_coupled coupled tokens) reached

include syntaxTransport in
/-- One actual position extraction crosses the view with its chosen heads and
post trees. The target structural receipt uses that same canonical tree. -/
theorem transport_prepared {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}
    (receipt : Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := source)
      (expressionSyntax := beforeSyntax) (certificates := before) (definitions := definitions) (administrative := administrative)
      (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context)
      context scope (.statements mode statements) expected type code)
    (reached : ∀ id ∈ statements, Reaches source roots (.statement id)) :
    ∃ _tree : Tree layouts owner active frame globals onError values view afterSyntax after definitions administrative
      context scope (.statements mode statements) expected type code,
      Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
        (globals := globals) (onError := onError) (values := values) (source := view)
        (expressionSyntax := afterSyntax) (certificates := after) (definitions := definitions) (administrative := administrative)
        (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
        (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
        (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
          (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
        (fun compilation context => Tree.MatchContextFields compilation context)
        context scope (.statements mode statements) expected type code := by
  exact CallableLambdaViewMatchRuntimeCertificates.transport_payload_with edited avoids unique syntaxTransport expressions
    (fun head => GenericForHeader.Structural.PreparedAssignment factory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked source invalidUnary head)
    (fun tree => Structural.PreparedHeader (factory := factory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
    (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
      (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    (fun {context scope position expected type code} tree => Structural.Eliminates (layouts := layouts) (owner := owner) (active := active) (frame := frame)
      (globals := globals) (onError := onError) (values := values) (source := view)
      (expressionSyntax := afterSyntax) (certificates := after) (definitions := definitions) (administrative := administrative)
      (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context)
      context scope position expected type code)
    (CallableLambdaViewPreparedStaticTransport.Match.structural_algebra
      (fun head => GenericForHeader.Structural.PreparedAssignment targetFactory invalidProjection missingDefault head)
      (fun head => GenericForHeader.Structural.PreparedUnary tracked view invalidUnary head)
      (fun tree => Structural.PreparedHeader (factory := targetFactory) (invalidProjection := invalidProjection)
        (missingDefault := missingDefault) (invalidUnary := invalidUnary) tree)
      (fun compilation context => Tree.MatchContextFields compilation context))
    (fun head reached receipt => CallableLambdaViewMatchRuntimeCertificates.assignment_payload edited avoids
      expressions unique receipt reached)
    (fun head receipt => CallableLambdaViewMatchRuntimeCertificates.unary_payload edited receipt)
    (fun _ receipt reached => header_prepared edited avoids unique expressions receipt reached)
    (fun _ _ receipt => receipt) receipt reached

end Transport
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

/-- Static policy and child evidence is for the actual supplied body lowerer.
The residual factory contains no required legacy error interpretation. -/
structure ExtractionInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
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
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered → certificates sourceContext scope id lowered
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  assignmentExpressions : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
    ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      certificates sourceContext scope id lowered ∧
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

/-- The original collector runs once at the actual accepted view flow. -/
theorem ExtractionInputs.extract {residualMode : Bool} {policy : SourceCoreLoops.Policy}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    (inputs : ExtractionInputs (layouts := layouts) (owner := owner) (active := active) (frame := frame)
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
  exact extraction_of_typed_position_with_catalog_coupled residualMode diagnosticPolicy
    (trackedFactory diagnosticPolicy source invalidOperand) inputs.matchPolicy inputs.matchValues inputs.matchDefinitions
    inputs.matchAllocator inputs.matchChildStatic inputs.readPolicy inputs.binderPolicy inputs.allocationPolicy
    inputs.expressions inputs.assignments inputs.unaries unique inputs.assignmentExpressions syntaxTree
    inputs.closed inputs.residual inputs.sourceSignatures inputs.declarations projection accepted nativeTyped

end Extraction

section Site
open CallableIndexedLambdaValues
open CallableIndexedLambdaGeneration
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode)

/-- The body recipe is the literal equation retained by the contextual producer. -/
def BodyRecipe {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : Prop :=
  code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
    (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements namedCompilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key [])
      compiled.indexed.base.locals named.signature.key [])

/-- This is the actual recipe's policy applied to its own recursive children. -/
def bodyPolicy {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) : SourceCoreLoops.Policy :=
  let representation := (CallableIndexedNamedGeneration.representation compiled.indexed).atContext named.signature.key []
  {representation.loopsWithSourceCells representation.expressions.sourceCells
    (CallableIndexedNamedGeneration.context compiled.indexed named).solvedRequirements namedCompilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context compiled.indexed named).owner
    (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) with
    sourceCells := representation.expressions.sourceCells
    lowerBinder := SourceCoreGeneralFunctions.contextualBinder representation compiled.indexed.base.locals named.signature.key []}

theorem callback_of_recipe {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative} (recipe : BodyRecipe namedCompilation code) :
    code.lowerBody (FunctionCode.children code.policy code.lowerBody code.fuel code.compilation) =
      SourceCoreLoops.lowerStatementsWithPolicy (bodyPolicy namedCompilation code) := by
  dsimp only [bodyPolicy]
  rw [recipe]
  rfl

/-- This receipt has the actual view extraction and the canonical prepared
eliminator at the same flow. It contains no body execution callback. -/
structure JointBody {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    extends CallableIndexedOwnedTypedLambdaStaticBody.Body code program expressionSyntax certificates where
  recipe : BodyRecipe namedCompilation code
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (bodyPolicy namedCompilation code) code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  actual : CatalogCoupledExtractionFor diagnosticPolicy compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) code.view (trackedFactory diagnosticPolicy code.view invalidOperand)
    invalidUnary invalidProjection missingDefault (expressionSyntax code.view) (certificates readFuel code.view)
    compiled.indexed.layouts.definitions administrative context.solvedRequirements context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow
  prepared : Structural.Eliminates (layouts := compiled.indexed.layouts) (owner := code.compilation.owner)
    (active := code.active) (frame := compiled.indexed.ancestry.layout.frame) (globals := compiled.indexed.base.globals.length)
    (onError := code.allocationError) (values := .initial compiled.compatible.checked) (source := function.source)
    (expressionSyntax := expressionSyntax function.source) (certificates := certificates readFuel function.source)
    (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
    (fun head => GenericForHeader.Structural.PreparedAssignment (trackedFactory diagnosticPolicy function.source invalidOperand)
      invalidProjection missingDefault head)
    (fun head => GenericForHeader.Structural.PreparedUnary true function.source invalidUnary head)
    (fun postTree => Structural.PreparedHeader (factory := trackedFactory diagnosticPolicy function.source invalidOperand)
      (invalidProjection := invalidProjection) (missingDefault := missingDefault) (invalidUnary := invalidUnary) postTree)
    (fun compilation context => Tree.MatchContextFields compilation context)
    context (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow

/-- The authentic chosen Site supplies its body recipe. The existing collector
runs at that accepted view, and the shared transport returns its canonical flow. -/
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
    (static : ExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaJointStaticReceipts
