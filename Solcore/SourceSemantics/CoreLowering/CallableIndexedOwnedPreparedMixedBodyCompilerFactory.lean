import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSamePolicyCompilerLeafReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedCompilerCertificates

/-! Raw body child certificates retain the actual accepted root compiler action.
The static shell excludes expression trees and completed joint bodies. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) caller.named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The compiler fuel belongs to this actual child action; readFuel is its
separate certificate index. Lexical and Source facts belong to this context. -/
inductive AcceptedAt (expressionSyntax : TypedSource → ExpressionId → Prop) (readFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate where
  | intro {scope id node lowered compilerFuel residualMode}
      (found : source.lookupExpression? id = some node)
      (typed : ExpressionHasType source sourceContext id node.type)
      (allowed : expressionSyntax source id)
      (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
      (closed : sourceContext.typeVariables = [])
      (residual : sourceContext.residualTypeVariables = residualMode)
      (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        compilerFuel (context compiled.indexed caller.named) source scope id rootReasonAt = .ok lowered) :
      AcceptedAt expressionSyntax readFuel source sourceContext scope id lowered

/-- This factory is chosen before any body collector runs. -/
def certificates (expressionSyntax : TypedSource → ExpressionId → Prop) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax

section Extraction
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : SourceCoreCompatibleValues.Context} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
    {reasonAt : ExpressionId → Word} {definitions : DataEnvironment} {administrative : Core.Context}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}

/-- Static policy and child evidence is for the actual supplied body lowerer.
The residual factory contains no required legacy error interpretation. -/
structure StaticInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
  matchCompilation : SourceCoreCompatibleDataMatches.Context
  matchPolicy : CompatibleMatchAmbientLowering.PolicySuccess policy matchCompilation
  matchValues : matchCompilation.values = values
  matchDefinitions : matchCompilation.definitions = definitions
  matchAllocator : matchCompilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  hidden : MatchHiddenFresh source
  readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked
  binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
    policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder
  allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
    (layouts.allocatorAt owner active onError))
  assignments : CompatibleAssignmentStatements.AssignmentPolicy policy values invalidProjection invalidOperand missingDefault
  unaries : CompatibleBitNotStatements.Policy policy values invalidProjection invalidUnary missingDefault
  assignmentNative : ∀ sourceContext scope fuel id lowered,
    sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
    sourceContext.signatures = values.checked.signatures → CompatibleExpressionReads.ScopeDeclarations source scope sourceContext →
    expressionSyntax id → ∀ node, source.lookupExpression? id = some node →
    ExpressionHasType source sourceContext id node.type →
    policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
        (LanguageResult.resultType lowered.type) definitions
  closed : context.typeVariables = []
  residual : context.residualTypeVariables = residualMode
  sourceSignatures : context.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope context
  ledger : context.solvedRequirements = matchCompilation.solvedRequirements

end Extraction

section Chosen
variable {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Non-expression collector inputs are supplied at the actual chosen Site.
Raw child acceptance will construct its certificate fields internally. -/
structure SiteShell (expressionSyntax : TypedSource → ExpressionId → Prop)
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered) where
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure caller.named parameters result statements sourceContext evidence [])
  readFuel : Nat
  canonical : produced.site.code.view = source caller.named
  unique : NodeOccurrencesUnique (source caller.named)
  sameLedger : sourceContext.solvedRequirements = produced.site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source caller.named) (expressionSyntax (source caller.named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok produced.site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
    (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
    (expressionSyntax := expressionSyntax produced.site.code.view) (reasonAt := produced.site.code.reasonAt)
    (definitions := compiled.indexed.layouts.definitions)
    (administrative := RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy produced.compilation produced.site.code) entry.context
    (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
  nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (produced.site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
    produced.site.code.receipt.body (LanguageResult.resultType produced.site.code.receipt.resultCore)
    compiled.indexed.layouts.definitions

end Chosen
section Domain
open RecursiveNamedExpressionCompilerCertificates
open RecursiveNamedCallSelectionCertificates CallableAncestryPairedLookup
open CallableIndexedOwnedPreparedMixedCompilerHeads (extraForm extraChildren)
open CallableIndexedOwnedPreparedMixedCompilerCertificates (ExtraMetadata baseAdmitted)

/-- These are the original compiler's static premises at the current lexical
context and scope. Accepted lambda inputs are raw shells, with no final tree. -/
structure DomainAt (expressionSyntax : TypedSource → ExpressionId → Prop)
    (readFuel : Nat) (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope)
    (headers : RecursiveNamedCatalog.Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions (Program.ofChecked compiled.sourceProgram)) : Prop where
  namedLedger : (context compiled.indexed caller.named).solvedRequirements = caller.solved
  admission : AdmissionWith extraForm extraChildren (source caller.named) (expressionSyntax (source caller.named))
  coverage : ReachedCoverage headers (context compiled.indexed caller.named) (source caller.named)
    (expressionSyntax (source caller.named))
  sourceTypes : RecursiveNamedCallEvidenceHeads.SourceTypes headers sourceContext
  emptyEvidence : SelectedEmptyEvidence headers (context compiled.indexed caller.named) (source caller.named)
    (expressionSyntax (source caller.named))
  order : ∀ id callee arguments instantiation node, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node →
    node.form = .call callee arguments (.declaration instantiation) → Ordered (context compiled.indexed caller.named).plan instantiation
  constructorValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext
    (expressionSyntax (source caller.named))
  fragmentValid : CompatibleExpressionInstantiationLaws.ConstructorLaw (source caller.named) sourceContext
    (CompatibleExpressionBuiltins.Syntax (source caller.named))
  selectedValid : SelectedDeclarationLaw headers (context compiled.indexed caller.named) (source caller.named) sourceContext
    (expressionSyntax (source caller.named))
  basePolicy : PolicyForWith (headers := headers) (some evidence) root.selected.policy
    (context compiled.indexed caller.named) readFuel (.initial compiled.compatible.checked)
    (source caller.named) sourceContext scope rootReasonAt (baseAdmitted (source caller.named) (expressionSyntax (source caller.named)))
  fragmentCoercions : ∀ id node, CompatibleExpressionBuiltins.Syntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.coercions = []
  coercions : ∀ id node, expressionSyntax (source caller.named) id → (source caller.named).lookupExpression? id = some node → node.coercions = []
  metadata : ExtraMetadata (caller := caller) (expressionSyntax (source caller.named))
  profile : compiled.compatible.checked.catalog.callableContracts = true
  native : ∀ childFuel id node parameters result statements lowered, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered →
    HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions
  shells : ∀ childFuel id node parameters result statements lowered, expressionSyntax (source caller.named) id →
    (source caller.named).lookupExpression? id = some node → node.form = .lambda parameters result statements →
    ExpressionHasType (source caller.named) sourceContext id node.type →
    SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
      (childFuel + 1) (context compiled.indexed caller.named) (source caller.named) scope id rootReasonAt = .ok lowered →
    ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      produced.site.code.policy = root.selected.policy → produced.site.code.lowerBody = root.selected.lowerBody →
      produced.site.code.fuel = childFuel → produced.site.code.view = source caller.named →
      produced.site.code.reasonAt = rootReasonAt →
      Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
        (closure caller.named parameters result statements sourceContext evidence []) →
      Nonempty (SiteShell expressionSyntax produced)

end Domain
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory
