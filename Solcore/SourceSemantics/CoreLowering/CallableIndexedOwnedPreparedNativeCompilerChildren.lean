import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeJointBodyCollectors
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedLambdaBodyNativeInversion
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren

/-! Actual enclosing compiler typing is retained in each local child certificate.
The same Named compilation works for a Header or a selected Principal. This
factory removes both the broad assignment-native supplier and separately typed
lambda body. One native-aware compiler induction builds the literal JointBody.
An older broad AcceptedAt or Collected does not acquire these local witnesses.
Source authority and compiler acceptance remain independent of native typing. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedNativeJointBodyCollectors
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

section Accepted
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- Native typing is for this exact emitted child and literal entry prefix.
The actual Source read/type and compiler action remain separate fields. -/
inductive AcceptedAt (expressionSyntax : TypedSource → ExpressionId → Prop)
    (administrative : Core.Context) (readFuel : Nat)
    (source : TypedSource) (sourceContext : SourceSemantics.Context) : GenericExpressionMeaning.Certificate where
  | intro {scope id node lowered compilerFuel residualMode nativeType}
      (found : source.lookupExpression? id = some node)
      (typed : ExpressionHasType source sourceContext id node.type)
      (allowed : expressionSyntax source id)
      (declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext)
      (closed : sourceContext.typeVariables = [])
      (residual : sourceContext.residualTypeVariables = residualMode)
      (signatures : sourceContext.signatures = compiled.compatible.checked.signatures)
      (accepted : SourceCoreFunctions.lowerExpressionWithPolicy root.selected.policy root.selected.lowerBody
        compilerFuel (context compiled.indexed named) source scope id rootReasonAt = .ok lowered)
      (raw : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType compiled.indexed.layouts.definitions) :
      AcceptedAt expressionSyntax administrative readFuel source sourceContext scope id lowered

def certificates (expressionSyntax : TypedSource → ExpressionId → Prop)
    (administrative : Core.Context) : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax administrative

end Accepted

section Static
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

/-- Only static policy, actual Source scope and hidden-match freshness remain.
Local expression typing comes from the enclosing emitted code, not this shell. -/
structure StaticInputs (residualMode : Bool) (policy : SourceCoreLoops.Policy)
    (sourceContext : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope) where
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
  closed : sourceContext.typeVariables = []
  residual : sourceContext.residualTypeVariables = residualMode
  sourceSignatures : sourceContext.signatures = values.checked.signatures
  declarations : CompatibleExpressionReads.ScopeDeclarations source scope sourceContext
  ledger : sourceContext.solvedRequirements = matchCompilation.solvedRequirements

end Static

section Site
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed named parameters result statements sourceContext evidence [] scope administrative)

/-- The exact chosen Site carries static Source/issuance inputs. Its body
native typing is derived from site.code.typed by literal wrapper inversion. -/
structure SiteShell where
  issuedCompilation : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics
  issued : IssuedSource compiled site.code.compilation.owner (source named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure named parameters result statements sourceContext evidence [])
  readFuel : Nat
  canonical : site.code.view = source named
  unique : NodeOccurrencesUnique (source named)
  sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source named) (expressionSyntax (source named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
    (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := site.code.view)
    (definitions := compiled.indexed.layouts.definitions)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy compilation site.code) entry.context
    (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)

/-- Actual callback acceptance fixes the minimum compiler fuel. The local
native witness is retained verbatim alongside independent Source facts. -/
theorem accepted_child
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {residualMode : Bool} {nativeType : Ty}
    (closed : currentContext.typeVariables = []) (residual : currentContext.residualTypeVariables = residualMode)
    (signatures : currentContext.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations site.code.view childScope currentContext)
    (allowed : expressionSyntax site.code.view id) (found : site.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType site.code.view currentContext id node.type)
    (accepted : (bodyPolicy compilation site.code).lowerExpression fuel
      site.code.view childScope id site.code.reasonAt = .ok lowered)
    (raw : HasType (SourceCoreLocalCell.coreContext childScope ++ administrative)
      lowered.expression nativeType compiled.indexed.layouts.definitions)
    (readFuel : Nat) :
    AcceptedAt root expressionSyntax administrative readFuel site.code.view currentContext childScope id lowered := by
  change FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation
    fuel site.code.view childScope id site.code.reasonAt = .ok lowered at accepted
  rw [FunctionCode.children, policyEq, bodyEq, reasonEq, site.compilation] at accepted
  exact .intro found typed allowed declarations closed residual signatures accepted raw

/-- Both static and local native child fields are constructed internally from
one enclosing compiler extraction; no final expression Tree is requested. -/
def SiteShell.extraction (shell : SiteShell (compilation := compilation) expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    NativeExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view)
      (certificates := certificates root expressionSyntax administrative shell.readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := shell.issued.invalidOperand) (invalidUnary := shell.issued.invalidUnary)
      (invalidProjection := shell.issued.invalidProjection) (missingDefault := shell.issued.missingDefault)
      shell.residualMode (bodyPolicy compilation site.code) shell.entry.context
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) where
  matchCompilation := shell.static.matchCompilation
  matchPolicy := shell.static.matchPolicy
  matchValues := shell.static.matchValues
  matchDefinitions := shell.static.matchDefinitions
  matchAllocator := shell.static.matchAllocator
  matchChildStatic := MatchChildStatic.of_hidden shell.static.hidden
  readPolicy := shell.static.readPolicy
  binderPolicy := shell.static.binderPolicy
  allocationPolicy := shell.static.allocationPolicy
  expressions := by
    intro currentContext closed residual signatures childScope fuel id node lowered declarations allowed found typed accepted nativeType raw
    exact accepted_child root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted raw shell.readFuel
  assignments := shell.static.assignments
  unaries := shell.static.unaries
  closed := shell.static.closed
  residual := shell.static.residual
  sourceSignatures := shell.static.sourceSignatures
  declarations := shell.static.declarations
  ledger := shell.static.ledger

/-- One same-Code joint body is built at the actual selected Site. The owning
Named record/dictionary is supplied by the caller's actual ordinary or Principal
producer; no Header is synthesized for a selected method. -/
theorem SiteShell.joint (shell : SiteShell (compilation := compilation) expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    ∃ body : JointBody compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax administrative) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault,
      body.toContext = shell.entry ∧ body.readFuel = shell.readFuel := by
  have recipe : BodyRecipe compilation site.code := bodyEq.trans root.selected.recipe
  have edited : LocalView (source named) site.code.view [] := by
    rw [shell.canonical]
    exact LocalView.refl _
  exact CallableIndexedOwnedPreparedNativeJointBodyCollectors.at_site compilation site recipe
    (Program.ofChecked compiled.sourceProgram) shell.entry shell.frame expressionSyntax
    (certificates root expressionSyntax administrative) shell.readFuel shell.diagnosticPolicy
    shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault
    edited (by intro id member; cases member) shell.unique shell.sameLedger
    (by intro id reached allowed; simpa only [shell.canonical] using allowed)
    (by intro currentContext childScope id lowered reached given; simpa only [shell.canonical] using given)
    shell.syntaxTree (shell.canonical.symm ▸ shell.syntaxTree) shell.projection
    (SiteShell.extraction root expressionSyntax site shell policyEq bodyEq reasonEq)
    (CallableIndexedOwnedPreparedLambdaBodyNativeInversion.body_native site.code)

end Site
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeCompilerChildren
