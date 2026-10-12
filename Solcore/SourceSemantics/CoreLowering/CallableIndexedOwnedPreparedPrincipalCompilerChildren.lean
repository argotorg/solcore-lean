import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualQualification
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedMixedBodyCompilerFactory

/-! The raw accepted-child factory is indexed by the actual Named compilation,
so a selected Principal can use its cached compilation and dictionary directly.
A same-site static shell constructs both expression fields of the original
JointBody extraction internally. Source context, scope, id, lowered value and
minimum compiler fuel remain exact. This is a compiler child collector, not a
body meaning theorem. The method expression Tree/head interpretation and the
joint graded family still require their genuine static and semantic producers.
-/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualCompilerPolicyProfiles
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedMixedBodyCompilerFactory (StaticInputs)
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

section Accepted
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered)

/-- The actual compiler action is retained before any expression Tree is
constructed. The separate readFuel indexes the receiving static body grammar. -/
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
        compilerFuel (context compiled.indexed named) source scope id rootReasonAt = .ok lowered) :
      AcceptedAt expressionSyntax readFuel source sourceContext scope id lowered

def certificates (expressionSyntax : TypedSource → ExpressionId → Prop) :
    Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate :=
  AcceptedAt root expressionSyntax

end Accepted

section Principal
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  (root : RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
    principal.cached.compilation rootFuel rootSource rootScope rootId rootReasonAt rootLowered)
  (expressionSyntax : TypedSource → ExpressionId → Prop)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  (site : Site compiled.indexed principal.named parameters result statements sourceContext principal.dictionary [] scope administrative)

/-- The real selected method Site fixes the physical prefix. No ordinary
Header or equality between independent body and receiving registries is used. -/
structure SiteShell where
  issued : IssuedSource compiled site.code.compilation.owner (source principal.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure principal.named parameters result statements sourceContext principal.dictionary [])
  readFuel : Nat
  canonical : site.code.view = source principal.named
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code
  unique : NodeOccurrencesUnique (source principal.named)
  sameLedger : sourceContext.solvedRequirements = site.code.compilation.solvedRequirements
  syntaxTree : Syntax (source principal.named) (expressionSyntax (source principal.named))
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok site.code.receipt.resultCore
  residualMode : Bool
  static : StaticInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
    (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := site.code.view)
    (expressionSyntax := expressionSyntax site.code.view) (reasonAt := site.code.reasonAt)
    (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
    (invalidOperand := issued.invalidOperand) (invalidUnary := issued.invalidUnary)
    (invalidProjection := issued.invalidProjection) (missingDefault := issued.missingDefault)
    residualMode (bodyPolicy principal.cached.compilation site.code) entry.context
    (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
  nativeTyped : HasType (SourceCoreLocalCell.coreContext
      (site.code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope) ++ administrative)
    site.code.receipt.body (LanguageResult.resultType site.code.receipt.resultCore) compiled.indexed.layouts.definitions

/-- This is the exact callback used by the method's original body recipe. -/
theorem body_expression : (bodyPolicy principal.cached.compilation site.code).lowerExpression =
    FunctionCode.children site.code.policy site.code.lowerBody site.code.fuel site.code.compilation := rfl

/-- The original minimum fuel stays inside the authentic accepted compiler
receipt. Source typing and lexical context are its actual supplied indices. -/
theorem accepted_child
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    {currentContext : SourceSemantics.Context} {childScope : SourceCoreLocalCell.Scope}
    {fuel : Nat} {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr} {residualMode : Bool}
    (closed : currentContext.typeVariables = []) (residual : currentContext.residualTypeVariables = residualMode)
    (signatures : currentContext.signatures = compiled.compatible.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations site.code.view childScope currentContext)
    (allowed : expressionSyntax site.code.view id) (found : site.code.view.lookupExpression? id = some node)
    (typed : ExpressionHasType site.code.view currentContext id node.type)
    (accepted : (bodyPolicy principal.cached.compilation site.code).lowerExpression fuel
      site.code.view childScope id site.code.reasonAt = .ok lowered)
    (readFuel : Nat) :
    AcceptedAt root expressionSyntax readFuel site.code.view currentContext childScope id lowered := by
  rw [body_expression, FunctionCode.children, policyEq, bodyEq, reasonEq, site.compilation] at accepted
  exact .intro found typed allowed declarations closed residual signatures accepted

/-- Both expression certificate fields of the existing collector are built
from actual callback acceptance. Every remaining field comes from the same
Site shell. No completed expression or body law is an input. -/
def SiteShell.extraction (shell : SiteShell principal expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt) :
    ExtractionInputs (layouts := compiled.indexed.layouts) (owner := site.code.compilation.owner)
      (active := site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
      (globals := compiled.indexed.base.globals.length) (onError := site.code.allocationError)
      (values := .initial compiled.compatible.checked) (source := site.code.view)
      (expressionSyntax := expressionSyntax site.code.view) (certificates := certificates root expressionSyntax shell.readFuel site.code.view)
      (reasonAt := site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions) (administrative := administrative)
      (invalidOperand := shell.issued.invalidOperand) (invalidUnary := shell.issued.invalidUnary)
      (invalidProjection := shell.issued.invalidProjection) (missingDefault := shell.issued.missingDefault)
      shell.residualMode (bodyPolicy principal.cached.compilation site.code) shell.entry.context
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
    intro currentContext closed residual signatures childScope fuel id node lowered declarations allowed found typed accepted
    exact accepted_child principal root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted shell.readFuel
  assignments := shell.static.assignments
  unaries := shell.static.unaries
  assignmentExpressions := by
    intro currentContext childScope fuel id lowered closed residual signatures declarations allowed node found typed accepted
    exact ⟨accepted_child principal root expressionSyntax site policyEq bodyEq reasonEq closed residual signatures
      declarations allowed found typed accepted shell.readFuel,
      shell.static.assignmentNative currentContext childScope fuel id lowered closed residual signatures declarations allowed
        node found typed accepted⟩
  closed := shell.static.closed
  residual := shell.static.residual
  sourceSignatures := shell.static.sourceSignatures
  declarations := shell.static.declarations
  ledger := shell.static.ledger

/-- The real method dictionary remains in the Source closure and retained
Support. A positive constructor requires the actual selected Site, its recipe,
original typed body and the real owning issuance. -/
inductive Collected : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) →
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code → Prop where
  | recaptured
      (shell : SiteShell principal expressionSyntax site)
      (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault)
      (policyEq : site.code.policy = root.selected.policy)
      (bodyEq : site.code.lowerBody = root.selected.lowerBody)
      (reasonEq : site.code.reasonAt = rootReasonAt)
      (entryEq : body.toContext = shell.entry)
      (readFuelEq : body.readFuel = shell.readFuel)
      (binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code)
      (environment : Dynamic.Environment) :
      Collected (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal site expressionSyntax
          (certificates root expressionSyntax) shell.issued shell.diagnosticPolicy body).recapture environment)

/-- The original joint producer runs once, at the actual method Site and its
body recipe. No preconstructed final joint body is asked of the shell. -/
theorem SiteShell.collected (shell : SiteShell principal expressionSyntax site)
    (policyEq : site.code.policy = root.selected.policy)
    (bodyEq : site.code.lowerBody = root.selected.lowerBody)
    (reasonEq : site.code.reasonAt = rootReasonAt)
    (environment : Dynamic.Environment) :
    ∃ body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax (certificates root expressionSyntax) shell.diagnosticPolicy
        shell.issued.invalidOperand shell.issued.invalidUnary shell.issued.invalidProjection shell.issued.missingDefault,
      body.toContext = shell.entry ∧ body.readFuel = shell.readFuel ∧
      Collected principal root expressionSyntax site
        (RecursiveNamedLambdaFormationHeads.recaptureCode
          (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal site expressionSyntax
          (certificates root expressionSyntax) shell.issued shell.diagnosticPolicy body).recapture environment) := by
  have recipe : BodyRecipe principal.cached.compilation site.code := bodyEq.trans root.selected.recipe
  have binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code :=
    (congrArg SourceCoreFunctions.Policy.lowerBinder policyEq).trans root.selected.binder
  have edited : LocalView (source principal.named) site.code.view [] := by
    rw [shell.canonical]
    exact LocalView.refl _
  obtain ⟨body, entryEq, readFuelEq⟩ := at_site principal.cached.compilation site recipe
    (Program.ofChecked compiled.sourceProgram) shell.entry shell.frame expressionSyntax (certificates root expressionSyntax)
    shell.readFuel shell.diagnosticPolicy shell.issued.invalidOperand shell.issued.invalidUnary
    shell.issued.invalidProjection shell.issued.missingDefault
    edited (by intro id member; cases member)
    shell.unique shell.sameLedger
    (by intro id reached allowed; simpa only [shell.canonical] using allowed)
    (by intro currentContext childScope id lowered reached given; simpa only [shell.canonical] using given)
    shell.syntaxTree (shell.canonical.symm ▸ shell.syntaxTree) shell.projection
    (SiteShell.extraction principal root expressionSyntax site shell policyEq bodyEq reasonEq) shell.nativeTyped
  exact ⟨body, entryEq, readFuelEq,
    .recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment⟩

variable {function : Dynamic.Closure} {currentScope : SourceCoreLocalCell.Scope}
  {currentAdministrative : Core.Context} {code : Code compiled.indexed function currentScope currentAdministrative}
  {support : CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support code}

/-- The real selected dictionary and same accepted child family remain
available after recapture; there is no certificate equality premise. -/
theorem Collected.factories
    (collected : Collected principal root expressionSyntax site code support) :
    support.method = method ∧ HEq support.principal principal ∧
      support.expressionSyntax = expressionSyntax ∧ support.certificates = certificates root expressionSyntax := by
  cases collected with
  | recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment =>
    exact ⟨rfl, HEq.rfl, rfl, rfl⟩

theorem Collected.prepared
    (collected : Collected principal root expressionSyntax site code support) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt code support := by
  cases collected with
  | recaptured shell body policyEq bodyEq reasonEq entryEq readFuelEq binderPolicy environment =>
    exact .recaptured principal site expressionSyntax (certificates root expressionSyntax)
      shell.issued shell.diagnosticPolicy body binderPolicy shell.compilerPolicy
      (CallableIndexedOwnedContextualLambdaProvenance.BodyView.of_eq shell.canonical) environment

end Principal

section ActualRoot
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- The full authentic method record selects the root policy from the real
contextual pass once. No top-level function instantiation or Header is invented. -/
theorem root_of_accepted
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext principal.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals principal.cached.compilation.parents principal.cached.compilation.own.assignments
      principal.cached.diagnostics (context compiled.indexed principal.named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    Nonempty (RootPolicyReceipt (compiled := compiled) principal.named principal.cached.diagnostics principal.cached.code
      principal.cached.compilation fuel view scope id reasonAt lowered) :=
  RootPolicyReceipt.of_accepted principal.cached.compilation principal.record accepted

end ActualRoot
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalCompilerChildren
