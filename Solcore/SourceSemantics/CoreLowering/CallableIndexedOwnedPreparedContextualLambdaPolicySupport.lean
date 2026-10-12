import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedQualifiedFormationReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-! Prepared compiler packets retain the complete policy at their one actual Site.
The input named Compilation remains concrete. Prepared provenance retains
the same policy and body view. An existing qualification Facet carries
the policy proof through qualified payloads and heaps. Raw body preparation,
catalog Sites, current packet authority and original policy metadata remain
independent static inputs. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualLambdaPolicySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The body equation and original input Compilation belong to this literal Site. -/
structure ProducedWithPolicy {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (parameters : List TypedBinder) (result : TypeSystem.Ty) (statements : List StatementId)
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  site : Site compiled.indexed named parameters result statements context evidence [] scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy named site.code
  recipe : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation site.code
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code

/-- Forward the policy proof without selecting another Site or Compilation. -/
def ProducedWithPolicy.forget {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed named diagnostics namedCode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : ProducedWithPolicy compilation parameters result statements context evidence
      scope administrative id lowered) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced (compiled := compiled)
      named parameters result statements context evidence scope administrative id lowered where
  diagnostics := diagnostics
  namedCode := namedCode
  compilation := compilation
  site := produced.site
  identifier := produced.identifier
  emitted := produced.emitted
  binderPolicy := produced.binderPolicy
  recipe := produced.recipe
  compilerPolicy := produced.policyRecipe

/-- Eliminate one accepted outer bind and keep all proofs at its same chosen Site. -/
theorem ProducedWithPolicy.of_contextual
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {id : ExpressionId} {sourceNode node : ExpressionNode} {parameters : List TypedBinder}
    {result : TypeSystem.Ty} {body : List StatementId} {reported : Ty}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source named) view)
    (sourceFound : (source named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result body)
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) lowered.expression
      (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions) :
    Nonempty (ProducedWithPolicy compilation parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, recipe, policyRecipe⟩ :=
    CallableIndexedLambdaGeneration.of_contextual_with_policy_recipe
      compiled.indexed compilation record sourceContext evidence [] profile viewOfSource
      sourceFound sourceForm found form owner requirements coercions ordinary read accepted typed
  exact ⟨⟨site, identifier, emitted, binderPolicy, recipe, policyRecipe⟩⟩

/-- The existing qualification relation inspects the exact original Support. -/
def policyFacet (compiled : SourceCoreUnifiedCompilation.Compiled) :
    CallableIndexedOwnedPreparedContextualQualification.Facet compiled where
  ordinary := fun code support =>
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.caller.named code
  principal := fun code support =>
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained support.principal.named code

/-- Recapture changes the environment while retaining every compiler-policy field. -/
theorem retained_recapture {named : Named} {function : Dynamic.Closure}
    {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    {code : Code compiled.indexed function scope administrative}
    (retained : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named
      (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, sameCompilation⟩

/-- A companion proof belongs to the existing complete prepared ordinary Formation. -/
structure OrdinaryWithPolicy
    (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
    (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr)
    extends CallableIndexedOwnedPreparedOrdinaryLambdaFormation.Formation
      caller context evidence scope id lowered where
  policyRecipe : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named produced.site.code

/-- The complete genuine JointBody is indexed by the one supplied Compilation. -/
def ordinary_of_produced
    (caller : Header compiled (Program.ofChecked compiled.sourceProgram))
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (produced : ProducedWithPolicy compilation parameters result statements context evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      id lowered)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : JointBody compilation produced.site.code (Program.ofChecked compiled.sourceProgram)
      expressionSyntax certificates diagnosticPolicy
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
    (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
    (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
    (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope context)
    (sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements context evidence []))
    (ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements
      produced.site.code.sourceNode.coercions [])
    (coercions : produced.site.code.sourceNode.coercions = []) :
    OrdinaryWithPolicy caller context evidence scope id lowered where
  toFormation := {
    parameters := parameters, result := result, statements := statements
    produced := produced.forget, expressionSyntax := expressionSyntax, certificates := certificates
    issued := issued, diagnosticPolicy := diagnosticPolicy, body := body
    bodyView := bodyView, bodyReasons := bodyReasons, declarations := declarations, sourceType := sourceType, ordinary := ordinary, coercions := coercions }
  policyRecipe := produced.policyRecipe

/-- Preparation and policy qualification refer to the same ordinary Code and Support. -/
theorem OrdinaryWithPolicy.prepared_at
    {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
    {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : OrdinaryWithPolicy caller context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedOrdinaryLambdaSupport.PreparedAt
      (head.toFormation.code environment) (head.toFormation.support environment) ∧
    (policyFacet compiled).ordinary (head.toFormation.code environment) (head.toFormation.support environment) :=
  ⟨head.toFormation.prepared environment, retained_recapture head.policyRecipe environment⟩

/-- A method seed fixes its actual cached Compilation and dictionary before recapture. -/
structure PrincipalWithPolicy {method : ExecutableImplMethods.CheckedMethod}
    (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
    (context : SourceSemantics.Context) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  produced : ProducedWithPolicy principal.cached.compilation parameters result statements
    context principal.dictionary scope (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) id lowered
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : IssuedSource compiled produced.site.code.compilation.owner (source principal.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : JointBody principal.cached.compilation produced.site.code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax certificates diagnosticPolicy
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
  bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code
  sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
    (closure principal.named parameters result statements context principal.dictionary [])
  ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements
    produced.site.code.sourceNode.coercions []
  coercions : produced.site.code.sourceNode.coercions = []

def PrincipalWithPolicy.function {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    Dynamic.Closure :=
  closure principal.named head.parameters head.result head.statements context principal.dictionary environment

def PrincipalWithPolicy.code {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    Code compiled.indexed (head.function environment) scope
      (CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode
    (values := .initial compiled.compatible.checked) head.produced.site.code environment

def PrincipalWithPolicy.support {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support (head.code environment) :=
  (CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.of_site principal head.produced.site
    head.expressionSyntax head.certificates head.issued head.diagnosticPolicy head.body).recapture environment

/-- Both witnesses preserve the original selected method and same cached body. -/
theorem PrincipalWithPolicy.prepared_at {method : ExecutableImplMethods.CheckedMethod}
    {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
    {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
    {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
    (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment) :
    CallableIndexedOwnedPreparedPrincipalLambdaSupport.PreparedAt
      (head.code environment) (head.support environment) ∧
    (policyFacet compiled).principal (head.code environment) (head.support environment) := by
  refine ⟨?_, retained_recapture head.produced.policyRecipe environment⟩
  exact .recaptured principal head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy head.produced.policyRecipe head.bodyView environment

/-- Normalize only the genuine administrative equality; all capture data is copied. -/
def capture_at {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (administrative : Core.Context) (same : captured.administrative = administrative) :
    Captures compiled.indexed mapping world scope function.captured actual where
  administrative := administrative
  canonical := captured.canonical
  actualContext := captured.actualContext
  embedding := captured.embedding
  represented := by rw [← same]; exact captured.represented
  agrees := captured.agrees
  respects := by rw [← same]; exact captured.respects
  typed := captured.typed

namespace Ordinary
variable {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : OrdinaryWithPolicy caller context evidence scope id lowered) (environment : Dynamic.Environment)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual canonical : Environment}
  {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (head.toFormation.function environment).captured actual)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree
    (head.toFormation.support environment).body).CatalogSites .reachable bodyRegistry faults)
  (sites : (head.toFormation.support environment).body.tree.CatalogSites .reachable bodyRegistry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

local notation "code" => head.toFormation.code environment
local notation "support" => head.toFormation.support environment
local notation "capturedAt" => capture_at captured _ prefixContext
local notation "plain" => CallableIndexedOwnedPreparedOrdinaryBodyProjection.plain support actualSites sites
local notation "history" => CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.history_at
  capturedAt code plain owner initial packet
local notation "carrier" => value code (CallableIndexedLambdaValues.Captures.embedding capturedAt) (History.native history) actual

include head environment captured prefixContext actualSites sites packet profile observed in
/-- The existing formation endpoint receives the derived same-Code policy qualification. -/
theorem formation_member (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      (head.toFormation.function environment).context (head.toFormation.function environment).evidence
      (head.toFormation.function environment).source (head.toFormation.function environment).captured
      heap (code).id (.closure (head.toFormation.function environment)) heap ∧
    Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) (.inRight .word carrier) store ∧
    CallableIndexedOwnedPreparedContextualQualification.StaticMember (policyFacet compiled)
      headers keys bodyRegistry faults mapping world (head.toFormation.function environment) carrier
      (code).receipt.loweredParameters (code).receipt.parameterCore (code).receipt.resultCore ∧
    (∀ result finalStore, Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  exact CallableIndexedOwnedPreparedQualifiedFormationReceipts.Ordinary.formation_member
    capturedAt code owner (policyFacet compiled) profile support (head.prepared_at environment).2
    actualSites sites (head.prepared_at environment).1 initial packet rfl observed stored
    head.toFormation.ordinary head.toFormation.coercions

end Ordinary

namespace Principal
variable {method : ExecutableImplMethods.CheckedMethod}
  {principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method}
  {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  (head : PrincipalWithPolicy principal context scope id lowered) (environment : Dynamic.Environment)
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {actual : Environment} {heap : Dynamic.Heap} {store : Store}
  (captured : Captures compiled.indexed mapping world scope (head.function environment).captured actual)
  (prefixContext : captured.administrative = CallableIndexedOwnedMethodPrincipalCaptures.nativePrefix principal)
  (actualSites : (CallableIndexedOwnedPreparedOrdinaryBodyProjection.actualTree
    (head.support environment).body).CatalogSites .reachable bodyRegistry faults)
  (sites : (head.support environment).body.tree.CatalogSites .reachable bodyRegistry faults)
  (owner : OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, captured.canonical⟩)
  (packet : CallableIndexedOwnedOriginCanonicalState.Packet owner principal.named _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

local notation "code" => head.code environment
local notation "support" => head.support environment
local notation "capturedAt" => capture_at captured _ prefixContext
local notation "plain" => CallableIndexedOwnedPreparedPrincipalLambdaSupport.Support.plain support actualSites sites
local notation "history" => CallableIndexedOwnedMethodLambdaFormationReceipts.history_at
  capturedAt code plain owner initial packet
local notation "carrier" => value code (CallableIndexedLambdaValues.Captures.embedding capturedAt) (History.native history) actual

include head environment captured prefixContext actualSites sites packet profile in
/-- The principal endpoint retains its original method, dictionary and cached Compilation. -/
theorem formation_member (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      (head.function environment).context (head.function environment).evidence
      (head.function environment).source (head.function environment).captured
      heap (code).id (.closure (head.function environment)) heap ∧
    Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) (.inRight .word carrier) store ∧
    CallableIndexedOwnedPreparedContextualQualification.StaticMember (policyFacet compiled)
      headers keys bodyRegistry faults mapping world (head.function environment) carrier
      (code).receipt.loweredParameters (code).receipt.parameterCore (code).receipt.resultCore ∧
    (∀ result finalStore, Evaluates actual store ((code).lowered.expression.rename (capturedAt).embedding) result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  exact CallableIndexedOwnedPreparedQualifiedFormationReceipts.Principal.formation_member
    capturedAt code owner (policyFacet compiled) profile support (head.prepared_at environment).2
    actualSites sites (head.prepared_at environment).1 initial packet stored head.ordinary head.coercions

end Principal
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedContextualLambdaPolicySupport
