import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryBodyProjection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames

/-! A prepared principal packet retains the actual selected method, dictionary
and cached named compilation. Its one JointBody projects to existing method
support with no ordinary Header. Actual method Sites establish provenance;
prepared flow uses owning issuance and reached diagnostic interpretation at the
receiving registry. Prospective positive leaves retain preparation before
forward erasure. Existing plain StaticMember leaves cannot be upgraded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody)
open CallableIndexedOwnedContextualLambdaSourceDiagnostics (IssuedSource)
open CallableIndexedOwnedPreparedOrdinaryBodyProjection (actualTree bodyWith)
open CallableIndexedOwnedTypedLambdaStaticBody (Body)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The selected method authority accompanies its actual prepared body. -/
structure Support (code : Code compiled.indexed function scope administrative) where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source principal.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed principal.named
  active : code.active = []
  issued : IssuedSource compiled code.compilation.owner function.source
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : JointBody principal.cached.compilation code (Program.ofChecked compiled.sourceProgram)
    expressionSyntax certificates diagnosticPolicy
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault

section Site
variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary environment scope administrative)

/-- The complete real method selector and same-Site joint body are retained. -/
def Support.of_site
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled site.code.compilation.owner
      (CallableIndexedNamedGeneration.source principal.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
      expressionSyntax certificates diagnosticPolicy
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault) : Support site.code :=
  ⟨method, principal, expressionSyntax, certificates, rfl, site.compilation, site.active,
    issued, diagnosticPolicy, body⟩

end Site

variable {code : Code compiled.indexed function scope administrative} (support : Support code)

/-- Recapture retains method selection, dictionary, preparation and exact flow. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) where
  method := support.method
  principal := support.principal
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  issued := support.issued
  diagnosticPolicy := support.diagnosticPolicy
  body := {
    toBody := {
      toContext := RecursiveNamedLambdaFormationHeads.recaptureContext
        (values := .initial compiled.compatible.checked) code support.body.toBody.toContext environment
      frame := RecursiveNamedLambdaFormationHeads.recaptureFrame support.body.frame environment
      readFuel := support.body.readFuel, flow := support.body.flow, projection := support.body.projection
      emitted := support.body.emitted, tree := support.body.tree, valid := support.body.valid
      unique := support.body.unique, syntaxTree := support.body.syntaxTree }
    recipe := support.body.recipe, generated := support.body.generated
    actual := support.body.actual, prepared := support.body.prepared }

/-- The genuine emitted hook's full method Source seed remains explicit. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.principal.named

/-- The original selected Site and its method dictionary establish provenance. -/
inductive PreparedAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) → Support code → Prop where
  | recaptured {method : ExecutableImplMethods.CheckedMethod}
      (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
        context principal.dictionary [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (issued : IssuedSource compiled site.code.compilation.owner
        (CallableIndexedNamedGeneration.source principal.named))
      (diagnosticPolicy : AssignmentDiagnosticPolicy)
      (body : JointBody principal.cached.compilation site.code (Program.ofChecked compiled.sourceProgram)
        expressionSyntax certificates diagnosticPolicy
        issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
      (binderPolicy : CallableIndexedOwnedContextualLambdaProvenance.BinderPolicy principal.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained principal.named site.code)
      (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView site.code)
      (environment : Dynamic.Environment) :
      PreparedAt (RecursiveNamedLambdaFormationHeads.recaptureCode
        (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) site.code environment)
        ((Support.of_site principal site expressionSyntax certificates issued diagnosticPolicy body).recapture environment)

section Projection
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)

/-- Forward projection retains the full Principal and dictionary verbatim. -/
def Support.plain : CallableIndexedOwnedMethodLambdaSupport.Support code bodyRegistry faults where
  method := support.method
  principal := support.principal
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  body := bodyWith support.body actualSites sites

theorem Support.plain_typed :
    Body.of_body_with (support.plain actualSites sites).body support.body.syntaxTree = support.body.toBody := rfl

theorem Support.plain_source_origin {history : History code} (origin : SourceOrigin support history) :
    CallableIndexedOwnedMethodLambdaSupport.SourceOrigin (support.plain actualSites sites) history := ⟨origin.metadata⟩

include support in
/-- Method authority remains the original selected trait implementation. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original support.principal.record

theorem PreparedAt.plain_provenance (prepared : PreparedAt code support) :
    CallableIndexedOwnedContextualLambdaProvenance.PrincipalAt code (support.plain actualSites sites) := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy bodyView environment =>
    exact .recaptured principal site expressionSyntax certificates
      (bodyWith body actualSites sites) binderPolicy
      (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe principal.cached.compilation body.recipe)
      compilerPolicy bodyView body.syntaxTree environment

theorem PreparedAt.projected_bindings (prepared : PreparedAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases prepared with
  | recaptured principal site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy bodyView environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

end Projection

section Flow
variable
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (sameCode : Code compiled.indexed function scope captured.administrative)
  (prepared : Support sameCode)
  (baseActualSites : (actualTree prepared.body).CatalogSites .reachable bodyRegistry faults)
  (baseSites : prepared.body.tree.CatalogSites .reachable bodyRegistry faults)
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {registry : SourceCoreRawMetadata.Registry}
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop}
  (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : prepared.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep
    prepared.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep
    prepared.issued.assignments reason token → faults reason token)
  (interprets : ∀ context,
    Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := prepared.certificates prepared.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        prepared.diagnosticPolicy function.source prepared.issued.invalidOperand)
      (faults := faults) (registry := registry) prepared.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) functions table)

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Original prepared head/loop producers discharge same-body flow preservation
at the receiving registry from strict expression children and reached tables. -/
theorem preserves_flow (budget : Nat)
    (meaning : ∀ context,
      Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
      RecursiveNamedHeaderContracts.AtMost budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context function.evidence function.source
          (prepared.certificates prepared.body.readFuel function.source context) faults size)) :
    RecursiveNamedHeaderContracts.AtMost budget
      (FlowPreserves captured sameCode
        (Body.of_body_with (prepared.plain baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [Support.plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.preserves_flow
    prepared.principal.cached.compilation captured sameCode prepared.issued prepared.body functions extension faithful
    observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget meaning

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets in
/-- Native flow keeps its own strict grade and independent Source completion. -/
theorem reflects_flow (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context,
      Validity (program := Program.ofChecked compiled.sourceProgram) captured sameCode context →
      RecursiveNamedCatalogInvocationBounds.Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
          context function.evidence function.source
          (prepared.certificates prepared.body.readFuel function.source context) faults size)) :
    RecursiveNamedCatalogInvocationBounds.Below budget
      (FlowReflects captured sameCode
        (Body.of_body_with (prepared.plain baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [Support.plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.reflects_flow
    prepared.principal.cached.compilation captured sameCode prepared.issued prepared.body functions extension faithful
    observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes reflection

end Flow

section Receipts
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A prospective method-authorized leaf keeps preparation beside its actual
captured method Source, emitted history and principal leading bundle. -/
inductive Receipt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code)
      (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
      (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
      (origin : SourceOrigin support history) (prepared : PreparedAt code support)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions) :
      Receipt headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- Existing typed association is a forward projection of the selected method. -/
def Receipt.forget
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore := by
  cases receipt with
  | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
    exact .principal owner captured code history (support.plain actualSites sites)
      (support.plain_source_origin actualSites sites origin) globals leading referenceIndex typed
      (PreparedAt.plain_provenance support actualSites sites prepared)

/-- Real capture and runtime-typing extension preserves all method authority. -/
def Receipt.extend
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Receipt headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases receipt with
  | principal owner captured code history support actualSites sites origin prepared globals leading referenceIndex typed =>
    exact .principal owner (captured.extend maps worlds) code history support actualSites sites origin prepared
      globals leading referenceIndex (typed.weaken worlds)

end Receipts

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPrincipalLambdaSupport
