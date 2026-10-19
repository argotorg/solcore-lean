import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodyStaticReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedBranchingTree

/-! The selected physical closure keeps its actual compiler flow and reached
place receipts. The older ordinary support retains its original contract. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaProvenance (BinderPolicy)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

abbrev Produced := @CallableIndexedOwnedPreparedOrdinaryLambdaSupport.Produced

/-- One accepted body keeps both its actual compiler callback and original
Source tree. Capture replacement changes none of these static witnesses. -/
structure Body {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (namedCompilation : Compilation compiled.indexed named diagnostics namedCode)
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
    (code : Code compiled.indexed function scope administrative) (program : Program)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word)
    (invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word)
    (missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word)
    extends CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code where
  frame : Dynamic.ClosureFrame program function
  readFuel : Nat
  flow : Expr
  projection : compiled.compatible.checked.catalog.project function.resultType = .ok code.receipt.resultCore
  emitted : code.receipt.body = CompatibleStatements.finish code.receipt.resultCore flow
    code.compilation.internalReason code.compilation.internalReason
  valid : CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  unique : NodeOccurrencesUnique function.source
  syntaxTree : GenericImperativeMatch.PreparedSyntax function.source (expressionSyntax function.source)
    context (.statements true function.body) function.resultType
  shape : CallableIndexedOwnedPreparedStagedBranchingTree.Shape function.source true function.body
  view : code.view = function.source
  recipe : BodyRecipe namedCompilation code
  generated : SourceCoreLoops.lowerFlowStatementsWithPolicy (bodyPolicy namedCompilation code) code.fuel code.view
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    function.body code.receipt.resultCore code.reasonAt true code.compilation.internalReason = .ok flow
  extraction : PreparedLambdaBodyStaticReceipts.PreparedExtraction compiled.indexed.layouts code.compilation.owner code.active
    compiled.indexed.ancestry.layout.frame compiled.indexed.base.globals.length code.allocationError
    (.initial compiled.compatible.checked) function.source invalidOperand invalidUnary invalidProjection missingDefault
    (expressionSyntax function.source) (certificates readFuel function.source)
    compiled.indexed.layouts.definitions administrative context
    (code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope)
    (.statements true function.body) function.resultType code.receipt.resultCore flow

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- Every field belongs to this literal Code and genuine owning Source. -/
structure Support (code : Code compiled.indexed function scope administrative) where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  namedCode : Expr
  namedCompilation : Compilation compiled.indexed caller.named diagnostics namedCode
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed caller.named
  active : code.active = []
  issued : IssuedSource compiled code.compilation.owner function.source
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : Body namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault

variable (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  (namedCompilation : Compilation compiled.indexed caller.named diagnostics namedCode)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  (site : Site compiled.indexed caller.named parameters result statements context evidence environment scope administrative)

/-- Independent same-Site static body and issuance construct support directly. -/
def Support.of_site
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (issued : IssuedSource compiled site.code.compilation.owner (CallableIndexedNamedGeneration.source caller.named))
    (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (body : Body namedCompilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
      issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault) :
    Support site.code :=
  ⟨caller, diagnostics, namedCode, namedCompilation, expressionSyntax, certificates, rfl, site.compilation, site.active,
    issued, diagnosticPolicy, body⟩

variable {code : Code compiled.indexed function scope administrative} (support : Support code)

include support in
/-- Source attribution follows from the retained actual Header. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)

include support in
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Static body, recipe and prepared packet keep their identical indices. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
      (indexed := compiled.indexed) code environment) where
  caller := support.caller
  diagnostics := support.diagnostics
  namedCode := support.namedCode
  namedCompilation := support.namedCompilation
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  issued := support.issued
  diagnosticPolicy := support.diagnosticPolicy
  body := {
    toContext := RecursiveNamedLambdaFormationHeads.recaptureContext (values := .initial compiled.compatible.checked) code support.body.toContext environment
    frame := RecursiveNamedLambdaFormationHeads.recaptureFrame support.body.frame environment
    readFuel := support.body.readFuel, flow := support.body.flow, projection := support.body.projection
    emitted := support.body.emitted, valid := support.body.valid
    unique := support.body.unique, syntaxTree := support.body.syntaxTree, shape := support.body.shape
    view := support.body.view, recipe := support.body.recipe, generated := support.body.generated
    extraction := support.body.extraction }

/-- Captured history keeps its full original compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = state support.caller.named

/-- Output indices keep the exact seed; no Site is reconstructed from Code. -/
inductive PreparedAt : {function : Dynamic.Closure} → {scope : SourceCoreLocalCell.Scope} →
    {administrative : Core.Context} → (code : Code compiled.indexed function scope administrative) → Support code → Prop where
  | recaptured
      (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
      {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
      (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
      {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
      {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
      {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
      (site : Site compiled.indexed caller.named parameters result statements context evidence [] scope administrative)
      (expressionSyntax : TypedSource → ExpressionId → Prop)
      (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
      (issued : IssuedSource compiled site.code.compilation.owner (CallableIndexedNamedGeneration.source caller.named))
      (diagnosticPolicy : AssignmentDiagnosticPolicy)
      (body : Body compilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
        issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
      (binderPolicy : BinderPolicy caller.named site.code)
      (compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained caller.named site.code)
      (issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained caller.named site.code)
      (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView site.code)
      (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons site.code caller.named)
      (declarations : CompatibleExpressionReads.ScopeDeclarations
        (CallableIndexedNamedGeneration.source caller.named) scope context)
      (environment : Dynamic.Environment) :
      PreparedAt (RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) site.code environment)
        ((Support.of_site caller compilation site expressionSyntax certificates issued diagnosticPolicy body).recapture environment)

/-- Genuine seed policy and Source metadata identify this ordered binder row. -/
theorem PreparedAt.projected_bindings (receipt : PreparedAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

end Solcore.SourceSemantics.CoreLowering.PreparedLambdaBodySupport
