import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts

/-! Actual owning Source and one contextual Site retain the prepared joint
body. Recapture changes only the stored Source environment. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedContextualLambdaProvenance (BinderPolicy)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

structure Produced (named : Named) (parameters : List TypedBinder) (result : TypeSystem.Ty)
    (statements : List StatementId) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (administrative : Core.Context)
    (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  diagnostics : SourceCoreDataPlaceFaultSites.Program
  namedCode : Expr
  compilation : Compilation compiled.indexed named diagnostics namedCode
  site : Site compiled.indexed named parameters result statements context evidence [] scope administrative
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  binderPolicy : BinderPolicy named site.code

  recipe : BodyRecipe compilation site.code

/-- This calls the original contextual producer once and keeps its exact
selected Site and policy equation together. -/
theorem of_contextual
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
    Nonempty (Produced (compiled := compiled) named parameters result body sourceContext evidence
      scope administrative id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, recipe⟩ := CallableIndexedLambdaGeneration.of_contextual_with_body_recipe
    compiled.indexed compilation record sourceContext evidence [] profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  exact ⟨⟨diagnostics, namedCode, compilation, site, identifier, emitted, binderPolicy, recipe⟩⟩


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
  body : JointBody namedCompilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault

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
    (body : JointBody namedCompilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
      diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault) :
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
    toBody := {
      toContext := RecursiveNamedLambdaFormationHeads.recaptureContext (values := .initial compiled.compatible.checked) code support.body.toBody.toContext environment
      frame := RecursiveNamedLambdaFormationHeads.recaptureFrame support.body.frame environment
      readFuel := support.body.readFuel, flow := support.body.flow, projection := support.body.projection
      emitted := support.body.emitted, tree := support.body.tree, valid := support.body.valid
      unique := support.body.unique, syntaxTree := support.body.syntaxTree }
    recipe := support.body.recipe, generated := support.body.generated
    actual := support.body.actual, prepared := support.body.prepared }

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
      (body : JointBody compilation site.code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
        diagnosticPolicy issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault)
      (binderPolicy : BinderPolicy caller.named site.code)
      (environment : Dynamic.Environment) :
      PreparedAt (RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
        (indexed := compiled.indexed) site.code environment)
        ((Support.of_site caller compilation site expressionSyntax certificates issued diagnosticPolicy body).recapture environment)

/-- Genuine seed policy and Source metadata identify this ordered binder row. -/
theorem PreparedAt.projected_bindings (receipt : PreparedAt code support) :
    ∀ binding ∈ code.receipt.loweredParameters,
      compiled.compatible.checked.catalog.project binding.1.scheme.body = .ok binding.2 := by
  cases receipt with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy environment =>
    exact CallableIndexedOwnedLambdaBinderProjections.Site.projected_bindings site binderPolicy body.extended

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
