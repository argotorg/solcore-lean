import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedProducer
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPreparedBodyBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaProvenance
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaBinderProjections
import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.LexicalBodies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFunctionValues
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogEntries
import Solcore.SourceSemantics.CoreLowering.BuiltinLexicalStatements
import Solcore.SourceSemantics.CoreLowering.TypedLexicalWhileNativeCertificates
import Solcore.SourceSemantics.CoreLowering.CompatibleMatchNativeReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts

/-!
# Prepared callables: ordinary lambdas

Support, values, formation, receipts and invocation of ordinary lambdas.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
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
  compilerPolicy : CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named site.code
  issuedRecipe : CallableIndexedOwnedContextualLambdaIssuedRecipes.Retained named site.code

/-- This calls the original contextual producer once and keeps its exact
selected Site and policy equation together. -/
theorem of_contextual
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
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
  obtain ⟨site, identifier, emitted, binderPolicy, recipe, issuedRecipe, _view, _reason⟩ := CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact
    compiled.indexed compilation issued record sourceContext evidence [] profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  exact ⟨⟨diagnostics, namedCode, compilation, site, identifier, emitted, binderPolicy, recipe, issuedRecipe.policy_recipe, issuedRecipe⟩⟩


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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
/-! Formation retains a prepared packet before storage. Exact selection keeps
prior General alternatives explicit; no legacy closure is upgraded. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CompatibleEquality
open CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionValues (Header Key OwnedKey)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
variable {compiled : SourceCoreUnifiedCompilation.Compiled}

inductive Represents (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
      (related : CallableIndexedOwnedGeneralLambdaValues.Represents headers keys registry faults mapping world sourceType source native type) :
      Represents headers keys registry faults mapping world sourceType source native type
  | prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code body) :
      Represents headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)

variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {native : Value} {type : Ty}

theorem Represents.forget (related : Represents headers keys registry faults mapping world sourceType source native type) :
    CallableIndexedLambdaValues.Represents compiled.indexed mapping world sourceType source native type := by
  cases related with
  | prior original => exact original.forget
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .lambda captured code history typed

def model (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed) where
  Represents := fun _ mapping world => Represents headers keys bodyRegistry faults mapping world
  projection := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).projection
    (registry := bodyRegistry) related.forget
  runtime_hasType := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := bodyRegistry) related.forget
  source_function := fun related => (CallableIndexedLambdaValues.model compiled.indexed profile).source_function
    (registry := bodyRegistry) related.forget
  extend := by
    intro registry futureRegistry mapping futureMap world futureWorld sourceType source native type related registries maps worlds
    cases related with
    | prior original => exact .prior ((CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).extend
        original registries maps worlds)
    | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
      exact .prepared_ordinary owner (captured.extend maps worlds) code history body origin prefixContext globals referenceIndex
        (typed.weaken worlds) prepared

theorem includes_general (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    (CallableIndexedOwnedGeneralLambdaValues.model headers keys bodyRegistry faults profile).Includes
      (model headers keys bodyRegistry faults profile) := fun related => .prior related

theorem observations (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionObservations compiled.compatible.checked.catalog (model headers keys bodyRegistry faults profile)
      (CallableIndexedLambdaValues.Identity compiled.indexed) := by
  intro registry mapping world sourceType source native type related
  exact CallableIndexedLambdaValues.observations compiled.indexed profile (registry := registry) related.forget

theorem runtime_views (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    FunctionRuntimeViews (model headers keys bodyRegistry faults profile) := by
  intro registry mapping world parameter result source native type related
  exact CallableIndexedLambdaValues.runtime_views compiled.indexed profile (registry := registry) related.forget

theorem Represents.map_keys {futureKeys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
    (embedding : CallableIndexedOwnedFunctionValues.KeyEmbedding keys futureKeys)
    (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Represents headers futureKeys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (original.map_keys embedding)
  | @prepared_ordinary function scope actual owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    have actualGlobals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers (embedding.map owner).key.locations 1 scope captured.canonical (embedding.map owner).key.frameLocation := by
      rw [embedding.same owner]
      exact globals
    exact .prepared_ordinary (embedding.map owner) captured code history body origin prefixContext actualGlobals referenceIndex typed prepared

/-- The prior branch preserves every original alternative and makes no
prepared-body promise for it. -/
inductive Selection (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) : TypeSystem.Ty → Dynamic.Value → Value → Ty → Prop where
  | prior {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {native : Value} {type : Ty}
      (selected : CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world sourceType source native type) :
      Selection headers keys registry faults mapping world sourceType source native type
  | prepared_ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (body : Support code) (origin : SourceOrigin body history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) body.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (prepared : PreparedAt code body) :
      Selection headers keys registry faults mapping world (FunctionValues.sourceType function) (.closure function)
        (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)


theorem Selection.of_represents (related : Represents headers keys registry faults mapping world sourceType source native type) :
    Selection headers keys registry faults mapping world sourceType source native type := by
  cases related with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.of_represents original)
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared

theorem Selection.represents (selected : Selection headers keys registry faults mapping world sourceType source native type) :
    Represents headers keys registry faults mapping world sourceType source native type := by
  cases selected with
  | prior original => exact .prior (CallableIndexedOwnedGeneralFunctionSelection.represents original)
  | prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared =>
    exact .prepared_ordinary owner captured code history body origin prefixContext globals referenceIndex typed prepared

section Observed
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {raw : TypeSystem.Ty} {function : Dynamic.Closure}

def Selected : Prop := ∃ parameter result,
  SourceCoreRawMetadata.runtimeType raw = SourceCoreRawMetadata.runtimeType (.function parameter result) ∧
  Selection headers keys registry faults mapping world (.function parameter result) (.closure function) native type

private theorem selected_of_representation {sourceValue : Dynamic.Value}
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      mapping world raw sourceValue native type) (closure : sourceValue = .closure function) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => cases closure
  | function value =>
    cases closure
    exact ⟨_, _, rfl, Selection.of_represents value⟩
  | compatible same inner ih =>
    obtain ⟨parameter, result, view, selected⟩ := ih closure
    exact ⟨parameter, result, same.trans view, selected⟩
  | nil | cons | empty | entry | absent | present => trivial

theorem selected_of_value
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      mapping world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := mapping) (world := world) (raw := raw) (function := function) (native := native) (type := type) :=
  selected_of_representation profile related rfl

universe u
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (CallableIndexedOwnedFunctionState.Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context) {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index)

/-- Source typing and current owned readiness come from this exact post. -/
theorem selected_at_success
    (post : CallableIndexedOwnedSourceAdmission.PostAdmission bridge context raw (.value (.closure function)) reached)
    (related : ValueRep compiled.compatible.checked registry (model headers keys registry faults profile)
      index.mapping index.world raw (.closure function) native type) :
    Selected (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (mapping := index.mapping) (world := index.world) (raw := raw) (function := function) (native := native) (type := type) ∧
    Dynamic.ValueHasType context index.heap (.closure function) raw ∧
    CallableIndexedOwnedSourceAdmission.Admission bridge context reached := by
  exact ⟨selected_of_value profile related, post.at_value⟩
end Observed
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
/-! Genuine unrestricted ordinary support forms a closure at its actual
nested Header packet. Source attribution and the full carried seed stay original.
Forward inclusion transfers only the new closure, with one function model for
all actual input/output heaps. The formation copies the captured cells, so the
reached packet is the original one transported to the formed state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission

section Seed
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- The actual chosen contextual seed carries its prepared body before any
capture value exists. No execution law or old body package is a field. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  produced : Produced (compiled := compiled) caller.named parameters result statements context evidence scope
    (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : CallableIndexedOwnedContextualLambdaSourceDiagnostics.IssuedSource compiled produced.site.code.compilation.owner
    (CallableIndexedNamedGeneration.source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  body : CallableIndexedOwnedContextualLambdaJointStaticReceipts.JointBody produced.compilation produced.site.code
    (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates diagnosticPolicy
    issued.invalidOperand issued.invalidUnary issued.invalidProjection issued.missingDefault
  bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations
    (CallableIndexedNamedGeneration.source caller.named) scope context
  sourceType : produced.site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  ordinary : Dynamic.OrdinaryRequirementLayout produced.site.code.sourceNode.requirements produced.site.code.sourceNode.coercions []
  coercions : produced.site.code.sourceNode.coercions = []

variable {caller context evidence}

def Formation.function {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements context evidence environment

def Formation.code {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) :=
  RecursiveNamedLambdaFormationHeads.recaptureCode (values := .initial compiled.compatible.checked)
    head.produced.site.code environment

def Formation.support {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) :=
  (Support.of_site caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body).recapture environment

theorem Formation.prepared {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : PreparedAt (head.code environment) (head.support environment) :=
  .recaptured caller head.produced.compilation head.produced.site head.expressionSyntax head.certificates
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy head.produced.compilerPolicy head.produced.issuedRecipe head.bodyView head.bodyReasons head.declarations environment

/-- The chosen Site's lambda copies its captures at creation. -/
theorem Formation.snapshots {scope id lowered} (head : Formation caller context evidence scope id lowered)
    (environment : Dynamic.Environment) :
    (head.code environment).policy.snapshotLambda (head.code environment).id = true :=
  head.produced.site.snapshots
end Seed

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The prepared seed of a code is the seed of the same code over other
captures. -/
theorem prepared_recapture {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) (environment : Dynamic.Environment) :
    PreparedAt (code.recapture environment) (support.recapture environment) := by
  cases prepared with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations _ =>
    exact .recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations environment

/-- A prepared code is the lambda of a chosen Site, which copies its captures. -/
theorem prepared_snapshots {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {administrative : Core.Context} {code : Code compiled.indexed function scope administrative}
    {support : Support code} (prepared : PreparedAt code support) :
    code.policy.snapshotLambda code.id = true := by
  cases prepared with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy body binderPolicy
      compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
    exact site.snapshots

variable
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store} {actual canonical : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured actual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code)
  (prepared : PreparedAt code support)
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (initial : State headers keys ⟨scope, mapping, world, heap, store, canonical⟩)
  (packet : CallableIndexedOwnedNestedCanonicalState.Packet owner support.caller _ initial)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) support.caller)
  (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)

/-- Full captured history comes from this actual Header row and genuine seed. -/
def history_at : History code where
  native := (initial.rows owner.position).authority.current
  ghost := (initial.rows owner.position).authority.ghost
  metadata := CallableIndexedNamedGeneration.state support.caller.named
  carried := packet.carried
  source := support.source.symm
  owner := by rw [support.compilation]; rfl
  active := support.active.symm

/-- The original named Source seed is retained by construction. -/
theorem source_origin : SourceOrigin support (history_at captured code support owner initial packet) := ⟨rfl⟩

include support in
/-- Actual ordinary compilation fixes the physical frame reference slot. -/
theorem reference_index : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length := by
  rw [CallableIndexedLambdaValues.Code.referenceIndex, support.compilation]
  rfl

variable
  (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Includes functions)

include packet profile observed in
/-- Actual formation copies the captured cells and supplies independent native
typing to the static constructor for the formed closure over the copies and
its history. The heap model stays arbitrary. -/
theorem formation_with_member
    (member : ∀ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        captured code (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      RuntimeValueHasType formed.finalWorld
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions →
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) := by
  let history := history_at captured code support owner initial packet
  have reference : captured.canonical[code.referenceIndex]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
    rw [reference_index captured code support]
    exact observed.reference
  have read : store.read? owner.key.frameLocation =
      some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native) := by
    have actualRead := (initial.rows owner.position).authority.frame.read
    rw [(initial.rows owner.position).frame_eq] at actualRead
    exact actualRead
  obtain ⟨formed⟩ := CallableIndexedLambdaValues.formation captured code history copied
    (reference_index captured code support) heaps reference read
  have nativeTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) (formed.represents heaps.runtime_hasTypes)
  exact ⟨formed, formed.source _ ordinary coercions, formed.evaluated, member formed nativeTyped,
    fun _ _ completed => Core.evaluation_deterministic completed formed.evaluated⟩

include prefixContext observed inclusion prepared in
/-- The prepared receipt, recaptured at the copies, places the formed closure
in the prepared model; only this representation is transferred forward to the
caller's model. -/
theorem formed_represents
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (nativeTyped : RuntimeValueHasType formed.finalWorld
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
      compiled.indexed.layouts.definitions) :
    functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
  inclusion (.prepared_ordinary (function := formed.closure) owner formed.captures formed.closureCode
    formed.closureHistory (support.recapture formed.captured)
    ⟨(source_origin captured code support owner initial packet).metadata⟩ prefixContext
    (observed.of_slots formed.slots) (reference_index captured code support) nativeTyped
    (prepared_recapture prepared formed.captured))

include packet prefixContext observed inclusion prepared in
/-- The original actual formation supplies the closure over the copies of its
captured cells; the prepared receipt fixes the snapshot policy. Only its
function representation is transferred forward to the caller's model. -/
theorem formation
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions mapping world heap store)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    ∃ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
        (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
        function.source function.captured heap code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual)) formed.finalStore ∧
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
        result = .inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
          formed.closureActual) ∧ finalStore = formed.finalStore) :=
  formation_with_member captured code support owner initial packet profile observed functions
    (formed_represents captured code support prepared owner initial packet profile prefixContext observed functions inclusion)
    heaps (prepared_snapshots prepared) ordinary coercions

/-- The output retains all ordinary leaf effects and the exact packet state,
in the formed state that holds the copies. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  ∃ finalMap finalWorld,
    GenericExpressionMeaning.ResultRepresents
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        functions)
      finalMap finalWorld code.sourceNode.type code.lowered.type faults outcome result ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
      functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
    AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
    ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
      (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
      PostAdmission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
        function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (copied : code.policy.snapshotLambda code.id = true)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)


include sourceType admitted wellFormed runtime covers locals typed in
/-- The formed closure, its traces and its representation give the result in
the formed state, with the original packet transported there. -/
private theorem result_of_formation
    (formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) captured code
      (history_at captured code support owner initial packet) heap store owner.key.frameLocation)
    (sourceTrace : Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram)
      function.context function.evidence function.source function.captured heap code.id (.closure formed.closure)
      formed.finalHeap)
    (native : Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore)
    (represented : functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
      (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)) :
    ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions
      (.value (.closure formed.closure)) formed.finalHeap
      (.inRight .word (value code formed.embedding (history_at captured code support owner initial packet).native
        formed.closureActual)) formed.finalStore := by
  have valueRep : ValueRep compiled.compatible.checked registry functions formed.finalMap formed.finalWorld
      code.sourceNode.type (.closure formed.closure)
      (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
      code.lowered.type := by
    rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
    exact .function represented
  obtain ⟨reached, related⟩ := ProtectedStateTransition.AdministrativeTransport.transition
    (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller)
    (CallableIndexedOwnedNestedCanonicalState.administrativeTransport (headers := headers) owner support.caller)
    ⟨initial, packet⟩ formed.maps formed.worlds formed.frame formed.copy.metadata_extends
  have post := after_expression
    (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
    ⟨initial, packet⟩ reached admitted wellFormed runtime covers locals typed
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) formed.frame
  exact ⟨native, formed.finalMap, formed.finalWorld, .value valueRep, formed.heaps,
    formed.maps, formed.worlds, formed.frame, formed.copy.metadata_extends, reached, related, post⟩

include profile observed sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The actual Source leaf constructs one formation over the copies and
transports the packet to the formed state, under its local static membership
constructor for the formed closure. -/
theorem preserves_at_with_member
    (member : ∀ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        captured code (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      RuntimeValueHasType formed.finalWorld
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions →
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
    {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨sourceCaptured, rfl, copy⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨formed, sourceTrace, native, represented, _determined⟩ :=
      formation_with_member captured code support owner initial packet profile observed functions member heaps
        copied ordinary coercions
    obtain ⟨rfl, rfl⟩ := Dynamic.EnvironmentCopies.functional copy formed.copy
    exact ⟨_, formed.finalStore, result_of_formation captured code support owner initial packet functions
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace native represented⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed inclusion prepared sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore :=
  preserves_at_with_member captured code support owner initial packet profile observed functions
    wellFormed runtime covers locals typed sourceType (prepared_snapshots prepared) ordinary coercions heaps admitted
    (formed_represents captured code support prepared owner initial packet profile prefixContext observed functions inclusion)
    trace

include profile observed sourceType copied ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Reflection uses one authentic formation over the copies, its deterministic
native completion and independently sized Source trace, under the same local
member constructor for the formed closure. -/
theorem reflects_at_with_member
    (member : ∀ formed : Formed (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
        captured code (history_at captured code support owner initial packet) heap store owner.key.frameLocation,
      RuntimeValueHasType formed.finalWorld
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions →
      functions.Represents registry formed.finalMap formed.finalWorld (FunctionValues.sourceType function)
        (.closure formed.closure)
        (value code formed.embedding (history_at captured code support owner initial packet).native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore))
    {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨formed, sourceTrace, native, represented, determined⟩ :=
    formation_with_member captured code support owner initial packet profile observed functions member heaps
      copied ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  exact ⟨sourceSize, _, formed.finalHeap, sized,
    result_of_formation captured code support owner initial packet functions
      wellFormed runtime covers locals typed sourceType admitted formed sourceTrace native represented⟩

include prefixContext observed inclusion prepared sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore :=
  reflects_at_with_member captured code support owner initial packet profile observed functions
    wellFormed runtime covers locals typed sourceType (prepared_snapshots prepared) ordinary coercions heaps admitted
    (formed_represents captured code support prepared owner initial packet profile prefixContext observed functions inclusion)
    completed

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
/-! One accepted contextual compiler call chooses the ordinary lambda Site.
Its dependent static inputs build the joint body at that same Site and factory.
The runtime prefix and public population of these static inputs remain explicit. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedNamedGeneration CallableIndexedLambdaGeneration CallableIndexedLambdaValues
open CallableIndexedOwnedContextualLambdaJointStaticReceipts
open CallableIndexedOwnedContextualLambdaSourceDiagnostics
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation
open CallableLambdaViewEdits CallableLambdaBodyReachability GenericImperativeMatch

variable {compiled : SourceCoreUnifiedCompilation.Compiled}

/-- The finite contextual inversion retains the actual policy and body lowerer.
It does not select a Site or certify execution of the body. -/
structure ContextualPolicyReceipt (named : Named)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (fuel : Nat) (view : TypedSource) (scope : SourceCoreLocalCell.Scope)
    (id : ExpressionId) (reasonAt : ExpressionId → Word) (lowered : SourceCoreBasic.LoweredExpr) where
  policy : SourceCoreFunctions.Policy
  lowerBody : SourceCoreFunctions.BodyLowerer
  accepted : SourceCoreFunctions.lowerExpressionWithPolicy policy lowerBody (fuel + 1)
    (context compiled.indexed named) view scope id reasonAt = .ok lowered
  binder : policy.lowerBinder = SourceCoreGeneralFunctions.contextualBinder
    ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key []
  recipe : lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((representation compiled.indexed).atContext named.signature.key [])
    (context compiled.indexed named).solvedRequirements compilation.own.assignments diagnostics
    (context compiled.indexed named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.locals named.signature.key [])

/-- Only the original contextual bind is eliminated; the recursive compiler
callback and its minimum budget stay inside the selected policy. -/
theorem ContextualPolicyReceipt.of_accepted
    {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed named diagnostics namedCode)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key = .ok named.specialized)
    {fuel : Nat} {view : TypedSource} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered) :
    Nonempty (ContextualPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation fuel view scope id reasonAt lowered) := by
  rw [SourceCoreGeneralFunctions.lowerContextualExpression.eq_def] at accepted
  dsimp only at accepted
  change (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan named.signature.key |>.mapError SourceCoreBasic.Error.callPreparation) >>= _ = .ok lowered at accepted
  rw [record] at accepted
  simp only [Except.mapError, bind, Except.bind] at accepted
  exact ⟨⟨_, _, accepted, rfl, rfl⟩⟩

section ChosenSite
variable (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every static field is indexed by this literal chosen Produced value.
There is no completed joint body or formation semantics among these inputs. -/
structure SiteInputs
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered) where
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  issued : IssuedSource compiled produced.site.code.compilation.owner (source caller.named)
  diagnosticPolicy : AssignmentDiagnosticPolicy
  entry : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) produced.site.code
  frame : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram)
    (closure caller.named parameters result statements sourceContext evidence [])
  readFuel : Nat
  changed : List ExpressionId
  edited : LocalView (source caller.named) produced.site.code.view changed
  avoids : Avoids (source caller.named) (statements.map NodeId.statement) changed
  bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named
  declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext
  unique : NodeOccurrencesUnique (source caller.named)
  sameLedger : sourceContext.solvedRequirements = produced.site.code.compilation.solvedRequirements
  syntaxTransport : ∀ id, Reaches (source caller.named) (statements.map NodeId.statement) (.expression id) →
    expressionSyntax produced.site.code.view id → expressionSyntax (source caller.named) id
  expressions : ∀ context scope id lowered,
    Reaches (source caller.named) (statements.map NodeId.statement) (.expression id) →
    certificates readFuel produced.site.code.view context scope id lowered →
    certificates readFuel (source caller.named) context scope id lowered
  syntaxTree : Syntax (source caller.named) (expressionSyntax (source caller.named))
    entry.context (.statements true statements) result
  viewSyntax : Syntax produced.site.code.view (expressionSyntax produced.site.code.view)
    entry.context (.statements true statements) result
  projection : compiled.compatible.checked.catalog.project result = .ok produced.site.code.receipt.resultCore
  residualMode : Bool
  static : ExtractionInputs (layouts := compiled.indexed.layouts) (owner := produced.site.code.compilation.owner)
    (active := produced.site.code.active) (frame := compiled.indexed.ancestry.layout.frame)
    (globals := compiled.indexed.base.globals.length) (onError := produced.site.code.allocationError)
    (values := .initial compiled.compatible.checked) (source := produced.site.code.view)
    (expressionSyntax := expressionSyntax produced.site.code.view) (certificates := certificates readFuel produced.site.code.view)
    (reasonAt := produced.site.code.reasonAt) (definitions := compiled.indexed.layouts.definitions)
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

/-- The genuine Source lookup fixes the selected raw node. No erased Code
field is recovered from an equality between certificate proofs. -/
theorem Produced.source_node {sourceNode : ExpressionNode}
    (produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered)
    (found : (source caller.named).lookupExpression? id = some sourceNode) :
    produced.site.code.sourceNode = sourceNode := by
  have actual : (source caller.named).lookupExpression? id = some produced.site.code.sourceNode := by
    simpa only [produced.identifier, CallableIndexedLambdaGeneration.closure] using produced.site.code.sourceFound
  exact Option.some.inj (actual.symm.trans found)

/-- The chosen formation keeps the input named compilation as well as the
chosen Site's factory. These equalities are literal constructor receipts. -/
structure Receipt (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
    (sourceContext : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (scope : SourceCoreLocalCell.Scope) (id : ExpressionId) (lowered : SourceCoreBasic.LoweredExpr) where
  formation : Formation caller sourceContext evidence scope id lowered
  diagnostics_eq : formation.produced.diagnostics = diagnostics
  namedCode_eq : formation.produced.namedCode = namedCode
  compilation_eq : HEq formation.produced.compilation compilation

/-- One actual contextual producer chooses the Site. Its dependent inputs
then run the existing static collector and canonical transport at that Site. -/
theorem receipt_of_contextual
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation compiled.indexed caller.named diagnostics namedCode)
    (issued : CallableIndexedOwnedContextualLambdaIssuedRecipes.IssuedAt compiled.indexed diagnostics)
    (record : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan caller.named.signature.key = .ok caller.named.specialized)
    {fuel : Nat} {view : TypedSource} {sourceNode node : ExpressionNode} {reported : Ty}
    {reasonAt : ExpressionId → Word}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (viewOfSource : LambdaMetadataViews.MetadataView (source caller.named) view)
    (sourceFound : (source caller.named).lookupExpression? id = some sourceNode)
    (sourceForm : sourceNode.form = .lambda parameters result statements)
    (rawType : sourceNode.type = FunctionValues.sourceType
      (closure caller.named parameters result statements sourceContext evidence []))
    (rawOrdinary : Dynamic.OrdinaryRequirementLayout sourceNode.requirements sourceNode.coercions [])
    (rawCoercions : sourceNode.coercions = [])
    (found : view.lookupExpression? id = some node) (form : node.form = sourceNode.form)
    (owner : id.occurrence.owner = view.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (ordinary : compiled.indexed.base.locals.bindings.find? (fun binding =>
      decide (binding.caller = (context compiled.indexed caller.named).owner ∧ binding.initializer = id)) = none)
    (read : SourceCoreCompatibleDataExpressions.readExpression compiled.compatible.checked view id = .ok (node, reported))
    (accepted : SourceCoreGeneralFunctions.lowerContextualExpression compiled.indexed.base.sourceProgram
      ((representation compiled.indexed).atContext caller.named.signature.key []) compiled.indexed.base.sourceProgram.signatures
      compiled.indexed.base.locals compilation.parents compilation.own.assignments diagnostics (context compiled.indexed caller.named)
      compiled.indexed.base.callableContext none none (fuel + 1) view scope id reasonAt = .ok lowered)
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++
      RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller)
      lowered.expression (LanguageResult.resultType lowered.type) compiled.indexed.layouts.definitions)
    (siteInputs : ∀ produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered,
      produced.diagnostics = diagnostics → produced.namedCode = namedCode → HEq produced.compilation compilation →
      Nonempty (SiteInputs caller produced)) :
    Nonempty (Receipt caller diagnostics namedCode compilation sourceContext evidence scope id lowered) := by
  obtain ⟨site, identifier, emitted, binderPolicy, recipe, issuedRecipe, _view, _reason⟩ := CallableIndexedLambdaGeneration.of_contextual_with_issued_recipe_exact
    compiled.indexed compilation issued record sourceContext evidence [] profile viewOfSource sourceFound sourceForm
    found form owner requirements coercions ordinary read accepted typed
  let produced : Produced (compiled := compiled) caller.named parameters result statements sourceContext evidence scope
      (RecursiveNamedLambdaFormationHeads.nativePrefix (values := .initial compiled.compatible.checked) caller) id lowered :=
    ⟨diagnostics, namedCode, compilation, site, identifier, emitted, binderPolicy, recipe, issuedRecipe.policy_recipe, issuedRecipe⟩
  obtain ⟨inputs⟩ := siteInputs produced rfl rfl (HEq.refl compilation)
  obtain ⟨body, _entry, _readFuel⟩ := at_site produced.compilation produced.site produced.recipe
    (Program.ofChecked compiled.sourceProgram) inputs.entry inputs.frame inputs.expressionSyntax inputs.certificates
    inputs.readFuel inputs.diagnosticPolicy inputs.issued.invalidOperand inputs.issued.invalidUnary
    inputs.issued.invalidProjection inputs.issued.missingDefault inputs.edited inputs.avoids inputs.unique
    inputs.sameLedger inputs.syntaxTransport inputs.expressions inputs.syntaxTree inputs.viewSyntax inputs.projection
    inputs.static inputs.nativeTyped
  have nodeEq := Produced.source_node caller produced sourceFound
  let formation : Formation caller sourceContext evidence scope id lowered := {
    parameters := parameters, result := result, statements := statements, produced := produced
    expressionSyntax := inputs.expressionSyntax, certificates := inputs.certificates, issued := inputs.issued
    diagnosticPolicy := inputs.diagnosticPolicy, body := body
    bodyView := fun _ reached => expression_lookup inputs.edited inputs.avoids reached
    bodyReasons := inputs.bodyReasons
    declarations := inputs.declarations
    sourceType := nodeEq ▸ rawType, ordinary := nodeEq ▸ rawOrdinary, coercions := nodeEq ▸ rawCoercions }
  exact ⟨⟨formation, rfl, rfl, HEq.refl compilation⟩⟩

/-- A finite projection forgets only the input compilation identities. -/
theorem formation_of_receipt
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
    (receipt : Receipt caller diagnostics namedCode compilation sourceContext evidence scope id lowered) :
    Nonempty (Formation caller sourceContext evidence scope id lowered) := ⟨receipt.formation⟩

end ChosenSite
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaCompilerReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
/-! Actual prepared formation heads and selected closure invocations reuse the
original finite parameter, body, and restoration proofs. A genuine JointBody
supplies prepared flow; only strict expression children supply runtime meaning.
Prior closures remain a separate selection alternative. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedOrdinaryLambdaFormation (Formation)
open RecursiveNamedLambdaFormationHeads

section FormationHeads
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

def Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Formation caller context evidence scope id lowered)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedPreparedOrdinaryLambdaValues.model headers keys registry faults profile).Includes functions)
  (complete : RecursiveNamedCatalogNativeContexts.Complete (values := .initial compiled.compatible.checked)
    (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed) headers)
  (globals : caller.globals = compiled.indexed.base.globals.length)
  (slots : ∀ header, header ∈ headers → header.slot < compiled.indexed.base.globals.length)
  (prefixZero : owner.key.capturePrefix = 0)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {source : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context source)
  (covers : evidence.Covers context)
  (sameSource : source = CallableIndexedNamedGeneration.source caller.named)

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual catalog/capture receipts construct the whole finite formation leaf.
Static body certificates remain unrestricted and never supply an execution law. -/
theorem preserves_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees nativeTyped initial admitted trace
  obtain ⟨head⟩ := certified
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : Support code := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      (head.function environment).context (head.function environment).evidence (head.function environment).source
      (head.function environment).captured before code.id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
  obtain ⟨result, finalStore, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at
      (function := head.function environment) (actual := actual)
      captured code support (head.prepared environment) owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.ordinary head.coercions heaps admitted original
  have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.produced.emitted, captured, captures_for] using native
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      finalMap finalWorld code.sourceNode.type lowered.type faults outcome result := by
    simpa only [model, code, Formation.code, recaptureCode, head.produced.emitted] using represented
  exact ⟨result, finalStore, finalMap, finalWorld, native, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual native formation reflects the original Source leaf with its own
independent grade, preserving the same caller packet and generic heap model. -/
theorem reflects_head_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate caller context evidence) faults size := by
  intro scope id lowered certified node found typed mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees nativeTyped initial admitted completed
  obtain ⟨head⟩ := certified
  let entry := CallableIndexedOwnedLambdaViewHeads.nested_entry initial.val owner prefixZero
    initial.property.observed initial.property.carried initial.property.bundle globals
  let captured := captures_for complete globals entry environments agrees nativeTyped
  have observed := capture_globals_for complete globals slots entry environments agrees nativeTyped
  have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation := by
    change CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
      headers owner.key.locations 1 scope
      captured.canonical (initial.val.rows owner.position).authority.frameLocation at observed
    rw [(initial.val.rows owner.position).frame_eq] at observed
    exact observed
  let code : Code compiled.indexed (head.function environment) scope captured.administrative := head.code environment
  let support : Support code := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.produced.identifier] using head.produced.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using typed
  have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.produced.emitted, captured, captures_for] using completed
  obtain ⟨sourceSize, outcome, after, trace, native, finalMap, finalWorld, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.reflects_at
      (function := head.function environment) (actual := actual)
      captured code support (head.prepared environment) owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.ordinary head.coercions heaps admitted actualCompleted
  have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.produced.identifier] using trace
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      finalMap finalWorld code.sourceNode.type lowered.type faults outcome value := by
    simpa only [model, code, Formation.code, recaptureCode, head.produced.emitted] using represented
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

end FormationHeads

section Invocation
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity)
open CallableIndexedOwnedParameterReadyContinuations (bridge)
open RecursiveNamedCatalogInvocationBounds (Below)
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative)
  (support : Support code) (prepared : PreparedAt code support)
  (history : History code)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (profile : compiled.compatible.checked.catalog.callableContracts = true)

include prepared profile in
/-- The genuine selected seed policy fixes this same ordered binder pack. -/
theorem binding_pack : code.receipt.parameterCore =
    SourceCoreCompatibleCatalog.packTypes (code.receipt.loweredParameters.map Prod.snd) :=
  CallableIndexedOwnedStoredNativePackReceipts.code_binding_pack code profile
    prepared.projected_bindings support.body.projection

variable {sourceTypes : List TypeSystem.Ty} {types : List Ty}
  {arguments : List Dynamic.Value} {nativeArguments : List Value}

include prepared profile in
/-- The actual values, genuine physical arity and two independent bundle
receipts construct the original argument vector at the current call heap. -/
theorem arguments_of_bundles
    (represented : DataExpressionSequence.Values
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world sourceTypes types arguments nativeArguments)
    (arity : function.parameters.length = arguments.length)
    (rawBundle : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (function.parameters.map (fun binding => binding.scheme.body)))
    (nativeBundle : SourceCoreCompatibleCatalog.packTypes types = code.receipt.parameterCore) :
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world code.receipt.loweredParameters arguments nativeArguments := by
  have parameters := CallableIndexedLambdaEntryPrefix.parameters (values := .initial compiled.compatible.checked) code
  have count : arguments.length = code.receipt.loweredParameters.length := by
    rw [parameters, List.length_map] at arity
    exact arity.symm
  have raw : TypeSystem.Ty.productMany sourceTypes =
      TypeSystem.Ty.productMany (code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) := by
    simpa only [parameters, List.map_map, Function.comp_def] using rawBundle
  exact CallableIndexedOwnedStoredArgumentAlignment.arguments_of_bundles code.receipt.loweredParameters
    represented count raw (nativeBundle.trans (binding_pack captured code support prepared profile))

variable
  (extension : SourceCoreRawMetadata.Extends (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry registry)
  {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog functions identities)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {table : SourceCoreFaultSites.Table}
  (rebuilt : support.issued.diagnostics.tableForRegistry registry extension = .ok table)
  (operandIncluded : ∀ reason token, GenericAssignmentDiagnostics.OperandRep support.issued.assignments reason token → faults reason token)
  (unaryIncluded : ∀ reason token, EmittedDiagnosticTokenPlan.UnaryRep support.issued.assignments reason token → faults reason token)
  (interprets : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
    CallableIndexedOwnedContextualLambdaAssignmentReadiness.ReachedInterpretations
      (context := context) (certificates := support.certificates support.body.readFuel function.source)
      (administrative := captured.administrative)
      (factory := CallableIndexedOwnedContextualLambdaJointStaticReceipts.trackedFactory
        support.diagnosticPolicy function.source support.issued.invalidOperand)
      (faults := faults) (registry := registry) support.issued
      (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys)) functions table)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments support.body.types)
  (stable : CallableIndexedOwnedIndirectExpressionHeads.StableRows caller)

/-- The genuine body result is restored to the current caller pool. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (finalStore : Store) (finalMap : LocationMap) (finalWorld : StoreTyping) : Prop :=
  FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    finalMap finalWorld function.resultType code.receipt.resultCore faults outcome value ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
  LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
  AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
  ProtectedStateTransition.Transition (protocol headers keys) caller
    ⟨callerScope, finalMap, finalWorld, after, finalStore, callerCanonical⟩

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
  represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable in
/-- Prepared flow and typed finish are derived internally from strict members
of the same expression family at the actual parameter entry. -/
theorem invocation_preserves (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (support.certificates support.body.readFuel function.source context) faults size))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size callContext callerEvidence
      function.evidence before (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
        store (code.body.rename captured.embedding.lift.lift) value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore finalMap finalWorld := by
  have continuation := CallableIndexedOwnedContextualLambdaPreparedBodyBounds.source_continuation
    (nativeArguments := nativeArguments) support.namedCompilation captured code support.issued support.body functions extension faithful observations wellFormed
    rebuilt operandIncluded unaryIncluded interprets history owner caller beforeTyped argumentsTyped stable budget meaning
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at_with_continuation
    captured code history support.body.toBody.toContext functions represented owner caller heaps locals reference
    currentCarried allowed budget continuation trace within

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
  represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable in
/-- Native body completion uses only strict same-family children. The Source
call grade is reconstructed independently before the same caller restoration. -/
theorem invocation_reflects (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (support.certificates support.body.readFuel function.source context) faults size))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      (DataPatternValues.packValues nativeArguments :: encode compiled.indexed.ancestry.layout.frame history.native :: capturedActual)
      store (code.body.rename captured.embedding.lift.lift) value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize callContext callerEvidence
        function.evidence before (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore finalMap finalWorld := by
  have continuation := CallableIndexedOwnedContextualLambdaPreparedBodyBounds.native_continuation
    support.namedCompilation captured code support.issued support.body functions extension faithful observations wellFormed
    rebuilt operandIncluded unaryIncluded interprets history owner caller beforeTyped argumentsTyped stable budget functionTypes reflection
  exact CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at_with_continuation
    captured code history support.body.toBody.toContext functions represented owner caller heaps locals reference
    currentCarried allowed support.body.frame budget continuation completed within

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
  represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable in
/-- The authentic payload apply edge preserves the same invocation result. -/
theorem application_preserves (budget : Nat)
    (meaning : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (support.certificates support.body.readFuel function.source context) faults size))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) size callContext callerEvidence
      function.evidence before (.closure function) arguments outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore finalMap finalWorld := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result⟩ :=
    invocation_preserves captured code support history functions extension faithful observations wellFormed
      rebuilt operandIncluded unaryIncluded interprets represented owner caller heaps locals reference currentCarried allowed
      beforeTyped argumentsTyped stable budget meaning trace within
  exact ⟨value, finalStore, finalMap, finalWorld,
    .apply (.second (.first (.var rfl))) (.var rfl) evaluated, result⟩

include extension faithful observations wellFormed rebuilt operandIncluded unaryIncluded interprets
  represented heaps locals reference currentCarried allowed beforeTyped argumentsTyped stable in
/-- The real apply edge keeps its strict body grade separate from the newly
constructed Source grade and unchanged reached caller pool. -/
theorem application_reflects (budget : Nat) (functionTypes : FunctionRuntimeViews functions)
    (reflection : ∀ context, Validity (program := Program.ofChecked compiled.sourceProgram) captured code context →
      Below budget (fun size =>
        CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt
          (CallableIndexedOwnedParameterReadyContinuations.bridge (headers := headers) (keys := keys))
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions) context function.evidence
          function.source (support.certificates support.body.readFuel function.source context) faults size))
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram) sourceSize callContext callerEvidence
        function.evidence before (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code functions caller outcome after value finalStore finalMap finalWorld := by
  obtain ⟨bodySize, smaller, applied⟩ := completed.apply_body (.second (.first (.var rfl))) (.var rfl)
  exact invocation_reflects captured code support history functions extension faithful observations wellFormed
    rebuilt operandIncluded unaryIncluded interprets represented owner caller heaps locals reference currentCarried allowed
    beforeTyped argumentsTyped stable budget functionTypes reflection applied (Nat.le_trans (Nat.le_of_lt smaller) within)

end Invocation

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaInvocation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
/-! Ordinary selection fixes an empty actual specialization dictionary. The
same Header retains its resolved Row and complete Source dictionary, so these
receipts manufacture the selected empty-evidence condition from compiler
provenance. Other Headers may keep nonempty dictionaries. No body execution
or completed expression Tree is an input. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
open Core Frontend SourceInference
open RecursiveNamedCatalog CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : Inventory compiled.indexed.ancestry (.initial compiled.compatible.checked)
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions
    (Program.ofChecked compiled.sourceProgram)}

/-- The actual ordinary selected row and retained resolver fix this Header's
dictionary. Signature/type equality alone does not supply this fact. -/
theorem selected_evidence_empty
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment} {global : Dynamic.GlobalFunction}
    (sourceAt : NamedSourceAt header rawD global)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {instantiation : DeclarationInstantiation}
    {index : Nat} {signature : SourceCoreCalls.Signature}
    (plan : compilation.plan = compiled.indexed.base.plan)
    (signatureEq : header.named.signature = signature)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node instantiation false =
      .ok (index, signature)) :
    header.function.evidence = [] := by
  obtain ⟨actual, record, _matched, closed, _slot⟩ :=
    CallableNamedMetadata.metadata_of_selected_signature selected
  rw [plan, ← signatureEq] at record
  have same : actual = header.named.specialized :=
    Except.ok.inj (record.symm.trans sourceAt.row.record)
  have actualClosed : header.named.specialized.assumptions = [] := same ▸ closed
  have emptyResolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment
      compiled.indexed.base.sourceProgram header.named.signature.key
      header.named.specialized.assumptions = .ok [] := by
    rw [actualClosed]
    rfl
  have rawEmpty : rawD = [] := Except.ok.inj (sourceAt.row.resolved.symm.trans emptyResolved)
  rw [sourceAt.dictionary, sourceAt.retained, rawEmpty]
  rfl

/-- A finite inventory keeps the original full Row, resolver, Source frame and
dictionary identity for each actual Header. This is static provenance. -/
structure SourceReceiptCover : Prop where
  receipts : ∀ header, header ∈ headers →
    ∃ rawD global, NamedSourceAt header rawD global

/-- Construct the existing selected-site condition internally from those real
receipts and the actual ordinary selection. No global emptiness is imposed. -/
theorem SourceReceiptCover.selected_empty
    (cover : SourceReceiptCover (headers := headers))
    (compilation : SourceCoreFunctions.Context)
    (plan : compilation.plan = compiled.indexed.base.plan)
    (source : TypedSource) (admitted : ExpressionId → Prop) :
    RecursiveNamedExpressionCompilerCertificates.SelectedEmptyEvidence headers compilation source admitted := by
  intro _id node _callee _arguments instantiation header policy index signature
    _allowed _found _form selected member _sameInstantiation _sameSlot signatureEq
  obtain ⟨rawD, global, sourceAt⟩ := cover.receipts header member
  exact selected_evidence_empty sourceAt plan signatureEq selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryNamedEvidenceReceipts
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
/-! This is the actual lexical compiler traversal with its local native child
witness retained at every expression callback. One enclosing HasType suffices;
Source lookup, Source typing and compiler acceptance remain separate inputs.
The certificate factory receives the arbitrary result type supplied by native
constructor inversion. Authentic lambda hooks can normalize it afterward.
Stopped suffixes remain the original issued dead code and receive no semantic
or expression-certificate manufacture. This is a static producer, not E/F. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
open Core Frontend SourceInference GenericLexicalStatements
open CompatibleEncoding (bind_ok)
private theorem read_found {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource}
    {id : StatementId} {node : StatementNode} {type : Ty}
    (accepted : SourceCoreCompatibleDataExpressions.readStatement checked source id = .ok (node, type)) :
    source.lookupStatement? id = some node := by
  unfold SourceCoreCompatibleDataExpressions.readStatement at accepted
  by_cases owner : id.occurrence.owner ≠ source.owner
  · simp [owner, throw, bind, Except.bind] at accepted
  · simp only [owner, ↓reduceIte, bind, Except.bind, pure, Except.pure] at accepted
    cases found : source.lookupStatement? id with
    | none => simp [found] at accepted
    | some actual =>
      simp only [found] at accepted
      obtain ⟨projected, _, same⟩ := bind_ok accepted
      cases same
      rfl

open CompatibleStatementBindings (binder_projected scope_bind)

private theorem ensure_same {site : SourceCoreElaboration.ErrorSite} {expected actual : Ty}
    (accepted : SourceCoreBasic.ensureType site expected actual = .ok ()) : expected = actual := by
  unfold SourceCoreBasic.ensureType at accepted
  split at accepted
  · assumption
  · cases accepted

private theorem computation_child {definitions : DataEnvironment}
    {context : Core.Context} {output nativeType : Ty} {computation body : Expr}
    (typed : HasType context (LanguageResult.bind output computation body) nativeType definitions) :
    ∃ childType, HasType context computation childType definitions := by
  cases typed with | caseE child _ _ => exact ⟨_, child⟩

variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {reasonAt : ExpressionId → Word} {policy : SourceCoreLoops.Policy}
  {definitions : DataEnvironment} {administrative : Core.Context}

/-- The original syntax/compiler induction supplies each callback with native
typing of that exact emitted expression, at its actual lexical scope. -/
theorem tree_of_typed_flow_with_residual (residualMode : Bool)
    (readPolicy : policy.readStatement = SourceCoreCompatibleDataExpressions.readStatement values.checked)
    (binderPolicy : ∀ scope binder, binder.scheme.quantified = [] →
      policy.lowerBinder source scope binder = SourceCoreCompatibleDataExpressions.lowerBinder values.checked source scope binder)
    (allocationPolicy : policy.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    (extractExpressions : ∀ sourceContext, sourceContext.typeVariables = [] → sourceContext.residualTypeVariables = residualMode →
      sourceContext.signatures = values.checked.signatures →
      ∀ {scope fuel id node lowered}, CompatibleExpressionReads.ScopeDeclarations source scope sourceContext → expressionSyntax id →
      source.lookupExpression? id = some node → ExpressionHasType source sourceContext id node.type →
      policy.lowerExpression fuel source scope id reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → certificates sourceContext scope id lowered)
    {context : SourceSemantics.Context} {scope : Scope} {mode : Bool} {statements : List StatementId} {expected : TypeSystem.Ty}
    (syntaxTree : Syntax source expressionSyntax context mode statements expected)
    (closed : context.typeVariables = []) (residual : context.residualTypeVariables = residualMode)
    (sourceSignatures : context.signatures = values.checked.signatures)
    (declarations : CompatibleExpressionReads.ScopeDeclarations source scope context)
    {fuel : Nat} {type : Ty} {code : Expr} {selfReason : Word} {nativeType : Ty}
    (projection : values.checked.catalog.project expected = .ok type)
    (accepted : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope statements type reasonAt mode selfReason = .ok code)
    (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code nativeType definitions) :
    Tree layouts owner active frame globals onError values source certificates
      context scope mode statements expected type code := by
  induction syntaxTree generalizing scope fuel code nativeType with
  | nil allowed =>
    simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
    cases accepted
    exact .nil allowed
  | @returnUnit context mode id node rest found form sourceType =>
    have same : type = .unit := (Except.ok.inj projection).symm
    subst type
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      cases accepted
      exact .returnUnit rest found form
  | @returnValue context mode id node expression expressionNode expected rest found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .returnValue rest found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped)
  | @tail context id node expression expressionNode expected found form sourceType expressionFound valueType typed syntaxValue =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [Bool.not_false, Bool.and_self, List.isEmpty_nil, ↓reduceIte] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have same := ensure_same checkedType
      subst type
      cases accepted
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .tail found form expressionFound valueType (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped)
  | @uninitialized context nextContext mode id node binder rest expected found form declaration monomorphic extended ordinary remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨body, generated, accepted⟩ := bind_ok accepted
      simp only [SourceCoreSourceCells.letUninitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ :=
        CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      exact .uninitialized found form monomorphic extended ordinary (binder_projected (binderPolicy scope binder monomorphic ▸ projected))
        allocation annotation same (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind payload declarations declaration extended) projection generated
          (TypedLexicalWhile.Native.absent_child allocation annotation same nativeTyped))

  | @initialized context nextContext mode id node binder initializer initializerNode rest expected found form declaration mono extended ordinary initializerFound sourceType typed initializerSyntax remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have identical := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨checked, _, accepted⟩ := bind_ok accepted
      cases checked
      obtain ⟨payload, projected, accepted⟩ := bind_ok accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedType, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedType
      subst payload
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      simp only [mono, List.isEmpty_nil, ↓reduceIte] at accepted
      simp only [SourceCoreSourceCells.letInitialized, allocationPolicy] at accepted
      obtain ⟨allocationCode, generatedAllocation, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨allocation, annotation, same, rfl⟩ := CallableIndexedAllocationCompletion.accepted_receipts onError generatedAllocation
      obtain ⟨_, childTyped⟩ := computation_child nativeTyped
      exact .initialized found form mono extended ordinary initializerFound sourceType
        (extractExpressions context closed residual sourceSignatures declarations initializerSyntax initializerFound typed generated childTyped)
        allocation annotation same
        (ih (by cases extended; exact closed) (by cases extended; exact residual) (by cases extended; exact sourceSignatures)
          (scope_bind lowered.type declarations declaration extended) projection generatedBody
          (TypedLexicalWhile.Native.initialized_child allocation annotation same nativeTyped))

  | @discard context mode id node expression expressionNode semicolon rest expected found form notTail sourceType expressionFound typed syntaxValue remaining ih =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨lowered, generated, accepted⟩ := bind_ok accepted
      simp only [notTail, Bool.false_eq_true, ↓reduceIte] at accepted
      cases semicolon <;> simp only [Bool.false_eq_true, ↓reduceIte] at accepted
      all_goals
        obtain ⟨checked, _, accepted⟩ := bind_ok accepted
        cases checked
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨_, childTyped⟩ := computation_child nativeTyped
        obtain ⟨_, tailTyped⟩ := TypedLexicalWhile.Native.discard_child nativeTyped
        exact .discard found form notTail expressionFound (extractExpressions context closed residual sourceSignatures declarations syntaxValue expressionFound typed generated childTyped)
          (ih closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @block context mode id node statements rest expected found form sourceType inner remaining innerIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .block found form (innerIH closed residual sourceSignatures declarations projection generatedInner innerTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
  | @ifThen context mode id node condition conditionNode thenBody elseBody rest expected found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining thenIH elseIH restIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have conditionTypeEq := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at conditionTypeEq
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      cases elseBody with
      | none =>
        simp only [bind, Except.bind, pure, Except.pure] at accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        have generatedElse : SourceCoreLoops.lowerFlowStatementsWithPolicy policy fuel source scope [] type reasonAt false selfReason =
            .ok (LocalLoop.fallthrough type) := by cases fuel <;> rfl
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)
      | some statements =>
        obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
        obtain ⟨body, generatedBody, accepted⟩ := bind_ok accepted
        cases accepted
        obtain ⟨⟨_, branchTyped⟩, ⟨_, tailTyped⟩⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
        obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
        obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
        exact .ifThen found form conditionFound conditionType
          (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped)
          (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped) (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped) (restIH closed residual sourceSignatures declarations projection generatedBody tailTyped)

  | @terminalBlock context mode id node statements rest expected exactUnique found form sourceType inner stops innerIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨innerCode, generatedInner, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, innerTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      exact .terminalBlock exactUnique found form
        (innerIH closed residual sourceSignatures declarations projection generatedInner innerTyped) stops
        (IssuedSuffix.of_accepted generatedSuffix)
  | @terminalIf context mode id node condition conditionNode thenBody elseBody rest expected exactUnique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops thenIH elseIH =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      simp only [SourceCoreLoops.lowerFlowStatementsWithPolicy] at accepted
      obtain ⟨⟨actual, stored⟩, read, accepted⟩ := bind_ok accepted
      have same := Option.some.inj ((read_found (readPolicy ▸ read)).symm.trans found)
      subst actual
      simp only [form] at accepted
      obtain ⟨conditionCode, generatedCondition, accepted⟩ := bind_ok accepted
      obtain ⟨checked, checkedCondition, accepted⟩ := bind_ok accepted
      cases checked
      have sameType := ensure_same checkedCondition
      rcases conditionCode with ⟨native, code⟩
      dsimp only at sameType
      subst native
      obtain ⟨thenCode, generatedThen, accepted⟩ := bind_ok accepted
      obtain ⟨elseCode, generatedElse, accepted⟩ := bind_ok accepted
      obtain ⟨suffix, generatedSuffix, accepted⟩ := bind_ok accepted
      cases accepted
      obtain ⟨⟨_, branchTyped⟩, _⟩ := TypedLexicalWhile.Native.sequence_children nativeTyped
      obtain ⟨_, conditionTyped⟩ := computation_child branchTyped
      obtain ⟨⟨_, thenTyped⟩, ⟨_, elseTyped⟩⟩ := TypedLexicalWhile.Native.conditional_children branchTyped
      exact .terminalIf exactUnique found form conditionFound conditionType
        (extractExpressions context closed residual sourceSignatures declarations conditionSyntax conditionFound typed generatedCondition conditionTyped)
        (thenIH closed residual sourceSignatures declarations projection generatedThen thenTyped)
        (elseIH closed residual sourceSignatures declarations projection generatedElse elseTyped)
        thenStops elseStops (IssuedSuffix.of_accepted generatedSuffix)

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeLexicalCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
/-! The literal compatible match retains native typing of its actual scrutinee
beside the existing native body receipts. The marked hidden allocation only
affects the continuation; its initializer is the raw lowered expression.
One enclosing HasType supplies both parts. Source lookup, Source typing and
compiler occurrence equations stay separate. This is a static collector. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
open Core Frontend SourceInference SourceCoreCompatibleDataMatches
open CompatibleMatchCertificates GenericMatchChildren
open CompatibleEncoding (bind_ok)

def TypedExpression (definitions : DataEnvironment) (administrative : Core.Context)
    (certificate : ExpressionCertificate) : ExpressionCertificate :=
  fun scope id lowered => certificate scope id lowered ∧
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      lowered.expression nativeType definitions

private theorem initializer_child
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {source : TypedSource} {scope : Scope} {binder : TypedBinder} {payload output : Ty}
    {initializer body code : Expr}
    (accepted : SourceCoreSourceCells.letInitialized compilation.sourceCells source scope Renaming.id binder
      output payload initializer body = .ok code)
    {definitions : DataEnvironment} {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    ∃ nativeType, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
      initializer nativeType definitions := by
  rw [allocator] at accepted
  unfold SourceCoreSourceCells.letInitialized at accepted
  obtain ⟨allocation, _allocated, exactCode⟩ := bind_ok accepted
  cases exactCode
  cases typed with | caseE initial _ _ => exact ⟨_, initial⟩

/-- The original real body typing producer runs once. Scrutinee typing is
added from that same emitted hidden-initialization wrapper, without replay. -/
theorem typed_expressions_and_bodies
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reason : Word} {expressionCertificate : ExpressionCertificate}
    {bodyCertificate : BodyCertificate} {code : Expr}
    (certificate : Certificate compilation source scope id resolution result reason
      expressionCertificate bodyCertificate code)
    {administrative : Core.Context} {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    Certificate compilation source scope id resolution result reason
      (TypedExpression definitions administrative expressionCertificate)
      (CompatibleMatchNativeChildren.TypedBody definitions administrative type bodyCertificate) code := by
  have native := CompatibleMatchNativeChildren.Certificate.typed_bodies
    onError allocator sameDefinitions certificate typed
  cases native with
  | matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection expression
      sameType arms fallback branches hiddenCompiled =>
    obtain ⟨nativeType, scrutineeTyped⟩ := initializer_child onError allocator hiddenCompiled typed
    exact .matchWith read allowed form requirements hiddenOwned hiddenFresh scrutineeOwned found projection
      ⟨expression, nativeType, scrutineeTyped⟩ sameType arms fallback branches hiddenCompiled

/-- The actual finite compiler collector supplies each expression factory
with its own native witness and every body with its original ordered action. -/
theorem finite_typed_of_lower
    {compilation : SourceCoreCompatibleDataMatches.Context}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
      (layouts.allocatorAt owner active onError)))
    {definitions : DataEnvironment} (sameDefinitions : compilation.definitions = definitions)
    {lowerExpression : ExpressionLowerer} {lowerBody : BodyLowerer} {fuel : Nat}
    {source : TypedSource} {scope : Scope} {id : StatementId} {resolution : MatchResolution}
    {result : Ty} {reasonAt : ExpressionId → Word} {reason : Word} {code : Expr}
    {expressionCertificate : ExpressionCertificate} {administrative : Core.Context}
    (expressionExtract : ∀ childFuel lowered,
      lowerExpression childFuel source scope resolution.scrutinee reasonAt = .ok lowered →
      ∀ {nativeType}, HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        lowered.expression nativeType definitions → expressionCertificate scope resolution.scrutinee lowered)
    (accepted : lowerWithReasons compilation lowerExpression lowerBody fuel source scope id resolution
      result reasonAt reason = .ok code)
    {type : Ty}
    (typed : HasType (SourceCoreLocalCell.coreContext scope ++ administrative) code type definitions) :
    ∃ requests,
      Certificate compilation source scope id resolution result reason expressionCertificate (Occurs requests) code ∧
      requests.length = resolution.cases.length + (if resolution.defaultBody.isSome then 1 else 0) ∧
      ∀ request ∈ requests,
        (∃ childFuel, lowerBody childFuel source request.scope request.statements result reasonAt reason = .ok request.code) ∧
        HasType (SourceCoreLocalCell.coreContext request.scope ++ administrative) request.code type definitions := by
  have raw := certificate_of_lowerWithReasons
    (expressionCertificate := fun scope id lowered => ∃ childFuel,
      lowerExpression childFuel source scope id reasonAt = .ok lowered)
    (bodyCertificate := fun scope statements code => ∃ childFuel,
      lowerBody childFuel source scope statements result reasonAt reason = .ok code)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩)
    (fun childFuel _ _ _ generated => ⟨childFuel, generated⟩) accepted
  have native := typed_expressions_and_bodies onError allocator sameDefinitions raw typed
  have selected := Certificate.mapExpressionAt native (fun lowered generated => by
    obtain ⟨⟨childFuel, compiled⟩, nativeType, childTyped⟩ := generated
    exact expressionExtract childFuel lowered compiled childTyped)
  exact Certificate.finite_children selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedNativeMatchCollectors
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryBodyProjection
/-! The real prepared ordinary support projects forward to the existing typed
receipt shape. Its BodyWith is built from the one retained JointBody: accepted
flow, compiler-view extraction, canonical Source tree and parameter context are
literal projections. The original support-registry site receipts remain honest
static inputs. Prepared flow at a receiving registry uses the owning issuance
and actual reached diagnostic table; it does not transport universal Sites.

This is a construction interface for new prepared formation packets. Existing
erased StaticMember leaves cannot supply discarded preparation data. Principal
method authority and the mixed positive-family dispatcher remain separate. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryBodyProjection
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedFunctionValues (Header Key)
open CallableIndexedOwnedContextualLambdaJointStaticReceipts (JointBody bodyPolicy callback_of_recipe)
open CallableIndexedOwnedPreparedOrdinaryLambdaSupport (Support PreparedAt)
open CallableIndexedOwnedTypedLambdaStaticBody (Body)
open CallableIndexedOwnedTypedLambdaBodyContinuations (Validity FlowPreserves FlowReflects)

section Joint
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : CallableIndexedNamedGeneration.Compilation compiled.indexed named diagnostics namedCode}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {diagnosticPolicy : AssignmentDiagnosticPolicy}
  {invalidOperand : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Syntax.ValueAssignOp → Word}
  {invalidUnary invalidProjection : SourceCoreElaboration.ErrorSite → Resolved.LocalId → Word}
  {missingDefault : SourceCoreElaboration.ErrorSite → Resolved.LocalId → TypeSystem.Ty → Word}
  (body : JointBody compilation code (Program.ofChecked compiled.sourceProgram) expressionSyntax certificates
    diagnosticPolicy invalidOperand invalidUnary invalidProjection missingDefault)

/-- The compiler-view tree is the exact extraction already retained by JointBody. -/
abbrev actualTree := body.actual.original.original.original.original.tree

variable {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (actualSites : (actualTree body).CatalogSites .reachable bodyRegistry faults)
  (sites : body.tree.CatalogSites .reachable bodyRegistry faults)

/-- There is one body. The callback follows from its actual compiler recipe. -/
def bodyWith : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates
    code (Program.ofChecked compiled.sourceProgram) bodyRegistry faults where
  toContext := body.toBody.toContext
  frame := body.frame
  readFuel := body.readFuel
  policy := bodyPolicy compilation code
  callback := callback_of_recipe compilation body.recipe
  flow := body.flow
  generated := body.generated
  projection := body.projection
  emitted := body.emitted
  actualTree := actualTree body
  actualSites := actualSites
  tree := body.tree
  sites := sites
  valid := body.valid
  unique := body.unique

/-- Typed finish sees the original parameter context, flow, Source tree and syntax. -/
theorem bodyWith_typed :
    Body.of_body_with (bodyWith body actualSites sites) body.syntaxTree = body.toBody := rfl

end Joint

section Support
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {code : Code compiled.indexed function scope administrative}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code)
  (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
  (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)

/-- Forward projection uses the actual prepared support; no second body is chosen. -/
def plain : CallableIndexedOwnedOrdinaryLambdaSupport.Support code bodyRegistry faults where
  caller := support.caller
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  body := bodyWith support.body actualSites sites

theorem plain_typed :
    Body.of_body_with (plain support actualSites sites).body support.body.syntaxTree =
      support.body.toBody := rfl

/-- Captures change only the original Source environment; projection commutes. -/
theorem plain_recapture (environment : Dynamic.Environment) :
    plain (support.recapture environment) actualSites sites =
      (plain support actualSites sites).recapture environment := rfl

/-- Genuine selected history keeps the same owning Header metadata. -/
theorem plain_source_origin {history : History code}
    (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history) :
    CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
      (plain support actualSites sites) history := ⟨origin.metadata⟩

/-- The actual Site, binder policy and body recipe supply provenance for this projection. -/
theorem plain_provenance (prepared : PreparedAt code support)
    (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
    (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence) :
    CallableIndexedOwnedContextualLambdaProvenance.OrdinaryAt code
      (plain support actualSites sites) := by
  cases prepared with
  | recaptured caller compilation site expressionSyntax certificates issued diagnosticPolicy
      body binderPolicy compilerPolicy issuedRecipe bodyView bodyReasons declarations environment =>
    exact .recaptured caller site expressionSyntax certificates
      (bodyWith body actualSites sites) binderPolicy
      (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation body.recipe)
      compilerPolicy issuedRecipe bodyView bodyReasons declarations body.syntaxTree environment callerGlobals callerReceipt

section Flow
variable
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
        (Body.of_body_with (plain prepared baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.preserves_flow
    prepared.namedCompilation captured sameCode prepared.issued prepared.body functions extension faithful
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
        (Body.of_body_with (plain prepared baseActualSites baseSites).body prepared.body.syntaxTree)
        functions (registry := registry) (faults := faults) (headers := headers) (keys := keys)) := by
  rw [plain_typed]
  exact CallableIndexedOwnedContextualLambdaPreparedBodyBounds.reflects_flow
    prepared.namedCompilation captured sameCode prepared.issued prepared.body functions extension faithful
    observations wellFormed rebuilt operandIncluded unaryIncluded interprets budget functionTypes reflection

end Flow
end Support

section Receipts
variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- A prospective positive ordinary leaf retains actual preparation before
erasure. Its existing typed Association is a forward, same-Code projection.
The principal branch needs its own dictionary-preserving prepared constructor. -/
inductive Receipt
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Type where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : Support code)
      (actualSites : (actualTree support.body).CatalogSites .reachable bodyRegistry faults)
      (sites : support.body.tree.CatalogSites .reachable bodyRegistry faults)
      (origin : CallableIndexedOwnedPreparedOrdinaryLambdaSupport.SourceOrigin support history)
      (prepared : PreparedAt code support)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore)
        compiled.indexed.layouts.definitions)
      (callerGlobals : support.caller.globals = compiled.indexed.base.globals.length)
      (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt support.caller function.context function.evidence) :
      Receipt headers keys bodyRegistry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

variable {mapping futureMapping : LocationMap} {world futureWorld : StoreTyping}
  {function : Dynamic.Closure} {native : Value}
  {bindings : List CallableIndexedParameterCertificates.Binding} {parameterCore resultCore : Ty}

/-- No discarded preparation is reconstructed from the old Association. -/
def Receipt.forget
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedContextualTypedClosureReceipts.Association headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore := by
  cases receipt with
  | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed callerGlobals callerReceipt =>
    exact .ordinary owner captured code history (plain support actualSites sites)
      (plain_source_origin support actualSites sites origin) prefixContext globals referenceIndex typed
      (plain_provenance support actualSites sites prepared callerGlobals callerReceipt)

/-- Real map/world growth preserves the prepared packet, Code, tree and history. -/
def Receipt.extend
    (receipt : Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    Receipt headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  cases receipt with
  | ordinary owner captured code history support actualSites sites origin prepared prefixContext globals referenceIndex typed callerGlobals callerReceipt =>
    exact .ordinary owner (captured.extend maps worlds) code history support actualSites sites origin prepared
      prefixContext globals referenceIndex (typed.weaken worlds) callerGlobals callerReceipt

/-- A positive prepared leaf may erase forward under Prop. The reverse
direction is intentionally absent because the old leaf discarded this data. -/
abbrev StaticMember
    (headers : List (Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (Key compiled (Program.ofChecked compiled.sourceProgram)))
    (bodyRegistry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping)
    (function : Dynamic.Closure) (native : Value)
    (bindings : List CallableIndexedParameterCertificates.Binding) (parameterCore resultCore : Ty) : Prop :=
  Nonempty (Receipt headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)

theorem StaticMember.forget
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedContextualTypedClosureReceipts.StaticMember headers keys bodyRegistry faults
      mapping world function native bindings parameterCore resultCore := by
  obtain ⟨receipt⟩ := member
  exact ⟨receipt.forget⟩

theorem StaticMember.extend
    (member : StaticMember headers keys bodyRegistry faults mapping world function native bindings parameterCore resultCore)
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    StaticMember headers keys bodyRegistry faults futureMapping futureWorld function native bindings parameterCore resultCore := by
  obtain ⟨receipt⟩ := member
  exact ⟨receipt.extend maps worlds⟩

end Receipts

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryBodyProjection
end
