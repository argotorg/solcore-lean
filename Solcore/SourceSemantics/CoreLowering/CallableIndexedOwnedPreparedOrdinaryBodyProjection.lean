import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaSupport
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualTypedClosureReceipts

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
      body binderPolicy compilerPolicy bodyView bodyReasons declarations environment =>
    exact .recaptured caller site expressionSyntax certificates
      (bodyWith body actualSites sites) binderPolicy
      (CallableIndexedOwnedContextualLambdaBodyRecipes.Retained.of_recipe compilation body.recipe)
      compilerPolicy bodyView bodyReasons declarations body.syntaxTree environment callerGlobals callerReceipt

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
