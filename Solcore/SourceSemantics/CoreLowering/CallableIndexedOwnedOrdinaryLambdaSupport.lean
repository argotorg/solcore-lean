import Solcore.SourceSemantics.CoreLowering.CallableIndexedActualNamedSourceReceipts
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds

/-! Genuine ordinary lambda support retains its actual cached Header and
accepted Site beside unrestricted same-Code static body receipts. The full
Source frame, compiler Trees, contexts and diagnostic sites stay original.
The ranked ordinary relation and every existing function model stay unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- An authentic cached Header accompanies the exact accepted lambda Code.
The expression grammar remains the genuine static body grammar supplied here. -/
structure Support (code : Code compiled.indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source caller.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed caller.named
  active : code.active = []
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
    code (Program.ofChecked compiled.sourceProgram) registry faults

variable
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence environment scope administrative)

/-- The real Site and complete same-Code body construct support directly.
The independently established Source frame is retained verbatim. -/
def Support.of_site {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults) :
    Support site.code registry faults :=
  ⟨caller, expressionSyntax, certificates, rfl, site.compilation, site.active, body⟩

variable {code : Code compiled.indexed function scope administrative}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults)

include support in
/-- Source attribution is derived from the actual cached Header record. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original (CallableIndexedActualNamedSourceReceipts.header_record compiled support.caller)

include support in
/-- The original static body retains uniqueness of this complete Source. -/
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Changing only the stored actual capture environment retains every same-Code
static receipt, including its original Source frame and body diagnostics. -/
def Support.recapture (environment : Dynamic.Environment) :
    Support (RecursiveNamedLambdaFormationHeads.recaptureCode
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code environment) registry faults where
  caller := support.caller
  expressionSyntax := support.expressionSyntax
  certificates := support.certificates
  source := support.source
  compilation := support.compilation
  active := support.active
  body := RecursiveNamedLambdaFormationHeads.recaptureBodyWith
    (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) code support.body environment

/-- Captured history retains the complete actual named compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.caller.named

/-- The actual selected named hook constructs the original full Source seed. -/
theorem Support.of_site_origin
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    {hook : Word}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named caller.named.signature.key) = some hook) :
    SourceOrigin (Support.of_site caller site expressionSyntax certificates body)
      (site.historyAt selected (CallableIndexedActualNamedSourceReceipts.header_record compiled caller)) := ⟨rfl⟩

/-- The original stage descriptor authenticates the same actual lambda payload.
Source attribution is derived from support; captures and history remain real. -/
theorem Support.stage_origin {mapping : LocationMap} {world : StoreTyping} {actual : Environment}
    (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (actualCode : Code compiled.indexed function scope captured.administrative)
    (actualSupport : Support actualCode registry faults) (history : History actualCode) :
    CallableLedger.OriginRep compiled.indexed.base.plan compiled.indexed.ancestry.graph.inputs.callable.table
      (.closure function) (value actualCode captured.embedding history.native actual) := by
  have prepared := RecursiveNamedPreparedStageContracts.of_compiled compiled
    compiled.indexed.ancestry.graph.inputs.callableSelected
  exact CompatibleAmbientStageOrigins.actual_lambda_origin prepared.accepted actualCode.descriptor
    actualSupport.source_receipt actualCode.viewOfSource actualSupport.unique actualCode.found
    (actualCode.form.trans actualCode.sourceForm) _

/-- Unrestricted same-Code static fields project to the shared body kernel.
Its original Source frame and compiler fields stay unchanged. -/
def Support.origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults where
  layouts := compiled.indexed.layouts
  owner := code.compilation.owner
  active := code.active
  frameLayout := compiled.indexed.ancestry.layout.frame
  globals := compiled.indexed.base.globals.length
  onError := code.allocationError
  function := function
  expressionSyntax := support.expressionSyntax function.source
  certificates := support.certificates support.body.readFuel function.source
  validity := fun context => CompatibleRuntimeContextValidity.Valid code.compilation.solvedRequirements context function.evidence
  diagnosticPolicy := .reachable
  administrative := administrative
  context := support.body.context
  scope := code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
  output := code.receipt.resultCore
  code := code.receipt.body
  fellThrough := code.compilation.internalReason
  escaped := code.compilation.internalReason
  solved := code.compilation.solvedRequirements
  body := { flow := support.body.flow
            tree := support.body.tree
            sites := support.body.sites
            initialValid := support.body.valid
            projection := support.body.projection
            unique := support.body.unique
            emitted := support.body.emitted }
  definitions := rfl
  registered := CallableIndexedAmbient.frame_registered compiled.indexed
  escapedFault := escaped
  extend := fun valid extended => valid.extend extended
  runtimeOf := fun valid => valid

/-- The actual static parameter context, full Source frame and emitted body
remain definitionally those of this same Code. -/
def Support.body_origin (escaped : faults .controlEscapedFunction code.compilation.internalReason) :
    CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := Program.ofChecked compiled.sourceProgram)
      code support.body.toContext registry faults :=
  ⟨support.origin escaped, support.body.frame, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaSupport
