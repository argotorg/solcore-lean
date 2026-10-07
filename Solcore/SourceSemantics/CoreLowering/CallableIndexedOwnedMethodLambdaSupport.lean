import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaFrames
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds

/-! Header-free static support retains a genuine method principal and the
same actual lambda Code. The complete generic body Tree, sites, context,
Source frame and dictionary remain static receipts. Original Header-ranked
support and its public interfaces stay separate and unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedHistory CallableIndexedLambdaValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- This alternative stores genuine trait Source authority beside the emitted
compiler seed; it contains no body execution law. -/
structure Support (code : Code compiled.indexed function scope administrative)
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep) where
  method : ExecutableImplMethods.CheckedMethod
  principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  source : function.source = CallableIndexedNamedGeneration.source principal.named
  compilation : code.compilation = CallableIndexedNamedGeneration.context compiled.indexed principal.named
  active : code.active = []
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
    code (Program.ofChecked compiled.sourceProgram) registry faults

variable {method : ExecutableImplMethods.CheckedMethod}
  (principal : CallableIndexedOwnedMethodPrincipal.Principal compiled method)
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment}
  (site : CallableIndexedLambdaGeneration.Site compiled.indexed principal.named parameters result statements
    context principal.dictionary environment scope administrative)

/-- Actual factory Code and original static body fields construct support.
The Source frame is established from the genuine method occurrence. -/
def Support.of_site {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults) :
    Support site.code registry faults :=
  ⟨method, principal, expressionSyntax, certificates, rfl, site.compilation, site.active,
    { body with frame := CallableIndexedOwnedMethodLambdaFrames.closure_frame principal site wellFormed runtime covers typed }⟩

variable {code : Code compiled.indexed function scope administrative}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (support : Support code registry faults)

include support in
/-- Source attribution is derived from the actual cached method record. -/
theorem Support.source_receipt :
    LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
      code.compilation.owner code.active function.source := by
  rw [support.compilation, support.active, support.source]
  exact .original support.principal.record

include support in
/-- The original static body retains uniqueness of this complete Source. -/
theorem Support.unique : NodeOccurrencesUnique function.source := support.body.unique

/-- Captured history retains the full genuine method compiler seed. -/
structure SourceOrigin (history : History code) : Prop where
  metadata : history.metadata = CallableIndexedNamedGeneration.state support.principal.named

/-- The genuine selected factory hook constructs this complete Source seed. -/
theorem Support.of_site_origin
    {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
    (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
    (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context principal.sourceBody.source)
    (covers : principal.dictionary.Covers context)
    (typed : ExpressionHasType principal.sourceBody.source context site.code.id site.code.sourceNode.type)
    (expressionSyntax : TypedSource → ExpressionId → Prop)
    (certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked) expressionSyntax certificates
      site.code (Program.ofChecked compiled.sourceProgram) registry faults)
    {hook : Word}
    (selected : compiled.indexed.ancestry.graph.inputs.callable.table.idAt?
      (.named principal.named.signature.key) = some hook) :
    SourceOrigin (Support.of_site principal site wellFormed runtime covers typed expressionSyntax certificates body)
      (site.historyAt selected principal.record) := ⟨rfl⟩

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

/-- Generic same-Code static body fields project to the shared body kernel.
No ordinary Header or function instantiation is introduced. -/
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

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedMethodLambdaSupport
