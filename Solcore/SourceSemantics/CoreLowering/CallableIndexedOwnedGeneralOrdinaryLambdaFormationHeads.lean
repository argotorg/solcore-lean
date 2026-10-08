import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds

/-! An accepted ordinary Site retains unrestricted same-Code static body
support. At each actual input its genuine nested Header packet and represented
environment construct captures and full carried history. All heaps use the
supplied function model; forward inclusion transfers only the formed closure. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedOrdinaryLambdaSupport CallableIndexedOwnedSourceAdmission
open RecursiveNamedLambdaFormationHeads

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (caller : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))
  (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)

/-- This original compiler receipt contains no dynamic capture or meaning
factory. Only the actual input fills its stored capture environment. -/
structure Formation (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) where
  parameters : List TypedBinder
  result : TypeSystem.Ty
  statements : List StatementId
  site : CallableIndexedLambdaGeneration.Site compiled.indexed caller.named parameters result statements
    context evidence [] scope (nativePrefix (values := .initial compiled.compatible.checked) caller)
  expressionSyntax : TypedSource → ExpressionId → Prop
  certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate
  body : CallableIndexedLambdaStaticBodySupport.BodyWith (values := .initial compiled.compatible.checked)
    expressionSyntax certificates site.code (Program.ofChecked compiled.sourceProgram) registry faults
  identifier : site.code.id = id
  emitted : site.code.lowered = lowered
  sourceType : site.code.sourceNode.type = FunctionValues.sourceType
    (CallableIndexedLambdaGeneration.closure caller.named parameters result statements context evidence [])
  ordinary : Dynamic.OrdinaryRequirementLayout site.code.sourceNode.requirements site.code.sourceNode.coercions []
  coercions : site.code.sourceNode.coercions = []

variable {caller context evidence}

/-- Recapture retains the complete original Source occurrence and dictionary. -/
def Formation.function {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Dynamic.Closure :=
  CallableIndexedLambdaGeneration.closure caller.named head.parameters head.result head.statements
    context evidence environment

/-- The accepted Code is reused with only its actual capture environment. -/
def Formation.code {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Code compiled.indexed (head.function environment) scope
      (nativePrefix (values := .initial compiled.compatible.checked) caller) :=
  recaptureCode (values := .initial compiled.compatible.checked) (indexed := compiled.indexed) head.site.code environment

/-- The genuine Header and full unrestricted static body remain the same. -/
def Formation.support {scope id lowered}
    (head : Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)
    (environment : Dynamic.Environment) : Support (head.code environment) registry faults :=
  (Support.of_site caller head.site head.expressionSyntax head.certificates head.body).recapture environment

variable (caller context evidence)

def Certificate : GenericExpressionMeaning.Certificate :=
  fun scope id lowered => Nonempty (Formation (registry := registry) (faults := faults) caller context evidence scope id lowered)

def bridge (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) :=
  CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner caller

def model (functions : FunctionModel compiled.compatible.checked.catalog
    (CallableIndexedAmbient.ambientDefinitions compiled.indexed)) :=
  CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions

variable
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  (inclusion : (CallableIndexedOwnedGeneralLambdaValues.model headers keys registry faults profile).Includes functions)
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
theorem preserves_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.PreservesAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate (registry := registry) (faults := faults) caller context evidence) faults size := by
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
  let support : Support code registry faults := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have original : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      (head.function environment).context (head.function environment).evidence (head.function environment).source
      (head.function environment).captured before code.id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using trace
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using typed
  obtain ⟨result, finalStore, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.preserves_at
      (function := head.function environment) (actual := actual)
      captured code support owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.ordinary head.coercions heaps admitted original
  have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.emitted, captured, captures_for] using native
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      mapping world code.sourceNode.type lowered.type faults outcome result := by
    simpa only [model, code, Formation.code, recaptureCode, head.emitted] using represented
  exact ⟨result, finalStore, mapping, world, native, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

include inclusion complete globals slots prefixZero wellFormed runtime covers sameSource in
/-- Actual native formation reflects the original Source leaf with its own
independent grade, preserving the same caller packet and generic heap model. -/
theorem reflects_at (size : Nat) :
    CallableIndexedOwnedAdmittedExpressionBounds.ReflectsAt (bridge (headers := headers) caller owner)
      (model (registry := registry) functions) context evidence source
      (Certificate (registry := registry) (faults := faults) caller context evidence) faults size := by
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
  let support : Support code registry faults := head.support environment
  have sourceFound : source.lookupExpression? id = some code.sourceNode := by
    simpa only [sameSource, code, Formation.code, recaptureCode,
      CallableIndexedLambdaGeneration.closure, head.identifier] using head.site.code.sourceFound
  have same := Option.some.inj (found.symm.trans sourceFound)
  subst node
  have actualTyped : ExpressionHasType (head.function environment).source (head.function environment).context
      code.id code.sourceNode.type := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using typed
  have actualCompleted : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) value finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.emitted, captured, captures_for] using completed
  obtain ⟨sourceSize, outcome, after, trace, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedAdmittedGeneralOrdinaryLambdaFormation.reflects_at
      (function := head.function environment) (actual := actual)
      captured code support owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.ordinary head.coercions heaps admitted actualCompleted
  have sourceTrace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
      context evidence source environment before id outcome after := by
    simpa only [sameSource, code, Formation.code, Formation.function,
      CallableIndexedLambdaGeneration.closure, recaptureCode, head.identifier] using trace
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      mapping world code.sourceNode.type lowered.type faults outcome value := by
    simpa only [model, code, Formation.code, recaptureCode, head.emitted] using represented
  exact ⟨sourceSize, outcome, after, mapping, world, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralOrdinaryLambdaFormationHeads
