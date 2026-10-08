import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries

/-! Genuine unrestricted ordinary support forms a closure at its actual
nested Header packet. Source attribution and the full carried seed stay original.
Forward inclusion transfers only the new closure, with one function model for
all actual input/output heaps and the unchanged reached packet. -/
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
    head.issued head.diagnosticPolicy head.body head.produced.binderPolicy environment
end Seed

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
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

include packet prefixContext observed inclusion prepared in
/-- The original actual formation supplies the closure. Only its function
representation is transferred forward to the caller's model. -/
theorem formation
    (stored : RuntimeStoreHasTypes world store compiled.indexed.layouts.definitions)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = []) :
    Dynamic.ExpressionEvaluates (Program.ofChecked compiled.sourceProgram) function.context function.evidence
      function.source function.captured heap code.id (.closure function) heap ∧
    Evaluates actual store (code.lowered.expression.rename captured.embedding)
      (.inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual)) store ∧
    functions.Represents registry mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding (history_at captured code support owner initial packet).native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
    (∀ result finalStore, Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore →
      result = .inRight .word (value code captured.embedding (history_at captured code support owner initial packet).native actual) ∧
      finalStore = store) := by
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
  obtain ⟨sourceTrace, native, represented⟩ := CallableIndexedLambdaValues.formation
    captured code history (Program.ofChecked compiled.sourceProgram) heap ordinary coercions stored reference read
  have nativeTyped := (CallableIndexedLambdaValues.model compiled.indexed profile).runtime_hasType
    (registry := registry) represented
  have rich : CallableIndexedOwnedPreparedOrdinaryLambdaValues.Represents headers keys registry faults
      mapping world (FunctionValues.sourceType function) (.closure function)
      (value code captured.embedding history.native actual)
      (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) :=
    .prepared_ordinary owner captured code history support (source_origin captured code support owner initial packet)
      prefixContext observed (reference_index captured code support) nativeTyped prepared
  exact ⟨sourceTrace, native, inclusion rich, fun _ _ completed => Core.evaluation_deterministic completed native⟩

/-- The output retains all ordinary leaf effects and the exact packet state. -/
def ResultAt (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap) (result : Value) (finalStore : Store) : Prop :=
  Evaluates actual store (code.lowered.expression.rename captured.embedding) result finalStore ∧
  GenericExpressionMeaning.ResultRepresents
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
      functions)
    mapping world code.sourceNode.type code.lowered.type faults outcome result ∧
  CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world after finalStore ∧
  LocationMap.Extends mapping mapping ∧ WorldExtends world world ∧
  AdministrativePreserved mapping store mapping finalStore ∧ Dynamic.HeapMetadataExtend heap after ∧
  ∃ reached : (CallableIndexedOwnedNestedCanonicalState.protocol (headers := headers) owner support.caller).State
      ⟨scope, mapping, world, after, finalStore, canonical⟩,
    (CallableIndexedOwnedNestedCanonicalState.protocol owner support.caller).Relates ⟨initial, packet⟩ reached ∧
    PostAdmission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      function.context code.sourceNode.type outcome reached

variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) function.context function.source)
  (covers : function.evidence.Covers function.context)
  (locals : Dynamic.EnvironmentAgrees heap function.context.locals function.captured)
  (typed : ExpressionHasType function.source function.context code.id code.sourceNode.type)
  (sourceType : code.sourceNode.type = FunctionValues.sourceType function)
  (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
  (coercions : code.sourceNode.coercions = [])
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    functions mapping world heap store)
  (admitted : Admission (CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
    function.context ⟨initial, packet⟩)

include prefixContext observed inclusion prepared sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- Original Source value and fault inversion select the authentic lambda
leaf. Its proved formation supplies the actual native and admitted post. -/
theorem preserves_at {size : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) size
      function.context function.evidence function.source function.captured heap code.id outcome after) :
    ∃ result finalStore, ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore := by
  cases trace.sound with
  | value evaluated =>
    obtain ⟨rfl, rfl⟩ := RecursiveNamedLambdaFormationHeads.source_value_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions evaluated
    obtain ⟨sourceTrace, native, represented, _determined⟩ :=
      formation captured code support prepared owner initial packet profile prefixContext observed functions inclusion heaps.runtime_hasTypes ordinary coercions
    have valueRep : ValueRep compiled.compatible.checked registry
        functions mapping world
        code.sourceNode.type (.closure function)
        (value code captured.embedding (history_at captured code support owner initial packet).native actual) code.lowered.type := by
      rw [sourceType, CallableIndexedOwnedAdmittedMethodLambdaFormation.native_type captured code]
      exact .function represented
    have post := after_expression
      (bridge := CallableIndexedOwnedOrdinaryLambdaEntries.bridge (headers := headers) owner support.caller)
      (context := function.context) (program := Program.ofChecked compiled.sourceProgram)
      ⟨initial, packet⟩ ⟨initial, packet⟩ admitted wellFormed runtime covers locals typed
      (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace) (AdministrativePreserved.refl mapping store)
    exact ⟨_, store, native, .value valueRep, heaps, .refl _, .refl _, .refl _ _, .refl _,
      ⟨initial, packet⟩, Relates.refl initial, post⟩
  | fault failed =>
    exact False.elim (RecursiveNamedLambdaFormationHeads.excludes_fault_of_code
      (values := .initial compiled.compatible.checked) (indexed := compiled.indexed)
      (program := Program.ofChecked compiled.sourceProgram) code support.unique coercions failed)

include prefixContext observed inclusion prepared sourceType ordinary coercions heaps admitted wellFormed runtime covers locals typed in
/-- The original native completion is deterministic against authentic
formation; its independently sized Source trace supplies the same admission. -/
theorem reflects_at {size : Nat} {result : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (code.lowered.expression.rename captured.embedding) result finalStore) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.ExpressionOutcome (Program.ofChecked compiled.sourceProgram) sourceSize
        function.context function.evidence function.source function.captured heap code.id outcome after ∧
      ResultAt (registry := registry) (faults := faults) captured code support owner initial packet functions outcome after result finalStore := by
  obtain ⟨sourceTrace, _native, _represented, determined⟩ :=
    formation captured code support prepared owner initial packet profile prefixContext observed functions inclusion heaps.runtime_hasTypes ordinary coercions
  obtain ⟨rfl, rfl⟩ := determined result finalStore completed.sound
  obtain ⟨sourceSize, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size
    (Dynamic.ExpressionEvaluatesOutcome.value sourceTrace)
  obtain ⟨nativeResult, reachedStore, resultAt⟩ := preserves_at captured code support prepared owner initial packet profile prefixContext observed functions inclusion
    wellFormed runtime covers locals typed sourceType ordinary coercions heaps admitted sized
  obtain ⟨rfl, rfl⟩ := determined nativeResult reachedStore resultAt.1
  exact ⟨sourceSize, _, heap, sized, resultAt⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
