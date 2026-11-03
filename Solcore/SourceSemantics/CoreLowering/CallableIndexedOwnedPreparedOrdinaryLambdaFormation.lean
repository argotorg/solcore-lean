import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedMethodLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaValues
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedOrdinaryLambdaEntries

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
