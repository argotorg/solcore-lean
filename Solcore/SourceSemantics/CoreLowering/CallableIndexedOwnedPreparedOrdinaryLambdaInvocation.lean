import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedOrdinaryLambdaFormation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAdmittedExpressionBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredArgumentAlignment
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredNativePackReceipts

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
  obtain ⟨result, finalStore, native, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related, post⟩ :=
    CallableIndexedOwnedPreparedOrdinaryLambdaFormation.preserves_at
      (function := head.function environment) (actual := actual)
      captured code support (head.prepared environment) owner initial.val initial.property profile rfl observed functions inclusion
      wellFormed (by simpa only [sameSource, Formation.function, CallableIndexedLambdaGeneration.closure] using runtime) covers locals actualTyped head.sourceType
      head.ordinary head.coercions heaps admitted original
  have native : Evaluates actual store (lowered.expression.rename ξ) result finalStore := by
    simpa only [code, Formation.code, recaptureCode, head.produced.emitted, captured, captures_for] using native
  have represented : GenericExpressionMeaning.ResultRepresents (model (registry := registry) functions)
      mapping world code.sourceNode.type lowered.type faults outcome result := by
    simpa only [model, code, Formation.code, recaptureCode, head.produced.emitted] using represented
  exact ⟨result, finalStore, mapping, world, native, represented, finalHeaps, maps, worlds, frame, metadata,
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
  obtain ⟨sourceSize, outcome, after, trace, native, represented, finalHeaps, maps, worlds, frame, metadata,
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
      mapping world code.sourceNode.type lowered.type faults outcome value := by
    simpa only [model, code, Formation.code, recaptureCode, head.produced.emitted] using represented
  exact ⟨sourceSize, outcome, after, mapping, world, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata,
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
