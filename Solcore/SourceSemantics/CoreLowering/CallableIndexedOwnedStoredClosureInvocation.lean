import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedGeneralFunctionSelection
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointLambdaReadyContinuations
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExtendedJointReadyContinuations

/-! Invocation starts at the actual pool after ordered arguments. The finite
association retains unrestricted ordinary or principal closure provenance,
original body Syntax and exact parameter/result compiler receipts. Captured
history and the current caller row are separate. Original payload application,
parameter allocation, strict body continuation and caller restoration retain
one actual returned pool. Legacy arbitrary-prefix selections need additional
authentic formation receipts; call-site stage/coercion gates remain separate.
No whole expression execution or completed body meaning is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Only full selected constructors with their genuine invocation prefixes
enter this association. Syntax belongs to exactly the retained same-Code body. -/
inductive Association (headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)))
    (keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram)))
    (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (mapping : LocationMap) (world : StoreTyping) :
    Dynamic.Closure → Value → List CallableIndexedParameterCertificates.Binding → Ty → Ty → Prop where
  | ordinary {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedOrdinaryLambdaSupport.Support code registry faults)
      (sourceOrigin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin support history)
      (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
        (values := .initial compiled.compatible.checked) support.caller)
      (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason)
      (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
        support.body.context (.statements true function.body) function.resultType) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore
  | principal {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
      (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
      (captured : Captures compiled.indexed mapping world scope function.captured actual)
      (code : Code compiled.indexed function scope captured.administrative) (history : History code)
      (support : CallableIndexedOwnedMethodLambdaSupport.Support code registry faults)
      (sourceOrigin : CallableIndexedOwnedMethodLambdaSupport.SourceOrigin support history)
      (observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
        (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
        headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
      (leading : captured.administrative[0]? = some support.principal.named.signature.parameterType)
      (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
      (typed : RuntimeValueHasType world (value code captured.embedding history.native actual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) compiled.indexed.layouts.definitions)
      (escaped : faults .controlEscapedFunction code.compilation.internalReason)
      (syntaxTree : GenericImperativeMatch.Syntax function.source (support.expressionSyntax function.source)
        support.body.context (.statements true function.body) function.resultType) :
      Association headers keys registry faults mapping world function
        (value code captured.embedding history.native actual) code.receipt.loweredParameters
        code.receipt.parameterCore code.receipt.resultCore

/-- The complete association reconstructs the exact same selected payload;
there is no inverse function-model inclusion or weaker representation. -/
theorem Association.selection {mapping : LocationMap} {world : StoreTyping}
    {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
    {parameterCore resultCore : Ty}
    (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore) :
    CallableIndexedOwnedGeneralFunctionSelection.Selection headers keys registry faults mapping world
      (FunctionValues.sourceType function) (.closure function) native
      (CallableContract.functionType parameterCore resultCore) := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex typed _escaped _syntax =>
    exact .ordinary_lambda owner captured code history support sourceOrigin prefixContext observed referenceIndex typed
  | principal owner captured code history support sourceOrigin observed leading referenceIndex typed _escaped _syntax =>
    exact .principal_lambda owner captured code history support sourceOrigin observed leading referenceIndex typed

variable (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))

/-- Every semantic/effect field and stable row describes the actual reached
pool returned by the original invocation, including fault outcomes. -/
def ResultAt {index : ProtectedStateTransition.Index} (initial : State headers keys index)
    (function : Dynamic.Closure) (resultCore : Ty) (outcome : Dynamic.ExpressionOutcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends index.mapping finalMap ∧ WorldExtends index.world finalWorld ∧
    AdministrativePreserved index.mapping index.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend index.heap after ∧
    ∃ reached : State headers keys (index.extend finalMap finalWorld after finalStore),
      Relates initial reached ∧ StableRows reached

section Invocation
variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows initial)

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- Actual raw arguments and current row admission select the original
parameter entry and strict shared-family body IH. The saved caller is current. -/
theorem preserves_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      ResultAt (registry := registry) (faults := faults) functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.source_continuation
      (nativeArguments := nativeArguments) captured code history support.body.toContext functions owner initial
      (support.body_origin escaped) beforeTyped raw stable support.caller observed prefixContext
      sourceOrigin.metadata syntaxTree wellFormed rfl budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support sourceOrigin observed leading referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_source_continuation
      (nativeArguments := nativeArguments) functions wellFormed captured code history support sourceOrigin owner
      observed leading initial escaped beforeTyped raw stable syntaxTree budget below
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_preserves_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning trace within
    exact ⟨value, finalStore, evaluated, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- The original measured payload prefix keeps its strict body bound and
reconstructs an independently sized Source call at the same returned pool. -/
theorem reflects_at (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      ResultAt (registry := registry) (faults := faults) functions initial function resultCore outcome after value finalStore := by
  cases association with
  | ordinary owner captured code history support sourceOrigin prefixContext observed referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointLambdaReadyContinuations.native_continuation
      captured code history support.body.toContext functions owner initial
      (support.body_origin escaped) beforeTyped raw stable support.caller observed prefixContext
      sourceOrigin.metadata syntaxTree wellFormed rfl budget below
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩
  | principal owner captured code history support sourceOrigin observed leading referenceIndex _typed escaped syntaxTree =>
    have raw : Dynamic.ValuesHaveTypes function.context before arguments support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using argumentsTyped
    obtain ⟨currentMetadata, currentCarried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact observed.reference
    have meaning := CallableIndexedOwnedExtendedJointReadyContinuations.method_lambda_native_continuation
      functions wellFormed captured code history support sourceOrigin owner observed leading initial escaped
      beforeTyped raw stable syntaxTree budget below
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      CallableIndexedOwnedLambdaInvocationBounds.application_reflects_bounded_at
        captured code history support.body.toContext functions represented owner initial heaps locals
        reference currentCarried (CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
        (support.body_origin escaped) budget meaning completed within
    exact ⟨sourceSize, outcome, after, trace, finalMap, finalWorld, result, finalHeaps, maps, worlds,
      frame, metadata, reached, related, StableRows.after_administrative initial reached stable frame⟩

end Invocation

section Caller
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  {slots : ProtectedStateTransition.Index → Prop}
  (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots callerProtocol)

/-- Repacking exposes both the exact invocation pool and the returned caller
whose pool equals it. Every original semantic and effect receipt is retained. -/
def CallerResultAt {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    (function : Dynamic.Closure) (resultCore : Ty) (outcome : Dynamic.ExpressionOutcome)
    (after : Dynamic.Heap) (value : Value) (finalStore : Store) : Prop :=
  ∃ finalMap finalWorld,
    FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      finalMap finalWorld function.resultType resultCore faults outcome value ∧
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions finalMap finalWorld after finalStore ∧
    LocationMap.Extends index.mapping finalMap ∧ WorldExtends index.world finalWorld ∧
    AdministrativePreserved index.mapping index.store finalMap finalStore ∧ Dynamic.HeapMetadataExtend index.heap after ∧
    ∃ reached : State headers keys (index.extend finalMap finalWorld after finalStore),
      Relates (carrier.pool initial) reached ∧ StableRows reached ∧
      ∃ returned : callerProtocol.State (index.extend finalMap finalWorld after finalStore),
        carrier.pool returned = reached ∧ callerProtocol.Relates initial returned

/-- The real invocation effects authorize restoration of the original caller
around exactly the same reached pool. No canonical slots are inferred. -/
theorem ResultAt.restore {index : ProtectedStateTransition.Index} (initial : callerProtocol.State index)
    {function : Dynamic.Closure} {resultCore : Ty} {outcome : Dynamic.ExpressionOutcome}
    {after : Dynamic.Heap} {value : Value} {finalStore : Store}
    (result : ResultAt (registry := registry) (faults := faults) functions
      (carrier.pool initial) function resultCore outcome after value finalStore) :
    CallerResultAt (registry := registry) (faults := faults) functions carrier initial
      function resultCore outcome after value finalStore := by
  obtain ⟨finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata, reached, related, stable⟩ := result
  obtain ⟨returned, samePool, callerRelated⟩ := carrier.restore initial reached maps worlds frame metadata related
  exact ⟨finalMap, finalWorld, represented, heaps, maps, worlds, frame, metadata,
    reached, related, stable, returned, samePool, callerRelated⟩

variable {certificates : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) →
    SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {expressionSyntax : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram) → ExpressionId → Prop}
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {callerScope : SourceCoreLocalCell.Scope} {callerCanonical : Environment}
  {function : Dynamic.Closure} {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}
  (association : Association headers keys registry faults mapping world function native bindings parameterCore resultCore)
  (initial : callerProtocol.State ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
    mapping world bindings arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world before store)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments
    (function.parameters.map (fun binding => binding.scheme.body)))
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (stable : StableRows (carrier.pool initial))

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- The stronger actual caller is returned using the same complete original
application result, current saved frame and actual administrative receipts. -/
theorem preserves_for (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.PreservingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
      size callContext callerEvidence function.evidence before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [native, DataPatternValues.packValues nativeArguments] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallerResultAt (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨value, finalStore, evaluated, result⟩ := preserves_at functions wellFormed association
    (carrier.pool initial) represented heaps beforeTyped argumentsTyped locals stable budget below trace within
  exact ⟨value, finalStore, evaluated, result.restore functions carrier initial⟩

include wellFormed association represented heaps beforeTyped argumentsTyped locals stable in
/-- Native reflection restores that same actual caller and retains the
independently reconstructed Source call, without comparing the two grades. -/
theorem reflects_for (budget : Nat)
    (below : CallableIndexedOwnedExtendedJointReadyContinuations.ReflectingBelow
      (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      (certificates := certificates) (expressionSyntax := expressionSyntax) functions wellFormed budget)
    {size : Nat} {callContext : SourceSemantics.Context} {callerEvidence : Dynamic.EvidenceEnvironment}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues nativeArguments] store
      CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      RecursiveNamedCallBounds.CallOutcome (Program.ofChecked compiled.sourceProgram)
        sourceSize callContext callerEvidence function.evidence before (.closure function) arguments outcome after ∧
      CallerResultAt (registry := registry) (faults := faults) functions carrier initial
        function resultCore outcome after value finalStore := by
  obtain ⟨sourceSize, outcome, after, trace, result⟩ := reflects_at functions wellFormed association
    (carrier.pool initial) represented heaps beforeTyped argumentsTyped locals stable budget below completed within
  exact ⟨sourceSize, outcome, after, trace, result.restore functions carrier initial⟩
end Caller
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedStoredClosureInvocation
