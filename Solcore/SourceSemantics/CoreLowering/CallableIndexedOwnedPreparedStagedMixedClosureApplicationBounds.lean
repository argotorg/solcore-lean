import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedTerminalClosureParentPreservation

/-! Contextual application over the statically chosen empty, terminal,
discard or sequence body.
All branches use the same authentic Association Code and BodyWith.toContext.
The strict Root IH constructs body ports internally; the original parameter
installation and saved caller restoration return their literal pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : SourceCoreCallableIndexedPrograms.Completion compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

section ContextualApplication
variable (association : Association headers keys bodyRegistry semanticFaults mapping world function native
    bindings parameterCore resultCore)
  (packet : PacketFor association stages)
  (supported : SupportFor association stages packet)
  {before : Dynamic.Heap} {store : Store} {scope : SourceCoreLocalCell.Scope} {canonical : Environment}
  (caller : State headers keys ⟨scope, mapping, world, before, store, canonical⟩)
  {sources : List Dynamic.Value} {values : List Value}
  (raw : CallableIndexedOwnedStoredClosureSourceArguments.SourceArguments function before sources)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)

include supported raw represented heaps stable runtime in
/-- The actual Association and chosen packet retain the original parameter
context. Each body branch constructs its application port from the strict Root IH. -/
theorem application_preserves (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation context before (.closure function) sources outcome after) (within : size ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates [native, DataPatternValues.packValues values] store
        CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        finalMap finalWorld function.resultType resultCore callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  cases association with
  | ordinary owner captured code history support _origin _prefix globals referenceIndex _typed _provenance =>
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have below := CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.selected_body_preserves_below
        supported children (Nat.le_refl budget)
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller stable raw.heaps typed
          terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | discard discard =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := discard) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | sequence sequence =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := sequence) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | lexical lexical =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := lexical) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | imperative imperative =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := imperative) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | empty empty =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := empty)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) trace
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have below := CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.selected_body_preserves_below
        supported children (Nat.le_refl budget)
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller stable raw.heaps typed
          terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | discard discard =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := discard) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | sequence sequence =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := sequence) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | lexical lexical =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := lexical) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | imperative imperative =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := imperative) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | empty empty =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds.application_preserves
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := empty)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) trace
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include supported raw represented heaps stable runtime in
/-- Reflection uses the packet-selected Source scope. The original parameter
installation, independent Source grade and literal returned caller are preserved. -/
theorem application_reflects (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size [native, DataPatternValues.packValues values] store
      CallableIndexedLambdaCalls.applyPayload value finalStore) (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context before (.closure function) sources outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        finalMap finalWorld function.resultType resultCore callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : State headers keys ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        Relates caller returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission
          (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
            (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
          context function.resultType outcome returned := by
  cases association with
  | ordinary owner captured code history support _origin _prefix globals referenceIndex _typed _provenance =>
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have below := CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.selected_body_reflects_below
        supported children (Nat.le_refl budget)
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller stable raw.heaps typed
          terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | discard discard =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := discard) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | sequence sequence =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := sequence) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | lexical lexical =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := lexical) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | imperative imperative =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := imperative) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | empty empty =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := empty)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) completed
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have below := CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.selected_body_reflects_below
        supported children (Nat.le_refl budget)
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller stable raw.heaps typed
          terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | discard discard =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := discard) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | sequence sequence =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedDiscardSequenceLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := sequence) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | lexical lexical =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedLexicalLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := lexical) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | imperative imperative =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedImperativeLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := imperative) (support := supported)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | empty empty =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedEmptyLambdaApplicationBounds.application_reflects
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := empty)
          (owner := owner) (caller := caller) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) completed
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end ContextualApplication

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds
