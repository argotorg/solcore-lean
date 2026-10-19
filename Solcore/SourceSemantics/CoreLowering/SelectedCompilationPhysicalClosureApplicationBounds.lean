import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalBranchingLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalTerminalLambdaApplicationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureStaticSupport
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMixedRootBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedPhysicalCellOrigins
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPublicFaultReceivers

/-! A positive retained closure keeps all captured physical slots. Its genuine
terminal or scoped application consumes the shared strict mixed-root induction and retains
the exact caller, Source heap, native store and ordered handle histories. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedPhysicalClosureAssociation (Association)
open SelectedCompilationPhysicalClosureStaticSupport (PacketFor SupportFor)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {native : Value} {bindings : List CallableIndexedParameterCertificates.Binding}
  {parameterCore resultCore : Ty}

local notation "functions" => CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token →
  CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))


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
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world bindings sources values)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedPreparedPhysicalCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (physical : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store)
  (owners : ∀ owner : CallableIndexedOwnedFunctionValues.OwnedKey keys,
    CallableIndexedOwnedNamedPhysicalCaptures.KeyPhysical owner.key headers)
  (stable : StableRows caller)
  {context : SourceSemantics.Context} {callerSource : TypedSource}
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context callerSource)


include physical owners supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- The actual Association and chosen packet retain the original parameter
context. Each body branch constructs its application port from the strict Root IH. -/
theorem application_preserves (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
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
  | legacy legacyAssociation =>
    rcases legacyAssociation with ⟨original, slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : ∀ child, stages.Closure function child →
            CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages child terminal.certificate callFaults budget := by
          intro child selected
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt child selected) owner
            (owners owner) point
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            budget below trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) children trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : ∀ child, stages.Closure function child →
            CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages child terminal.certificate callFaults budget := by
          intro child selected
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt child selected) owner
            (owners owner) point
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            budget below trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨value, finalStore, evaluated, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) children trace within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt child selected) owner
          (owners owner) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt child selected) owner
          (owners owner) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

include physical owners supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- Reflection uses the packet-selected Source scope. The original parameter
installation, independent Source grade and literal returned caller are preserved. -/
theorem application_reflects (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      SelectedCompilationMixedRootBounds.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
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
  | legacy legacyAssociation =>
    rcases legacyAssociation with ⟨original, slots⟩
    cases original with
    | ordinary owner captured code history support origin prefixContext globals referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages terminal.child terminal.certificate callFaults budget := by
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
            (owners owner) point
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            terminal.child terminal.selected valid budget below completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) valid children completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | principal owner captured code history support _origin globals _leading referenceIndex _typed _provenance =>
      rename_i capturedScope capturedActual
      have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
        simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
      obtain ⟨_metadata, carried⟩ := stable owner.position
      have reference : captured.canonical[code.referenceIndex]? =
          some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
        rw [referenceIndex]
        exact globals.reference
      cases packet with
      | terminal terminal =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
            (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
            support.body.toContext.context
            (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
            stages terminal.child terminal.certificate callFaults budget := by
          intro childSize smaller current id lowered point
          rw [supported.point] at point
          exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
            (owners owner) point
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
            captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
            stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
            (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
            terminal.child terminal.selected valid budget below completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

      | branching branch =>
        have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
            code.compilation.administrativePrefix capturedScope captured.canonical := by
          rw [supported.prefix]
          exact slots
        obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
          SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
            (assignmentInterpretation := assignmentInterpretation)
            (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
            (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
            (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
            («functions» := functions) (captured := captured) (code := code) (history := history)
            (inputs := support.body.toContext) (packet := branch) (support := supported)
            (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
            (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
            (argumentsTyped := typed) (represented := represented) (heaps := heaps)
            (locals := raw.captures) (reference := reference) (currentCarried := carried)
            (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
            (callerRuntime := runtime) valid children completed within
        obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
          metadata, returned, related, post⟩ := result
        exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
          finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedOrdinary owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (owners owner) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) valid children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  | preparedBranching owner captured code history support origin prefixContext globals referenceIndex _typed _prepared slots _callerReceipt =>
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | terminal terminal =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedPhysicalCanonicalState.caller (headers := headers) (keys := keys) code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact children childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (owners owner) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed physical
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

    | branching branch =>
      have observed : CallableIndexedOwnedPhysicalGlobals.Slots compiled
          code.compilation.administrativePrefix capturedScope captured.canonical := by
        rw [supported.prefix]
        exact slots
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        SelectedCompilationPhysicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (faithful := CallableIndexedLambdaValues.identity_faithful compiled.indexed)
          (observations := CallableIndexedOwnedPreparedPhysicalCellOrigins.observations profile)
          (functionTypes := CallableIndexedOwnedPreparedPhysicalCellOrigins.runtime_views profile)
          («functions» := functions) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branch) (support := supported)
          (owner := owner) (caller := caller) (capturedSlots := observed) (physical := physical)
          (ownerPhysical := owners owner) (stable := stable) (beforeTyped := raw.heaps)
          (argumentsTyped := typed) (represented := represented) (heaps := heaps)
          (locals := raw.captures) (reference := reference) (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) valid children completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩

end ContextualApplication
end Solcore.SourceSemantics.CoreLowering.SelectedCompilationPhysicalClosureApplicationBounds
