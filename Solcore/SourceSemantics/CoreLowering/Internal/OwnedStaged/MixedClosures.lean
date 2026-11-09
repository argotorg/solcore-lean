import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.PlaceDiagnostics
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MixedBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedPrepared.LambdaPhysical
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalBodies
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.LexicalBodyFaults
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.LambdaBodies
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.MethodBodySupport
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.DiscardSequences
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.TerminalClosures
import Solcore.SourceSemantics.CoreLowering.Internal.Diagnostics.PreparedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedTerminalDispatch
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedGeneralCalls
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedAdmitted.StagedAssignments
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.Builtins
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.ExpressionBounds
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.RecursiveCallerCertificates
import Solcore.SourceSemantics.CoreLowering.Internal.OwnedStaged.SelectedBodyCompiler

/-!
# Staged bounds: mixed closures and calls

Closures of mixed bodies, their application, parent bounds and user dispatch, with mixed indirect calls and recursive callers.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaBodyBounds
/-! The chosen discard packet supplies the existing shape-independent body
ports at the genuine parameter entry. Original parameter admission and native
allocation typing are reused literally. Strong numeric Root induction supplies
the evaluated children; no whole-body meaning is a static packet field. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaBodyBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedAdmittedStagedTerminalStatements (control)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport parameterScope)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Discard code stages)
  (support : DiscardSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped in
/-- Preservation receives the actual Source-selected scope and allocation.
The already constructed parameter admission feeds the strict whole-body port. -/
theorem source_body_at
    (entry : CallableIndexedLambdaEntryPrefix.EntryFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry
      arguments nativeArguments before store owner.key.frameLocation
      (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost)
    (reached : State headers keys
      ⟨parameterScope code, entry.entry.mapping, entry.entry.world, entry.entry.heap,
        entry.entry.store, entry.entry.canonical⟩)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {bodySize : Nat} (within : bodySize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.SourceBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached bodySize := by
  intro child finalContext bodyOutcome outcome after selected valid trace matched
  have admitted := CallableIndexedOwnedPreparedLambdaParameterAdmission.at_parameters
    captured code history inputs functions owner caller entry reached valid beforeTyped argumentsTyped stable
  obtain ⟨_sameContext, produced, sameBody, _derivedResult, value, bodyStore, finalMap, finalWorld,
      evaluated, result, heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds.preserves_body
      (profile := profile) (packet := packet) (support := support) (selected := selected)
      (environments := entry.entry.environments) (heaps := entry.entry.heaps)
      (locals := entry.entry.locals) (agrees := entry.entry.lookups)
      (actualTyped := entry.entry.actualTyped) (initial := reached) (admitted := admitted)
      children within trace
  have sameOutcome : outcome = produced :=
    CallableIndexedOwnedPreparedStagedTerminalSourceBodyInversion.result_of_control (sameBody ▸ matched)
  subst outcome
  exact ⟨value, bodyStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, returned, related, post⟩

include support stable beforeTyped argumentsTyped in
/-- Reflection uses the literal chosen scope and real prefix allocation. It
constructs the original body trace and full post without a new body callback. -/
theorem native_body_at
    (entry : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions completion.result.context.registry arguments before store
      owner.key.frameLocation (caller.rows owner.position).authority.current)
    (reached : State headers keys
      ⟨parameterScope code, entry.mapping, entry.world, entry.heap, entry.store, entry.canonical⟩)
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {nativeSize : Nat} (within : nativeSize ≤ budget) :
    CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.NativeBodyAt
      (stages := stages) (faults := callFaults)
      captured code history inputs functions owner caller entry reached packet.child nativeSize := by
  intro value bodyStore completed
  have rawTypes := Dynamic.MonoBindersExtend.bodyTypes_eq inputs.extended
  have rawArguments : Dynamic.ValuesHaveTypes function.context before arguments
      (function.parameters.map (fun binder => binder.scheme.body)) := by
    simpa only [rawTypes] using argumentsTyped
  have allocated := Dynamic.BindersAllocate.preservesHeapTyping (beforeTyped.copy entry.copy)
    (rawArguments.mono entry.copy.metadata_extends) entry.allocation
  have fields := Dynamic.MonoBindersExtend.runtimeContextFields inputs.extended
  have heapTyped : Dynamic.HeapWellTyped inputs.context entry.heap :=
    allocated.transportClosed fields.signatures valid.code.closed (fields.targetClosed valid.code.closed)
      valid.code.variables_closed (fields.targetResidualVariablesOpen valid.code.residual_variables_open)
  have rows := CallableIndexedOwnedPreparedLambdaParameterAdmission.after_parameters
    caller reached owner.position stable entry.nextHistory entry.frame
  have admitted : CallableIndexedOwnedSourceAdmission.Admission
      (CallableIndexedOwnedBodyRestorationAdmission.bridge (compiled := compiled)
        (program := Program.ofChecked compiled.sourceProgram) (headers := headers) (keys := keys))
      inputs.context reached := ⟨heapTyped, rows⟩
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, matched, meaning,
      heaps, maps, worlds, frame, metadata, returned, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedDiscardBodyBounds.reflects_body
      (profile := profile) (packet := packet) (support := support) (selected := packet.selected)
      (environments := entry.environments) (heaps := entry.heaps)
      (locals := entry.locals) (agrees := entry.lookups) (actualTyped := entry.actualTyped)
      (initial := reached) (admitted := admitted) children within completed
  exact ⟨sourceSize, inputs.context, control outcome, outcome, after, finalMap, finalWorld,
    trace, matched, meaning, heaps, maps, worlds, frame, metadata, returned, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaBodyBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds
/-! A chosen real discard body fills the existing closure application ports.
Parameter installation and the saved caller restoration remain their original
producers. The body ports are manufactured from static support and the strict
Root induction hypothesis, preserving the literal returned pool and post. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open SourceCoreCallableIndexedFrames
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (Discard DiscardSupport)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {stages : Staging.Recursive.Registry}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {mapping : LocationMap} {world : StoreTyping} {capturedActual : Environment}
  (captured : Captures compiled.indexed mapping world scope function.captured capturedActual)
  (code : Code compiled.indexed function scope captured.administrative) (history : History code)
  (inputs : CallableIndexedLambdaEntryPrefix.Context
    (values := .initial compiled.compatible.checked) (prepared := compiled.indexed) code)
  (packet : Discard code stages)
  (support : DiscardSupport code inputs stages packet semanticFaults)
  {arguments : List Dynamic.Value} {nativeArguments : List Value}
  {before : Dynamic.Heap} {store : Store} {callerScope : SourceCoreLocalCell.Scope}
  {callerCanonical : Environment}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  (caller : State headers keys ⟨callerScope, mapping, world, before, store, callerCanonical⟩)
  (stable : StableRows caller)
  (beforeTyped : Dynamic.HeapWellTyped function.context before)
  (argumentsTyped : Dynamic.ValuesHaveTypes function.context before arguments inputs.types)
  (represented : CallableIndexedParameterMeaning.Arguments
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    mapping world code.receipt.loweredParameters arguments nativeArguments)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked
    completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before function.context.locals function.captured)
  (reference : captured.canonical[code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation))
  {currentMetadata : Option MetadataState}
  (currentCarried : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
    (caller.rows owner.position).authority.current (caller.rows owner.position).authority.ghost currentMetadata)
  (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed compiled.indexed.ancestry.graph.inputs
    history.metadata code.descriptor.id = true)
  {callerContext : SourceSemantics.Context} {callerSource : TypedSource}
  (callerRuntime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) callerContext callerSource)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- The genuine Source application chooses its own scope and parameter entry.
The same internally constructed body port returns through the saved caller. -/
theorem application_preserves {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages size
      invocation callContext before (.closure function) arguments outcome after)
    (within : size ≤ budget) :
    ∃ value finalStore,
      Evaluates [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_preserves
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedMixedDiscardLambdaBodyBounds.source_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached children (Nat.le_of_lt strict))
    trace within

include support stable beforeTyped argumentsTyped represented heaps locals reference currentCarried allowed callerRuntime in
/-- Native application selects its real strict body child. The packet's
chosen Source scope supplies that body and the original returned caller post. -/
theorem application_reflects
    (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    {budget : Nat}
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    {invocation : Staging.Recursive.Scope} {callContext : SourceSemantics.Context} {size : Nat}
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size
      [CallableIndexedLambdaValues.value code captured.embedding history.native capturedActual,
        DataPatternValues.packValues nativeArguments] store CallableIndexedLambdaCalls.applyPayload value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after,
      Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation callContext before (.closure function) arguments outcome after ∧
      CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.ResultAt
        (registry := completion.result.context.registry) (faults := callFaults) (callerContext := callerContext)
        captured code functions caller outcome after value finalStore := by
  exact CallableIndexedOwnedPreparedStagedClosureInvocationPostBounds.application_reflects
    captured code history inputs functions represented owner caller heaps locals reference currentCarried
    allowed callerRuntime stable packet.child packet.selected valid budget
    (fun entry reached childSize strict =>
      CallableIndexedOwnedPreparedStagedMixedDiscardLambdaBodyBounds.native_body_at
        (profile := profile) (captured := captured) (code := code) (history := history)
        (inputs := inputs) (packet := packet) (support := support) (owner := owner) (caller := caller)
        (stable := stable) (beforeTyped := beforeTyped) (argumentsTyped := argumentsTyped)
        entry reached valid children (Nat.le_of_lt strict))
    completed within

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedDiscardLambdaApplicationBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds
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
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
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

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- The actual Association and chosen packet retain the original parameter
context. Each body branch constructs its application port from the strict Root IH. -/
theorem application_preserves [FunctionCalls.FaultTokens semanticFaults] (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
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
    | canonicalTerminal terminal =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact canonicalChildren childSize smaller (supported.rootAt child selected) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
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
    | nestedBranching branching =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedNestedBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (ordinary := support) (origin := origin) (prefixContext := prefixContext)
          (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := globals) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) children canonicalChildren trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | canonicalBranching branching =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := observed) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) canonicalChildren trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | branching branching =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
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
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | canonicalTerminal terminal =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      have below : ∀ child, stages.Closure function child →
          CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages child terminal.certificate callFaults budget := by
        intro child selected
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact canonicalChildren childSize smaller (supported.rootAt child selected) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix) point
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds.application_preserves
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          budget below trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
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
    | nestedBranching _ => exact nomatch supported
    | canonicalBranching branching =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := observed) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) canonicalChildren trace within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨value, finalStore, finalMap, finalWorld, evaluated, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | branching branching =>
      obtain ⟨value, finalStore, evaluated, result⟩ :=
        CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds.application_preserves (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
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

include supported raw represented heaps stable runtime semantic assignmentInterpretation in
/-- Reflection uses the packet-selected Source scope. The original parameter
installation, independent Source grade and literal returned caller are preserved. -/
theorem application_reflects [FunctionCalls.FaultTokens semanticFaults] (valid : Dynamic.ClosureFrame (Program.ofChecked compiled.sourceProgram) function)
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
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
  haveI : RecursiveStageMeaning.FaultTokens
      (CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics) :=
    ⟨fun code => semantic _ _ (FunctionCalls.FaultTokens.panic code)⟩
  cases association with
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
    | canonicalTerminal terminal =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact canonicalChildren childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
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
    | nestedBranching branching =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedNestedBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (ordinary := support) (origin := origin) (prefixContext := prefixContext)
          (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := globals) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) children canonicalChildren completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | canonicalBranching branching =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := observed) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) canonicalChildren completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | branching branching =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
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
    rename_i capturedScope capturedActual
    have typed : Dynamic.ValuesHaveTypes function.context before sources support.body.types := by
      simpa only [Dynamic.MonoBindersExtend.bodyTypes_eq support.body.extended] using raw.arguments
    obtain ⟨_metadata, carried⟩ := stable owner.position
    have reference : captured.canonical[code.referenceIndex]? =
        some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) := by
      rw [referenceIndex]
      exact globals.reference
    cases packet with
    | canonicalTerminal terminal =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      have below : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix).forgetSlots
          support.body.toContext.context
          (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
          stages terminal.child terminal.certificate callFaults budget := by
        intro childSize smaller current id lowered point
        rw [supported.point] at point
        exact canonicalChildren childSize smaller (supported.rootAt terminal.child terminal.selected) owner
          (CallableIndexedOwnedExpressionHeads.canonicalCaller (headers := headers) owner code.compilation.administrativePrefix) point
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalTerminalLambdaApplicationBounds.application_reflects
          captured code history support.body.toContext functions owner caller code.compilation.administrativePrefix observed
          stable raw.heaps typed terminal.receipt terminal.certifies represented heaps raw.captures reference carried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed code history) runtime
          terminal.child terminal.selected valid budget below completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
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
    | nestedBranching _ => exact nomatch supported
    | canonicalBranching branching =>
      have observed : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
          (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
          headers owner.key.locations code.compilation.administrativePrefix capturedScope captured.canonical owner.key.frameLocation := by
        rw [supported.prefix]
        exact globals
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedCanonicalBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
          (owner := owner) (caller := caller) (observed := observed) (stable := stable)
          (beforeTyped := raw.heaps) (argumentsTyped := typed) (represented := represented)
          (heaps := heaps) (locals := raw.captures) (reference := reference)
          (currentCarried := carried)
          (allowed := CallableIndexedLambdaTemplatePermission.lambda_allowed code history)
          (callerRuntime := runtime) (valid := valid) canonicalChildren completed within
      obtain ⟨finalMap, finalWorld, representedResult, finalHeaps, maps, worlds, frame,
        metadata, returned, related, post⟩ := result
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, representedResult,
        finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
    | branching branching =>
      obtain ⟨sourceSize, outcome, after, trace, result⟩ :=
        CallableIndexedOwnedPreparedStagedBranchingLambdaApplicationBounds.application_reflects (semantic := semantic)
          (assignmentInterpretation := assignmentInterpretation)
          (profile := profile) (captured := captured) (code := code) (history := history)
          (inputs := support.body.toContext) (packet := branching) (support := supported)
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureParentBounds
/-! The real indirect closure parent uses the same selected Association and
chosen terminal or discard packet at its application boundary. Both numeric
grades, physical gates, original three binds and returned caller restoration
are the existing proofs. The strict Root IH supplies the called body internally. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureParentBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory CallableIndexedLambdaValues CallableIndexedOwnedFunctionState
open CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {stages : Staging.Recursive.Registry}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}

section Parent
variable {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {before calleeHeap argumentsHeap : Dynamic.Heap} {store argumentsStore : Store}
  {argumentMap : LocationMap} {argumentWorld : StoreTyping}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (reached : callerProtocol.State ⟨scope, argumentMap, argumentWorld, argumentsHeap, argumentsStore, canonical⟩)
  (related : callerProtocol.Relates initial reached)
  (admitted : Admission bridge context reached)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    argumentMap argumentWorld argumentsHeap argumentsStore)
  (maps : LocationMap.Extends mapping argumentMap) (worlds : WorldExtends world argumentWorld)
  (frame : AdministrativePreserved mapping store argumentMap argumentsStore)
  (heapMetadata : Dynamic.HeapMetadataExtend before argumentsHeap)
  {carrier : Value} {sources : List Dynamic.Value} {values : List Value}
  {sourceTypes : List TypeSystem.Ty} {parameter result : TypeSystem.Ty}
  {sidecar : SourceCoreStageContracts.Sidecar} {originalNode : ExpressionNode}
  {originalMetadata : IndirectCallResolution}
  (dispatch : CallStageBoundary.Dispatch (CallableLedger.frame sidecar) prepared.site prepared.site.call ids
    (.closure function) carrier)
  (selected : CallableIndexedOwnedSelectedCallCodebookReceipts.Selected
    sidecar prepared.site callee ids originalMetadata originalNode dispatch.row)
  (count : dispatch.row.entry.parameterCount = ids.length)
  (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids (.closure function))
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (calleeHeapTyped : Dynamic.HeapWellTyped context calleeHeap)
  (typing : ExpressionsHaveTypes invocation.source context ids sourceTypes)
  (calleeTyped : Dynamic.ValueHasType context calleeHeap (.closure function) (.function parameter result))
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  (calleeRelated : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
    headers keys bodyRegistry completion.result.context.registry semanticFaults profile argumentMap argumentWorld
    (.function parameter result) (.closure function) carrier compiler.calleeCode.type)
  (represented : DataExpressionSequence.Values
    (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry
      (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile))
    argumentMap argumentWorld sourceTypes (compiler.codes.map (·.type)) sources values)
  (bundle : TypeSystem.Ty.productMany sourceTypes = parameter)
  (originalResult : compiler.original.type = result)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions

local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

  (assignmentInterpretation : PreparedAssignmentDiagnosticAuthority.Interprets compiled
    completion.result.context.registry (fun reason token =>
      CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token))

include bridge profile compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  dispatch selected count accepted wellFormed runtime covers locals calleeHeapTyped typing calleeTyped
  actualFunctionType calleeRelated represented bundle originalResult semantic assignmentInterpretation in
/-- The genuine argument endpoint feeds the actual closure application once.
Its native suffix and original three binds complete the whole parent. -/
theorem preserves_parent [FunctionCalls.FaultTokens semanticFaults]
    (packets : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize applicationSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap (.closure function) sources outcome after)
    (within : applicationSize ≤ budget)
    {calleeStore : Store}
    (calleeNative : Evaluates actual store (compiler.calleeCode.expression.rename ξ)
      (.inRight .word carrier) calleeStore)
    (firstGate : Evaluates (carrier :: actual) calleeStore
      (CallableContract.dispatch prepared.site.gates .beforeArguments
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 0)))
      (.inRight .word .unit) calleeStore)
    (argumentsNative : Evaluates (.unit :: carrier :: actual) calleeStore
      ((SourceCoreCalls.packArguments compiler.codes).expression.rename
        (Renaming.comp (Renaming.insertion 0) (Renaming.comp (Renaming.insertion 0) ξ)))
      (.inRight .word (DataPatternValues.packValues values)) argumentsStore) :
    Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize])
      invocation context environment before id outcome after ∧
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, _valid, bindings, parameterCore, resultCore, member, _parameterEq, resultEq, parameters⟩ :=
    CallableIndexedOwnedPreparedStagedClosureArgumentRows.at_arguments bridge profile compiler reached dispatch
      selected count wellFormed runtime covers locals calleeHeapTyped typing calleeTyped bundle admitted
      actualFunctionType calleeRelated represented argumentsTrace
  obtain ⟨association⟩ := member
  obtain ⟨value, finalStore, finalMap, finalWorld, application, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ :=
    CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds.application_preserves (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      profile association (packets association) (supported association) (bridge.pool reached)
      raw parameters heaps admitted.rows runtime budget children canonicalChildren called within
  have suffix := CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.preserves_suffix
    (actual := actual) (result := compiler.resultType)
    (unknown := compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown)
    dispatch.shape selected dispatch.found count application
  have whole : Evaluates actual store
      (CallableContract.call prepared.site.gates
        compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
        (compiler.calleeCode.expression.rename ξ)
        ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) value finalStore := by
    apply LanguageResult.bind_success compiler.resultType calleeNative
    apply LanguageResult.bind_success compiler.resultType firstGate
    apply LanguageResult.bind_success compiler.resultType
    · simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] using argumentsNative
    · exact suffix
  rw [← prepared.lowered_rename compiler ξ] at whole
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity called,
    value, finalStore, finalMap, finalWorld, whole, parentRep, finalHeaps,
    maps.trans applicationMaps, worlds.trans applicationWorlds, frame.trans applicationFrame,
    heapMetadata.trans applicationMetadata, returned, callerProtocol.trans related callerRelated, parentPost⟩

include bridge profile compiler prepared sourceParent occurrence related admitted heaps maps worlds frame heapMetadata
  dispatch selected count accepted wellFormed runtime covers locals calleeHeapTyped typing calleeTyped
  actualFunctionType calleeRelated represented bundle originalResult semantic assignmentInterpretation in
/-- The concrete selected closure suffix constructs the original applied
parent. Both numeric grades and every transient reached effect are retained. -/
theorem reflects_suffix [FunctionCalls.FaultTokens semanticFaults]
    (packets : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults argumentMap argumentWorld function carrier
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (children : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize : Nat}
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value (.closure function)) calleeHeap)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    {suffixSize : Nat} {value : Value} {finalStore : Store}
    (suffix : EvaluationSize suffixSize (DataPatternValues.packValues values :: .unit :: carrier :: actual)
      argumentsStore
      (LanguageResult.bind compiler.resultType
        (CallableContract.dispatch prepared.site.gates .beforeApplication
          compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown (.second (.var 2)))
        (.apply (.second (.first (.var 3))) (.var 1))) value finalStore)
    (within : suffixSize ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages sourceSize
        invocation context environment before id outcome after ∧
      RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
        compiler.original.type lowered.type callFaults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry functions
        finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ returned : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial returned ∧
        CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
          compiler.original.type outcome returned := by
  obtain ⟨raw, valid, bindings, parameterCore, resultCore, member, parameterEq, resultEq, parameters⟩ :=
    CallableIndexedOwnedPreparedStagedClosureArgumentRows.at_arguments bridge profile compiler reached dispatch
      selected count wellFormed runtime covers locals calleeHeapTyped typing calleeTyped bundle admitted
      actualFunctionType calleeRelated represented argumentsTrace
  obtain ⟨association⟩ := member
  obtain ⟨applicationSize, strict, application⟩ :=
    CallableIndexedOwnedPreparedStagedIndirectApplicationSuffix.reflects_suffix dispatch.shape
      selected dispatch.found count suffix within
  obtain ⟨applicationSourceSize, outcome, after, finalMap, finalWorld, applied, resultRep, finalHeaps,
    applicationMaps, applicationWorlds, applicationFrame, applicationMetadata, ownedReturned, ownedRelated, ownedPost⟩ :=
    CallableIndexedOwnedPreparedStagedMixedClosureApplicationBounds.application_reflects (semantic := semantic)
      (assignmentInterpretation := assignmentInterpretation)
      profile association (packets association) (supported association) (bridge.pool reached)
      raw parameters heaps admitted.rows runtime valid budget children canonicalChildren application (Nat.le_of_lt strict)
  obtain ⟨returned, samePool, callerRelated⟩ := bridge.restore reached ownedReturned
    applicationMaps applicationWorlds applicationFrame applicationMetadata ownedRelated
  have sameSource : compiler.original.type = function.resultType := by
    obtain ⟨_parameters, sourceResult, _signatures, _code, _covers, _captures⟩ := calleeTyped.closure_function_inv
    exact originalResult.trans sourceResult
  have sameCore : lowered.type = resultCore :=
    (congrArg (fun output => output.type) compiler.output).trans (compiler.resultTypeEq.symm.trans resultEq)
  have parentRep : RecursiveStageMeaning.ResultRepresentsFor model finalMap finalWorld
      compiler.original.type lowered.type callFaults outcome value := by
    rw [sameSource, sameCore]
    exact resultRep
  have parentPost : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
      compiler.original.type outcome returned := by
    rw [sameSource]
    cases outcome with
    | value sourceValue =>
      change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
      exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
    | fault failure =>
      cases failure with
      | semantic reason =>
        change CallableIndexedOwnedSourceAdmission.PostAdmission _ _ _ _ _ at ownedPost ⊢
        exact ⟨by rw [samePool]; exact ownedPost.rows, ownedPost.successful⟩
      | stage failedScope failedCall reason =>
        change StableRows (bridge.pool returned)
        rw [samePool]
        exact ownedPost
  exact ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSourceSize],
    outcome, after, finalMap, finalWorld,
    .applied occurrence compiler.argumentCoercions calleeTrace accepted argumentsTrace sourceParent.arity applied,
    parentRep, finalHeaps, maps.trans applicationMaps, worlds.trans applicationWorlds,
    frame.trans applicationFrame, heapMetadata.trans applicationMetadata,
    returned, callerProtocol.trans related callerRelated, parentPost⟩

end Parent

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureParentBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch
/-! The authentic user prefix dispatches a closure through its exact chosen
terminal or discard packet and static support. A strict Root family at the same
point budget constructs the called body. Physical arity rejection, original
argument rows, independent numeric grades and the returned caller PostAdmission
retain their existing proofs. The global prefix remains the original named
branch. This internal interface supplies the future mutual body induction. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedIndirectNativePrefix (CalleePost)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (UserApplicationPrefix ParentResult)
open CallableIndexedOwnedPreparedScopedCallBoundaryReceipts (CallView)
open CallableIndexedOwnedContextualCalleeStageReceipts (BoundaryAt)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {context : SourceSemantics.Context} {stages : Staging.Recursive.Registry}
  {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : CallableIndexedOwnedIndirectSourceAdapters.Prepared compiler
    compiled.indexed.ancestry.graph.inputs.callable)
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sourceTypes : List TypeSystem.Ty} {calleeNode : ExpressionNode}
  {sidecar : SourceCoreStageContracts.Sidecar}

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  (preparedStages : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (receiver : CallableIndexedOwnedPublicFaultReceiverTables.IssuedAt compiled.indexed completion.entry
    completion.result.context.registry completion.result.extension completion.result.diagnostics)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  {certificate : GenericExpressionMeaning.Certificate}
  (sourceEq : invocation.source = source)
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)
  (calleeFound : source.lookupExpression? callee = some calleeNode)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include sourceParent occurrence preparedStages receiver wellFormed runtime covers locals sourceEq tree unique
  parentTyped calleeFound guardFrame actualFunctionType semantic in
/-- Authentic Source application and prefix witnesses construct the original
closure parent. Physical count rejection keeps the reached argument heap and
literal receiving arity word; success preserves the actual selected body once. -/
theorem preserves_closure_or_global [FunctionCalls.FaultTokens semanticFaults]
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {calleeSize argumentsSize applicationSize : Nat}
    {sourceValue : Dynamic.Value} {calleeHeap argumentsHeap after : Dynamic.Heap}
    {sources : List Dynamic.Value} {outcome : Staging.Recursive.Outcome}
    (user : Staging.CallBoundary.UserCallable sourceValue)
    (calleeTrace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages calleeSize
      invocation context environment before callee (.value sourceValue) calleeHeap)
    (accepted : Staging.CallBoundary.GuardAccepts invocation.guards id ids sourceValue)
    (argumentsTrace : Staging.Recursive.Size.Expressions (Program.ofChecked compiled.sourceProgram) stages argumentsSize
      invocation context environment calleeHeap ids (.values sources) argumentsHeap)
    (called : Staging.Recursive.Size.Applies (Program.ofChecked compiled.sourceProgram) stages applicationSize
      invocation context argumentsHeap sourceValue sources outcome after)
    (within : applicationSize ≤ budget)
    (prefixResult : CallableIndexedOwnedPreparedStagedIndirectValuesPrefix.ValuesPrefix (functionModel := functions)
      (registry := completion.result.context.registry) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial sourceValue calleeHeap argumentsHeap sources) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial
      (Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, applicationSize]) outcome after ∨
    GlobalAppliedPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial calleeSize argumentsSize applicationSize sourceValue
      calleeHeap argumentsHeap sources outcome after := by
  cases user with
  | global function =>
    exact .inr ⟨function, rfl, calleeTrace, accepted, argumentsTrace, called, prefixResult⟩
  | closure function =>
    have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
      simpa only [sourceEq] using tree
    have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
    have originalTyping : ExpressionHasType source context id compiler.original.type := by
      simpa only [sourceEq] using parentTyped
    obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
      CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
        originalTree originalUnique originalTyping calleeFound
    have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
      simpa only [sourceEq] using argumentsTyped
    obtain ⟨rawParameter, rawResult, functionType, bundle, originalResult,
      calleeStore, calleeMap, calleeWorld, carrier, values, argumentsStore, finalMap, finalWorld,
      originalNode, originalMetadata, calleePost, calleeTyped, firstGate, argumentsNative,
      represented, calleeRelated, _callView, boundary, heaps, maps, worlds,
      frame, heapMetadata, reached, related, admitted⟩ := prefixResult
    cases boundary with
    | user dispatch selected =>
      by_cases count : dispatch.row.entry.parameterCount = ids.length
      · have calleeNative := calleePost.1
        obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
        have calleeHeapTyped := calleeAdmission.at_value.2.heap
        have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        have relatedCallee : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
            headers keys bodyRegistry completion.result.context.registry semanticFaults profile finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
          change GenericHeap.PayloadModel.Represents model finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type
          simpa only [functionType] using calleeRelated
        exact .inl (CallableIndexedOwnedPreparedStagedMixedClosureParentBounds.preserves_parent (semantic := semantic)
          (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
          bridge profile compiler prepared sourceParent occurrence initial reached related admitted
          heaps maps worlds frame heapMetadata dispatch selected count accepted wellFormed runtime covers
          (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType relatedCallee
          represented bundle originalResult packets supported budget bodyChildren canonicalChildren calleeTrace argumentsTrace called within
          calleeNative firstGate argumentsNative)
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have valuesCount := CallableIndexedOwnedPreparedSecondCallGateRejection.values_count argumentsTrace
        have different : function.parameters.length ≠ ids.length := by
          simpa only [physical] using count
        cases called with
        | closure selectedChild valid parameters _copy allocate bodyTrace bodyResult =>
          exact False.elim (different (allocate.length_eq.trans valuesCount))
        | closureArity mismatch =>
          have actualAccepted : Staging.CallBoundary.GuardAccepts (CallableLedger.frame sidecar)
              prepared.site.call ids (.closure function) := by
            simpa only [guardFrame, prepared.call] using accepted
          have argumentsWeaken : Evaluates (.unit :: carrier :: actual) calleeStore
              (((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
              (.inRight .word (DataPatternValues.packValues values)) argumentsStore := by
            simpa only [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix]
              using argumentsNative
          have native := CallableIndexedOwnedPreparedSecondCallGateRejection.user_native_preserves
            (result := compiler.resultType) dispatch selected actualAccepted count
            compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown calleePost.1 argumentsWeaken
          change Evaluates actual store
            (CallableContract.call prepared.site.gates
              compiled.indexed.ancestry.graph.inputs.callable.diagnostics.unknown compiler.resultType
              (compiler.calleeCode.expression.rename ξ)
              ((SourceCoreCalls.packArguments compiler.codes).expression.rename ξ)) _ argumentsStore at native
          rw [← prepared.lowered_rename compiler ξ] at native
          obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
            CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
              compiler prepared preparedStages selected receiver initial functions reached related heaps
              (sourceResult := compiler.original.type) (resultCore := lowered.type) count
          cases sameState
          have loweredType : lowered.type = compiler.resultType :=
            (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
          have faultRep := CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
          have post : CallableIndexedOwnedAdmittedStagedExpressionBounds.PostAdmission bridge context
              compiler.original.type
              (.fault (.semantic (.argumentArityMismatch function.parameters.length sources.length))) reached :=
            ⟨admitted.rows, by intro value impossible; cases impossible⟩
          refine .inl ⟨.applied occurrence compiler.argumentCoercions calleeTrace accepted
            argumentsTrace sourceParent.arity (.closureArity mismatch),
            .inLeft lowered.type (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
              .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))),
            argumentsStore, finalMap, finalWorld, ?_, ?_, keptHeaps, maps, worlds, frame,
            heapMetadata, reached, keptRelated, post⟩
          · simpa only [loweredType] using native
          · simpa only [physical, valuesCount] using faultRep


include sourceParent occurrence preparedStages receiver wellFormed runtime covers locals sourceEq tree unique parentTyped calleeFound actualFunctionType semantic in
/-- User classification and physical arity happen inside the actual retained
prefix. The closure branch constructs full parent meaning; only the literal
global application remains for the separate named producer. -/
theorem reflects_closure_or_global [FunctionCalls.FaultTokens semanticFaults]
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    {budget size : Nat} {value : Value} {finalStore : Store}
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (user : UserApplicationPrefix (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry)
      (semanticFaults := semanticFaults) (context := context) (stages := stages) (invocation := invocation)
      (environment := environment) (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes)
      (calleeNode := calleeNode) (sidecar := sidecar) bridge profile compiler prepared initial budget value finalStore) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  have originalTree : DataExpressionSequence.Tree source certificate scope ids sourceTypes compiler.codes := by
    simpa only [sourceEq] using tree
  have originalUnique : NodeOccurrencesUnique source := by simpa only [sourceEq] using unique
  have originalTyping : ExpressionHasType source context id compiler.original.type := by
    simpa only [sourceEq] using parentTyped
  obtain ⟨_parameter, _result, _calleeType, argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedIndirectSourceTypeRows.original_rows compiler sourceParent
      originalTree originalUnique originalTyping calleeFound
  have typing : ExpressionsHaveTypes invocation.source context ids sourceTypes := by
    simpa only [sourceEq] using argumentsTyped
  obtain ⟨sourceValue, userKind, rawParameter, rawResult, functionType, bundle, originalResult,
    calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
    argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩ := user
  cases userKind with
  | global function =>
    exact .inr ⟨function, rawParameter, rawResult, functionType, bundle, originalResult,
      calleeSize, argumentsSize, calleeHeap, calleeStore, calleeMap, calleeWorld, sources, values, carrier,
      argumentsHeap, argumentsStore, finalMap, finalWorld, originalNode, originalMetadata, tail⟩
  | closure function =>
    obtain ⟨calleePost, calleeTyped, calleeTrace, accepted, argumentsTrace, represented, calleeRelated,
      _callView, boundary, heaps, maps, worlds, frame, heapMetadata, ⟨reached, related, admitted⟩,
      suffixSize, suffix, strict⟩ := tail
    cases boundary with
    | user dispatch selected =>
      by_cases same : dispatch.row.entry.parameterCount = ids.length
      · obtain ⟨_nativeCallee, _representedCallee, _calleeHeaps, _calleeMaps, _calleeWorlds,
          _calleeFrame, calleeMetadata, calleeReached, _calleeRelated, calleeAdmission⟩ := calleePost
        have calleeHeapTyped := calleeAdmission.at_value.2.heap
        have rawCallee : Dynamic.ValueHasType context calleeHeap (.closure function)
            (.function rawParameter rawResult) := by
          simpa only [functionType] using calleeTyped
        have relatedCallee : CallableIndexedOwnedContextualCellOrigins.PayloadOrigins
            headers keys bodyRegistry completion.result.context.registry semanticFaults profile finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type := by
          change GenericHeap.PayloadModel.Represents model finalMap finalWorld
            (.function rawParameter rawResult) (.closure function) carrier compiler.calleeCode.type
          simpa only [functionType] using calleeRelated
        obtain ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, resultRep, returnedHeaps,
          returnedMaps, returnedWorlds, returnedFrame, returnedMetadata, returned, returnedRelated, returnedPost⟩ :=
          CallableIndexedOwnedPreparedStagedMixedClosureParentBounds.reflects_suffix (semantic := semantic)
            (assignmentInterpretation := PreparedAssignmentDiagnosticAuthority.interprets receiver)
            bridge profile compiler prepared sourceParent occurrence initial reached related admitted
            heaps maps worlds frame heapMetadata dispatch selected same accepted wellFormed runtime covers
            (locals.mono calleeMetadata) calleeHeapTyped typing rawCallee actualFunctionType relatedCallee
            represented bundle originalResult packets supported budget bodyChildren canonicalChildren calleeTrace argumentsTrace suffix
            (Nat.le_of_lt strict)
        exact .inl ⟨sourceSize, outcome, after, returnedMap, returnedWorld, trace, completed.sound,
          resultRep, returnedHeaps, returnedMaps, returnedWorlds, returnedFrame, returnedMetadata,
          returned, returnedRelated, returnedPost⟩
      · have physical := CallableIndexedOwnedStoredClosureArityBoundary.parameter_count dispatch selected
        have failedSource := CallableIndexedOwnedPreparedSecondCallGateRejection.closure_source
          occurrence compiler.argumentCoercions sourceParent.arity argumentsTrace calleeTrace accepted
          (by simpa only [physical] using same)
        have lowerType : lowered.type = compiler.resultType :=
          (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
        obtain ⟨sameValue, sameStore⟩ :=
          CallableIndexedOwnedPreparedStagedIndirectSecondGateBounds.rejected_suffix
            dispatch.shape selected dispatch.found same suffix
        cases sameStore
        obtain ⟨representedFault, keptHeaps, keptState, sameState, keptRelated⟩ :=
          CallableIndexedOwnedPreparedReceivingCallRejectionPosts.receiving_staged_argument_post
            compiler prepared preparedStages selected receiver initial functions reached related heaps
            (sourceResult := compiler.original.type) (resultCore := lowered.type) same
        cases sameState
        refine .inl ⟨Staging.Recursive.Size.stepSize [calleeSize, argumentsSize, Staging.Recursive.Size.stepSize []],
          .fault (.semantic (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length)),
          argumentsHeap, finalMap, finalWorld, ?_, completed.sound, ?_, keptHeaps, maps, worlds, frame,
          heapMetadata, reached, keptRelated, ?_⟩
        · simpa only [physical] using failedSource
        · have exactValue : value = .inLeft lowered.type
              (.word (prepared.site.reasonAt dispatch.row.caller dispatch.row.call dispatch.row.entry.id
                .beforeApplication (.argumentArityMismatch dispatch.row.entry.parameterCount ids.length))) := by
            simpa only [lowerType] using sameValue
          rw [exactValue]
          exact CallableIndexedOwnedPublicDecodedStagedCallFaults.arity_result model representedFault
        · change CallableIndexedOwnedSourceAdmission.PostAdmission bridge context compiler.original.type (.fault _) reached
          exact ⟨admitted.rows, by intro sourceValue impossible; cases impossible⟩


end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectDispatch
/-! The original caller prefix classifies fault, builtin, closure and global
branches once. Mixed closure packets retain their exact Association and static
support; strict Root children use the same parent budget. Authentic named
global prefixes and every reached state remain the existing contracts. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectDispatch
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserDispatch (GlobalApplicationPrefix)
open CallableIndexedOwnedPreparedStagedTerminalClosureUserPreservationDispatch (GlobalAppliedPrefix)
open CallableIndexedOwnedPreparedStagedIndirectTerminalPreservationDispatch (GlobalAt)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations semantic in
/-- One original Source parent constructs its complete native result or
retains the authentic named suffix. The concrete call producers reuse the
literal callee and argument evaluations and their reached pool. -/
theorem preserves_parent_or_global [FunctionCalls.FaultTokens semanticFaults] (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after ∨
    GlobalAt (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge (profile := profile) compiler prepared initial budget size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedIndirectSourcePrefixDispatch.preserves_fault_or_application
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      bridge profile compiler prepared sourceEq occurrence certified found sourceTyped
      environments heaps locals agrees typed initial admitted caller view originalUnique guardFrame
      sourceParent tree unique parentTyped stagePrepared receiver budget children trace within with fault | application
  · exact .inl ⟨trace, fault⟩
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, calleeTrace, accepted, argumentsTrace, called, constructedPrefix⟩ := application
    cases sizeEq
    rcases CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch.preserves_builtin_or_user
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations calleeTrace accepted argumentsTrace called constructedPrefix with user | parent
    · rcases CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch.preserves_closure_or_global (semantic := semantic)
          bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
          wellFormed runtime covers locals sourceEq tree unique parentTyped found guardFrame actualFunctionType
          packets supported budget bodyChildren canonicalChildren user.1 calleeTrace accepted argumentsTrace called (Nat.le_of_lt strict)
          user.2 with closureParent | global
      · exact .inl closureParent
      · exact .inr ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap,
          argumentsHeap, sources, rfl, strict, global⟩
    · exact .inl parent

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations semantic in
/-- One original native parent completion either gives full Source parent
meaning or retains its actual named application prefix. Concrete call branches
share the same reached state; no caller or argument trace is replayed. -/
theorem reflects_parent_or_global [FunctionCalls.FaultTokens semanticFaults] (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (packets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (supported : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (packets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore ∨
    GlobalApplicationPrefix (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) (sourceTypes := sourceTypes) (calleeNode := calleeNode) (sidecar := sidecar)
      bridge profile compiler prepared initial budget value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedIndirectRetainedCalleeFaultDispatch.reflects_fault_or_application
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped budget children completed within with fault | application
  · obtain ⟨sourceSize, failure, after, token, finalMap, finalWorld, trace, valueEq,
      native, represented, finalHeaps, maps, worlds, frame, metadata,
      returned, related, post⟩ := fault
    cases valueEq
    exact .inl ⟨sourceSize, .fault failure, after, finalMap, finalWorld, trace, native,
      represented, finalHeaps, maps, worlds, frame, metadata, returned, related, post⟩
  · rcases CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch.reflects_builtin_or_user
      (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        actualFunctionType observations completed application with user | parent
    · exact CallableIndexedOwnedPreparedStagedMixedClosureUserDispatch.reflects_closure_or_global (semantic := semantic)
        bridge profile compiler prepared initial sourceParent occurrence stagePrepared receiver
        wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
        packets supported bodyChildren canonicalChildren completed user
    · exact .inl parent

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectDispatch
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectCallBounds
/-! Original whole indirect calls consume the mixed closure dispatch and the
unchanged selected named global producer. Caller callee/argument children and
strict called Root children are distinct and share the literal point budget.
The original ParentAt/ParentResult includes the full restored caller post. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectCallBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinApplicationDispatch (ParentResult)
open CallableIndexedOwnedPreparedStagedIndirectBuiltinPreservationDispatch (ParentAt)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {context : SourceSemantics.Context}
  {stages : Staging.Recursive.Registry} {invocation : Staging.Recursive.Scope}

section Calls
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered)
  (prepared : Prepared compiler compiled.indexed.ancestry.graph.inputs.callable)
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  (occurrence : Staging.Recursive.Occurrence invocation id (.call callee ids (.indirect metadata)))
  {calleeNode : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {before : Dynamic.Heap} {store : Store}
  {environment : Dynamic.Environment} {canonical actual : Environment} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  {sidecar : SourceCoreStageContracts.Sidecar}
  (view : SourceView sidecar.source source)
  (guardFrame : invocation.guards = CallableLedger.frame sidecar)

section PositiveModel
variable {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {certificate : GenericExpressionMeaning.Certificate}
  (certified : certificate scope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
  (sourceTyped : ExpressionHasType source context callee calleeNode.type)
  {administrative actualContext : Core.Context}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative scope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked completion.result.context.registry
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile)
    mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (admitted : Admission bridge context initial)
  (caller : SourceCoreStageContracts.prepareSidecar compiled.indexed.base.plan prepared.site.caller = .ok sidecar)
  (originalUnique : NodeOccurrencesUnique sidecar.source)
  (sourceParent : CallableIndexedOwnedIndirectSourceAdapters.SourceParent compiler)
  {sourceTypes : List TypeSystem.Ty}
  (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
  (unique : NodeOccurrencesUnique invocation.source)
  (parentTyped : ExpressionHasType invocation.source context id compiler.original.type)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics


variable (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations semantic in
/-- One original native completion gives full staged Source parent meaning,
including the actual named global branch and restored caller post. -/
theorem reflects_parent [FunctionCalls.FaultTokens semanticFaults]
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.ReflectsBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedTerminals : ∀ header, header ∈ headers → Body header)
    (namedChildren : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model (RecursiveNamedPreparedStageScopes.registry stagePrepared)
          child callFaults budget)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ParentResult (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial value finalStore := by
  rcases CallableIndexedOwnedPreparedStagedMixedIndirectDispatch.reflects_parent_or_global (semantic := semantic)
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closurePackets closureSupport bodyChildren canonicalChildren completed within with parent | global
  · exact parent
  · exact CallableIndexedOwnedPreparedStagedSelectedNamedGlobalDispatch.reflects_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared stageEq caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals namedChildren completed global

include receiver prepared stagePrepared sourceEq occurrence certified found sourceTyped
  environments heaps locals agrees typed admitted caller view originalUnique guardFrame
  sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations semantic in
/-- One original staged Source parent constructs its native completion and
full caller post. The authentic named branch uses its actual strict application
child; Source and native grades remain independent. -/
theorem preserves_parent [FunctionCalls.FaultTokens semanticFaults] (budget : Nat)
    (children : CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesBelow
      bridge context model stages invocation certificate callFaults budget)
    (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), PacketFor association stages)
    (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
      (association : Association headers keys bodyRegistry semanticFaults mapping world function native
        bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedTerminals : ∀ header, header ∈ headers → Body header)
    (namedChildren : ∀ header, ∀ _member : header ∈ headers,
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child callFaults budget)
    {size : Nat} {outcome : Staging.Recursive.Outcome} {after : Dynamic.Heap}
    (trace : Staging.Recursive.Size.Expression (Program.ofChecked compiled.sourceProgram) stages size
      invocation context environment before id outcome after)
    (within : size ≤ budget) :
    ParentAt (functionModel := functions) (completion := completion) (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults)
      (context := context) (stages := stages) (invocation := invocation) (environment := environment)
      (actual := actual) (ξ := ξ) bridge profile compiler initial size outcome after := by
  rcases CallableIndexedOwnedPreparedStagedMixedIndirectDispatch.preserves_parent_or_global (semantic := semantic)
      bridge receiver compiler prepared stagePrepared sourceEq occurrence initial view guardFrame profile
      certified found sourceTyped environments heaps locals agrees typed admitted caller originalUnique
      sourceParent tree unique parentTyped wellFormed runtime covers actualFunctionType observations
      budget children closurePackets closureSupport bodyChildren canonicalChildren trace within with parent | global
  · exact parent
  · obtain ⟨calleeSize, argumentsSize, applicationSize, sourceValue, calleeHeap, argumentsHeap,
      sources, sizeEq, strict, globalPrefix⟩ := global
    cases sizeEq
    exact CallableIndexedOwnedPreparedStagedSelectedNamedGlobalDispatch.preserves_global
      bridge profile compiler prepared initial sourceParent occurrence stagePrepared caller receiver
      wellFormed runtime covers locals sourceEq tree unique parentTyped found actualFunctionType
      namedTerminals guardFrame budget namedChildren globalPrefix (Nat.le_of_lt strict)

end PositiveModel
end Calls
end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedIndirectCallBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds
/-! Call-head assembly for the original static Port and Point. The structural
caller supplies strict callee/argument children. The numeric family supplies
Root children below its outer budget, restricted here to the current call size.
Actual selected mixed closure bodies and terminal named bodies then construct
the original whole-call result and restored caller state. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectSourceAdapters (Prepared SourceParent)
open CallableIndexedOwnedContextualDiagnosticSources (SourceView)
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedSelectedGeneralCallHeadBounds (Point Port)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  (sourceEq : invocation.source = source)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

variable (semantic : ∀ reason token, semanticFaults reason token → CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations closurePackets closureSupport namedTerminals semantic in
/-- Reuse the original whole-call producer at the supplied genuine Source
grade. The returned caller state and post are retained literally. -/
theorem preserves [FunctionCalls.FaultTokens semanticFaults]
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : PreservesBelow bridge context model stages invocation certificate callFaults size)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    (within : size ≤ budget) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  exact (CallableIndexedOwnedPreparedStagedMixedIndirectCallBounds.preserves_parent (semantic := semantic)
    bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
    profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
    admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
    wellFormed runtime covers actualFunctionType observations
    size children closurePackets closureSupport
    (fun childSize smaller => bodyChildren childSize (Nat.lt_of_lt_of_le smaller within))
    (fun childSize smaller => canonicalChildren childSize (Nat.lt_of_lt_of_le smaller within))
    namedTerminals namedChildren trace (Nat.le_refl _)).2

include bridge receiver stagePrepared sourceEq profile wellFormed runtime covers unique
  actualFunctionType observations closurePackets closureSupport namedTerminals semantic in
/-- The native completion keeps its independent Source grade and exact
staged fault scope. Only the duplicate native evaluation witness is omitted. -/
theorem reflects [FunctionCalls.FaultTokens semanticFaults]
    (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (port : Port (compiled := compiled) (invocation := invocation) compiler)
    {certificate : GenericExpressionMeaning.Certificate}
    (calleeCertified : certificate scope callee compiler.calleeCode)
    {sourceTypes : List TypeSystem.Ty}
    (tree : DataExpressionSequence.Tree invocation.source certificate scope ids sourceTypes compiler.codes)
    (size : Nat)
    (children : ReflectsBelow bridge context model stages invocation certificate callFaults size)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    (within : size ≤ budget) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) callFaults size := by
  intro current child code point node found parentTyped
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases sourceEq
  cases Option.some.inj (found.symm.trans compiler.found)
  obtain ⟨parameter, result, rawTypes, calleeTyped, _argumentsTyped, _bundle, _resultType⟩ :=
    CallableIndexedOwnedPreparedStagedRecursiveCallerSourceReceipts.original_child_types
      compiler port.sourceParent unique parentTyped
  have reported := CallableIndexedOwnedContextualInitializedClosureReceipts.reported_type_at
    unique port.calleeFound calleeTyped
  have sourceTyped : ExpressionHasType invocation.source context callee port.calleeNode.type := by
    simpa only [reported] using calleeTyped
  have occurrence : Staging.Recursive.Occurrence invocation child (.call callee ids (.indirect metadata)) :=
    ⟨compiler.original, lookupExpression?_sound compiler.found, compiler.originalForm,
      port.sourceParent.requirements, port.sourceParent.coercions⟩
  have actualNamedChildren : ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope},
        (RecursiveNamedPreparedStageScopes.registry stagePrepared).Closure header.function child →
        CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model
          (RecursiveNamedPreparedStageScopes.registry stagePrepared) child
          callFaults size := by
    simpa only [stageEq] using namedChildren
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, _evaluated,
    represented, finalHeaps, maps, worlds, frame, metadataExtended, reached, related, post⟩ :=
    CallableIndexedOwnedPreparedStagedMixedIndirectCallBounds.reflects_parent (semantic := semantic)
      bridge receiver compiler port.prepared stagePrepared rfl occurrence initial port.view port.guardFrame
      profile calleeCertified port.calleeFound sourceTyped environments heaps locals agrees actualTyped
      admitted port.caller port.originalUnique port.sourceParent tree unique parentTyped
      wellFormed runtime covers actualFunctionType observations
      stageEq size children closurePackets closureSupport
      (fun childSize smaller => bodyChildren childSize (Nat.lt_of_lt_of_le smaller within))
    (fun childSize smaller => canonicalChildren childSize (Nat.lt_of_lt_of_le smaller within))
      namedTerminals actualNamedChildren completed (Nat.le_refl _)
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps,
    maps, worlds, frame, metadataExtended, reached, related, post⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds
/-! Internal structural caller fold for chosen terminal or discard closure
bodies. The original Certificate, Point and CallsReady retain their static
indices. Caller children are generated structurally, while strict numeric
Root children feed the concrete mixed call-head assembly. The public numeric
family constructs this internal IH and the named terminal restrictions. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 8192
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPublicFaultReceiverTables (IssuedAt)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport (PacketFor SupportFor)
open CallableIndexedOwnedPreparedStagedNamedBodies (Body)
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Certificate Calls NoMethods NoDirect NoIndexes)
universe u
open CallableLambdaBodyReachability

open CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds (Point CallsReady)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {completion : CallableIndexedOwnedPublicFaultReceivers.Receiver compiled.indexed}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

variable {readFuel : Nat}

variable {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
  (receiver : IssuedAt compiled.indexed completion.entry completion.result.context.registry
    completion.result.extension completion.result.diagnostics)
  {stages : Staging.Recursive.Registry}
  (stagePrepared : RecursiveNamedPreparedStageContracts.Prepared compiled
    compiled.indexed.ancestry.graph.inputs.callable)
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  (wellFormed : ProgramWellFormed (Program.ofChecked compiled.sourceProgram))
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)
  (covers : invocation.evidence.Covers context)
  (unique : NodeOccurrencesUnique invocation.source)
  (actualFunctionType : policy.callables.functionType = CallableContract.functionType)
  {identities : Dynamic.Value → Word → Prop}
  (observations : CompatibleEquality.FunctionObservations compiled.compatible.checked.catalog
    (CallableIndexedOwnedContextualCellOrigins.functions headers keys bodyRegistry semanticFaults profile) identities)
  (extension : SourceCoreRawMetadata.Extends
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked).registry
    completion.result.context.registry)
  (semantic : ∀ reason token, semanticFaults reason token →
    CallableIndexedOwnedPublicDecodedStagedCallFaults.faults completion.result.diagnostics (.semantic reason) token)
  (closurePackets : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), PacketFor association stages)
  (closureSupport : ∀ {mapping world function native bindings parameterCore resultCore}
    (association : Association headers keys bodyRegistry semanticFaults mapping world function native
      bindings parameterCore resultCore), SupportFor association stages (closurePackets association))
  (namedTerminals : ∀ header, header ∈ headers → Body header)

variable
  (sameLedger : context.solvedRequirements = compilation.solvedRequirements)
  (runtimeLedger : RuntimeRequirementLedgerValid context)
  (uninitialized : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))
  {faultRoot : ExpressionId}
  (uninitializedOn : ∀ current child code,
    CompatibleExpressionReads.LoweredRead readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt current child code →
    Reaches invocation.source [.expression faultRoot] (.expression child) →
    ∀ location, semanticFaults (.uninitializedLocation location) (reasonAt child))

local notation "functions" => CallableIndexedOwnedContextualCellOrigins.functions headers keys
  bodyRegistry semanticFaults profile
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked
  completion.result.context.registry functions
local notation "poolBridge" => CallableIndexedOwnedBodyRestorationAdmission.bridge (headers := headers) (keys := keys)
local notation "callFaults" => CallableIndexedOwnedPublicDecodedStagedCallFaults.faults
  completion.result.diagnostics

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves_reached [FunctionCalls.FaultTokens semanticFaults]
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  revert reached
  induction root with
  | proxy receipt =>
      intro _reached _noMethods _noDirect _noIndexes _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.preserves
        functions extension bridge unique callFaults size (.proxy receipt)
  | leaf tree =>
      intro reached _noMethods _noDirect _noIndexes _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.preserves_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => noMethods compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => noDirect compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => noMethods compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => noMethods compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition reached0 (fun compiler inside => noMethods compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => noMethods compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => noMethods compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.preserves_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro childSize _smaller current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => noMethods compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => noDirect compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_preserves bridge unique size
        childMeaning size (Nat.le_refl _) (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => noMethods compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_preserves
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => noMethods compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_preserves
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => noMethods nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.preserves
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree _ihFirst _ihSecond =>
      intro _reached _noMethods _noDirect noIndexes
      exact False.elim (noIndexes header keyFound form sourceType (.here firstTree secondTree))
  | @method id fuel lowered types compiler sequence children _ih =>
      intro  _reached noMethods
      exact False.elim (noMethods compiler (.here sequence children))
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children _ih =>
      intro _reached noMethods noDirect
      exact False.elim (noDirect compiler (.here calleeTyped application sequence children))
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : PreservesBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => noMethods nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds.preserves (semantic := semantic)
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations closurePackets closureSupport namedTerminals
        compiler port calleeCertified sequence size childMeaning
        budget bodyChildren canonicalChildren (namedChildren size within) within ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitializedOn in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects_reached [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode)
    (reached : Reaches invocation.source [.expression faultRoot] (.expression rootId)) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  haveI := CallableIndexedOwnedPublicDecodedStagedCallFaults.tokens
    (CallableIndexedOwnedReceivingPreparedShapeInterpretations.issued_panicFree compiled receiver)
  revert reached
  induction root with
  | proxy receipt =>
      intro _reached _noMethods _noDirect _noIndexes _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedAdmittedStagedProxyBounds.reflects
        functions extension bridge callFaults size (.proxy receipt)
  | leaf tree =>
      intro reached _noMethods _noDirect _noIndexes _ports size _within current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedReadProductTreeBounds.reflects_reached
        bridge functions extension sameLedger runtimeLedger callFaults uninitializedOn semantic
        unique wellFormed runtime covers size ⟨tree, reached⟩
  | @unary id node operand childNode operator operandType resultType core childCode metadata form found inputType outputType unaryProfile child ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression operand) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(operand, ⟨core.operandType, childCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        have pair := Prod.mk.inj member
        obtain ⟨rfl, rfl⟩ := pair
        intro node
        exact ih reached0 (fun compiler inside => noMethods compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => noDirect compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) (fun compiler inside => ports compiler (.unary_child
            (actual := metadata) (form := form) (found := found) (inputType := inputType) (outputType := outputType) (profile := unaryProfile) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .unary metadata form found inputType outputType unaryProfile (by exact ⟨rfl, by simp⟩)
  | @binary id node left right leftNode rightNode operator operandType resultType operatorMode leftCode rightCode metadata form leftFound rightFound leftType rightType outputType binaryProfile first second ihFirst ihSecond =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression left) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression right) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(left, ⟨operatorMode.operandType operator, leftCode⟩), (right, ⟨operatorMode.operandType operator, rightCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihFirst reached0 (fun compiler inside => noMethods compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_left
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihSecond reached1 (fun compiler inside => noMethods compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => noDirect compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) (fun compiler inside => ports compiler (.binary_right
            (actual := metadata) (form := form) (leftFound := leftFound) (rightFound := rightFound) (leftType := leftType) (rightType := rightType) (outputType := outputType)
            (profile := binaryProfile) (first := first) (second := second) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .binary metadata form leftFound rightFound leftType rightType outputType binaryProfile (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @conditional id node condition thenId elseId conditionNode thenNode elseNode type conditionCode thenCode elseCode metadata form conditionFound thenFound elseFound conditionType thenType elseType conditionTree thenTree elseTree ihCondition ihThen ihElse =>
      intro reached noMethods noDirect noIndexes ports size within
      have reached0 : Reaches invocation.source [.expression faultRoot] (.expression condition) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached1 : Reaches invocation.source [.expression faultRoot] (.expression thenId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have reached2 : Reaches invocation.source [.expression faultRoot] (.expression elseId) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope [(condition, ⟨.bool, conditionCode⟩), (thenId, ⟨type, thenCode⟩), (elseId, ⟨type, elseCode⟩)]) callFaults size := by
        intro childSize smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with member0 | member1 | member2
        · have pair := Prod.mk.inj member0
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihCondition reached0 (fun compiler inside => noMethods compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_condition
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member1
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihThen reached1 (fun compiler inside => noMethods compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_then
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
        · have pair := Prod.mk.inj member2
          obtain ⟨rfl, rfl⟩ := pair
          intro node
          exact ihElse reached2 (fun compiler inside => noMethods compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => noDirect compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) (fun compiler inside => ports compiler (.conditional_else
            (actual := metadata) (form := form) (conditionFound := conditionFound) (thenFound := thenFound) (elseFound := elseFound)
            (conditionType := conditionType) (thenType := thenType) (elseType := elseType)
            (conditionTree := conditionTree) (thenTree := thenTree) (elseTree := elseTree) inside)) childSize (Nat.le_trans (Nat.le_of_lt smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      apply CallableIndexedOwnedPreparedStagedOperatorBounds.reflects_at
        bridge functions size size (Nat.le_refl _) unique wellFormed runtime covers childMeaning
      exact .conditional metadata form conditionFound thenFound elseFound conditionType thenType elseType (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩) (by exact ⟨rfl, by simp⟩)
  | @group id node inner innerNode code metadata form innerFound sourceType child ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have innerReached : Reaches invocation.source [.expression faultRoot] (.expression inner) :=
        .expression reached metadata.found (by simp [form, ExpressionForm.references])
      have childMeaning : ReflectsAt bridge context model stages invocation
          (Point rootScope inner code) callFaults size := by
        intro current child actual point
        obtain ⟨rfl, rfl, rfl⟩ := point
        exact ih innerReached (fun compiler inside => noMethods compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => noDirect compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) (fun compiler inside => ports compiler
          (.group (actual := metadata) (form := form) (found := innerFound) (type := sourceType) inside)) size within ⟨rfl, rfl, rfl⟩
      intro current child actual point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedGroupBounds.group_reflects bridge unique size
        childMeaning (.actual metadata form innerFound sourceType ⟨rfl, rfl, rfl⟩)
  | @tuple id node ids types codes header sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [header.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults (size + 1) := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => noMethods compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.tuple_child (header := header) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt_succ _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedTupleHeadBounds.tuple_reflects
        bridge functions callFaults unique wellFormed runtime covers size childMeaning
        ⟨node, ids, types, codes, rfl, header, sequence⟩
  | @constructor id node instantiation ids tag headerWord codes header form admissible ranges count nodes sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached header.metadata.found
          (by simp [form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun compiler inside => noMethods compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => noDirect compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) (fun compiler inside => ports compiler
          (.constructor_child (header := header) (form := form) (admissible := admissible) (ranges := ranges) (count := count) (nodes := nodes) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedConstructorHeadBounds.constructor_reflects
        bridge functions extension callFaults unique wellFormed runtime covers size childMeaning
        header form admissible ranges count nodes sequence ⟨rfl, rfl, rfl⟩
  | @builtin id callee ids function fuel lowered compiler calleeTyped sourceType nativeTypes sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ ids.zip compiler.codes →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        exact .expression reached compiler.metadata.found
          (by simp [compiler.form, ExpressionForm.references, (List.of_mem_zip member).1])
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope (ids.zip compiler.codes)) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => noMethods nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.builtin_child (outer := compiler) (calleeTyped := calleeTyped)
            (sourceType := sourceType) (nativeTypes := nativeTypes)
            (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedDirectBuiltinHeadBounds.reflects
        bridge functions observations callFaults unique wellFormed runtime covers
        (compiler.result ▸ compiler.metadata) compiler.form nativeTypes size sequence childMeaning
        ⟨rfl, rfl, compiler.output⟩
  | @index id node base key baseNode keyNode layout comparison first second header keyFound form sourceType firstTree secondTree _ihFirst _ihSecond =>
      intro _reached _noMethods _noDirect noIndexes
      exact False.elim (noIndexes header keyFound form sourceType (.here firstTree secondTree))
  | @method id fuel lowered types compiler sequence children _ih =>
      intro  _reached noMethods
      exact False.elim (noMethods compiler (.here sequence children))
  | @direct id callee ids instantiation fuel lowered types compiler calleeTyped application sequence children _ih =>
      intro _reached noMethods noDirect
      exact False.elim (noDirect compiler (.here calleeTyped application sequence children))
  | @call id callee ids metadata fuel lowered types compiler sequence children ih =>
      intro reached noMethods noDirect noIndexes ports size within
      have childReached : ∀ child code, (child, code) ∈ compiler.entries →
          Reaches invocation.source [.expression faultRoot] (.expression child) := by
        intro child code member
        apply Reaches.expression reached compiler.found
        simp only [CallableIndirectCallCertificates.Receipt.entries, List.mem_cons] at member
        rcases member with same | member
        · have sameId : child = callee := congrArg Prod.fst same
          simp [compiler.originalForm, ExpressionForm.references, sameId]
        · simp [compiler.originalForm, ExpressionForm.references, (List.of_mem_zip member).1]
      have childMeaning : ReflectsBelow bridge context model stages invocation
          (RecursiveStageTupleMeaning.Entries rootScope compiler.entries) callFaults size := by
        intro childSize _smaller current child code entry
        obtain ⟨rfl, member⟩ := entry
        exact ih child code member (childReached child code member)
          (fun nested inside => noMethods nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => noDirect nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun indexed indexFound indexForm indexType inside => noIndexes indexed indexFound indexForm indexType
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) (fun nested inside => ports nested
          (.call_child (outer := compiler) (sequence := sequence) (children := children) member inside)) childSize (Nat.le_trans (Nat.le_of_lt _smaller) within) ⟨rfl, rfl, rfl⟩
      obtain ⟨port⟩ := ports compiler (.here sequence children)
      have calleeCertified : RecursiveStageTupleMeaning.Entries rootScope compiler.entries
          rootScope callee compiler.calleeCode := ⟨rfl, by simp [CallableIndirectCallCertificates.Receipt.entries]⟩
      intro current child code point
      obtain ⟨rfl, rfl, rfl⟩ := point
      exact CallableIndexedOwnedPreparedStagedMixedGeneralCallHeadBounds.reflects (semantic := semantic)
        bridge receiver stagePrepared rfl profile wellFormed runtime covers unique
        actualFunctionType observations closurePackets closureSupport namedTerminals
        stageEq compiler port calleeCertified sequence size childMeaning
        budget bodyChildren canonicalChildren (namedChildren size within) within ⟨rfl, rfl, rfl⟩

include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every strict Source child is supplied by structural recursion at its actual
reached state. The numeric family supplies only the chosen called-body laws below the fixed
budget; all caller child laws are constructed here. -/
theorem preserves [FunctionCalls.FaultTokens semanticFaults]
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.PreservesRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.PreservesRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.PreservesBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size) {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size, size ≤ budget →
      PreservesAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact preserves_reached (faultRoot := rootId) bridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closurePackets closureSupport namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    budget bodyChildren canonicalChildren namedChildren root (.root (by simp))


include bridge receiver stagePrepared profile wellFormed runtime covers unique
  actualFunctionType observations extension semantic closurePackets closureSupport namedTerminals
  sameLedger runtimeLedger uninitialized in
/-- Every child native grade comes from structural recursion. The returned
Source grade is independent, including exact nested stage failure scope. -/
theorem reflects [FunctionCalls.FaultTokens semanticFaults] (stageEq : stages = RecursiveNamedPreparedStageScopes.registry stagePrepared)
    (budget : Nat)
    (bodyChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedSelectedRecursiveBodyBounds.ReflectsRootsAt
        (completion := completion) (stages := stages) (headers := headers) (keys := keys)
        (bodyRegistry := bodyRegistry) (semanticFaults := semanticFaults) profile childSize)
    (canonicalChildren : ∀ childSize, childSize < budget →
      CallableIndexedOwnedPreparedStagedCanonicalBodyStaticSupport.ReflectsRootsAt
        (headers := headers) (keys := keys)
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked completion.result.context.registry functions)
        stages semanticFaults callFaults childSize)
    (namedChildren : ∀ size, size ≤ budget → ∀ header (_member : header ∈ headers),
      ∀ {child : Staging.Recursive.Scope}, stages.Closure header.function child →
      CallableIndexedOwnedPreparedStagedNamedBodyPorts.ReflectsBelow (headers := headers) (keys := keys)
        header model stages child
        callFaults size)
    {rootScope : SourceCoreLocalCell.Scope} {rootId : ExpressionId}
    {rootCode : SourceCoreBasic.LoweredExpr}
    (root : Certificate policy body compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
      invocation.source context reasonAt rootScope rootId rootCode) :
    NoMethods root → NoDirect root → NoIndexes root → CallsReady root → ∀ size, size ≤ budget →
      ReflectsAt bridge context model stages invocation
        (Point rootScope rootId rootCode) callFaults size := by
  exact reflects_reached (faultRoot := rootId) bridge receiver stagePrepared profile
    wellFormed runtime covers unique actualFunctionType observations extension semantic
    closurePackets closureSupport namedTerminals sameLedger runtimeLedger
    (fun current child code receipt _reached => uninitialized current child code receipt)
    stageEq budget bodyChildren canonicalChildren namedChildren root (.root (by simp))

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedRecursiveCallerBounds
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureCompilerFactories
/-! The same produced lambda Site supplies a discard-and-terminal packet on
its literal recaptured Code. The retained production recipe constructs the
whole compiler action, expression callback and statement reader internally.
Original frame and parameter typing supply both raw children at every selected
Source scope. Policy coverage, declarations, view edits and callsite authority
remain separate static inputs at the exact internally issued certificates.
The Association endpoint covers this actual ordinary formation only. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureCompilerFactories
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedLambdaValues CallableIndexedNamedGeneration
open CallableIndexedOwnedFunctionValues (Header OwnedKey)
open CallableIndexedOwnedContextualTypedClosureReceipts (Association)
open CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks (Produced loop_policy)
open CallableIndexedOwnedPreparedStagedSelectedClosureCompilerFactories
  (function code ordinary_support association body_callback)
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (Syntax PolicyFor)
open CallableIndexedOwnedPreparedStagedSelectedBodySupportFactories (OriginalConditions)
open CallableIndexedOwnedPreparedStagedMixedBodyStaticSupport
  (Discard DiscardSupport PacketFor SupportFor parameterScope)
open CallableLambdaViewEdits CallableLambdaBodyReachability

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {caller : Header compiled (Program.ofChecked compiled.sourceProgram)}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed caller.named diagnostics namedCode}
  {parameters : List TypedBinder} {result : TypeSystem.Ty} {statements : List StatementId}
  {sourceContext : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}
  {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {expressionSyntax : TypedSource → ExpressionId → Prop}
  {certificates : Nat → TypedSource → SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {semanticFaults : FunctionCalls.FaultRep}

section Produced
variable (produced : Produced compiled caller.named diagnostics namedCode compilation
  parameters result statements sourceContext evidence [] scope administrative id lowered)
  {environment : Dynamic.Environment} {stages : Staging.Recursive.Registry}

/-- The chosen receipt and its compiler identities belong to one produced
Code. No choice is extracted from Prop into a new Type-valued selector. -/
structure Choice where
  packet : Discard (code produced environment) stages
  callback : packet.policy.lowerExpression = FunctionCode.children (code produced environment).policy
    (code produced environment).lowerBody (code produced environment).fuel
    (code produced environment).compilation
  reason : packet.reasonAt = (code produced environment).reasonAt
  fuel : packet.fuel = (code produced environment).fuel

/-- The actual production body recipe and discard shape manufacture the
receipt. The selected Source child is retained unchanged in that receipt. -/
theorem choose (statement next : StatementId) (rest : List StatementId)
    (firstExpression terminalExpression : ExpressionId)
    (bodyShape : statements = statement :: next :: rest)
    (shape : CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.Shape
      (code produced environment).view statement firstExpression terminalExpression (next :: rest))
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    Nonempty (Choice produced (environment := environment) (stages := stages)) := by
  let policy := loop_policy compiled.indexed caller.named compilation.own.assignments diagnostics
    (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
      (code produced environment).fuel (code produced environment).compilation)
  have accepted := CallableIndexedLambdaSemanticInvocation.loops_accepted
    (values := SourceCoreCompatibleValues.Context.initial compiled.compatible.checked)
    (code produced environment) policy (body_callback produced environment)
  have actualBody :
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).body =
        statement :: next :: rest := bodyShape
  obtain ⟨receipt⟩ := CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerReceipts.of_accepted
    (CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.statement_reader
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation))
    shape (by simpa only [actualBody] using accepted)
  let packet : Discard (code produced environment) stages := {
    policy := policy
    fuel := (code produced environment).fuel
    statement := statement
    next := next
    rest := rest
    firstExpression := firstExpression
    terminalExpression := terminalExpression
    reasonAt := (code produced environment).reasonAt
    fellThrough := (code produced environment).compilation.internalReason
    escaped := (code produced environment).compilation.internalReason
    body := actualBody
    receipt := receipt
    child := child
    selected := selected }
  exact ⟨{
    packet := packet
    callback := CallableIndexedOwnedPreparedStagedSelectedBodyCompilerCallbacks.expression_callback
      compiled.indexed caller.named compilation.own.assignments diagnostics
      (FunctionCode.children (code produced environment).policy (code produced environment).lowerBody
        (code produced environment).fuel (code produced environment).compilation)
    reason := rfl
    fuel := rfl }⟩

private theorem terminal_reaches {source view : TypedSource}
    {statement next : StatementId} {rest : List StatementId} {expression : ExpressionId}
    (metadata : LambdaMetadataViews.MetadataView source view)
    (terminal : CallableIndexedOwnedPreparedTerminalBodyCompilerReceipts.Terminal
      view expression (next :: rest)) :
    Reaches source ((statement :: next :: rest).map NodeId.statement) (.expression expression) := by
  cases terminal with
  | returning rest found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])
  | tail found form =>
      exact .statement (.root (by simp)) (metadata.statement found)
        (by simp [form, StatementForm.references])

variable (body : CallableIndexedLambdaStaticBodySupport.BodyWith
  (values := .initial compiled.compatible.checked) expressionSyntax certificates
  produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (choice : Choice produced (environment := environment) (stages := stages))

/-- These are original static facts at the retained parameter context. The
expression callback, frame, parameter typing and reachable child paths are
constructed from the produced Site and packet instead of being supplied. -/
structure Conditions where
  readFuel : Nat
  changed : List ExpressionId
  edited : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    LocalView child.source (code produced environment).view changed
  avoids : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    Avoids child.source (statements.map NodeId.statement) changed
  sourceProfile : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
      (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) child.source
      (parameterScope (code produced environment)) choice.packet.reasonAt
  viewProfile : PolicyFor (code produced environment).policy (code produced environment).compilation readFuel
    (SourceCoreCompatibleValues.Context.initial compiled.compatible.checked) (code produced environment).view
    (parameterScope (code produced environment)) choice.packet.reasonAt
  firstSyntax : Syntax (code produced environment).view choice.packet.firstExpression
  terminalSyntax : Syntax (code produced environment).view choice.packet.terminalExpression
  original : ∀ child, stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child →
    OriginalConditions compiled (code produced environment).policy (code produced environment).compilation readFuel
      (ordinary_support produced body environment).body.toContext.context child choice.packet.reasonAt
      (parameterScope (code produced environment)) semanticFaults

/-- The original discard occurrence supplies its child's reference path. -/
theorem first_reached : Reaches
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
    (statements.map NodeId.statement) (.expression choice.packet.firstExpression) := by
  have reached : Reaches
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
      ((choice.packet.statement :: choice.packet.next :: choice.packet.rest).map NodeId.statement)
      (.expression choice.packet.firstExpression) :=
    .statement (.root (by simp))
      ((code produced environment).viewOfSource.statement choice.packet.receipt.shape.found)
      (by simp [choice.packet.receipt.shape.form, StatementForm.references])
  have bodyShape : statements = choice.packet.statement :: choice.packet.next :: choice.packet.rest :=
    choice.packet.body
  simpa only [bodyShape] using reached

/-- The tail occurrence keeps its own path through the same body roots. -/
theorem terminal_reached : Reaches
    (function (caller := caller) (parameters := parameters) (result := result)
      (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment).source
    (statements.map NodeId.statement) (.expression choice.packet.terminalExpression) := by
  have reached := terminal_reaches (statement := choice.packet.statement)
    (code produced environment).viewOfSource choice.packet.receipt.shape.terminal
  have bodyShape : statements = choice.packet.statement :: choice.packet.next :: choice.packet.rest :=
    choice.packet.body
  simpa only [bodyShape] using reached

/-- Actual BodyWith inputs and frame produce raw Source typing before the
checked original-root issuer is used at each genuine selected scope. -/
theorem static (conditions : Conditions produced body choice)
    (child : Staging.Recursive.Scope)
    (selected : stages.Closure
      (function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment) child) :
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Static
      (statementPolicy := choice.packet.policy) (fuel := choice.packet.fuel)
      (view := (code produced environment).view) (scope := parameterScope (code produced environment))
      (statement := choice.packet.statement) (next := choice.packet.next) (rest := choice.packet.rest)
      (firstExpression := choice.packet.firstExpression) (terminalExpression := choice.packet.terminalExpression)
      (result := (code produced environment).receipt.resultCore) (reasonAt := choice.packet.reasonAt)
      (fellThrough := choice.packet.fellThrough) (escaped := choice.packet.escaped)
      (code := (code produced environment).receipt.body)
      (compiled := compiled)
      (function := function (caller := caller) (parameters := parameters) (result := result)
        (statements := statements) (sourceContext := sourceContext) (evidence := evidence) environment)
      (context := (ordinary_support produced body environment).body.toContext.context)
      (types := (ordinary_support produced body environment).body.toContext.types)
      (invocation := child) (changed := conditions.changed) (roots := statements.map NodeId.statement)
      (policy := (code produced environment).policy) (lowerBody := (code produced environment).lowerBody)
      (compilation := (code produced environment).compilation)
      (readFuel := conditions.readFuel) (bodyFuel := (code produced environment).fuel)
      (semanticFaults := semanticFaults)
      (native := some compiled.indexed.ancestry.graph.inputs.callable)
      (active := (code produced environment).active) choice.packet.receipt := {
  edited := conditions.edited child selected
  avoids := conditions.avoids child selected
  sourceProfile := conditions.sourceProfile child selected
  viewProfile := conditions.viewProfile
  callables := (code produced environment).callables
  expressionCallback := by
    funext childFuel actualSource current expression reasonAt
    have callbackAt := congrArg
      (fun lower : SourceCoreFunctions.ExpressionLowerer =>
        lower childFuel actualSource current expression reasonAt) choice.callback
    simpa only [FunctionCode.children] using callbackAt
  frame := (ordinary_support produced body environment).body.frame
  parameters := (ordinary_support produced body environment).body.toContext.extended
  sameSource := stages.source selected
  body := choice.packet.body
  firstSyntax := conditions.firstSyntax
  terminalSyntax := conditions.terminalSyntax
  firstReached := by simpa only [stages.source selected] using first_reached produced choice
  terminalReached := by simpa only [stages.source selected] using terminal_reached produced choice
  conditions := conditions.original child selected }

/-- Readiness concerns only the two certificates issued from this same
packet; it contains actual call authority and no execution theorem. -/
def Ready (conditions : Conditions produced body choice) : Prop :=
  ∀ child selected,
    CallableIndexedOwnedPreparedStagedDiscardTerminalCompilerFlowBounds.Ready
      (static produced body choice conditions child selected)

/-- The real two original Roots and terminal result type are built internally. -/
def support (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    DiscardSupport (code produced environment) (ordinary_support produced body environment).body.toContext
      stages choice.packet semanticFaults :=
  CallableIndexedOwnedPreparedStagedMixedBodyCompilerSupport.of_static choice.packet
    (static produced body choice conditions) ready
end Produced

section Association
variable {headers : List (Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {actual : Environment}
  (captured : Captures compiled.indexed mapping world scope environment actual)
  (produced : Produced compiled caller.named diagnostics namedCode compilation
    parameters result statements sourceContext evidence [] scope captured.administrative id lowered)
  (body : CallableIndexedLambdaStaticBodySupport.BodyWith
    (values := .initial compiled.compatible.checked) expressionSyntax certificates
    produced.site.code (Program.ofChecked compiled.sourceProgram) bodyRegistry semanticFaults)
  (bodyView : CallableIndexedOwnedContextualLambdaProvenance.BodyView produced.site.code)
  (bodyReasons : CallableIndexedOwnedContextualLambdaProvenance.BodyReasons produced.site.code caller.named)
  (declarations : CompatibleExpressionReads.ScopeDeclarations (source caller.named) scope sourceContext)
  (callerGlobals : caller.globals = compiled.indexed.base.globals.length)
  (callerReceipt : CallableIndexedOwnedOrdinaryCallerReceipts.CallerAt caller sourceContext evidence)
  {stages : Staging.Recursive.Registry}
  (owner : OwnedKey keys) (history : CallableIndexedLambdaValues.History (code produced environment))
  (origin : CallableIndexedOwnedOrdinaryLambdaSupport.SourceOrigin
    (ordinary_support produced body environment) history)
  (prefixContext : captured.administrative = RecursiveNamedLambdaFormationHeads.nativePrefix
    (values := .initial compiled.compatible.checked) caller)
  (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := Program.ofChecked compiled.sourceProgram)
    headers owner.key.locations 1 scope captured.canonical owner.key.frameLocation)
  (referenceIndex : (code produced environment).referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
  (typed : RuntimeValueHasType world (value (code produced environment) captured.embedding history.native actual)
    (CallableContract.functionType (code produced environment).receipt.parameterCore
      (code produced environment).receipt.resultCore) compiled.indexed.layouts.definitions)
  (syntaxTree : GenericImperativeMatch.Syntax (source caller.named)
    (expressionSyntax (source caller.named)) body.context (.statements true statements) result)

/-- This ordinary Association reduces to the same recaptured Code. -/
def packet_for (choice : Choice produced (environment := environment) (stages := stages)) :
    PacketFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages := .discard choice.packet

/-- No callback or body law is supplied for arbitrary Associations. This
support is at the actual retained ordinary formation and its literal packet. -/
def support_for (choice : Choice produced (environment := environment) (stages := stages))
    (conditions : Conditions produced body choice)
    (ready : Ready produced body choice conditions) :
    SupportFor
      (association captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree)
      stages
      (packet_for captured produced body bodyView bodyReasons declarations callerGlobals callerReceipt owner history origin prefixContext globals referenceIndex typed syntaxTree choice) :=
  support produced body choice conditions ready
end Association

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMixedClosureCompilerFactories
end
