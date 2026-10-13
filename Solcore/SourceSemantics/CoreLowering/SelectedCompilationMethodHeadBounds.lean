import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedMethodSourceArguments
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentRows
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodInvocationBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodPhysicalCaptures
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerSlotForgetting
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedExpressionHeads
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodArgumentBounds
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationSourceAdmission

/-! Actual selected operator calls preserve and reflect the full caller state.
Ordered operand meaning supplies the reached argument heap; the real physical
method slot and marked parameter entry feed strict method body callbacks. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedAdmittedStagedExpressionBounds
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
universe u

def Point (scope : SourceCoreLocalCell.Scope) (id : ExpressionId)
    (lowered : SourceCoreBasic.LoweredExpr) : GenericExpressionMeaning.Certificate :=
  fun current child code => current = scope ∧ child = id ∧ code = lowered

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram))}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled (Program.ofChecked compiled.sourceProgram))}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {scope : SourceCoreLocalCell.Scope}
  {context : SourceSemantics.Context} {invocation : Staging.Recursive.Scope}
  {id : ExpressionId} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (receipt : Receipt policy body fuel compilation (.initial compiled.compatible.checked)
    invocation.source scope id reasonAt lowered)
  {stages : Staging.Recursive.Registry}
  (port : Port (compiled := compiled) receipt context invocation.evidence stages)
  (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun index => CallableIndexedOwnedExpressionHeads.Globals (headers := headers)
      owner compilation.administrativePrefix index.scope index.canonical) callerProtocol)
  (ownerFrame : owner.key.frameLocation = 0)
  (physical : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Authority compiled index.mapping index.store)
  (slots : ∀ {index}, callerProtocol.State index →
    CallableIndexedOwnedPhysicalGlobals.Slots compiled compilation.administrativePrefix index.scope index.canonical)
  (functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed))
  {receiving : SourceCoreRawMetadata.Registry}
  (faults : RecursiveStageMeaning.FaultRep)
  (unique : NodeOccurrencesUnique invocation.source)
  (catalog : SignatureCatalogWellFormed compiled.sourceProgram.signatures)
  (selection : Dynamic.TypedOperatorMethodSelected (Program.ofChecked compiled.sourceProgram)
    context invocation.evidence port.principal.traitName port.principal.methodName receipt.node.requirements
    port.principal.sourceBody port.principal.dictionary)
  (runtime : Dynamic.SourceRuntimeValid (Program.ofChecked compiled.sourceProgram) context invocation.source)

local notation "bridge" => callerBridge.forgetSlots
local notation "model" => CompatibleAmbientHeap.payloadModel compiled.compatible.checked receiving functions

/-- A strict Source body callback at an authentic reached argument state. -/
def SourceBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.SourceContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

/-- The native counterpart uses the same independently typed argument heap. -/
def NativeBodies (budget : Nat) : Prop :=
  ∀ {mapping world heap store callerScope canonical administrative arguments payloads}
    (caller : State headers keys ⟨callerScope, mapping, world, heap, store, canonical⟩)
    (installed : CallablePreparedMethodRuntimeMeaning.Installed port.principal.cached.compilation
      (values := .initial compiled.compatible.checked) (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      (sourceBody := port.principal.sourceBody) (administrative := administrative)
      functions mapping world heap store canonical),
    CallableIndexedParameterMeaning.Arguments model mapping world port.principal.named.inputs arguments payloads →
    Dynamic.HeapWellTyped port.principal.sourceFunction.context heap →
    Dynamic.ValuesHaveTypes port.principal.sourceFunction.context heap arguments port.sourceAt.types →
    CallableIndexedOwnedIndirectExpressionHeads.StableRows caller →
    ∀ {child}, stages.Closure port.principal.sourceFunction child →
    SelectedCompilationMethodInvocationBounds.NativeContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child) (faults := faults)
      port.principal.cached.compilation port.sourceAt functions installed budget

private theorem result_type : lowered.type = port.principal.named.signature.resultType :=
  receipt.result.symm.trans ((congrArg SourceCoreCalls.Signature.resultType port.signature).symm)

private theorem parameter_type : port.principal.named.signature.parameterType =
    (SourceCoreCalls.packArguments receipt.codes).type := by
  rw [port.signature]
  exact receipt.parameter

private theorem capture_read {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap}
    {store : Store} {canonical : Environment}
    (capture : CallableIndexedOwnedMethodPhysicalCaptures.Capture port.principal.cached port.principal.dictionary
      functions mapping world heap store canonical)
    (authority : CallableIndexedOwnedPhysicalGlobals.Authority compiled mapping store) :
    store.read? (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index) = some (.inRight .unit
      (.closure port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        (port.principal.cached.compilation.output.rename capture.installed.embedding.lift) capture.installed.captured)) := by
  have cachedCode : compiled.indexed.secondPass.closures[port.principal.cached.index]? = some
      (.lambda port.principal.named.signature.parameterType (LanguageResult.resultType port.principal.named.signature.resultType)
        port.principal.cached.compilation.output) := by
    simpa only [port.principal.cached.compilation.emitted] using port.principal.cached.cached
  simpa only [capture.embedding_eq, capture.captured_eq] using (authority.cached cachedCode).2

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem preserves {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : PreservesBelow bridge context model stages invocation children faults size)
    (bodyMeaning : SourceBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    PreservesAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted trace
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  have originalTrace := trace
  rcases CallableIndexedOwnedPreparedStagedMethodSourceArguments.children receipt port unique trace with
    ⟨argumentsHeap, sources, sourceTrace, bodySize, bodyEnvironment, bound, finalContext, bodyOutcome, selectedChild,
      selected, allocated, bodyTrace, matched, strict⟩ | ⟨failure, outcomeEq, sourceTrace⟩
  · obtain ⟨values, middleStore, middleMap, middleWorld, argumentsEvaluated, represented, middleHeaps,
        argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
      SelectedCompilationMethodArgumentBounds.preserves_values bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    have argumentsTyped := post.values_typed
    have argumentsHeapTyped := post.at_values.heap
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port represented
    obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    obtain ⟨value, finalStore, finalMap, finalWorld, bodyEvaluated, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨finalState, bodyRelated⟩, bodyPreserved⟩ :=
      SelectedCompilationMethodInvocationBounds.preserves
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows selected)
        allocated bodyTrace matched strict
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    have selectedValue := OptionalCell.read_success compilation.internalReason
      (show Evaluates (packValues values :: actual) middleStore
        (.var (ξ (current.length + compilation.administrativePrefix + port.principal.cached.index) + 1))
        (.cellRef (OptionalCell.cellType port.principal.named.signature.functionType)
          (CallableIndexedOwnedPhysicalGlobals.location compiled port.principal.cached.index)) middleStore from .var reference) read
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨value, finalStore, finalMap, finalWorld, ?_, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot]
      exact SourceCoreCalls.call_success argumentsEvaluated selectedValue bodyEvaluated
    · simpa only [sourceResult, nativeResult] using result
    · refine after_expression_sized_of_preserved initial returned admitted originalTrace ?_
        (argumentFrame.trans bodyFrame)
      intro sourceValue same
      have preserved := bodyPreserved sourceValue same
      have actual := SelectedCompilationMethodArgumentRows.result_at_values receipt port catalog selection
        runtime unique typed preserved
      exact ⟨actual.1, actual.2, argumentMetadata.trans bodyMetadata⟩
  · subst outcome
    obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEvaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related, post⟩ :=
      SelectedCompilationMethodArgumentBounds.preserves_fault bridge size sequence unique orderedTyping
        childMeaning environments heaps locals agrees actualTyped initial admitted sourceTrace
    refine ⟨_, finalStore, finalMap, finalWorld, ?_, .fault matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related, ?_⟩
    · rw [receipt.emitted, NamedCalls.Arguments.call_rename]
      simpa only [receipt.result] using SourceCoreCalls.call_argument_failure
        (signature := receipt.signature) (index := ξ (current.length + compilation.administrativePrefix + receipt.index))
        (internalReason := compilation.internalReason) (receipt.parameter.symm ▸ argumentsEvaluated)
    · exact post.fault

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem reflects {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childMeaning : ReflectsBelow bridge context model stages invocation children faults size)
    (bodyMeaning : NativeBodies (headers := headers) (receiving := receiving) owner receipt port functions faults size) :
    ReflectsAt bridge context model stages invocation (Point scope id lowered) faults size := by
  intro current child code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees actualTyped initial admitted completed
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  obtain ⟨orderedTyping, sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  have nativeResult := result_type receipt port
  have parameter := parameter_type receipt port
  rw [receipt.emitted, NamedCalls.Arguments.call_rename, ← port.signature, ← port.slot] at completed
  obtain ⟨sequenceSize, argumentValue, middleStore, smaller, argumentEvaluation⟩ :=
    RecursiveNamedCallBounds.call_arguments completed
  obtain ⟨sourceSize, sourceOutcome, argumentsHeap, middleMap, middleWorld, sourceTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, post⟩ :=
    SelectedCompilationExpressionSequence.reflects bridge size sequence unique orderedTyping childMeaning
      environments heaps locals agrees actualTyped initial admitted argumentEvaluation smaller
  cases represented with
  | fault matched =>
    have evaluated := SourceCoreCalls.call_argument_failure
      (signature := port.principal.named.signature)
      (index := ξ (current.length + compilation.administrativePrefix + port.principal.cached.index))
      (internalReason := compilation.internalReason) (parameter.symm ▸ argumentEvaluation.sound)
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluated
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port sourceTrace
    refine ⟨_, _, argumentsHeap, middleMap, middleWorld, trace, ?_, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, reached, related, ?_⟩
    · rw [nativeResult]
      exact .fault matched
    · exact post.fault
  | @values sources values payloads =>
    have argumentsTyped := post.values_typed
    have argumentsHeapTyped := post.at_values.heap
    obtain ⟨headerHeap, headerArguments, _result⟩ :=
      SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
        argumentsHeapTyped argumentsTyped
    have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port payloads
    obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
      port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
      (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
    have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
      rw [capture.canonical_eq]
      exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
    have reference := agrees (slots initial _ _
      (CallableIndexedPreparedInventories.cached_global_at compiled port.principal.cached.selected))
    have read := capture_read receipt port functions capture (physical reached)
    obtain ⟨bodySize, bodySmaller, bodyEvaluation⟩ := RecursiveNamedCallBounds.call_body
      argumentEvaluation.sound reference read completed
    obtain ⟨bodySourceSize, bodyEnvironment, bound, finalContext, bodyOutcome, outcome, after, finalMap, finalWorld,
        allocated, bodyTrace, matched, result, finalHeaps,
        bodyMaps, bodyWorlds, bodyFrame, bodyMetadata, ⟨finalState, bodyRelated⟩, bodyPreserved⟩ :=
      SelectedCompilationMethodInvocationBounds.reflects
        port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
        (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size
        (bodyMeaning (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows port.staged)
        bodyEvaluation (Nat.le_of_lt bodySmaller)
    obtain ⟨_, trace⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.applied receipt port sourceTrace
      port.staged allocated bodyTrace matched
    obtain ⟨returned, _samePool, returnedRelated⟩ := callerBridge.restore initial finalState
      (argumentMaps.trans bodyMaps) (argumentWorlds.trans bodyWorlds)
      (argumentFrame.trans bodyFrame) (argumentMetadata.trans bodyMetadata)
      ((callerBridge.related related).trans bodyRelated)
    refine ⟨_, outcome, after, finalMap, finalWorld, trace, ?_, finalHeaps,
      argumentMaps.trans bodyMaps, argumentWorlds.trans bodyWorlds,
      argumentFrame.trans bodyFrame, argumentMetadata.trans bodyMetadata, returned, returnedRelated, ?_⟩
    · simpa only [sourceResult, nativeResult] using result
    · refine after_expression_sized_of_preserved initial returned admitted trace ?_
        (argumentFrame.trans bodyFrame)
      intro sourceValue same
      have preserved := bodyPreserved sourceValue same
      have actual := SelectedCompilationMethodArgumentRows.result_at_values receipt port catalog selection
        runtime unique typed preserved
      exact ⟨actual.1, actual.2, argumentMetadata.trans bodyMetadata⟩

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds
