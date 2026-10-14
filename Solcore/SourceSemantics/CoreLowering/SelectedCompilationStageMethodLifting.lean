import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorArgumentsLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageOperatorSourceTrace
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodInvocationLifting
import Solcore.SourceSemantics.CoreLowering.SelectedCompilationMethodHeadBounds

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof DataPatternValues
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedPreparedStagedOperatorMethodCertificates (Receipt)
open CallableIndexedOwnedPreparedStagedOperatorMethodAuthority (Port)
open SelectedCompilationStageLiftBounds (LiftsAt)
open Staging.Recursive.Lifting (ExpressionLift)
universe u

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
def BodyLifts (budget : Nat) : Prop :=
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
    SelectedCompilationStageMethodInvocationLifting.LiftContinuation
      (program := Program.ofChecked compiled.sourceProgram) (registry := receiving)
      (owner := owner) (caller := caller) (arguments := arguments) (payloads := payloads)
      (stages := stages) (child := child)
      port.principal.cached.compilation port.sourceAt functions installed budget


include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem raw_trace {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodies : BodyLifts (headers := headers) (receiving := receiving) owner receipt port functions size)
    (typed : ExpressionHasType invocation.source context id receipt.node.type)
    {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after}
    (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) mapping world administrativeContext scope
      environment canonical (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext (CallableIndexedAmbient.ambientDefinitions compiled.indexed).definitions)
    (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (admitted : Admission bridge context initial)
    (original : CallablePreparedOperatorSourceBounds.RawTraceAt (Program.ofChecked compiled.sourceProgram) size
      context invocation.evidence port.principal.dictionary invocation.source environment before
      receipt.arguments port.principal.sourceBody outcome after) :
    ExpressionLift (Program.ofChecked compiled.sourceProgram) stages invocation context environment before id outcome after := by
  obtain ⟨orderedTyping, _sourceResult⟩ :=
    SelectedCompilationMethodArgumentRows.raw_types receipt port catalog selection runtime unique typed
  cases original with
  | argumentFault failed =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageOperatorArgumentsLifting.fault bridge
      size sequence unique orderedTyping childLift preservation environments heaps locals agrees actualTyped initial admitted failed
    cases adapted with
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .completed⟩
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .rejected origin call reason _⟩
  | apply evaluated called strict =>
    obtain ⟨staged, reached, trace, adapted⟩ := SelectedCompilationStageOperatorArgumentsLifting.values bridge
      size sequence unique orderedTyping childLift preservation environments heaps locals agrees actualTyped initial admitted evaluated
    cases adapted with
    | rejected origin call reason reached =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.arguments_fault receipt port measured
      exact ⟨_, _, lifted.sound, .rejected origin call reason _⟩
    | completed =>
      obtain ⟨grade, measured⟩ := Staging.Recursive.Size.Expressions.of_trace trace
      obtain ⟨values, middleStore, middleMap, middleWorld, _argumentsEvaluated, represented, middleHeaps,
          _argumentMaps, _argumentWorlds, _argumentFrame, _argumentMetadata, reached, _related, post⟩ :=
        SelectedCompilationExpressionSequence.preserves_values bridge grade sequence unique orderedTyping
          (fun size _ => preservation size) environments heaps locals agrees actualTyped initial admitted measured (Nat.le_refl _)
      obtain ⟨headerHeap, headerArguments, _result⟩ :=
        SelectedCompilationMethodArgumentRows.at_values receipt port catalog selection runtime unique typed
          post.at_values.heap post.values_typed
      have parameters := SelectedCompilationMethodArgumentRows.represented_arguments receipt port represented
      obtain ⟨capture⟩ := SelectedCompilationMethodPhysicalCaptures.of_typed
        port.principal.cached port.principal.dictionary functions owner (callerBridge.pool reached) ownerFrame
        (physical reached) middleHeaps.runtime_hasTypes (slots reached) selection
      have capturedSlots : CallableIndexedOwnedPhysicalGlobals.Slots compiled 0 [] capture.installed.canonical := by
        rw [capture.canonical_eq]
        exact CallableIndexedOwnedPhysicalGlobals.environment_slots compiled
      obtain ⟨bodyEnvironment, bound, finalContext, stagedBody, result, finalHeap, allocated, bodyTrace, matched, adapted⟩ :=
        SelectedCompilationStageMethodInvocationLifting.lifts_invocation
          port.principal.cached.compilation port.sourceAt functions capture.installed parameters owner (callerBridge.pool reached)
          (capture.frame_eq.trans ownerFrame.symm) middleHeaps (physical reached) capturedSlots size port.staged
          (bodies (callerBridge.pool reached) capture.installed parameters headerHeap headerArguments post.at_values.rows port.staged)
          called (Nat.le_of_lt strict)
      obtain ⟨bodyGrade, bodyMeasured⟩ := Staging.Recursive.Size.StatementsIn.of_trace bodyTrace
      obtain ⟨_, lifted⟩ := CallableIndexedOwnedPreparedStagedMethodSourceArguments.applied receipt port
        measured port.staged allocated bodyMeasured matched
      exact ⟨_, _, lifted.sound, adapted⟩

include owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime in
theorem method {children : GenericExpressionMeaning.Certificate}
    (size : Nat)
    (sequence : DataExpressionSequence.Tree invocation.source children scope receipt.arguments
      (port.principal.named.inputs.map (fun binding => binding.1.scheme.body)) receipt.codes)
    (childLift : ∀ childSize, childSize < size → LiftsAt bridge context model stages invocation children childSize)
    (preservation : ∀ childSize, CallableIndexedOwnedAdmittedStagedExpressionBounds.PreservesAt
      bridge context model stages invocation children faults childSize)
    (bodies : BodyLifts (headers := headers) (receiving := receiving) owner receipt port functions size) :
    LiftsAt bridge context model stages invocation
      (CallableIndexedOwnedPreparedStagedSelectedRecursiveCallerBounds.Point scope id lowered) size := by
  intro current expression code point actualNode found typed
    mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees actualTyped initial admitted execution
  obtain ⟨rfl, rfl, rfl⟩ := point
  cases Option.some.inj (found.symm.trans receipt.metadata.found)
  exact raw_trace owner receipt port callerBridge ownerFrame physical slots functions faults unique catalog selection runtime
    size sequence childLift preservation bodies typed environments heaps locals agrees actualTyped initial admitted
    (SelectedCompilationStageOperatorSourceTrace.source_inv receipt port unique runtime.requirements.idsUnique execution)

end Solcore.SourceSemantics.CoreLowering.SelectedCompilationStageMethodLifting
