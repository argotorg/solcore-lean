import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaInvocationBounds
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedLambdaCanonicalEntries
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCallerProtocol
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallCertificates
import Solcore.SourceSemantics.CoreLowering.CallableIndirectCallSourceBounds
import Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaTemplatePermission
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedCaptureExecutionValidity

/-! Actual indirect lambda prefixes keep the callee and argument reached pools.
An owned function leaf supplies physical ownership and complete static captures.
Source capture validity and an original stable selected-frame read are separate
receipts; projected Core typing supplies neither. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory SourceCoreCallableIndexedFrames CallableIndexedLambdaValues
open CallableIndexedOwnedFunctionState
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedExpressionHeads (argumentProtocol)

universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- Compatibility adds only the already authentic global-slot proof beside
one actual base entry and its same returned pool. -/
private theorem body_preserves_to_canonical
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
    {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size) :
    CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) owner callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size := by
  intro entry outcome after trace
  let baseEntry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) origin
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) :=
    { entry with initial := entry.initial.val }
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning baseEntry trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, result, heaps, maps, worlds,
    frame, metadata, exit, ⟨reached, entry.initial.property⟩, related⟩

/-- Native compatibility retains its independently obtained Source grade and
adds the same slot proof to the actual reached pool. -/
private theorem body_reflects_to_canonical
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (owner : CallableIndexedOwnedFunctionValues.OwnedKey keys) (callerPrefix : Nat)
    (origin : CallableRuntimeBodyOrigins.StaticOrigin (.initial compiled.compatible.checked)
      (CallableIndexedAmbient.ambientDefinitions compiled.indexed) registry faults)
    {size : Nat}
    (meaning : CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size) :
    CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) owner callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program origin size := by
  intro entry value finalStore completed
  let baseEntry : CallableRuntimeBodyOrigins.Stateful.Entry (protocol headers keys)
      (CallableIndexedOwnedAllocationProducer.StableOwner keys) origin
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) :=
    { entry with initial := entry.initial.val }
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
      frame, metadata, exit, reached, related⟩ := meaning baseEntry completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, heaps, maps, worlds,
    frame, metadata, exit, ⟨reached, entry.initial.property⟩, related⟩

/-- Stable histories concern the actual selected rows, rather than arbitrary
native type tags. Temporary reading frames do not satisfy this receipt. -/
def StableRows {index : ProtectedStateTransition.Index} (state : State headers keys index) : Prop :=
  ∀ selected : Fin keys.length, ∃ metadata, Carries compiled.indexed.ancestry.graph.inputs
    compiled.indexed.ancestry.graph.table (state.rows selected).authority.current
    (state.rows selected).authority.ghost metadata

private theorem current_stable {native : NativeFrame} {firstGhost secondGhost : GhostFrame}
    {metadata : Option MetadataState}
    (stable : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native firstGhost metadata)
    (current : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native secondGhost) :
    ∃ nextMetadata, Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native secondGhost nextMetadata := by
  cases stable with
  | empty => cases current with | stable history => exact ⟨_, history⟩
  | state stored history => cases current with | stable history => exact ⟨_, history⟩

/-- Real administrative preservation retains every original stable frame read.
The reached row's own Current receipt then authenticates its own ghost. -/
theorem StableRows.after_administrative {initial reached : ProtectedStateTransition.Index}
    (first : State headers keys initial) (second : State headers keys reached)
    (stable : StableRows first)
    (preserved : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    StableRows second := by
  intro selected
  obtain ⟨metadata, history⟩ := stable selected
  have read := (first.rows selected).authority.frame.read
  have physical := (first.rows selected).frame_eq
  have unmapped := (first.rows selected).authority.unmapped
  rw [physical] at read unmapped
  have retained := (preserved keys[selected.val].frameLocation unmapped (List.getElem?_eq_some_iff.mp read).1).2.trans read
  have actualRead := (second.rows selected).authority.frame.read
  rw [(second.rows selected).frame_eq] at actualRead
  have encoded := Option.some.inj (actualRead.symm.trans retained)
  have same : (second.rows selected).authority.current = (first.rows selected).authority.current := by
    have decoded := congrArg (decode compiled.indexed.ancestry.layout.frame) encoded
    simpa only [decode_encode, Option.some.injEq] using decoded
  have current := (second.rows selected).authority.frame.history
  rw [same] at current
  obtain ⟨nextMetadata, authenticated⟩ := current_stable history current
  exact ⟨nextMetadata, same.symm ▸ authenticated⟩

/-- This receipt is recovered from the actual owned callee leaf. It retains
its full source function, original dictionary, captures and ranked body. -/
structure ClosureAt (mapping : LocationMap) (world : StoreTyping) (function : Dynamic.Closure)
    (sourceType : TypeSystem.Ty) (carrier : Value) (type : Ty) where
  owner : CallableIndexedOwnedFunctionValues.OwnedKey keys
  scope : SourceCoreLocalCell.Scope
  capturedActual : Environment
  callerPrefix : Nat
  captured : Captures compiled.indexed mapping world scope function.captured capturedActual
  code : Code compiled.indexed function scope captured.administrative
  history : History code
  support : CallableIndexedOwnedFunctionValues.StaticSupport headers registry faults code
  origin : CallableIndexedOwnedFunctionValues.ActualSourceOrigin code history support
  globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
    (values := .initial compiled.compatible.checked) (program := program)
    headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation
  referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length
  sourceView : SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType (FunctionValues.sourceType function)
  value_eq : carrier = value code captured.embedding history.native capturedActual
  type_eq : type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore
  typed : RuntimeValueHasType world carrier type compiled.indexed.layouts.definitions

/-- No pool or native typing is inspected to choose this immutable owner. -/
theorem ClosureAt.of_represents {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (related : CallableIndexedOwnedFunctionValues.Represents headers keys registry faults mapping world sourceType
      (.closure function) carrier type) : Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        mapping world function sourceType carrier type) := by
  obtain ⟨owner, scope, actual, callerPrefix, captured, code, history, support, origin,
    globals, referenceIndex, source_eq, value_eq, type_eq⟩ := CallableIndexedOwnedFunctionValues.Represents.closure_inv related
  exact ⟨⟨owner, scope, actual, callerPrefix, captured, code, history, support, origin, globals,
    referenceIndex, congrArg SourceCoreRawMetadata.runtimeType source_eq, value_eq, type_eq,
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile).runtime_hasType (registry := registry) related⟩⟩

private theorem closure_functions {checked : SourceCoreCompatibleCatalog.Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value}
    {carrier : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source carrier type) :
    ∀ {function : Dynamic.Closure}, source = .closure function →
      ∃ actualType, functions.Represents registry mapping world actualType (.closure function) carrier type ∧
        SourceCoreRawMetadata.runtimeType sourceType = SourceCoreRawMetadata.runtimeType actualType := by
  induction related using ValueRep.rec
    (motive_2 := fun _ _ _ _ _ => True) (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | proxy | constructed | mappingValue => intro _ impossible; cases impossible
  | function related => intro _ same; subst same; exact ⟨_, related, rfl⟩
  | compatible same related ih =>
    intro function source
    obtain ⟨actualType, relation, view⟩ := ih source
    exact ⟨actualType, relation, same.trans view⟩
  | nil | cons | empty | entry | absent | present => trivial

/-- Raw metadata compatibility is retained separately from the original
function's full binder types and evidence. -/
theorem ClosureAt.of_value_rep {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
    {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    (related : ValueRep compiled.compatible.checked registry
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world sourceType
      (.closure function) carrier type) : Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
        mapping world function sourceType carrier type) := by
  obtain ⟨actualType, actual, view⟩ := closure_functions related rfl
  obtain ⟨receipt⟩ := ClosureAt.of_represents profile actual
  exact ⟨{ receipt with sourceView := view.trans receipt.sourceView }⟩

section Closure
variable {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (receipt : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)


/-- Every source field and the full stored native captures remain identical
through real argument effects. Only their reached map/world receipts weaken. -/
def ClosureAt.extend {futureMap : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends mapping futureMap) (worlds : WorldExtends world futureWorld) :
    ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
      futureMap futureWorld function sourceType carrier type :=
  { receipt with captured := receipt.captured.extend maps worlds, typed := receipt.typed.weaken worlds }

/-- The same-Code ranked support supplies the existing exact body context. -/
def ClosureAt.inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) receipt.code :=
  receipt.support.2.2.receipt.body.toContext

/-- The body factory retains its authentic profile, source and dictionary. -/
def ClosureAt.bodyOrigin (escaped : faults .controlEscapedFunction receipt.code.compilation.internalReason) :
    CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin (program := program) receipt.code receipt.inputs registry faults :=
  CallableIndexedOwnedLambdaInvocationBounds.BodyOrigin.nested receipt.code receipt.inputs receipt.support.2.2.receipt escaped

/-- The physical frame reference is the original actual capture slot. -/
theorem ClosureAt.reference : receipt.captured.canonical[receipt.code.referenceIndex]? =
    some (.cellRef compiled.indexed.ancestry.layout.frame.type receipt.owner.key.frameLocation) := by
  rw [receipt.referenceIndex]
  exact receipt.globals.reference

end Closure

section Callee
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {callerScope : SourceCoreLocalCell.Scope}
  {callee : ExpressionId} {calleeCode : SourceCoreBasic.LoweredExpr} {calleeNode : ExpressionNode}
  (certified : certificate callerScope callee calleeCode) (found : source.lookupExpression? callee = some calleeNode)
  {mapping : LocationMap} {world : StoreTyping} {administrative actualContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {before calleeHeap : Dynamic.Heap}
  {store : Store} {ξ : Renaming} {function : Dynamic.Closure}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (stable : StableRows initial)

include certified found environments heaps locals agrees typed in
/-- The callee child evaluates from the actual input pool. Its owned relation
then chooses one immutable key and complete original closure receipt. -/
theorem callee_preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier calleeCode.type) := by
  obtain ⟨native, calleeStore, calleeMap, calleeWorld, evaluated, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    children size smaller certified found environments heaps locals agrees typed callerInitial (.value executed)
  cases result with
  | value payload =>
    exact ⟨_, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
      reached, related, StableRows.after_administrative (callerBridge.pool callerInitial) (callerBridge.pool reached) callerStable frame, ClosureAt.of_value_rep profile payload⟩

include certified found environments heaps locals agrees typed stable in
theorem callee_preserves_bounded (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : State headers keys ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        Relates initial reached ∧ StableRows reached ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier calleeCode.type) := by
  exact callee_preserves_bounded_with_caller profile certified found environments heaps locals agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget children executed smaller


include certified found environments heaps locals agrees typed in
/-- Original Source admission closes capture validity at the actual callee
heap. It uses existing Source preservation and the same observed closure. -/
theorem callee_preserves_bounded_with_source_admission_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
    {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) := by
  obtain ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
      reached, related, reachedStable, closure⟩ :=
    callee_preserves_bounded_with_caller profile certified found environments heaps locals agrees typed callerBridge callerInitial callerStable budget children executed smaller
  have captures := CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped executed.sound
  exact ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reachedStable, closure, captures.1⟩


include certified found environments heaps locals agrees typed stable in
theorem callee_preserves_bounded_with_source_admission (budget : Nat)
    (children : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context before)
    {parameter result : TypeSystem.Ty} (sourceTyped : ExpressionHasType source context callee (.function parameter result))
    {size : Nat}
    (executed : SourceExecutionSize.ExpressionEvaluates program size context evidence source environment before callee
      (.closure function) calleeHeap) (smaller : size < budget) :
    ∃ carrier calleeStore calleeMap calleeWorld,
      Evaluates actual store (calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : State headers keys ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        Relates initial reached ∧ StableRows reached ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) := by
  exact callee_preserves_bounded_with_source_admission_with_caller profile certified found environments heaps locals agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

end Callee



section NativeCompletion
variable {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (receipt : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)

/-- These are the original measured children of the accepted selected call.
Argument failure retains its actual post; successful application retains the
complete stored capture suffix and the original strict body grade. -/
inductive SelectedCompletion (budget : Nat) (arguments : Expr) (actual : Environment) (store : Store) : Value → Store → Prop where
  | argumentFailure {size : Nat} {input : Ty} {token : Value} {after : Store}
      (trace : EvaluationSize size (.unit :: carrier :: actual) store
        ((arguments.weakenAt 0).weakenAt 0) (.inLeft input token) after)
      (smaller : size < budget) :
      SelectedCompletion budget arguments actual store (.inLeft receipt.code.receipt.resultCore token) after
  | applied {argumentsSize bodySize : Nat} {input : Ty} {argument value : Value} {middle after : Store}
      (argumentsTrace : EvaluationSize argumentsSize (.unit :: carrier :: actual) store
        ((arguments.weakenAt 0).weakenAt 0) (.inRight input argument) middle)
      (bodyTrace : EvaluationSize bodySize
        (argument :: encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
        middle (receipt.code.body.rename receipt.captured.embedding.lift.lift) value after)
      (argumentsSmaller : argumentsSize < budget) (bodySmaller : bodySize < budget) :
      SelectedCompletion budget arguments actual store value after

/-- Original callee completion and pure guard/projection reads identify the
same selected lambda. This proof only inverts the existing measured derivation. -/
theorem selected_completed {budget size : Nat} {actual : Environment} {firstStore store finalStore : Store}
    {callee arguments : Expr} {gates : List CallableContract.Gate} {unknown : Word} {value : Value}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    (completed : EvaluationSize size actual firstStore
      (CallableContract.call gates unknown receipt.code.receipt.resultCore callee arguments) value finalStore)
    (within : size ≤ budget) : SelectedCompletion receipt budget arguments actual store value finalStore := by
  have descriptor : Evaluates (carrier :: actual) store (.second (.var 0)) (.word receipt.code.descriptor.id) store := by
    simp only [receipt.value_eq, CallableIndexedLambdaValues.value]
    exact .second (.var rfl)
  cases CallableIndirectCallBounds.call_completed completed within with
  | calleeFailure calleeTrace smaller =>
    obtain ⟨same, _⟩ := evaluation_deterministic calleeTrace.sound calleeEvaluation
    cases same
  | stageRejected calleeTrace gate calleeSmaller gateSmaller =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic calleeTrace.sound calleeEvaluation
    cases same
    obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stageAccepted, CallableContract.resultValue] at same
    cases same
  | argumentFailure calleeTrace gate argumentsTrace calleeSmaller gateSmaller argumentsSmaller =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic calleeTrace.sound calleeEvaluation
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stageAccepted, CallableContract.resultValue] at same
    cases same
    exact .argumentFailure argumentsTrace argumentsSmaller
  | arityRejected calleeTrace gate argumentsTrace arity calleeSmaller gateSmaller argumentsSmaller aritySmaller =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic calleeTrace.sound calleeEvaluation
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stageAccepted, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, _⟩ := CallableIndirectCallBounds.dispatch_decision
      (by simp only [receipt.value_eq, CallableIndexedLambdaValues.value]; exact .second (.var rfl)) arity
    simp only [arityAccepted, CallableContract.resultValue] at same
    cases same
  | applied calleeTrace gate argumentsTrace arity functionTrace parameterTrace bodyTrace
      calleeSmaller gateSmaller argumentsSmaller aritySmaller functionSmaller parameterSmaller bodySmaller =>
    obtain ⟨same, rfl⟩ := evaluation_deterministic calleeTrace.sound calleeEvaluation
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision descriptor gate
    simp only [stageAccepted, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, rfl⟩ := CallableIndirectCallBounds.dispatch_decision
      (by simp only [receipt.value_eq, CallableIndexedLambdaValues.value]; exact .second (.var rfl)) arity
    simp only [arityAccepted, CallableContract.resultValue] at same
    cases same
    obtain ⟨same, rfl⟩ := evaluation_deterministic
      (right := .closure receipt.code.receipt.parameterCore (LanguageResult.resultType receipt.code.receipt.resultCore)
        (receipt.code.body.rename receipt.captured.embedding.lift.lift)
        (encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual))
      functionTrace.sound (by simp only [receipt.value_eq, CallableIndexedLambdaValues.value]; exact .second (.first (.var rfl)))
    cases same
    obtain ⟨same, rfl⟩ := evaluation_deterministic parameterTrace.sound (.var rfl)
    cases same
    exact .applied argumentsTrace bodyTrace argumentsSmaller bodySmaller
end NativeCompletion

private theorem values_arguments {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {mapping : LocationMap} {world : StoreTyping} (bindings : List CallableIndexedParameterCertificates.Binding)
    {sources : List Dynamic.Value} {payloads : List Value}
    (represented : DataExpressionSequence.Values model mapping world
      (bindings.map (fun binding => binding.1.scheme.body)) (bindings.map Prod.snd) sources payloads) :
    CallableIndexedParameterMeaning.Arguments model mapping world bindings sources payloads := by
  induction bindings generalizing sources payloads with
  | nil => cases represented; exact .nil
  | cons binding rest ih => cases represented with
    | cons head tail => exact .cons head (ih tail)


/-- The original accepted indirect suffix either fails while evaluating its
arguments or calls the exact observed closure with its original dictionary.
The two Source grades are recorded independently of native completion. -/
inductive SourceSuffix (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap)
    (ids : List ExpressionId) (function : Dynamic.Closure) : Nat → Nat → Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | argumentFault {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
      (failed : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after) :
      SourceSuffix program context evidence source environment before ids function size 0 (.fault reason) after
  | called {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
      {outcome : Dynamic.ExpressionOutcome}
      (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
      (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
        (.closure function) arguments outcome after) :
      SourceSuffix program context evidence source environment before ids function argumentsSize callSize outcome after

section Selected
variable (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {source : TypedSource} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {callerScope : SourceCoreLocalCell.Scope}
  {ids : List ExpressionId} {codes : List SourceCoreBasic.LoweredExpr}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (receipt : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (children : DataExpressionSequence.Tree source certificate callerScope ids
    (receipt.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) codes)
  (nativeTypes : codes.map (·.type) = receipt.code.receipt.loweredParameters.map Prod.snd)
  (escaped : faults .controlEscapedFunction receipt.code.compilation.internalReason)
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (capturesValid : FunctionValues.SourceCapturesValid before (.closure function))
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨callerScope, mapping, world, before, store, canonical⟩)
  (stable : StableRows initial)

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- The selected lambda's arguments run in their actual two-guard environment.
Their reached pool supplies the caller for the real parameter/body invocation.
The input Source closure retains its full dictionary and capture validity. -/
theorem arguments_preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore value finalStore finalMap finalWorld,
      Evaluates (.unit :: carrier :: actual) store
        (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads ::
          encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
        middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol callerInitial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt
      callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults := fun child smaller =>
        ProtectedStateTransition.SequenceBridge.preserves_at _ (argumentMeaning child smaller)
  obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEval, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    ProtectedDataExpressionSequence.Stateful.preserves_values_bounded callerProtocol budget children meanings
      environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
      (.cons .unit (.cons receipt.typed typed)) callerInitial evaluated argumentsWithin
  rw [nativeTypes] at represented
  have parameterArguments := values_arguments receipt.code.receipt.loweredParameters represented
  let future := receipt.extend argumentMaps argumentWorlds
  have futureStable := StableRows.after_administrative (callerBridge.pool callerInitial) (callerBridge.pool argumentState) callerStable argumentFrame
  obtain ⟨currentMetadata, currentCarried⟩ := futureStable receipt.owner.position
  let actualMeaning := CallableIndexedOwnedLambdaCanonicalEntries.source_continuation_of_canonical (arguments := arguments) (nativeArguments := payloads)
    future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget
    (fun entry added length spine reached child strict => bodyMeaning child strict
      (CallableIndexedOwnedLambdaCanonicalEntries.source_entry (arguments := arguments) (nativeArguments := payloads)
        future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped)
        entry added length spine reached))
  obtain ⟨value, finalStore, finalMap, finalWorld, bodyEval, result, finalHeaps,
      maps, worlds, frame, metadata, finalState, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at
      future.captured future.code future.history future.inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) parameterArguments
      future.owner (callerBridge.pool argumentState) middleHeaps (capturesValid.extend argumentMetadata) future.reference currentCarried
      (CallableIndexedLambdaTemplatePermission.lambda_allowed future.code future.history)
      (future.bodyOrigin escaped) budget actualMeaning called callWithin
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentsEval
  exact ⟨payloads, middleStore, value, finalStore, finalMap, finalWorld, argumentsEval, bodyEval, result, finalHeaps,
    argumentMaps.trans maps, argumentWorlds.trans worlds, argumentFrame.trans frame, argumentMetadata.trans metadata,
    callerBridge.of_pool callerInitial finalState,
    callerBridge.return_related callerInitial finalState ((callerBridge.related argumentRelated).trans related)⟩


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem arguments_preserves_bounded_canonical (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore value finalStore finalMap finalWorld,
      Evaluates (.unit :: carrier :: actual) store
        (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads ::
          encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
        middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact arguments_preserves_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning bodyMeaning evaluated argumentsWithin called callWithin


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem arguments_preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ payloads middleStore value finalStore finalMap finalWorld,
      Evaluates (.unit :: carrier :: actual) store
        (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) middleStore ∧
      Evaluates (DataPatternValues.packValues payloads ::
          encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
        middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact arguments_preserves_bounded_canonical profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed initial stable
    budget argumentMeaning (fun child strict => body_preserves_to_canonical profile receipt.owner receipt.callerPrefix
      (receipt.bodyOrigin escaped).origin (bodyMeaning child strict)) evaluated argumentsWithin called callWithin


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- Successful original argument and body children are reflected independently.
The ordered sequence's actual post is the real invocation input; the resulting
Source argument and call grades remain independent of the native children. -/
theorem arguments_reflects_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument value : Value} {middleStore finalStore : Store}
    (evaluated : EvaluationSize argumentsSize (.unit :: carrier :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore) (argumentsWithin : argumentsSize < budget)
    (completed : EvaluationSize bodySize
      (argument :: encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
      middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate program sourceArgumentsSize context evidence source environment before ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome program sourceCallSize context evidence function.evidence middle
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol callerInitial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt
      callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults := fun child smaller =>
        ProtectedStateTransition.SequenceBridge.reflects_at _ (argumentMeaning child smaller)
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at evaluated
  obtain ⟨sourceArgumentsSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    ProtectedDataExpressionSequence.Stateful.reflects_bounded callerProtocol budget children meanings
      environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
      (.cons .unit (.cons receipt.typed typed)) callerInitial evaluated argumentsWithin
  cases represented with
  | @values sources payloads represented =>
    cases argumentTrace with
    | values argumentsTrace =>
      rw [nativeTypes] at represented
      have parameterArguments := values_arguments receipt.code.receipt.loweredParameters represented
      let future := receipt.extend argumentMaps argumentWorlds
      have futureStable := StableRows.after_administrative (callerBridge.pool callerInitial) (callerBridge.pool argumentState) callerStable argumentFrame
      obtain ⟨currentMetadata, currentCarried⟩ := futureStable receipt.owner.position
      let actualMeaning := CallableIndexedOwnedLambdaCanonicalEntries.native_continuation_of_canonical (arguments := sources)
        future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget
        (fun entry reached child strict => bodyMeaning child strict
          (CallableIndexedOwnedLambdaCanonicalEntries.native_entry (arguments := sources)
            future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
            (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped)
            entry reached))
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, callTrace, result, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at
          future.captured future.code future.history future.inputs
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) parameterArguments
          future.owner (callerBridge.pool argumentState) middleHeaps (capturesValid.extend argumentMetadata) future.reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed future.code future.history)
          (future.bodyOrigin escaped) budget actualMeaning completed bodyWithin
      exact ⟨sourceArgumentsSize, sourceCallSize, _, middle, outcome, after, finalMap, finalWorld,
        argumentsTrace, callTrace, result, finalHeaps,
        argumentMaps.trans maps, argumentWorlds.trans worlds, argumentFrame.trans frame, argumentMetadata.trans metadata,
        callerBridge.of_pool callerInitial finalState,
        callerBridge.return_related callerInitial finalState ((callerBridge.related argumentRelated).trans related)⟩


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem arguments_reflects_bounded_canonical (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument value : Value} {middleStore finalStore : Store}
    (evaluated : EvaluationSize argumentsSize (.unit :: carrier :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore) (argumentsWithin : argumentsSize < budget)
    (completed : EvaluationSize bodySize
      (argument :: encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
      middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate program sourceArgumentsSize context evidence source environment before ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome program sourceCallSize context evidence function.evidence middle
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact arguments_reflects_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning bodyMeaning evaluated argumentsWithin completed bodyWithin


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem arguments_reflects_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {argumentsSize bodySize : Nat} {argumentInput : Ty} {argument value : Value} {middleStore finalStore : Store}
    (evaluated : EvaluationSize argumentsSize (.unit :: carrier :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
      (.inRight argumentInput argument) middleStore) (argumentsWithin : argumentsSize < budget)
    (completed : EvaluationSize bodySize
      (argument :: encode compiled.indexed.ancestry.layout.frame receipt.history.native :: receipt.capturedActual)
      middleStore (receipt.code.body.rename receipt.captured.embedding.lift.lift) value finalStore)
    (bodyWithin : bodySize ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize arguments middle outcome after finalMap finalWorld,
      SourceExecutionSize.ExpressionsEvaluate program sourceArgumentsSize context evidence source environment before ids arguments middle ∧
      RecursiveNamedCallBounds.CallOutcome program sourceCallSize context evidence function.evidence middle
        (.closure function) arguments outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition (protocol headers keys) initial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact arguments_reflects_bounded_canonical profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed initial stable
    budget argumentMeaning (fun child strict => body_reflects_to_canonical profile receipt.owner receipt.callerPrefix
      (receipt.bodyOrigin escaped).origin (bodyMeaning child strict)) evaluated argumentsWithin completed bodyWithin


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- The accepted two-guard call composes the real callee post with ordered
arguments and the restored body post. Its input records are never rebuilt. -/
theorem call_preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual firstStore (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨payloads, middleStore, value, finalStore, finalMap, finalWorld, argumentEvaluation, bodyEvaluation,
      result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
    arguments_preserves_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid
      agrees typed callerBridge callerInitial callerStable budget argumentMeaning bodyMeaning evaluated argumentsWithin called callWithin
  rw [receipt.value_eq] at calleeEvaluation argumentEvaluation
  exact ⟨value, finalStore, finalMap, finalWorld,
    CallableContract.call_success gates unknown calleeEvaluation stageAccepted argumentEvaluation arityAccepted bodyEvaluation,
    result, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
    calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem call_preserves_bounded_canonical (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual firstStore (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact call_preserves_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted evaluated argumentsWithin called callWithin


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem call_preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle after : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids arguments middle)
    (argumentsWithin : argumentsSize ≤ budget)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence function.evidence middle
      (.closure function) arguments outcome after) (callWithin : callSize ≤ budget) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual firstStore (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact call_preserves_bounded_canonical profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed initial stable
    budget argumentMeaning (fun child strict => body_preserves_to_canonical profile receipt.owner receipt.callerPrefix
      (receipt.bodyOrigin escaped).origin (bodyMeaning child strict)) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted evaluated argumentsWithin called callWithin


include receipt children environments heaps locals agrees typed in
/-- An argument fault keeps the exact reached argument pool in the enclosing
accepted call. No parameter or body state is constructed on this path. -/
theorem call_argument_fault_preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after)
    (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual firstStore (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft receipt.code.receipt.resultCore (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt
      callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults := fun child smaller =>
        ProtectedStateTransition.SequenceBridge.preserves_at _ (argumentMeaning child smaller)
  obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEval, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    ProtectedDataExpressionSequence.Stateful.preserves_fault_bounded callerProtocol budget children meanings
      environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
      (.cons .unit (.cons receipt.typed typed)) callerInitial failed within
  rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at argumentsEval
  rw [receipt.value_eq] at calleeEvaluation argumentsEval
  exact ⟨token, finalStore, finalMap, finalWorld,
    CallableContract.call_argument_failure gates unknown calleeEvaluation stageAccepted argumentsEval,
    matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
    calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩

include receipt children environments heaps locals agrees typed in
theorem call_argument_fault_preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap}
    (failed : SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after)
    (within : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual firstStore (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) (.inLeft receipt.code.receipt.resultCore (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact call_argument_fault_preserves_bounded_with_caller (callerProtocol := protocol headers keys) (callerInitial := initial)
    profile receipt children environments heaps locals agrees typed budget argumentMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted failed within


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- Native accepted-call completion uses its original measured children. The
actual callee post feeds the argument post, then the same real body post and
restoration. Source argument fault and call grades remain independent. -/
theorem call_reflects_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore
      (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize outcome after finalMap finalWorld,
      SourceSuffix program context evidence source environment before ids function sourceArgumentsSize sourceCallSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  cases selected_completed receipt calleeEvaluation stageAccepted arityAccepted completed within with
  | argumentFailure argumentsTrace smaller =>
    have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt
        callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        program context evidence source certificate faults := fun child smaller =>
          ProtectedStateTransition.SequenceBridge.reflects_at _ (argumentMeaning child smaller)
    rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at argumentsTrace
    obtain ⟨sourceArgumentsSize, argumentOutcome, after, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      ProtectedDataExpressionSequence.Stateful.reflects_bounded callerProtocol budget children meanings
        environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) callerInitial argumentsTrace smaller
    cases represented with
    | fault matched =>
      cases argumentTrace with
      | fault failed =>
        exact ⟨sourceArgumentsSize, 0, _, after, finalMap, finalWorld, .argumentFault failed,
          .fault matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
          calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩
  | applied argumentsTrace bodyTrace argumentsSmaller bodySmaller =>
    obtain ⟨sourceArgumentsSize, sourceCallSize, arguments, middle, outcome, after, finalMap, finalWorld,
        sourceArguments, sourceCall, result, finalHeaps, maps, worlds, frame, metadata, reached, related⟩ :=
      arguments_reflects_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed callerBridge callerInitial callerStable
        budget argumentMeaning bodyMeaning argumentsTrace argumentsSmaller bodyTrace (Nat.le_of_lt bodySmaller)
    exact ⟨sourceArgumentsSize, sourceCallSize, outcome, after, finalMap, finalWorld, .called sourceArguments sourceCall,
      result, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
      calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem call_reflects_bounded_canonical (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore
      (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize outcome after finalMap finalWorld,
      SourceSuffix program context evidence source environment before ids function sourceArgumentsSize sourceCallSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact call_reflects_bounded_with_caller profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted completed within


include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed stable in
theorem call_reflects_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap before)
    {callee : Expr} {gates : List CallableContract.Gate} {unknown : Word}
    (calleeEvaluation : Evaluates actual firstStore callee (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision gates .beforeArguments unknown receipt.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision gates .beforeApplication unknown receipt.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore
      (CallableContract.call gates unknown receipt.code.receipt.resultCore callee
        ((SourceCoreCalls.packArguments codes).expression.rename ξ)) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceArgumentsSize sourceCallSize outcome after finalMap finalWorld,
      SourceSuffix program context evidence source environment before ids function sourceArgumentsSize sourceCallSize outcome after ∧
      FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld function.resultType receipt.code.receipt.resultCore faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact call_reflects_bounded_canonical profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed initial stable
    budget argumentMeaning (fun child strict => body_reflects_to_canonical profile receipt.owner receipt.callerPrefix
      (receipt.bodyOrigin escaped).origin (bodyMeaning child strict)) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted completed within

end Selected

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
