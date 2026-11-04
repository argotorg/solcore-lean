import Solcore.SourceSemantics.CoreLowering.Internal.Owned.CanonicalCallerState
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.InvocationBounds
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.RuntimeIndirectCalls
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation
import Solcore.SourceSemantics.WellFormed
import Solcore.SourceSemantics.Dynamic.Preservation

/-!
# Owned callables: indirect expression heads

The indirect caller protocol and expression heads, with `StableRows`, Source and snapshot admission.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
/-! Indirect callers return their same actual pool using the real preservation
receipts. Original callers and callers with stronger static slots use the same
return interface; no stronger admission is recovered from a bare pool. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {caller : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}

/-- Indirect selection does not consume named slots. This projection retains
the original caller's actual pool and its complete return operation. -/
def forget_slots {slots : ProtectedStateTransition.Index → Prop}
    (carrier : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) slots caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => True.intro
  restore := carrier.restore

/-- Compatibility wraps exactly the original returned pool. Original callers
need no extra static admission, so the added preservation receipts are unused. -/
def of_legacy (carrier : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) caller) :
    CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) caller where
  pool := carrier.pool
  records_eq := carrier.records_eq
  related := carrier.related
  slots := fun _ => True.intro
  restore := fun {_index} initial {_mapping _world _heap _store} reached _maps _worlds _frame _metadata related =>
    ⟨carrier.of_pool initial reached, carrier.pool_of_pool initial reached,
      carrier.return_related initial reached related⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectCallerProtocol
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectExpressionHeads
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
theorem callee_preserves_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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

include certified found environments heaps locals agrees typed in
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
  exact callee_preserves_bounded_with_receipts profile certified found environments heaps locals agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget children executed smaller

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
theorem callee_preserves_bounded_with_source_admission_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
    callee_preserves_bounded_with_receipts profile certified found environments heaps locals agrees typed callerBridge callerInitial callerStable budget children executed smaller
  have captures := CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped executed.sound
  exact ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reachedStable, closure, captures.1⟩


include certified found environments heaps locals agrees typed in
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
  exact callee_preserves_bounded_with_source_admission_with_receipts profile certified found environments heaps locals agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

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

/-- The real ordered argument post and its actual effects select an entry-specific
source body continuation. No arbitrary origin entry is admitted. -/
def SourceContinuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping}
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    {arguments : List Dynamic.Value} {payloads : List Value} {middle : Dynamic.Heap} {middleStore : Store}
    (argumentState : callerProtocol.State ⟨callerScope, middleMap, middleWorld, middle, middleStore, canonical⟩),
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      middleMap middleWorld receipt.code.receipt.loweredParameters arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      middleMap middleWorld middle middleStore →
    FunctionValues.SourceCapturesValid middle (.closure function) →
    AdministrativePreserved mapping store middleMap middleStore →
    Dynamic.HeapMetadataExtend before middle → callerProtocol.Relates callerInitial argumentState →
    ∀ {sourceArgumentsSize : Nat},
    SourceExecutionSize.ExpressionsEvaluate program sourceArgumentsSize context evidence source environment before ids arguments middle →
    let future := receipt.extend maps worlds
    CallableIndexedOwnedLambdaInvocationBounds.SourceContinuation
      (arguments := arguments) (nativeArguments := payloads)
      future.captured future.code future.history future.inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      future.owner (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget

include receipt escaped in
/-- Compatibility specializes the original uniform canonical family only at
this exact real parameter continuation. -/
theorem source_continuations_of_canonical
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin)) :
    SourceContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget := by
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    _represented _heaps _locals _frame _metadata _related sourceArgumentsSize _trace
  let future := receipt.extend maps worlds
  exact CallableIndexedOwnedLambdaCanonicalEntries.source_continuation_of_canonical
    (arguments := arguments) (nativeArguments := payloads)
    future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget
    (fun entry added length copied spine kept reached child strict => meaning child strict
      (CallableIndexedOwnedLambdaCanonicalEntries.source_entry
        (arguments := arguments) (nativeArguments := payloads)
        future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped)
        entry added length copied spine kept reached))

/-- The real ordered argument post and its actual effects select an entry-specific
native body continuation. No arbitrary origin entry is admitted. -/
def NativeContinuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {middleMap : LocationMap} {middleWorld : StoreTyping}
    (maps : LocationMap.Extends mapping middleMap) (worlds : WorldExtends world middleWorld)
    {arguments : List Dynamic.Value} {payloads : List Value} {middle : Dynamic.Heap} {middleStore : Store}
    (argumentState : callerProtocol.State ⟨callerScope, middleMap, middleWorld, middle, middleStore, canonical⟩),
    CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      middleMap middleWorld receipt.code.receipt.loweredParameters arguments payloads →
    CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      middleMap middleWorld middle middleStore →
    FunctionValues.SourceCapturesValid middle (.closure function) →
    AdministrativePreserved mapping store middleMap middleStore →
    Dynamic.HeapMetadataExtend before middle → callerProtocol.Relates callerInitial argumentState →
    ∀ {sourceArgumentsSize : Nat},
    SourceExecutionSize.ExpressionsEvaluate program sourceArgumentsSize context evidence source environment before ids arguments middle →
    let future := receipt.extend maps worlds
    CallableIndexedOwnedLambdaInvocationBounds.NativeContinuation
      (arguments := arguments)
      future.captured future.code future.history future.inputs (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile)
      future.owner (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget

include receipt escaped in
/-- Compatibility specializes the original uniform canonical family only at
this exact real parameter continuation. -/
theorem native_continuations_of_canonical
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat)
    (meaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) receipt.owner receipt.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (receipt.bodyOrigin escaped).origin)) :
    NativeContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget := by
  intro middleMap middleWorld maps worlds arguments payloads middle middleStore argumentState
    _represented _heaps _locals _frame _metadata _related sourceArgumentsSize _trace
  let future := receipt.extend maps worlds
  exact CallableIndexedOwnedLambdaCanonicalEntries.native_continuation_of_canonical
    (arguments := arguments)
    future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped) budget
    (fun entry reached child strict => meaning child strict
      (CallableIndexedOwnedLambdaCanonicalEntries.native_entry
        (arguments := arguments)
        future.captured future.code future.owner future.callerPrefix future.globals future.history future.inputs
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) (callerBridge.pool argumentState) (future.bodyOrigin escaped)
        entry reached))

/-- A whole ordered argument producer at this exact real caller state. Both
Source outcomes retain the guarded environment, original grades and actual post.
Extra admission receipts can be consumed by the provider without entering this
neutral low contract. -/
def SequencePreserves
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat) : Prop :=
  (∀ {size : Nat} {arguments : List Dynamic.Value} {after : Dynamic.Heap},
    SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment before ids arguments after →
    size ≤ budget →
    ∃ payloads finalStore finalMap finalWorld,
      Evaluates (.unit :: carrier :: actual) store
        (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
        (.inRight .word (DataPatternValues.packValues payloads)) finalStore ∧
      DataExpressionSequence.Values
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld (receipt.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body))
        (codes.map (·.type)) arguments payloads ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol callerInitial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩) ∧
  (∀ {size : Nat} {reason : Dynamic.SemanticFault} {after : Dynamic.Heap},
    SourceExecutionSize.ExpressionsFault program size context evidence source environment before ids reason after →
    size ≤ budget →
    ∃ token finalStore finalMap finalWorld,
      Evaluates (.unit :: carrier :: actual) store
        (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol callerInitial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩)

/-- Native ordered arguments return the original independently graded Source
trace and exact reached state for either success or fault. -/
def SequenceReflects
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {size : Nat} {value : Value} {finalStore : Store},
    EvaluationSize size (.unit :: carrier :: actual) store
      (((SourceCoreCalls.packArguments codes).expression.rename ξ).weakenAt 0 |>.weakenAt 0) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      ProtectedDataExpressionSequence.TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      DataExpressionSequence.Result
        (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld (receipt.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) codes faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition callerProtocol callerInitial
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩

include receipt children environments heaps locals agrees typed in
/-- The original uniform child family instantiates the same existing Source
sequence folds at this exact guarded input. -/
theorem SequencePreserves.of_uniform
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults)) :
    SequencePreserves (source := source) (context := context) (evidence := evidence) (profile := profile) (receipt := receipt) (codes := codes)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget := by
  have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt
      callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults := fun child smaller =>
        ProtectedStateTransition.SequenceBridge.preserves_at _ (argumentMeaning child smaller)
  constructor
  · intro size arguments after evaluated within
    obtain ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      ProtectedDataExpressionSequence.Stateful.preserves_values_bounded callerProtocol budget children meanings
        environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) callerInitial evaluated within
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨payloads, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
  · intro size reason after failed within
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      ProtectedDataExpressionSequence.Stateful.preserves_fault_bounded callerProtocol budget children meanings
        environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
        (.cons .unit (.cons receipt.typed typed)) callerInitial failed within
    rw [GenericExpressionMeaning.rename_prefix, GenericExpressionMeaning.rename_prefix] at evaluated
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩

include receipt children environments heaps locals agrees typed in
/-- The original native sequence fold supplies this pointwise provider, with
its independently measured Source outcome and actual reached witness. -/
theorem SequenceReflects.of_uniform
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults)) :
    SequenceReflects (source := source) (context := context) (evidence := evidence) (profile := profile) (receipt := receipt) (codes := codes)
      (environment := environment) (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget := by
  have meanings : ∀ child, child < budget → ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt
      callerProtocol child (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults := fun child smaller =>
        ProtectedStateTransition.SequenceBridge.reflects_at _ (argumentMeaning child smaller)
  intro size value finalStore evaluated within
  rw [← GenericExpressionMeaning.rename_prefix, ← GenericExpressionMeaning.rename_prefix] at evaluated
  exact ProtectedDataExpressionSequence.Stateful.reflects_bounded callerProtocol budget children meanings
    environments heaps locals (GenericExpressionMeaning.agree_prefix (GenericExpressionMeaning.agree_prefix agrees carrier) .unit)
    (.cons .unit (.cons receipt.typed typed)) callerInitial evaluated within

include receipt nativeTypes escaped capturesValid in
/-- The selected lambda's arguments run in their actual two-guard environment.
Their reached pool supplies the caller for the real parameter/body invocation.
The input Source closure retains its full dictionary and capture validity. -/
theorem arguments_preserves_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  obtain ⟨payloads, middleStore, middleMap, middleWorld, argumentsEval, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    argumentSequence.1 evaluated argumentsWithin
  rw [nativeTypes] at represented
  have parameterArguments := values_arguments receipt.code.receipt.loweredParameters represented
  let future := receipt.extend argumentMaps argumentWorlds
  have futureStable := StableRows.after_administrative (callerBridge.pool callerInitial) (callerBridge.pool argumentState) callerStable argumentFrame
  obtain ⟨currentMetadata, currentCarried⟩ := futureStable receipt.owner.position
  let actualMeaning := bodyContinuations argumentMaps argumentWorlds argumentState parameterArguments
    middleHeaps (capturesValid.extend argumentMetadata) argumentFrame argumentMetadata argumentRelated
    evaluated
  obtain ⟨value, finalStore, finalMap, finalWorld, bodyEval, result, finalHeaps,
      maps, worlds, frame, metadata, finalState, related⟩ :=
    CallableIndexedOwnedLambdaInvocationBounds.invocation_preserves_bounded_at
      future.captured future.code future.history future.inputs
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) parameterArguments
      future.owner (callerBridge.pool argumentState) middleHeaps (capturesValid.extend argumentMetadata) future.reference currentCarried
      (CallableIndexedLambdaTemplatePermission.lambda_allowed future.code future.history)
      (future.bodyOrigin escaped) budget actualMeaning called callWithin
  obtain ⟨returned, _samePool, relatedCaller⟩ := callerBridge.restore callerInitial finalState
    (argumentMaps.trans maps) (argumentWorlds.trans worlds) (argumentFrame.trans frame)
    (argumentMetadata.trans metadata) ((callerBridge.related argumentRelated).trans related)
  exact ⟨payloads, middleStore, value, finalStore, finalMap, finalWorld, argumentsEval, bodyEval, result, finalHeaps,
    argumentMaps.trans maps, argumentWorlds.trans worlds, argumentFrame.trans frame, argumentMetadata.trans metadata,
    returned, relatedCaller⟩



include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- The selected lambda's arguments run in their actual two-guard environment.
Their reached pool supplies the caller for the real parameter/body invocation.
The input Source closure retains its full dictionary and capture validity. -/
theorem arguments_preserves_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  exact arguments_preserves_bounded_with_sequence profile receipt nativeTypes escaped capturesValid
    callerBridge callerInitial callerStable budget
    (SequencePreserves.of_uniform profile receipt children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations evaluated argumentsWithin called callWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
theorem arguments_preserves_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  exact arguments_preserves_bounded_with_continuations profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    callerBridge callerInitial callerStable budget argumentMeaning
      (source_continuations_of_canonical (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget bodyMeaning) evaluated argumentsWithin called callWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
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
  exact arguments_preserves_bounded_with_receipts profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning evaluated argumentsWithin called callWithin

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


include receipt nativeTypes escaped capturesValid in
/-- Successful original argument and body children are reflected independently.
The ordered sequence's actual post is the real invocation input; the resulting
Source argument and call grades remain independent of the native children. -/
theorem arguments_reflects_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  obtain ⟨sourceArgumentsSize, argumentOutcome, middle, middleMap, middleWorld, argumentTrace, represented, middleHeaps,
      argumentMaps, argumentWorlds, argumentFrame, argumentMetadata, argumentState, argumentRelated⟩ :=
    argumentSequence evaluated argumentsWithin
  cases represented with
  | @values sources payloads represented =>
    cases argumentTrace with
    | values argumentsTrace =>
      rw [nativeTypes] at represented
      have parameterArguments := values_arguments receipt.code.receipt.loweredParameters represented
      let future := receipt.extend argumentMaps argumentWorlds
      have futureStable := StableRows.after_administrative (callerBridge.pool callerInitial) (callerBridge.pool argumentState) callerStable argumentFrame
      obtain ⟨currentMetadata, currentCarried⟩ := futureStable receipt.owner.position
      let actualMeaning := bodyContinuations argumentMaps argumentWorlds argumentState parameterArguments
        middleHeaps (capturesValid.extend argumentMetadata) argumentFrame argumentMetadata argumentRelated
        argumentsTrace
      obtain ⟨sourceCallSize, outcome, after, finalMap, finalWorld, callTrace, result, finalHeaps,
          maps, worlds, frame, metadata, finalState, related⟩ :=
        CallableIndexedOwnedLambdaInvocationBounds.invocation_reflects_bounded_at
          future.captured future.code future.history future.inputs
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) parameterArguments
          future.owner (callerBridge.pool argumentState) middleHeaps (capturesValid.extend argumentMetadata) future.reference currentCarried
          (CallableIndexedLambdaTemplatePermission.lambda_allowed future.code future.history)
          (future.bodyOrigin escaped) budget actualMeaning completed bodyWithin
      obtain ⟨returned, _samePool, relatedCaller⟩ := callerBridge.restore callerInitial finalState
        (argumentMaps.trans maps) (argumentWorlds.trans worlds) (argumentFrame.trans frame)
        (argumentMetadata.trans metadata) ((callerBridge.related argumentRelated).trans related)
      exact ⟨sourceArgumentsSize, sourceCallSize, _, middle, outcome, after, finalMap, finalWorld,
        argumentsTrace, callTrace, result, finalHeaps,
        argumentMaps.trans maps, argumentWorlds.trans worlds, argumentFrame.trans frame, argumentMetadata.trans metadata,
        returned, relatedCaller⟩



include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- Successful original argument and body children are reflected independently.
The ordered sequence's actual post is the real invocation input; the resulting
Source argument and call grades remain independent of the native children. -/
theorem arguments_reflects_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  exact arguments_reflects_bounded_with_sequence profile receipt nativeTypes escaped capturesValid
    callerBridge callerInitial callerStable budget
    (SequenceReflects.of_uniform profile receipt children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations evaluated argumentsWithin completed bodyWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
theorem arguments_reflects_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  exact arguments_reflects_bounded_with_continuations profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    callerBridge callerInitial callerStable budget argumentMeaning
      (native_continuations_of_canonical (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget bodyMeaning) evaluated argumentsWithin completed bodyWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
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
  exact arguments_reflects_bounded_with_receipts profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning evaluated argumentsWithin completed bodyWithin

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


include receipt nativeTypes escaped capturesValid in
/-- The accepted two-guard call composes the real callee post with ordered
arguments and the restored body post. Its input records are never rebuilt. -/
theorem call_preserves_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
    arguments_preserves_bounded_with_sequence profile receipt nativeTypes escaped capturesValid callerBridge callerInitial callerStable budget argumentSequence bodyContinuations evaluated argumentsWithin called callWithin
  rw [receipt.value_eq] at calleeEvaluation argumentEvaluation
  exact ⟨value, finalStore, finalMap, finalWorld,
    CallableContract.call_success gates unknown calleeEvaluation stageAccepted argumentEvaluation arityAccepted bodyEvaluation,
    result, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
    calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩



include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- The accepted two-guard call composes the real callee post with ordered
arguments and the restored body post. Its input records are never rebuilt. -/
theorem call_preserves_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  exact call_preserves_bounded_with_sequence profile receipt nativeTypes escaped capturesValid
    callerBridge callerInitial callerStable budget
    (SequencePreserves.of_uniform profile receipt children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted evaluated argumentsWithin called callWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
theorem call_preserves_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  exact call_preserves_bounded_with_continuations profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    callerBridge callerInitial callerStable budget argumentMeaning
      (source_continuations_of_canonical (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted arityAccepted evaluated argumentsWithin called callWithin

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
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
  exact call_preserves_bounded_with_receipts profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted arityAccepted evaluated argumentsWithin called callWithin

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


include receipt in
/-- An argument fault keeps the exact reached argument pool in the enclosing
accepted call. No parameter or body state is constructed on this path. -/
theorem call_argument_fault_preserves_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩) (budget : Nat)
    (argumentSequence : SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
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
  obtain ⟨token, finalStore, finalMap, finalWorld, argumentsEval, matched, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    argumentSequence.2 failed within
  rw [receipt.value_eq] at calleeEvaluation argumentsEval
  exact ⟨token, finalStore, finalMap, finalWorld,
    CallableContract.call_argument_failure gates unknown calleeEvaluation stageAccepted argumentsEval,
    matched, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
    calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩

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
  exact call_argument_fault_preserves_bounded_with_sequence profile receipt callerInitial budget
    (SequencePreserves.of_uniform profile receipt children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted failed within

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


include receipt nativeTypes escaped capturesValid in
/-- Native accepted-call completion uses its original measured children. The
actual callee post feeds the argument post, then the same real body post and
restoration. Source argument fault and call grades remain independent. -/
theorem call_reflects_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := receipt) (codes := codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
    obtain ⟨sourceArgumentsSize, argumentOutcome, after, finalMap, finalWorld, argumentTrace, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      argumentSequence argumentsTrace smaller
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
      arguments_reflects_bounded_with_sequence profile receipt nativeTypes escaped capturesValid callerBridge callerInitial callerStable
        budget argumentSequence bodyContinuations argumentsTrace argumentsSmaller bodyTrace (Nat.le_of_lt bodySmaller)
    exact ⟨sourceArgumentsSize, sourceCallSize, outcome, after, finalMap, finalWorld, .called sourceArguments sourceCall,
      result, finalHeaps, calleeMaps.trans maps, calleeWorlds.trans worlds,
      calleeFrame.trans frame, calleeMetadata.trans metadata, reached, callerProtocol.trans calleeRelated related⟩



include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
/-- Native accepted-call completion uses its original measured children. The
actual callee post feeds the argument post, then the same real body post and
restoration. Source argument fault and call grades remain independent. -/
theorem call_reflects_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, before, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget)
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
  exact call_reflects_bounded_with_sequence profile receipt nativeTypes escaped capturesValid
    callerBridge callerInitial callerStable budget
    (SequenceReflects.of_uniform profile receipt children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
    calleeEvaluation stageAccepted arityAccepted completed within

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
theorem call_reflects_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
  exact call_reflects_bounded_with_continuations profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    callerBridge callerInitial callerStable budget argumentMeaning
      (native_continuations_of_canonical (source := source) (context := context) (evidence := evidence) (environment := environment) (ids := ids) profile receipt escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted arityAccepted completed within

include receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed in
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
  exact call_reflects_bounded_with_receipts profile receipt children nativeTypes escaped environments heaps locals capturesValid agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted arityAccepted completed within

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
/-! Source admission is a pointwise receipt at an actual caller state. Deep
Source heap typing follows real successful Source execution; administrative
preservation separately retains every reached row's own stable history.
Faults retain the actual post and stable rows. They carry no claim of deep heap
typing. These adapters supply no administrative transport or execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers)
    (fun _ => True) callerProtocol)
  (context : SourceSemantics.Context)

/-- Both facets describe this actual input. A single selected-row packet does
not supply the all-row receipt or the deep Source heap receipt. -/
structure Admission {index : ProtectedStateTransition.Index}
    (initial : callerProtocol.State index) : Prop where
  heap : Dynamic.HeapWellTyped context index.heap
  rows : StableRows (bridge.pool initial)

/-- Only a successful Source outcome supplies value and deep heap typing.
The reached pool and every row's own stable history are retained for faults. -/
structure PostAdmission (type : TypeSystem.Ty) (outcome : Dynamic.ExpressionOutcome)
    {index : ProtectedStateTransition.Index} (reached : callerProtocol.State index) : Prop where
  rows : StableRows (bridge.pool reached)
  successful : ∀ value, outcome = .value value →
    Dynamic.ValueHasType context index.heap value type ∧ Dynamic.HeapWellTyped context index.heap

variable {bridge context}

/-- Successful posts become genuine input admission at the same actual state. -/
theorem PostAdmission.at_value {type : TypeSystem.Ty} {value : Dynamic.Value}
    {index : ProtectedStateTransition.Index} {reached : callerProtocol.State index}
    (post : PostAdmission bridge context type (.value value) reached) :
    Dynamic.ValueHasType context index.heap value type ∧ Admission bridge context reached := by
  have typed := post.successful value rfl
  exact ⟨typed.1, typed.2, post.rows⟩

/-- Pair the real Source derivation with the actual reached caller witness.
No old state is substituted for that witness, and its own ghosts authenticate
all reached stable histories. -/
theorem after_expression {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last := by
  refine ⟨StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame, ?_⟩
  intro value same
  cases trace with
  | value evaluated =>
    cases same
    have preserved := wellFormed.wholeLanguagePreservation.expression context evidence source environment
      initial.heap reached.heap id _ type runtime covers locals admitted.heap typed evaluated
    exact ⟨preserved.value_typed, preserved.heap_typed⟩
  | fault _ => cases same

/-- Source and Core grades remain independent. The exact original sized
Source derivation supplies the admission; its grade is not changed. -/
theorem after_expression_sized {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {outcome : Dynamic.ExpressionOutcome} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment
      initial.heap id outcome reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    PostAdmission bridge context type outcome last :=
  after_expression first last admitted wellFormed runtime covers locals typed trace.sound frame

/-- Sequential use consumes the actual first successful post together with
its Source admission. The callback never receives an administrative surrogate. -/
theorem then_value {initial middle final : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {id : ExpressionId} {type : TypeSystem.Ty}
    {value : Dynamic.Value} {size : Nat}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typed : ExpressionHasType source context id type)
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment
      initial.heap id (.value value) middle.heap)
    (frame : AdministrativePreserved initial.mapping initial.store middle.mapping middle.store)
    (transition : ProtectedStateTransition.Transition callerProtocol first middle)
    (next : ∀ reached : callerProtocol.State middle, callerProtocol.Relates first reached →
      Admission bridge context reached → Dynamic.ValueHasType context middle.heap value type →
      ProtectedStateTransition.Transition callerProtocol reached final) :
    ProtectedStateTransition.Transition callerProtocol first final := by
  apply transition.then
  intro reached related
  have post := after_expression_sized first reached admitted wellFormed runtime covers locals typed trace frame
  have actualAdmission := post.at_value
  exact next reached related actualAdmission.2 actualAdmission.1

section ExpressionConsumer
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
  {size : Nat} {scope : SourceCoreLocalCell.Scope} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {node : ExpressionNode}
  {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
  {environment : Dynamic.Environment} {canonical actual : Environment} {actualContext : Core.Context}
  {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : callerProtocol.State ⟨scope, mapping, world, before, store, canonical⟩)
  (admitted : Admission bridge context initial)
  (wellFormed : ProgramWellFormed program)
  (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context)
  (certified : certificate scope id lowered)
  (found : source.lookupExpression? id = some node)
  (sourceTyped : ExpressionHasType source context id node.type)
  (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
  (heaps : GenericHeap.HeapRepresents model mapping world before store)
  (locals : Dynamic.EnvironmentAgrees before context.locals environment)
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions)

include admitted wellFormed runtime covers certified found sourceTyped environments heaps locals agrees typed

/-- Consume an existing actual-state producer pointwise and retain its full
semantic result, exact reached witness, relation and authentic Source admission. -/
theorem preserves_at
    (meaning : ProtectedStateTransition.PreservesAt callerProtocol model program context evidence source certificate faults size)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩

/-- Native reflection first obtains its independently graded real Source
trace. That trace authenticates successful admission at the same returned post. -/
theorem reflects_at
    (meaning : ProtectedStateTransition.ReflectsAt callerProtocol model program context evidence source certificate faults size)
    {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ reached : callerProtocol.State ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩,
        callerProtocol.Relates initial reached ∧ PostAdmission bridge context node.type outcome reached := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
      frame, metadata, reached, related⟩ :=
    meaning certified found environments heaps locals agrees typed initial completed
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds,
    frame, metadata, reached, related,
    after_expression_sized initial reached admitted wellFormed runtime covers locals sourceTyped trace frame⟩
end ExpressionConsumer

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSourceAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
/-! Bit-not assignment retains its real resolution snapshot and writes the
latest root. The genuine Source trace supplies deep heap typing at that exact
written state; native administrative effects authenticate row history only. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open CallableIndexedOwnedFunctionState CallableIndexedOwnedSourceAdmission
open CallableIndexedOwnedIndirectExpressionHeads (StableRows)
universe u
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
  (bridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)

/-- Resolution and the actual snapshot write preserve Source typing through
the already proved Source semantics. No expression execution law is assumed. -/
theorem after_snapshot {initial reached : ProtectedStateTransition.Index}
    (first : callerProtocol.State initial) (last : callerProtocol.State reached)
    {context : SourceSemantics.Context}
    (admitted : Admission bridge context first)
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {assignment : AssignmentResolution} {updatedRoot : Dynamic.Value}
    (wellFormed : ProgramWellFormed program)
    (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context)
    (locals : Dynamic.EnvironmentAgrees initial.heap context.locals environment)
    (typing : SourceBitNotAssignmentValid source context assignment)
    (trace : Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment initial.heap assignment.target updatedRoot reached.heap)
    (frame : AdministrativePreserved initial.mapping initial.store reached.mapping reached.store) :
    Admission bridge context last ∧ Dynamic.HeapTypesExtend initial.heap reached.heap := by
  have expressionPreserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covered agreed heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment
      before after id value type runtime covered agreed heapTyped typed evaluated
  obtain ⟨heapTyped, extension⟩ := trace.bitNotPreserves expressionPreserves covers locals admitted.heap typing
  exact ⟨⟨heapTyped,
    StableRows.after_administrative (bridge.pool first) (bridge.pool last) admitted.rows frame⟩, extension⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedSnapshotAdmission
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
/-! Selected indirect-call Source adapters retain the actual compiler receipt,
original parent node and prepared callsite. Caller protocols carry their same
actual pools separately from the selected closure capture protocol. Source suffix
construction uses original measured children; argument counts follow existing Source preservation
under real Source admission. -/
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedOwnedFunctionState CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedOwnedIndirectExpressionHeads
open RecursiveNamedCatalogInvocationBounds (Below)
open CallableIndexedOwnedExpressionHeads (argumentProtocol)

universe u

section LegacyBody
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

end LegacyBody

section Source
variable {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {environment : Dynamic.Environment} {before calleeHeap after : Dynamic.Heap}
  {call callee : ExpressionId} {ids : List ExpressionId} {function : Dynamic.Closure}
  {node : ExpressionNode} {metadata : IndirectCallResolution}

/-- Raw source argument typing and original Source preservation prove the
count of this actual argument result. No execution callback is a premise. -/
theorem arguments_count_of_source_admission
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {size : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program size context evidence source environment calleeHeap ids arguments middle) :
    arguments.length = metadata.argumentCount := by
  have preserves : Dynamic.ExpressionExecutionPreserves program context evidence source environment := by
    intro before after id value type covers locals heapTyped typed evaluated
    exact wellFormed.wholeLanguagePreservation.expression context evidence source environment before after id value type
      runtime covers locals heapTyped typed evaluated
  have reached := Dynamic.ExpressionsEvaluate.preserves preserves covers locals heapTyped typed evaluated.sound
  exact reached.1.length_eq.trans count

/-- The original closure application fixes its invocation dictionary. Arity
failure has no dictionary-dependent execution, so its same receipt is retained. -/
theorem call_with_closure_evidence
    {size : Nat} {invocation : Dynamic.EvidenceEnvironment} {arguments : List Dynamic.Value}
    {outcome : Dynamic.ExpressionOutcome}
    (called : RecursiveNamedCallBounds.CallOutcome program size context evidence invocation before
      (.closure function) arguments outcome after) :
    RecursiveNamedCallBounds.CallOutcome program size context evidence function.evidence before
      (.closure function) arguments outcome after := by
  cases called with
  | value applied =>
    cases applied with
    | closure same frame parameters copy allocation executed returned =>
      cases same
      exact .value (.closure rfl frame parameters copy allocation executed returned)
    | closureUnit same frame unit parameters copy allocation executed fellThrough =>
      cases same
      exact .value (.closureUnit rfl frame unit parameters copy allocation executed fellThrough)
  | fault failed =>
    cases failed with
    | notCallable invalid => exact False.elim (invalid trivial)
    | closureArity mismatch => exact .fault (.closureArity mismatch)
    | closureBody same frame parameters copy allocation failed =>
      cases same
      exact .fault (.closureBody rfl frame parameters copy allocation failed)
    | closureControlEscape same frame parameters copy allocation executed escaped =>
      cases same
      exact .fault (.closureControlEscape rfl frame parameters copy allocation executed escaped)

/-- This packet is made from the actual ordered arguments and application
children of the selected Source call, preserving their separate grades. -/
theorem SourceSuffix.of_call
    {argumentsSize callSize : Nat} {arguments : List Dynamic.Value} {middle : Dynamic.Heap}
    {outcome : Dynamic.ExpressionOutcome} {invocation : Dynamic.EvidenceEnvironment}
    (evaluated : SourceExecutionSize.ExpressionsEvaluate program argumentsSize context evidence source environment before ids
      arguments middle)
    (called : RecursiveNamedCallBounds.CallOutcome program callSize context evidence invocation middle
      (.closure function) arguments outcome after) :
    SourceSuffix program context evidence source environment before ids function argumentsSize callSize outcome after :=
  .called evaluated (call_with_closure_evidence called)

/-- The selected suffix is wrapped in the original whole parent Source rule.
Both dictionaries, the original measured callee and argument/call grades, and
all raw source metadata remain explicit. -/
theorem SourceSuffix.to_expression
    (found : source.lookupExpression? call = some node)
    (form : node.form = .call callee ids (.indirect metadata))
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (argumentCoercions : metadata.argumentCoercions = [])
    (sourceArity : ids.length = metadata.argumentCount)
    (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
    (covers : evidence.Covers context) (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
    (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
    {types : List TypeSystem.Ty} (typed : ExpressionsHaveTypes source context ids types)
    (count : types.length = metadata.argumentCount)
    {calleeSize argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment before callee
      (.closure function) calleeHeap)
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after) :
    ∃ size, RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before call outcome after := by
  cases suffix with
  | argumentFault failed =>
    refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize]], .fault (.form (lookupExpression?_sound found) ?_)⟩
    rw [form]
    exact .indirectArguments calleeTrace trivial failed
  | called argumentsTrace called =>
    rename_i arguments middle
    have appliedArity := arguments_count_of_source_admission wellFormed runtime covers locals heapTyped typed count argumentsTrace
    obtain ⟨packed, pack⟩ := Dynamic.ValuesPack.exists_pack arguments
    cases called with
    | @value result _ applied =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize], SourceExecutionSize.stepSize []], .value (.intro (raw := result) (middle := after) (lookupExpression?_sound found) ?_ ?_)⟩
      · rw [form]
        refine .indirectCall ?_ calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity applied
        · simp [requirements, argumentCoercions, coercions, coercionRequirementIds]
        · rw [argumentCoercions]; exact .nil
      · rw [coercions]; exact .nil
    | fault failed =>
      refine ⟨SourceExecutionSize.stepSize [SourceExecutionSize.stepSize [calleeSize, argumentsSize, SourceExecutionSize.stepSize [], callSize]], .fault (.form (lookupExpression?_sound found) ?_)⟩
      rw [form]
      refine .indirectApply calleeTrace argumentsTrace pack ?_ pack sourceArity appliedArity failed
      rw [argumentCoercions]; exact .nil
end Source


section Compiler
variable {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
  {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource}
  {scope : SourceCoreBasic.Scope} {id callee : ExpressionId} {ids : List ExpressionId}
  {metadata : IndirectCallResolution} {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}

/-- This packet keeps the actual hook receipt and prepared callsite. The
policy-read node is aligned with the original call occurrence explicitly. -/
structure Prepared (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
    id callee ids metadata reasonAt lowered) (native : SourceCoreGeneralFunctions.CallableContext) where
  site : SourceCoreCallableContracts.Callsite
  prepared : SourceCoreCallableContracts.prepareCallsite native.table compilation.owner receipt.node.id
    native.diagnostics.reasonAt = .ok site
  table : site.table = native.table
  caller : site.caller = compilation.owner
  call : site.call = id
  emitted : receipt.expression = site.lower native.diagnostics.unknown receipt.resultType receipt.calleeCode.expression
    (SourceCoreCalls.packArguments receipt.codes).expression

theorem Prepared.of_receipt
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    (native : SourceCoreGeneralFunctions.CallableContext) (active : TypeSystem.Substitution)
    (actualPolicy : policy.callables = SourceCoreGeneralFunctions.callablePolicy (some native) active)
    (nodeId : receipt.node.id = id) : Nonempty (Prepared receipt native) := by
  obtain ⟨site, prepared, table, caller, call, emitted⟩ := receipt.prepared_site native active actualPolicy
  exact ⟨⟨site, prepared, table, caller, call.trans nodeId, emitted⟩⟩

private theorem guardResult_rename (reason : Option Word) (ξ : Renaming) :
    (CallableContract.guardResult reason).rename ξ = CallableContract.guardResult reason := by
  cases reason <;> rfl

private theorem dispatch_rename (gates : List CallableContract.Gate) (phase : CallableContract.Phase)
    (unknown : Word) (contract : Expr) (ξ : Renaming) :
    (CallableContract.dispatch gates phase unknown contract).rename ξ =
      CallableContract.dispatch gates phase unknown (contract.rename ξ) := by
  induction gates with
  | nil => exact guardResult_rename _ _
  | cons gate rest ih =>
    simp only [CallableContract.dispatch, Expr.rename, guardResult_rename, ih]

/-- Only static guard syntax is folded here. Renaming preserves the actual
callee, ordered argument vector and both accepted stage decisions. -/
theorem call_rename (gates : List CallableContract.Gate) (unknown : Word) (result : Ty)
    (callee arguments : Expr) (ξ : Renaming) :
    (CallableContract.call gates unknown result callee arguments).rename ξ =
      CallableContract.call gates unknown result (callee.rename ξ) (arguments.rename ξ) := by
  simp only [CallableContract.call, LanguageResult.bind, Expr.rename, dispatch_rename,
    Expr.rename_weakenAt_zero, Renaming.lift]

/-- The emitted whole parent is the exact prepared callsite after the current
runtime renaming. No arbitrary callable policy is replaced. -/
theorem Prepared.lowered_rename
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered)
    {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared receipt native) (ξ : Renaming) :
    lowered.expression.rename ξ = CallableContract.call prepared.site.gates native.diagnostics.unknown receipt.resultType
      (receipt.calleeCode.expression.rename ξ) ((SourceCoreCalls.packArguments receipt.codes).expression.rename ξ) := by
  have emitted : lowered.expression = receipt.expression := congrArg (fun output => output.expression) receipt.output
  rw [emitted, prepared.emitted]
  exact call_rename _ _ _ _ _ _
end Compiler


/-- Original Source metadata for this exact parent. Successful native lowering
alone does not replace the original node's requirements or coercion path. -/
structure SourceParent {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer}
    {fuel : Nat} {compilation : SourceCoreFunctions.Context} {source : TypedSource} {scope : SourceCoreBasic.Scope}
    {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
    {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
    (receipt : CallableIndirectCallCertificates.Receipt policy body fuel compilation source scope
      id callee ids metadata reasonAt lowered) : Prop where
  requirements : receipt.original.requirements = []
  coercions : receipt.original.coercions = []
  arity : ids.length = metadata.argumentCount

section SelectedParent
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {callerScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  {native : SourceCoreGeneralFunctions.CallableContext} (prepared : Prepared compiler native)
  (parent : SourceParent compiler)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate}
  {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure}
  {sourceType : TypeSystem.Ty} {carrier : Value} {type : Ty}
  (closure : ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
    mapping world function sourceType carrier type)
  (children : DataExpressionSequence.Tree source certificate callerScope ids
    (closure.code.receipt.loweredParameters.map (fun binding => binding.1.scheme.body)) compiler.codes)
  (nativeTypes : compiler.codes.map (·.type) = closure.code.receipt.loweredParameters.map Prod.snd)
  (escaped : faults .controlEscapedFunction closure.code.compilation.internalReason)
  (rawResult : SourceCoreRawMetadata.runtimeType compiler.original.type = SourceCoreRawMetadata.runtimeType function.resultType)
  (nativeResult : compiler.resultType = closure.code.receipt.resultCore)
  {administrative actualContext : Core.Context} {environment : Dynamic.Environment}
  {canonical actual : Environment} {calleeHeap : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (environments : DataHeap.EnvRepresents (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog)
    mapping world administrative callerScope environment canonical compiled.indexed.layouts.definitions)
  (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
    (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) mapping world calleeHeap store)
  (locals : Dynamic.EnvironmentAgrees calleeHeap context.locals environment)
  (capturesValid : FunctionValues.SourceCapturesValid calleeHeap (.closure function))
  (agrees : EnvironmentsAgree ξ canonical actual)
  (typed : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
  (initial : State headers keys ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
  (stable : StableRows initial)
  (wellFormed : ProgramWellFormed program) (runtime : Dynamic.SourceRuntimeValid program context source)
  (covers : evidence.Covers context) (heapTyped : Dynamic.HeapWellTyped context calleeHeap)
  {types : List TypeSystem.Ty} (sourceArguments : ExpressionsHaveTypes source context ids types)
  (sourceCount : types.length = metadata.argumentCount)

include rawResult nativeResult in
private theorem parent_result {finalMap : LocationMap} {finalWorld : StoreTyping}
    {outcome : Dynamic.ExpressionOutcome} {value : Value}
    (represented : FunctionCalls.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      finalMap finalWorld function.resultType closure.code.receipt.resultCore faults outcome value) :
    GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      finalMap finalWorld compiler.original.type lowered.type faults outcome value := by
  have loweredType : lowered.type = compiler.resultType :=
    (congrArg (fun output => output.type) compiler.output).trans compiler.resultTypeEq.symm
  rw [loweredType, nativeResult]
  cases represented with
  | value related => exact .value (.compatible rawResult related)
  | fault matched => exact .fault matched

include prepared parent nativeTypes escaped rawResult nativeResult locals capturesValid
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Reflection of this accepted selected parent uses the actual callee post,
original argument/body grades and the same returned pool. Source reconstruction
uses the original parent node and independently graded child traces. -/
theorem reflects_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequenceReflects (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := closure) (codes := compiler.codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have emitted := prepared.lowered_rename compiler ξ
  rw [emitted, nativeResult] at completed
  obtain ⟨argumentsSize, callSize, outcome, after, finalMap, finalWorld, suffix, represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩ :=
    call_reflects_bounded_with_sequence profile closure nativeTypes escaped capturesValid callerBridge callerInitial callerStable
      budget argumentSequence bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
      calleeEvaluation stageAccepted arityAccepted completed within
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers locals heapTyped sourceArguments sourceCount calleeTrace suffix
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, original,
    parent_result profile compiler closure rawResult nativeResult represented, finalHeaps,
    maps, worlds, frame, metadata, reached, related⟩


include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Reflection of this accepted selected parent uses the actual callee post,
original argument/body grades and the same returned pool. Source reconstruction
uses the original parent node and independently graded child traces. -/
theorem reflects_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : NativeContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_sequence profile compiler prepared parent closure nativeTypes escaped rawResult nativeResult
    locals capturesValid wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget
    (SequenceReflects.of_uniform profile closure children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace
    calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_continuations profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget argumentMeaning
      (native_continuations_of_canonical (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_receipts profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted completed within

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  stable wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem reflects_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.ReflectsAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.ReflectsAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {size : Nat} {value : Value} {finalStore : Store}
    (completed : EvaluationSize size actual firstStore (lowered.expression.rename ξ) value finalStore)
    (within : size ≤ budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_caller profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult
    environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning
    (fun child strict => body_reflects_to_canonical profile closure.owner closure.callerPrefix
      (closure.bodyOrigin escaped).origin (bodyMeaning child strict))
    first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation
    stageAccepted arityAccepted completed within

include prepared parent nativeTypes escaped rawResult nativeResult locals capturesValid
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Source callee and suffix receipts produce this actual emitted parent.
Arguments and called-body grades are the original inclusive Source children;
argument faults retain their reached pool without constructing a body state. -/
theorem preserves_bounded_with_sequence
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentSequence : SequencePreserves (source := source) (context := context) (evidence := evidence)
      (profile := profile) (receipt := closure) (codes := compiler.codes) (environment := environment)
      (actual := actual) (ξ := ξ) (ids := ids) callerInitial budget)
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sourceSize, original⟩ := SourceSuffix.to_expression compiler.found compiler.originalForm parent.requirements parent.coercions
    compiler.argumentCoercions parent.arity wellFormed runtime covers locals heapTyped sourceArguments sourceCount calleeTrace suffix
  have emitted := prepared.lowered_rename compiler ξ
  rw [nativeResult] at emitted
  cases suffix with
  | argumentFault failed =>
    obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      call_argument_fault_preserves_bounded_with_sequence profile closure callerInitial
        budget argumentSequence first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeEvaluation stageAccepted
        failed argumentsWithin
    refine ⟨sourceSize, .inLeft closure.code.receipt.resultCore (.word token), finalStore, finalMap, finalWorld, original, ?_, ?_, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
    · rw [emitted]; exact evaluated
    · exact parent_result profile compiler closure rawResult nativeResult (.fault matched)
  | called argumentsTrace called =>
    obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
        maps, worlds, frame, metadata, reached, related⟩ :=
      call_preserves_bounded_with_sequence profile closure nativeTypes escaped capturesValid callerBridge callerInitial callerStable
        budget argumentSequence bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata
        calleeEvaluation stageAccepted arityAccepted argumentsTrace argumentsWithin called callWithin
    refine ⟨sourceSize, value, finalStore, finalMap, finalWorld, original, ?_,
      parent_result profile compiler closure rawResult nativeResult represented, finalHeaps,
      maps, worlds, frame, metadata, reached, related⟩
    rw [emitted]; exact evaluated


include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
/-- Source callee and suffix receipts produce this actual emitted parent.
Arguments and called-body grades are the original inclusive Source children;
argument faults retain their reached pool without constructing a body state. -/
theorem preserves_bounded_with_continuations
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyContinuations : SourceContinuations (source := source) (context := context) (evidence := evidence)
      (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget)
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_sequence profile compiler prepared parent closure nativeTypes escaped rawResult nativeResult
    locals capturesValid wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget
    (SequencePreserves.of_uniform profile closure children environments heaps locals agrees typed callerInitial budget argumentMeaning)
    bodyContinuations first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace
    calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_continuations profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    callerBridge callerInitial callerStable budget argumentMeaning
      (source_continuations_of_canonical (source := source) (context := context) (evidence := evidence)
        (environment := environment) (ids := ids) profile closure escaped callerBridge callerInitial budget bodyMeaning) first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded_with_caller
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedCallerProtocol.Carrier (headers := headers) callerProtocol)
    (callerInitial : callerProtocol.State ⟨callerScope, mapping, world, calleeHeap, store, canonical⟩)
    (callerStable : StableRows (callerBridge.pool callerInitial)) (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt callerProtocol
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (argumentProtocol (headers := headers) closure.owner closure.callerPrefix) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : callerProtocol.State ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : callerProtocol.Relates first callerInitial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition callerProtocol first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_receipts profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget argumentMeaning bodyMeaning first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation stageAccepted arityAccepted suffix argumentsWithin callWithin

include prepared parent children nativeTypes escaped rawResult nativeResult environments heaps locals capturesValid agrees typed
  stable wellFormed runtime covers heapTyped sourceArguments sourceCount in
theorem preserves_bounded (budget : Nat)
    (argumentMeaning : Below budget (ProtectedStateTransition.PreservesAt (protocol headers keys)
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
      program context evidence source certificate faults))
    (bodyMeaning : Below budget (CallableRuntimeBodyOrigins.Stateful.PreservesAt
      (protocol headers keys) (CallableIndexedOwnedAllocationProducer.StableOwner keys)
      (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) program (closure.bodyOrigin escaped).origin))
    {firstMap : LocationMap} {firstWorld : StoreTyping} {firstHeap : Dynamic.Heap} {firstStore : Store}
    (first : State headers keys ⟨callerScope, firstMap, firstWorld, firstHeap, firstStore, canonical⟩)
    (calleeRelated : Relates first initial)
    (calleeMaps : LocationMap.Extends firstMap mapping) (calleeWorlds : WorldExtends firstWorld world)
    (calleeFrame : AdministrativePreserved firstMap firstStore mapping store)
    (calleeMetadata : Dynamic.HeapMetadataExtend firstHeap calleeHeap)
    {calleeSize : Nat}
    (calleeTrace : SourceExecutionSize.ExpressionEvaluates program calleeSize context evidence source environment firstHeap callee
      (.closure function) calleeHeap)
    (calleeEvaluation : Evaluates actual firstStore (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) store)
    (stageAccepted : CallableContract.decision prepared.site.gates .beforeArguments native.diagnostics.unknown closure.code.descriptor.id = none)
    (arityAccepted : CallableContract.decision prepared.site.gates .beforeApplication native.diagnostics.unknown closure.code.descriptor.id = none)
    {argumentsSize callSize : Nat} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (suffix : SourceSuffix program context evidence source environment calleeHeap ids function argumentsSize callSize outcome after)
    (argumentsWithin : argumentsSize ≤ budget) (callWithin : callSize ≤ budget) :
    ∃ sourceSize value finalStore finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment firstHeap id outcome after ∧
      Evaluates actual firstStore (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry
          (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile))
        finalMap finalWorld compiler.original.type lowered.type faults outcome value ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) finalMap finalWorld after finalStore ∧
      LocationMap.Extends firstMap finalMap ∧ WorldExtends firstWorld finalWorld ∧
      AdministrativePreserved firstMap firstStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend firstHeap after ∧
      ProtectedStateTransition.Transition (protocol headers keys) first
        ⟨callerScope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_caller profile compiler prepared parent closure children nativeTypes escaped rawResult nativeResult
    environments heaps locals capturesValid agrees typed wellFormed runtime covers heapTyped sourceArguments sourceCount
    CallableIndexedOwnedCallerProtocol.base initial stable budget argumentMeaning
    (fun child strict => body_preserves_to_canonical profile closure.owner closure.callerPrefix
      (closure.bodyOrigin escaped).origin (bodyMeaning child strict))
    first calleeRelated calleeMaps calleeWorlds calleeFrame calleeMetadata calleeTrace calleeEvaluation
    stageAccepted arityAccepted suffix argumentsWithin callWithin

end SelectedParent


section AdmittedCallee
variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  (profile : compiled.compatible.checked.catalog.callableContracts = true)
  {policy : SourceCoreFunctions.Policy} {body : SourceCoreFunctions.BodyLowerer} {fuel : Nat}
  {compilation : SourceCoreFunctions.Context} {source : TypedSource} {callerScope : SourceCoreLocalCell.Scope}
  {id callee : ExpressionId} {ids : List ExpressionId} {metadata : IndirectCallResolution}
  {reasonAt : ExpressionId → Word} {lowered : SourceCoreBasic.LoweredExpr}
  (compiler : CallableIndirectCallCertificates.Receipt policy body fuel compilation source callerScope
    id callee ids metadata reasonAt lowered)
  {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {certificate : GenericExpressionMeaning.Certificate} {calleeNode : ExpressionNode}
  (certified : certificate callerScope callee compiler.calleeCode)
  (found : source.lookupExpression? callee = some calleeNode)
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
/-- Callee evaluation keeps its real post pool together with the Source heap
and lexical admission needed to type the original parent's actual arguments.
The policy-read callee node is not substituted for its original Source node. -/
theorem callee_preserves_admitted_bounded_with_receipts
    {callerProtocol : ProtectedStateTransition.Protocol.{u, 0} (Records keys)}
    (callerBridge : CallableIndexedOwnedNamedCallerProtocol.Carrier (headers := headers) (fun _ => True) callerProtocol)
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
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  obtain ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
      reached, related, reachedStable, closure⟩ :=
    callee_preserves_bounded_with_receipts profile certified found environments heaps locals agrees typed callerBridge callerInitial callerStable budget children executed smaller
  obtain ⟨captures, reachedTyped, sourceMetadata⟩ := CallableIndexedOwnedCaptureExecutionValidity.captures_of_expression
    wellFormed runtime covers locals heapTyped sourceTyped executed.sound
  exact ⟨carrier, calleeStore, calleeMap, calleeWorld, evaluated, finalHeaps, maps, worlds, frame, metadata,
    reached, related, reachedStable, closure, captures, Dynamic.EnvironmentAgrees.mono sourceMetadata locals, reachedTyped⟩
include certified found environments heaps locals agrees typed in
theorem callee_preserves_admitted_bounded_with_caller
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
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : callerProtocol.State ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        callerProtocol.Relates callerInitial reached ∧ StableRows (callerBridge.pool reached) ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  exact callee_preserves_admitted_bounded_with_receipts profile compiler certified found environments heaps locals agrees typed
    (CallableIndexedOwnedIndirectCallerProtocol.of_legacy callerBridge) callerInitial callerStable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

include certified found environments heaps locals agrees typed stable in
theorem callee_preserves_admitted_bounded (budget : Nat)
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
      Evaluates actual store (compiler.calleeCode.expression.rename ξ) (.inRight .word carrier) calleeStore ∧
      CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry
        (CallableIndexedOwnedFunctionValues.model headers keys registry faults profile) calleeMap calleeWorld calleeHeap calleeStore ∧
      LocationMap.Extends mapping calleeMap ∧ WorldExtends world calleeWorld ∧
      AdministrativePreserved mapping store calleeMap calleeStore ∧ Dynamic.HeapMetadataExtend before calleeHeap ∧
      ∃ reached : State headers keys ⟨callerScope, calleeMap, calleeWorld, calleeHeap, calleeStore, canonical⟩,
        Relates initial reached ∧ StableRows reached ∧
        Nonempty (ClosureAt (headers := headers) (keys := keys) (registry := registry) (faults := faults)
          calleeMap calleeWorld function calleeNode.type carrier compiler.calleeCode.type) ∧
        FunctionValues.SourceCapturesValid calleeHeap (.closure function) ∧
        Dynamic.EnvironmentAgrees calleeHeap context.locals environment ∧ Dynamic.HeapWellTyped context calleeHeap := by
  exact callee_preserves_admitted_bounded_with_caller profile compiler certified found environments heaps locals agrees typed
    CallableIndexedOwnedCallerProtocol.base initial stable budget children wellFormed runtime covers heapTyped sourceTyped executed smaller

end AdmittedCallee

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedIndirectSourceAdapters
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
/-! Finite checks establish the independent occurrence-graph invariants for
an unchanged typed Source. Actual context fields and a separately proved
runtime requirement ledger then establish its runtime validity. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
open Frontend.SourceInference

/-- Check category-safe roots and edges as well as erased occurrence identity.
Every equality is decided propositionally; no structural BEq law is assumed. -/
def checkGraph (source : TypedSource) : Bool :=
  decide (nodeOccurrenceIds source).Nodup &&
    (source.nodes.all (fun node => decide (node.occurrenceId.owner = source.owner)) &&
      (source.roots.all (fun root => decide (root.occurrenceId.owner = source.owner)) &&
        (source.roots.all (fun root => (nodeIds source).any (fun known => decide (root = known))) &&
          source.nodes.all (fun node =>
            (nodeChildIds node).all (fun child => (nodeIds source).any (fun known => decide (child = known)))))))

/-- Successful finite checks prove the original declarative graph invariant. -/
theorem checkGraph_sound {source : TypedSource} (accepted : checkGraph source = true) :
    OccurrenceGraphWellFormed source := by
  unfold checkGraph at accepted
  obtain ⟨unique, rest⟩ := Bool.and_eq_true_iff.mp accepted
  obtain ⟨nodes, rest⟩ := Bool.and_eq_true_iff.mp rest
  obtain ⟨roots, rest⟩ := Bool.and_eq_true_iff.mp rest
  obtain ⟨exist, children⟩ := Bool.and_eq_true_iff.mp rest
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · change (nodeOccurrenceIds source).Nodup
    exact of_decide_eq_true unique
  · intro node member
    change node.occurrenceId.owner = source.owner
    exact of_decide_eq_true (List.all_eq_true.mp nodes node member)
  · intro root member
    change root.occurrenceId.owner = source.owner
    exact of_decide_eq_true (List.all_eq_true.mp roots root member)
  · intro root member
    obtain ⟨known, present, same⟩ := List.any_eq_true.mp (List.all_eq_true.mp exist root member)
    exact (of_decide_eq_true same).symm ▸ present
  · intro node member child edge
    obtain ⟨known, present, same⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp (List.all_eq_true.mp children node member) child edge)
    exact (of_decide_eq_true same).symm ▸ present

/-- The proof is erased during the finite check; the Source remains unchanged. -/
def graphReceipt? (source : TypedSource) : Option (PLift (OccurrenceGraphWellFormed source)) :=
  if accepted : checkGraph source = true then some ⟨checkGraph_sound accepted⟩ else none

/-- These are literal context fields, independent of program execution. -/
structure RuntimeFields (program : Program) (context : Context) (source : TypedSource) : Prop where
  signatures : context.signatures = program.signatures
  owner : context.currentDeclaration = some source.owner
  closed : context.typeParameters = []
  variables_closed : context.typeVariables = []
  residual_variables_open : context.residualTypeVariables = true

/-- Runtime validity follows from the actual checked graph, context fields,
and independent validity of its implementation-backed requirement rows. -/
theorem source_runtime {program : Program} {context : Context} {source : TypedSource}
    (fields : RuntimeFields program context source)
    (accepted : checkGraph source = true)
    (ledger : RuntimeRequirementLedgerValid context) :
    Dynamic.SourceRuntimeValid program context source :=
  { signatures := fields.signatures
    graph := checkGraph_sound accepted
    owner := fields.owner
    closed := fields.closed
    variables_closed := fields.variables_closed
    residual_variables_open := fields.residual_variables_open
    requirements := ledger }

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedFiniteSourceRuntimeReceipts
end
