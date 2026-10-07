import Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderControl
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalControl

/-! Header readiness follows the actual Source item slots, allocations and
written prefixes. The live tail retains its original state and a concrete
restoration receipt for that same state after later effects. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof CompatibleHeap CompatibleEquality SourceCoreCompatibleDataPlaces
open ProtectedStateTransition
open RecursiveNamedLexicalContracts.Stateful.WithReady
open CallableIndexedHistory (NativeFrame)
universe u v
variable {Records : Type v} {protocol : Protocol.{u, v} Records}

def ReadyTransition (readiness : Readiness protocol) (context : SourceSemantics.Context)
    {initial : Index} (first : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final, protocol.Relates first reached ∧ readiness.Ready context reached

def FaultTransition (readiness : Readiness protocol)
    {initial : Index} (first : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final, protocol.Relates first reached ∧ readiness.FaultReady reached

theorem ReadyTransition.forget {readiness : Readiness protocol} {context : SourceSemantics.Context}
    {initial final : Index} {first : protocol.State initial}
    (post : ReadyTransition readiness context first final) : Transition protocol first final := by
  obtain ⟨last, related, _⟩ := post
  exact ⟨last, related⟩

theorem FaultTransition.forget {readiness : Readiness protocol}
    {initial final : Index} {first : protocol.State initial}
    (post : FaultTransition readiness first final) : Transition protocol first final := by
  obtain ⟨last, related, _⟩ := post
  exact ⟨last, related⟩

structure ReadyReturn (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (context : SourceSemantics.Context) (scope : Scope) (canonical : Environment)
    (finalContext : SourceSemantics.Context) (finalScope : Scope) (finalCanonical : Environment)
    extends ReturnTo protocol scope canonical finalScope finalCanonical where
  restore_ready : ∀ {mapping world heap store}
    (reached : protocol.State ⟨finalScope, mapping, world, heap, store, finalCanonical⟩),
    readiness.Ready finalContext reached → readiness.Ready context (restore reached)

def ReadyReturn.refl (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (context : SourceSemantics.Context) (scope : Scope) (canonical : Environment) :
    ReadyReturn protocol readiness context scope canonical context scope canonical where
  toReturnTo := ReturnTo.refl protocol scope canonical
  restore_ready := fun _ ready => ready

def ReadyReturn.then {readiness : Readiness protocol}
    {context middleContext finalContext : SourceSemantics.Context}
    {scope middleScope finalScope : Scope} {canonical middleCanonical finalCanonical : Environment}
    (first : ReadyReturn protocol readiness context scope canonical middleContext middleScope middleCanonical)
    (last : ReadyReturn protocol readiness middleContext middleScope middleCanonical finalContext finalScope finalCanonical) :
    ReadyReturn protocol readiness context scope canonical finalContext finalScope finalCanonical where
  toReturnTo := ReturnTo.then first.toReturnTo last.toReturnTo
  restore_ready := fun reached ready => first.restore_ready (last.restore reached) (last.restore_ready reached ready)

def ReadyReturn.binding {readiness : Readiness protocol} (bindings : Bindings protocol)
    {source : TypedSource} (transfers : AllocationTransfers protocol readiness bindings source)
    {context nextContext : SourceSemantics.Context} {binder : TypedBinder}
    (extended : BinderExtends source.owner context binder nextContext)
    (scope : Scope) (canonical : Environment) (type : Ty) (value : Value) :
    ReadyReturn protocol readiness context scope canonical nextContext ((binder.id, type) :: scope) (value :: canonical) where
  toReturnTo := ReturnTo.binding bindings scope canonical binder.id type value
  restore_ready := fun {mapping world heap store} reached ready =>
    transfers.restore_ready (index := ⟨scope, mapping, world, heap, store, canonical⟩) extended reached ready

inductive ExpressionSlot : ForItemForm → ExpressionId → Prop where
  | initialized {binder id} (mono : binder.scheme.quantified = []) : ExpressionSlot (.letDecl binder (some id)) id
  | discard {id} : ExpressionSlot (.expression id) id

structure StaticSites
    (facts : SourceSemantics.Context → List ForItemForm → Prop)
    (itemFacts : SourceSemantics.Context → ForItemForm → Prop)
    (exprFacts : SourceSemantics.Context → ExpressionId → ExpressionNode → Prop)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  head : ∀ {context item rest}, facts context (item :: rest) → itemFacts context item
  expression : ∀ {context item id node}, itemFacts context item → ExpressionSlot item id →
    source.lookupExpression? id = some node → exprFacts context id node
  assignment : ∀ {context assignment operator rhs}, itemFacts context (.assignValue assignment operator rhs) →
    assignmentFacts context assignment operator rhs
  snapshot : ∀ {context assignment}, itemFacts context (.assignBitNot assignment) → snapshotFacts context assignment
  tail : ∀ {context nextContext item rest environment next before after},
    facts context (item :: rest) →
    Dynamic.ForItemExecutes program context evidence source environment before item nextContext next after →
    facts nextContext rest

theorem StaticSites.trivial (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    StaticSites (fun _ _ => True) (fun _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ _ => True) (fun _ _ => True) program evidence source := by
  constructor <;> intros <;> exact True.intro

structure SnapshotTransfers (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (validity : SourceSemantics.Context → Prop) (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) : Prop where
  ready : ∀ {initial final : Index} (first : protocol.State initial) (last : protocol.State final)
    {context : SourceSemantics.Context} {assignment : AssignmentResolution}
    {environment : Dynamic.Environment} {updated : Dynamic.Value},
    readiness.Ready context first → validity context → snapshotFacts context assignment →
    Dynamic.SourcePlaceSnapshotUpdate program context evidence source Dynamic.BitNotSnapshot
      environment initial.heap assignment.target updated final.heap →
    Dynamic.EnvironmentAgrees initial.heap context.locals environment →
    AdministrativePreserved initial.mapping initial.store final.mapping final.store → readiness.Ready context last

theorem SnapshotTransfers.trivial (protocol : Protocol.{u, v} Records) (validity : SourceSemantics.Context → Prop) (program : Program)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) :
    SnapshotTransfers protocol (Readiness.trivial protocol) validity (fun _ _ => True) program evidence source where
  ready := by intros; exact True.intro

inductive AssignmentResultAt {Records : Type v} (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (size : Nat) (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions} (functions : FunctionModel checked.catalog ambient)
    (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (faults : FunctionCalls.FaultRep) (scope : Scope) (writtenContext : Core.Context)
    (place : PlaceResolution) (operator : Syntax.ValueAssignOp) (rhs : ExpressionId)
    (environment : Dynamic.Environment) (canonical actual : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (next : Expr) (output : Ty) (value : Value) (finalStore : Store) : Prop where
  | fault {sourceSize : Nat} {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program sourceSize context evidence source environment before place operator rhs reason after)
      (same : value = .inLeft output (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after)
      (post : FaultTransition readiness initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩) :
      AssignmentResultAt protocol readiness size checked registry functions program context evidence source faults scope writtenContext place operator rhs
        environment canonical actual before store mapping world initial next output value finalStore
  | success {sourceSize remainingSize : Nat} {updated : Dynamic.Value} {after : Dynamic.Heap}
      {written : Store} {finalMap : LocationMap} {finalWorld : StoreTyping} {slots : Environment}
      (trace : SourceExecutionSize.SourcePlaceAssignment program sourceSize context evidence source (Dynamic.AssignmentValueApplies operator)
        environment before place rhs updated after)
      (heaps : CompatibleAmbientHeap.HeapRepresents checked registry functions finalMap finalWorld after written)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap written) (metadata : Dynamic.HeapMetadataExtend before after)
      (count : slots.length = 7)
      (typed : RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) writtenContext ambient.definitions)
      (post : ReadyTransition readiness context initial ⟨scope, finalMap, finalWorld, after, written, canonical⟩)
      (bounded : remainingSize < size)
      (remaining : EvaluationSize remainingSize (slots ++ actual) written (SourceCoreDataPlaces.shift 7 next) value finalStore) :
      AssignmentResultAt protocol readiness size checked registry functions program context evidence source faults scope writtenContext place operator rhs
        environment canonical actual before store mapping world initial next output value finalStore


def AssignmentPrefixPreservesAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context) (administrative : Core.Context)
    (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
  ∀ {updated after size},
    SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after → size ≤ budget →
    ∃ finalStore finalMap finalWorld slots,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      ReadyTransition readiness context initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (SourceCoreDataPlaces.shift 7 (next.rename ξ))

def AssignmentFaultPreservesAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    head.ReachableErrors registry faults →
  ∀ {reason after size},
    SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before
      assignment.target operator rhs reason after → size ≤ budget → ∀ next output,
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      FaultTransition readiness initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def AssignmentReflectsAt (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    (_facts : assignmentFacts context assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    readiness.Ready context initial →
    head.ReachableErrors registry faults →
  ∀ {next output value finalStore size},
    EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore → size ≤ budget →
    AssignmentResultAt protocol readiness size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore


variable {condition : Location → NativeFrame → Prop}
  {validity : SourceSemantics.Context → Prop} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {source : TypedSource} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {contextLocation : Location} {native : NativeFrame}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}


inductive ResultAtFor (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol) (condition : Location → NativeFrame → Prop)
    (validity : SourceSemantics.Context → Prop) (headerSize : Nat)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (program : Program) (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame) (type : Ty) (faults : FunctionCalls.FaultRep)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment)
    (index : Index) (initial : protocol.State index)
    (items : List ForItemForm) (value : Value) (finalStore : Store) : Prop where
  | continues {sourceSize remainingSize finalContext finalEnvironment after}
      (tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals
        contextLocation native continuation finalContext finalEnvironment after)
      (trace : SourceExecutionSize.ForItemsExecute program sourceSize context evidence source environment index.heap
        items finalContext finalEnvironment after)
      (maps : LocationMap.Extends index.mapping tail.mapping) (worlds : WorldExtends index.world tail.world)
      (preservation : AdministrativePreserved index.mapping index.store tail.mapping tail.store)
      (metadata : Dynamic.HeapMetadataExtend index.heap after)
      (related : protocol.Relates initial tail.state)
      (returnTo : Nonempty (ReadyReturn protocol readiness context index.scope index.canonical finalContext tail.scope tail.canonical))
      (ready : readiness.Ready finalContext tail.state)
      (remaining : EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore)
      (bounded : remainingSize ≤ headerSize) :
      ResultAtFor protocol readiness condition validity headerSize registry functions program source solved evidence administrative
        frame globals contextLocation native type faults continuation context environment index initial items value finalStore
  | fault {sourceSize finalContext reason token after finalMap finalWorld}
      (trace : SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment index.heap
        items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends index.mapping finalMap) (worlds : WorldExtends index.world finalWorld)
      (preservation : AdministrativePreserved index.mapping index.store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend index.heap after)
      (transition : FaultTransition readiness initial ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩) :
      ResultAtFor protocol readiness condition validity headerSize registry functions program source solved evidence administrative
        frame globals contextLocation native type faults continuation context environment index initial items value finalStore

variable {program : Program} {type : Ty} {faults : FunctionCalls.FaultRep}
  {index : Index} {initial : protocol.State index} {items : List ForItemForm} {value : Value} {finalStore : Store}


variable {readiness : Readiness protocol}

theorem ResultAtFor.prepend {headerSize childSize headSize : Nat}
    {nextEnvironment : Dynamic.Environment} {middle : Dynamic.Heap}
    {item : ForItemForm} {nextMap : LocationMap} {nextWorld : StoreTyping} {middleStore : Store}
    (middleState : protocol.State (index.extend nextMap nextWorld middle middleStore))
    (related : protocol.Relates initial middleState)
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment index.heap
      item context nextEnvironment middle)
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (preservation : AdministrativePreserved index.mapping index.store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap middle) (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor protocol readiness condition validity childSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context nextEnvironment
      (index.extend nextMap nextWorld middle middleStore) middleState items value finalStore) :
    ResultAtFor protocol readiness condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial
      (item :: items) value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata tailRelated returnReceipt ready remaining remainingBound =>
    obtain ⟨tailReturn⟩ := returnReceipt
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) (protocol.trans related tailRelated) ⟨tailReturn⟩ ready
      remaining (Nat.le_trans remainingBound bounded)
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata transition =>
    obtain ⟨reached, lastRelated, post⟩ := transition
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) ⟨reached, protocol.trans related lastRelated, post⟩


theorem ResultAtFor.prepend_binding {headerSize childSize headSize : Nat}
    {middleContext : SourceSemantics.Context} {nextEnvironment : Dynamic.Environment} {middle : Dynamic.Heap}
    {item : ForItemForm} {nextMap : LocationMap} {nextWorld : StoreTyping} {middleStore : Store}
    {binder : TypedBinder} {binderType : Ty} {binderValue : Value}
    (bindings : Bindings protocol)
    (transfers : AllocationTransfers protocol readiness bindings source)
    (extended : BinderExtends source.owner context binder middleContext)
    (middleState : protocol.State ((index.extend nextMap nextWorld middle middleStore).prepend binder.id binderType binderValue))
    (related : protocol.Relates initial middleState)
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment index.heap
      item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (preservation : AdministrativePreserved index.mapping index.store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap middle) (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor protocol readiness condition validity childSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation middleContext nextEnvironment
      ((index.extend nextMap nextWorld middle middleStore).prepend binder.id binderType binderValue) middleState
      items value finalStore) :
    ResultAtFor protocol readiness condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial
      (item :: items) value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata tailRelated returnReceipt ready remaining remainingBound =>
    obtain ⟨tailReturn⟩ := returnReceipt
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) (protocol.trans related tailRelated)
      ⟨ReadyReturn.then (ReadyReturn.binding bindings transfers extended index.scope index.canonical binderType binderValue) tailReturn⟩
      ready remaining (Nat.le_trans remainingBound bounded)
  | @fault sourceSize finalContext reason token after finalMap finalWorld trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata transition =>
    obtain ⟨reached, lastRelated, post⟩ := transition
    let restored := bindings.restore (index := ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩)
      (id := binder.id) (type := binderType) (value := binderValue) reached
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata)
      ⟨restored, protocol.trans related (protocol.trans lastRelated (bindings.restore_related (index := ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩)
          (id := binder.id) (type := binderType) (value := binderValue) reached)),
        transfers.restore_fault (index := ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩)
          (binder := binder) (type := binderType) (value := binderValue) reached post⟩

theorem ResultAtFor.toOriginal {headerSize : Nat}
    (result : ResultAtFor protocol readiness condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial items value finalStore) :
    ProtectedForHeader.Stateful.ResultAtFor protocol condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial items value finalStore := by
  cases result with
  | continues tail trace maps worlds preservation metadata related returnReceipt _ready remaining bounded =>
    obtain ⟨returnTo⟩ := returnReceipt
    exact .continues tail trace maps worlds preservation metadata related ⟨returnTo.toReturnTo⟩ remaining bounded
  | fault trace same matched heaps maps worlds preservation metadata transition =>
    exact .fault trace same matched heaps maps worlds preservation metadata transition.forget

theorem AssignmentResultAt.toOriginal {size : Nat} {checked : Checked}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {scope : Scope} {writtenContext : Core.Context} {place : PlaceResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩} {next : Expr} {output : Ty}
    (result : AssignmentResultAt protocol readiness size checked registry functions program context evidence source faults
      scope writtenContext place operator rhs environment canonical actual before store mapping world initial next output value finalStore) :
    ProtectedStateAssignmentHeadContracts.ResultAt protocol size checked registry functions program context evidence source faults
      scope writtenContext place operator rhs environment canonical actual before store mapping world initial next output value finalStore := by
  cases result with
  | fault trace same matched heaps maps worlds frame metadata post =>
    exact .fault trace same matched heaps maps worlds frame metadata post.forget
  | success trace heaps maps worlds frame metadata count typed post bounded remaining =>
    exact .success trace heaps maps worlds frame metadata count typed post.forget bounded remaining


section TrivialAssignments
variable (protocol : Protocol.{u, v} Records) {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
  (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
  (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat)

theorem assignment_prefix_trivial
    (meaning : ProtectedForHeader.Stateful.AssignmentPrefixPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative budget) :
    AssignmentPrefixPreservesAt protocol (Readiness.trivial protocol) (fun _ _ _ _ => True)
      functions (registry := registry) program evidence source certificate context administrative budget := by
  intro scope assignment operator rhs head _facts mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed initial _ready updated after size trace within
  obtain ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, finalTyped, post, agreement⟩ :=
    meaning head environments heaps locals agrees typed initial trace within
  obtain ⟨last, related⟩ := post
  exact ⟨finalStore, finalMap, finalWorld, slots, finalHeaps, maps, worlds, frame, metadata, count, finalTyped,
    ⟨last, related, True.intro⟩, agreement⟩

theorem assignment_fault_trivial
    (meaning : ProtectedForHeader.Stateful.AssignmentFaultPreservesAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget) :
    AssignmentFaultPreservesAt protocol (Readiness.trivial protocol) (fun _ _ _ _ => True)
      functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head _facts mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed initial _ready errors reason after size trace within next output
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    meaning head environments heaps locals agrees typed initial errors trace within next output
  obtain ⟨last, related⟩ := post
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps, maps, worlds, frame, metadata,
    last, related, True.intro⟩

theorem assignment_reflection_trivial
    (meaning : ProtectedForHeader.Stateful.AssignmentReflectsAt protocol functions (registry := registry)
      program evidence source certificate context administrative faults budget) :
    AssignmentReflectsAt protocol (Readiness.trivial protocol) (fun _ _ _ _ => True)
      functions (registry := registry) program evidence source certificate context administrative faults budget := by
  intro scope assignment operator rhs head _facts mapping world environment canonical actual before store actualContext ξ
    environments heaps locals agrees typed initial _ready errors next output value finalStore size completed within
  cases meaning head environments heaps locals agrees typed initial errors completed within with
  | fault trace same matched finalHeaps maps worlds frame metadata post =>
    obtain ⟨last, related⟩ := post
    exact .fault trace same matched finalHeaps maps worlds frame metadata ⟨last, related, True.intro⟩
  | success trace finalHeaps maps worlds frame metadata count finalTyped post bounded remaining =>
    obtain ⟨last, related⟩ := post
    exact .success trace finalHeaps maps worlds frame metadata count finalTyped ⟨last, related, True.intro⟩ bounded remaining

end TrivialAssignments
end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful.WithReady
