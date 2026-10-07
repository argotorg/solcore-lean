import Solcore.SourceSemantics.CoreLowering.RecursiveNamedHeaderContracts
import Solcore.SourceSemantics.CoreLowering.ProtectedStateLexicalGate
import Solcore.SourceSemantics.CoreLowering.ProtectedStateScopeReturn
import Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
import Solcore.SourceSemantics.CoreLowering.ProtectedStateAssignmentHeadContracts

/-! A live header tail keeps the actual state at its reached lexical prefix.
The static continuation and diagnostic receipts remain the existing generic
header receipts. Source-prefix and Core-continuation sizes stay independent;
an empty header can retain the entire Core derivation at equal size. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open CallableIndexedHistory (NativeFrame)
open ProtectedStateTransition
universe u v

variable {Records : Type v}

structure TailFor (protocol : Protocol.{u, v} Records)
    (condition : Location → NativeFrame → Prop) (validity : SourceSemantics.Context → Prop)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (registry : SourceCoreRawMetadata.Registry) (functions : FunctionModel values.checked.catalog ambient)
    (source : TypedSource) (solved : List SolvedRequirement) (evidence : Dynamic.EvidenceEnvironment)
    (administrative : Core.Context) (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (contextLocation : Location) (native : NativeFrame)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (context : SourceSemantics.Context) (environment : Dynamic.Environment) (heap : Dynamic.Heap)
    extends TypedForHeader.TailFor validity registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap where
  state : protocol.State ⟨scope, mapping, world, heap, store, canonical⟩
  gate : condition contextLocation native

variable {protocol : Protocol.{u, v} Records} {condition : Location → NativeFrame → Prop}
  {validity : SourceSemantics.Context → Prop} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {functions : FunctionModel values.checked.catalog ambient}
  {source : TypedSource} {solved : List SolvedRequirement} {evidence : Dynamic.EvidenceEnvironment}
  {administrative : Core.Context} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {contextLocation : Location} {native : NativeFrame}
  {continuation : SourceSemantics.Context → Scope → Expr → Prop}
  {context : SourceSemantics.Context} {environment : Dynamic.Environment} {heap : Dynamic.Heap}

/-- The tail's index is its actual stopping prefix, including source binders. -/
def TailFor.index (tail : TailFor protocol condition validity registry functions source solved evidence
    administrative frame globals contextLocation native continuation context environment heap) : Index :=
  ⟨tail.scope, tail.mapping, tail.world, heap, tail.store, tail.canonical⟩

/-- Observe the complete ordered records of this exact witness. -/
def TailFor.records (tail : TailFor protocol condition validity registry functions source solved evidence
    administrative frame globals contextLocation native continuation context environment heap) : Records :=
  protocol.records tail.state

/-- Apply the prefix's binder receipt to its actual later reached state. -/
theorem TailFor.return_reached {scope : Scope} {canonical : Environment}
    (tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (receipt : ReturnTo protocol scope canonical tail.scope tail.canonical)
    {mapping world after store}
    (reached : protocol.State ⟨tail.scope, mapping, world, after, store, tail.canonical⟩) :
    Transition protocol reached ⟨scope, mapping, world, after, store, canonical⟩ :=
  receipt.transition reached

/-- The original guarded view can forget the concrete state safely. -/
def TailFor.toProtected (tail : TailFor protocol condition validity registry functions source solved evidence
    administrative frame globals contextLocation native continuation context environment heap) :
    ProtectedForHeader.TailFor validity (entry := ProtectedStateTransition.entry protocol)
      registry functions source solved evidence administrative frame globals contextLocation native continuation
      context environment heap :=
  ⟨tail.toTailFor, ⟨tail.state⟩⟩

/-- Legacy callers recover their original guarded proposition field for field. -/
def TailFor.toLegacy {entry : ProtectedExpressionMeaning.Entry}
    (tail : TailFor (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) validity
      registry functions source solved evidence administrative frame globals contextLocation native continuation
      context environment heap) :
    ProtectedForHeader.TailFor validity (entry := entry) registry functions source solved evidence
      administrative frame globals contextLocation native continuation context environment heap :=
  ⟨tail.toTailFor, tail.state.down⟩

/-- Empty-prefix compatibility keeps the same actual typed prefix. -/
def TailFor.ofLegacy {entry : ProtectedExpressionMeaning.Entry}
    (tail : ProtectedForHeader.TailFor validity (entry := entry) registry functions source solved evidence
      administrative frame globals contextLocation native continuation context environment heap) :
    TailFor (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True) validity
      registry functions source solved evidence administrative frame globals contextLocation native continuation
      context environment heap :=
  ⟨tail.toTailFor, ⟨tail.installed⟩, trivial⟩

/-- The actual remaining grade may equal the inclusive fixed budget. -/
theorem TailFor.at_remaining {budget headerSize remainingSize : Nat}
    {meaning : Nat → SourceSemantics.Context → Scope → Expr → Prop}
    (tail : TailFor protocol condition validity registry functions source solved evidence
      administrative frame globals contextLocation native
      (RecursiveNamedHeaderContracts.ContinuationWithin budget meaning) context environment heap)
    (remainingBound : remainingSize ≤ headerSize) (headerBound : headerSize ≤ budget) :
    meaning remainingSize context tail.scope tail.code :=
  tail.certificate remainingSize (Nat.le_trans remainingBound headerBound)

/-- This is a static header/error receipt. It assumes no execution of the
syntactic continuation and uses the existing diagnostic policy exactly. -/
structure HeaderFor (layouts : SourceCoreAllocationLayouts.Prepared)
    (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (frame : SourceCoreCallableIndexedFrames.Layout) (globals : Nat)
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    (values : ValuesContext) (source : TypedSource)
    (certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate)
    (definitions : DataEnvironment) (administrative : Core.Context) (type : Ty)
    (continuation : SourceSemantics.Context → Scope → Expr → Prop)
    (policy : AssignmentDiagnosticPolicy) (registry : SourceCoreRawMetadata.Registry) (faults : FunctionCalls.FaultRep)
    (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm) (code : Expr) where
  tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates
    definitions administrative type continuation context scope items code
  errors : GenericForHeader.Tree.ErrorsFor policy registry faults tree

/-- Successful reflection carries its actual live tail. A header fault is
normalized to the caller's lexical index, retaining its reached state. -/
inductive ResultAtFor (protocol : Protocol.{u, v} Records) (condition : Location → NativeFrame → Prop)
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
      (returnTo : Nonempty (ReturnTo protocol index.scope index.canonical tail.scope tail.canonical))
      (remaining : EvaluationSize remainingSize tail.actual tail.store (tail.code.rename tail.embedding) value finalStore)
      (bounded : remainingSize ≤ headerSize) :
      ResultAtFor protocol condition validity headerSize registry functions program source solved evidence administrative
        frame globals contextLocation native type faults continuation context environment index initial items value finalStore
  | fault {sourceSize finalContext reason token after finalMap finalWorld}
      (trace : SourceExecutionSize.ForItemsFault program sourceSize context evidence source environment index.heap
        items finalContext reason after)
      (same : value = .inLeft (LocalLoop.controlType type) (.word token)) (matched : faults reason token)
      (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends index.mapping finalMap) (worlds : WorldExtends index.world finalWorld)
      (preservation : AdministrativePreserved index.mapping index.store finalMap finalStore)
      (metadata : Dynamic.HeapMetadataExtend index.heap after)
      (transition : Transition protocol initial ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩) :
      ResultAtFor protocol condition validity headerSize registry functions program source solved evidence administrative
        frame globals contextLocation native type faults continuation context environment index initial items value finalStore

variable {program : Program} {type : Ty} {faults : FunctionCalls.FaultRep}
  {index : Index} {initial : protocol.State index} {items : List ForItemForm} {value : Value} {finalStore : Store}

/-- Forget the transition suffix without changing either measured trace. -/
theorem ResultAtFor.toProtected {headerSize : Nat}
    (result : ResultAtFor protocol condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial
      items value finalStore) :
    RecursiveNamedHeaderContracts.ResultAtFor validity headerSize (entry := ProtectedStateTransition.entry protocol)
      registry functions program source solved evidence administrative frame globals contextLocation native type faults
      continuation context environment index.heap items index.mapping index.world index.store value finalStore := by
  cases result with
  | continues tail trace maps worlds preservation metadata _related _returnTo remaining bounded =>
    exact .continues tail.toProtected trace maps worlds preservation metadata remaining bounded
  | fault trace same matched heaps maps worlds preservation metadata _transition =>
    exact .fault trace same matched heaps maps worlds preservation metadata

/-- The nil receipt keeps the entire original continuation at equal size. -/
theorem ResultAtFor.nil {size : Nat}
    (tail : TailFor protocol condition validity registry functions source solved evidence administrative frame globals
      contextLocation native continuation context environment heap)
    (evaluated : EvaluationSize size tail.actual tail.store (tail.code.rename tail.embedding) value finalStore) :
    ResultAtFor protocol condition validity size registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment tail.index tail.state [] value finalStore :=
  .continues tail .nil (.refl _) (.refl _) (.refl _ _) (.refl _) (protocol.refl tail.state) ⟨ReturnTo.refl protocol tail.scope tail.canonical⟩ evaluated (Nat.le_refl _)

/-- The shared assignment child must return its genuine reached witness along
with the existing seven slots and actual continuation agreement. Projected
assignment consumers must discharge this separate primitive proof obligation. -/
def AssignmentPrefixPreservesAt (protocol : Protocol.{u, v} Records)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context) (administrative : Core.Context)
    (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
  ∀ {updated after size},
    SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before assignment.target rhs updated after → size ≤ budget →
    ∃ finalStore finalMap finalWorld slots,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      slots.length = 7 ∧ RuntimeEnvironmentHasTypes finalWorld (slots ++ actual) (head.writtenContext actualContext) ambient.definitions ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ ∧
      ∀ next output, ContinuationAgreement actual store ((head.emit next output).rename ξ)
        (slots ++ actual) finalStore (SourceCoreDataPlaces.shift 7 (next.rename ξ))


/-- A successful prefix with no source binder passes its actual reached state
into the suffix, then retains the actual fault or live continuation witness. -/
theorem ResultAtFor.prepend {headerSize childSize headSize : Nat}
    {middleContext : SourceSemantics.Context} {nextEnvironment : Dynamic.Environment} {middle : Dynamic.Heap}
    {item : ForItemForm} {nextMap : LocationMap} {nextWorld : StoreTyping} {middleStore : Store}
    (middleState : protocol.State (index.extend nextMap nextWorld middle middleStore))
    (related : protocol.Relates initial middleState)
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment index.heap
      item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (preservation : AdministrativePreserved index.mapping index.store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap middle) (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor protocol condition validity childSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation middleContext nextEnvironment
      (index.extend nextMap nextWorld middle middleStore) middleState items value finalStore) :
    ResultAtFor protocol condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial
      (item :: items) value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata tailRelated returnReceipt remaining remainingBound =>
    obtain ⟨tailReturn⟩ := returnReceipt
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) (protocol.trans related tailRelated) ⟨tailReturn⟩
      remaining (Nat.le_trans remainingBound bounded)
  | fault trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata transition =>
    obtain ⟨reached, lastRelated⟩ := transition
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) ⟨reached, protocol.trans related lastRelated⟩

/-- The continuation retains its new binder. A fault removes the binder from
its actual reached witness and preserves any records produced in the suffix. -/
theorem ResultAtFor.prepend_binding {headerSize childSize headSize : Nat}
    {middleContext : SourceSemantics.Context} {nextEnvironment : Dynamic.Environment} {middle : Dynamic.Heap}
    {item : ForItemForm} {nextMap : LocationMap} {nextWorld : StoreTyping} {middleStore : Store}
    {id : Resolved.LocalId} {binderType : Ty} {binderValue : Value}
    (bindings : Bindings protocol)
    (middleState : protocol.State ((index.extend nextMap nextWorld middle middleStore).prepend id binderType binderValue))
    (related : protocol.Relates initial middleState)
    (head : SourceExecutionSize.ForItemExecutes program headSize context evidence source environment index.heap
      item middleContext nextEnvironment middle)
    (maps : LocationMap.Extends index.mapping nextMap) (worlds : WorldExtends index.world nextWorld)
    (preservation : AdministrativePreserved index.mapping index.store nextMap middleStore)
    (metadata : Dynamic.HeapMetadataExtend index.heap middle) (bounded : childSize ≤ headerSize)
    (tail : ResultAtFor protocol condition validity childSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation middleContext nextEnvironment
      ((index.extend nextMap nextWorld middle middleStore).prepend id binderType binderValue) middleState
      items value finalStore) :
    ResultAtFor protocol condition validity headerSize registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index initial
      (item :: items) value finalStore := by
  cases tail with
  | continues tail trace lastMaps lastWorlds lastFrame lastMetadata tailRelated returnReceipt remaining remainingBound =>
    obtain ⟨tailReturn⟩ := returnReceipt
    exact .continues tail (.cons head trace) (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) (protocol.trans related tailRelated)
      ⟨ReturnTo.then (ReturnTo.binding bindings index.scope index.canonical id binderType binderValue) tailReturn⟩
      remaining (Nat.le_trans remainingBound bounded)
  | @fault sourceSize finalContext reason token after finalMap finalWorld trace same matched heaps lastMaps lastWorlds lastFrame lastMetadata transition =>
    have restored := bindings.restore_reached (reached := ⟨index.scope, finalMap, finalWorld, after, finalStore, index.canonical⟩)
      (id := id) (type := binderType) (value := binderValue) middleState transition
    obtain ⟨reached, lastRelated⟩ := restored
    exact .fault (.tail head trace) same matched heaps (maps.trans lastMaps) (worlds.trans lastWorlds)
      (preservation.trans lastFrame) (metadata.trans lastMetadata) ⟨reached, protocol.trans related lastRelated⟩

/-- Legacy reflection keeps its original trace and guarded live tail. -/
theorem ResultAtFor.toLegacy {entry : ProtectedExpressionMeaning.Entry} {headerSize : Nat}
    {initial : (ProtectedStateTransition.Lexical.legacyProtocol entry).State index}
    (result : ResultAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry) (fun _ _ => True)
      validity headerSize registry functions program source solved evidence administrative frame globals
      contextLocation native type faults continuation context environment index initial items value finalStore) :
    RecursiveNamedHeaderContracts.ResultAtFor validity headerSize (entry := entry) registry functions program source solved evidence
      administrative frame globals contextLocation native type faults continuation context environment index.heap
      items index.mapping index.world index.store value finalStore := by
  cases result with
  | continues tail trace maps worlds preservation metadata _related _returnTo remaining bounded =>
    exact .continues tail.toLegacy trace maps worlds preservation metadata remaining bounded
  | fault trace same matched heaps maps worlds preservation metadata _transition =>
    exact .fault trace same matched heaps maps worlds preservation metadata

/-- Actual first-fault assignment receipt. Projected child producers remain an
explicit primitive obligation, with the original source and native grades. -/
def AssignmentFaultPreservesAt (protocol : Protocol.{u, v} Records)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    head.ReachableErrors registry faults →
  ∀ {reason after size},
    SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before
      assignment.target operator rhs reason after → size ≤ budget → ∀ next output,
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((head.emit next output).rename ξ) (.inLeft output (.word token)) finalStore ∧
      faults reason token ∧ CompatibleAmbientHeap.HeapRepresents values.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- Actual reflected assignment prefix or first fault, using the existing
seven native slots and the original strict continuation bound. -/
def AssignmentReflectsAt (protocol : Protocol.{u, v} Records)
    {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions}
    (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
    (program : Program) (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource)
    (certificate : GenericExpressionMeaning.Certificate) (context : SourceSemantics.Context)
    (administrative : Core.Context) (faults : FunctionCalls.FaultRep) (budget : Nat) : Prop :=
  ∀ {scope assignment operator rhs}
    (head : GenericAssignmentStatements.Head values source context certificate scope administrative ambient.definitions assignment operator rhs)
    {mapping world environment canonical actual before store actualContext ξ},
    DataHeap.EnvRepresents (CompatibleEquality.storageCatalog values.checked.catalog)
      mapping world administrative scope environment canonical ambient.definitions →
    CompatibleAmbientHeap.HeapRepresents values.checked registry functions mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment → EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    head.ReachableErrors registry faults →
  ∀ {next output value finalStore size},
    EvaluationSize size actual store ((head.emit next output).rename ξ) value finalStore → size ≤ budget →
    ProtectedStateAssignmentHeadContracts.ResultAt protocol size values.checked registry functions program context evidence source faults
      scope (head.writtenContext actualContext) assignment.target operator rhs environment canonical actual before store mapping world
      initial (next.rename ξ) output value finalStore

end Solcore.SourceSemantics.CoreLowering.ProtectedForHeader.Stateful
