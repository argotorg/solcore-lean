import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CallEvidence
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateStatements
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.GenericImperativeMatchTree
import Solcore.SourceSemantics.CoreLowering.GenericForHeaderContinuationMap
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.ForIterations
import Solcore.SourceSemantics.CoreLowering.GenericImperativeForMatchEmbedding
import Solcore.SourceSemantics.CoreLowering.ForSourceViews
import Solcore.SourceSemantics.CoreLowering.CompatibleBitNotStatementComposition
import Solcore.SourceSemantics.CoreLowering.ReachableMatchContinuationMeaning
import Solcore.SourceSemantics.Dynamic.WholeLanguagePreservation

/-!
# Protected contracts: for headers on the state

Control and readiness of `for` headers on the protected state, catalog goals and source sites.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderControl
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderReady
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
  | projectedBitNotKey {assignment id}
      (member : id ∈ DataPlaceKeyOrder.sourceKeys assignment.target.projections) :
      ExpressionSlot (.assignBitNot assignment) id

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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogGoals
/-! One static CatalogSites goal family. Statement goals carry the actual
reached state; initializer goals retain the same ordered header tree with an
actual loop continuation. Source and native grades remain independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedImperativeFor (Position)
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)

abbrev PreservingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => AtMost budget (fun size => ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => ProtectedStateTransition.Lexical.Gated.PreservesAtFor protocol conditionGate (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => ProtectedStateTransition.Lexical.Gated.ReflectsAtFor protocol conditionGate (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWith protocol conditionGate (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful

namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.CatalogCompatibility
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
variable {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frameLayout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {entry : ProtectedExpressionMeaning.Entry} {validity : SourceSemantics.Context → Prop}
  {size : Nat} {scope : Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {condition : ExpressionId} {post : List ForItemForm}

/-- The legacy flow observes the actual producer's result. -/
theorem preserves
    (actual : ProtectedStateTransition.Lexical.Gated.PreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.PreservesAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _post⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Reflection retains its independent source grade. -/
theorem reflects
    (actual : ProtectedStateTransition.Lexical.Gated.ReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code) :
    RecursiveNamedLoopContracts.ReflectsAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) mode statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, _post⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical⟩

/-- Header continuation observation uses the actual reached loop entry. -/
theorem loop_preserves
    (actual : ProtectedFor.Body.Stateful.LoopPreservesAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) condition post statements expected type code) :
    RecursiveNamedForContracts.LoopPreservesAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped installed trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached, _related⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached.down⟩

/-- The reached observer is extracted from the actual native loop result. -/
theorem loop_reflects
    (actual : ProtectedFor.Body.Stateful.LoopReflectsAtFor (ProtectedStateTransition.Lexical.legacyProtocol entry)
      (fun _ _ => True) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative) (scope := scope) condition post statements expected type code) :
    RecursiveNamedForContracts.LoopReflectsAtFor (entry := entry) functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frameLayout) (globals := globals) (administrative := administrative)
      (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical runtime before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped installed evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached, _related⟩ :=
    actual valid environments heaps locals agrees typed reference read unmapped ⟨installed⟩ trivial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached.down⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.CatalogCompatibility
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
/-! Ready catalog positions retain the actual statement post. An initializer
keeps the original ordered header Tree and requires genuine pending loop facts
before its actual loop continuation. Source and native grades stay independent. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedImperativeFor (Position)
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
universe u v
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (readiness : RecursiveNamedLexicalContracts.Stateful.WithReady.Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)

abbrev PreservingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev ReflectingHeaderWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (items : List ForItemForm)
    (condition : ExpressionId) (post : List ForItemForm) (statements : List StatementId)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  initializerFacts context items condition post statements expected →
  ∃ tree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
    type (fun context scope code => loopFacts context condition post statements expected ∧ AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity) functions program evidence size (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) condition post statements expected type code)) context scope items code,
    GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults tree

abbrev PreservesAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => AtMost budget (fun size => Control.Stateful.WithReady.PreservesAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => PreservingHeaderWith protocol readiness conditionGate loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

abbrev ReflectsAtWith (diagnosticPolicy : AssignmentDiagnosticPolicy) (context : SourceSemantics.Context) (scope : Scope) (position : Position)
    (expected : TypeSystem.Ty) (type : Ty) (code : Expr) : Prop :=
  match position with
  | .statements mode statements => Below budget (fun size => Control.Stateful.WithReady.ReflectsAtWith protocol readiness conditionGate facts (validity := validity) functions program evidence (registry := registry) (source := source)
      (context := context) (scope := scope) (faults := faults)  (frameLayout := frame)
      (globals := globals) (administrative := administrative) size mode statements expected type code)
  | .initializers items condition post statements => ReflectingHeaderWith protocol readiness conditionGate loopFacts initializerFacts (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates) functions program evidence budget
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source)
      (administrative := administrative) (registry := registry) (faults := faults)
      context scope items condition post statements expected type code

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedImperativeFor.Stateful.WithReady

/-! Pointwise assignment prefixes keep the real seven-slot continuation and
its exact successful or fault state. Source facts stay independent of native
projection; high producers establish them from the actual parent statement. -/
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady.Assignment
abbrev ResultAt := @ProtectedForHeader.Stateful.WithReady.AssignmentResultAt
abbrev AssignmentPrefixPreservesAt := @ProtectedForHeader.Stateful.WithReady.AssignmentPrefixPreservesAt
abbrev AssignmentFaultPreservesAt := @ProtectedForHeader.Stateful.WithReady.AssignmentFaultPreservesAt
abbrev AssignmentReflectsAt := @ProtectedForHeader.Stateful.WithReady.AssignmentReflectsAt
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady.Assignment

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v

/-- Authentic initializer facts follow the original static item contexts.
The done field supplies the pending loop facts at the actual nil site. -/
structure InitializerSites
    (initializerFacts : SourceSemantics.Context → List ForItemForm → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
    (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
    (source : TypedSource) : Prop where
  done : ∀ {context condition post statements expected},
    initializerFacts context [] condition post statements expected → loopFacts context condition post statements expected
  absent : ∀ {context next binder rest condition post statements expected},
    initializerFacts context (.letDecl binder none :: rest) condition post statements expected →
    BinderExtends source.owner context binder next →
    initializerFacts next rest condition post statements expected
  initialized : ∀ {context next binder expression rest condition post statements expected},
    initializerFacts context (.letDecl binder (some expression) :: rest) condition post statements expected →
    BinderExtends source.owner context binder next →
    initializerFacts next rest condition post statements expected
  discard : ∀ {context expression rest condition post statements expected},
    initializerFacts context (.expression expression :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected
  assignment : ∀ {context resolution operator rhs rest condition post statements expected},
    initializerFacts context (.assignValue resolution operator rhs :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected
  snapshot : ∀ {context resolution rest condition post statements expected},
    initializerFacts context (.assignBitNot resolution :: rest) condition post statements expected →
    initializerFacts context rest condition post statements expected

/-- The exact Source assignment and snapshot site are projected from the
actual typed parent, independently of its compiler/native representation. -/
structure AssignmentSites
    (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
    (assignmentFacts : SourceSemantics.Context → AssignmentResolution → Syntax.ValueAssignOp → ExpressionId → Prop)
    (snapshotFacts : SourceSemantics.Context → AssignmentResolution → Prop)
    (source : TypedSource) : Prop where
  assignment : ∀ {context id expected node resolution operator rhs}, headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .assignValue resolution operator rhs →
    assignmentFacts context resolution operator rhs
  snapshot : ∀ {context id expected node resolution}, headFacts context id expected →
    source.lookupStatement? id = some node → node.form = .assignBitNot resolution →
    snapshotFacts context resolution

/-- Successful bit-not transfer uses the real Source snapshot update and the
actual written state. Fault rows use the shared actual administrative rule. -/
abbrev SnapshotTransfers := @ProtectedForHeader.Stateful.WithReady.SnapshotTransfers

namespace Lexical
variable {Records : Type v} (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (condition : Location → CallableIndexedHistory.NativeFrame → Prop)
  (facts : SourceSemantics.Context → Bool → List StatementId → TypeSystem.Ty → Prop)
  {values : TypedLexicalWhile.ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient) {registry : SourceCoreRawMetadata.Registry}
  (program : Program) (evidence : Dynamic.EvidenceEnvironment) {faults : FunctionCalls.FaultRep}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat} {administrative : Core.Context}
  {scope : SourceCoreLocalCell.Scope} {mode : Bool} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr} {size : Nat}

theorem preserves (validity : SourceSemantics.Context → Prop)
    (meaning : PreservesAtFor protocol readiness condition facts functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith protocol readiness condition facts
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code := by
  intro valid static mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome finalContext
    environments heaps locals agrees typed reference read unmapped initial gate ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    meaning valid static environments heaps locals agrees typed reference read unmapped initial gate ready trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, post⟩

theorem reflects (validity : SourceSemantics.Context → Prop)
    (meaning : ReflectsAtFor protocol readiness condition facts functions program evidence validity size
      (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (scope := scope) mode statements expected type code) :
    RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith protocol readiness condition facts
      functions program evidence validity size (source := source) (context := context) (registry := registry) (faults := faults)
      (frameLayout := frame) (globals := globals) (administrative := administrative) (scope := scope) mode statements expected type code := by
  intro valid static mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial gate ready evaluated
  obtain ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, lexical, post⟩ :=
    meaning valid static environments heaps locals agrees typed reference read unmapped initial gate ready evaluated
  exact ⟨sourceSize, finalContext, outcome, after, finalMap, finalWorld, trace, TypedLexicalWhile.FlowRep.of_lexical represented,
    finalHeaps, maps, worlds, frame, metadata, lexical, post⟩
end Lexical
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {registry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}

/-- The three catalog-specific heads retain their authentic compiler receipts
and only their recursive child goals. A recipe contains no completed head or
body execution proof. The Source parent facts and actual input state are
consumed separately by its pointwise producer. -/
inductive HeadRecipe (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | whileLoop {context scope id node condition conditionNode statements expected type conditionCode loopCode selfReason}
      (found : source.lookupStatement? id = some node) (form : node.form = .whileLoop condition statements)
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type loopCode)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.whileLoop type conditionCode loopCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type loopCode) :
      HeadRecipe goal context scope id expected type (LocalLoop.whileLoop type conditionCode loopCode selfReason)
  | forLoop {context scope id node initializer condition post statements expected type initialCode}
      (found : source.lookupStatement? id = some node) (form : node.form = .forLoop initializer condition post statements)
      (child : goal context scope (.initializers initializer condition post statements) expected type initialCode) :
      HeadRecipe goal context scope id expected type initialCode
  | matchWith {context scope id node resolution scrutineeNode expected type matched selfReason control caseFacts}
      (found : source.lookupStatement? id = some node) (form : node.form = .matchWith resolution)
      (scrutineeFound : source.lookupExpression? resolution.scrutinee = some scrutineeNode)
      (scrutineeTyped : ExpressionHasType source context resolution.scrutinee scrutineeNode.type)
      (casesTyped : MatchCasesHaveType source control context scrutineeNode.type resolution.cases caseFacts)
      (defaultTyped : ∀ statements, resolution.defaultBody = some statements →
        ∃ finalContext facts, StatementsHaveType source control context statements finalContext facts)
      (compilation : SourceCoreCompatibleDataMatches.Context)
      (sameValues : compilation.values = values) (sameDefinitions : compilation.definitions = ambient.definitions)
      (allocator : compilation.sourceCells = some (SourceCoreCallableIndexedAllocationFrames.allocator frame globals
        (layouts.allocatorAt owner active onError)))
      (requests : List GenericMatchChildren.Request)
      (receipt : CompatibleMatchCertificates.Certificate compilation source scope id resolution type selfReason
        (certificates context) (GenericMatchChildren.Occurs requests) matched)
      (ordinary : CompatibleMatchSelectionPrefix.Ordinary receipt)
      (children : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
          childContext request.scope (.statements false request.statements) expected type request.code)
      (catalog : SignatureCatalogWellFormed values.checked.signatures)
      (patternContext : GenericImperativeMatch.Tree.MatchContextFields compilation context)
      (child : ∀ request, request ∈ requests → ∀ childContext,
        GenericMatchChildren.ScopedContextFor source context (resolution.hiddenScrutinee :: scope.map Prod.fst) scrutineeNode.type resolution.cases resolution.defaultBody request childContext →
        goal childContext request.scope (.statements false request.statements) expected type request.code) :
      HeadRecipe goal context scope id expected type matched

/-- A completed initializer keeps the original condition, body, and ordered
post-header compiler receipts. Its body premise is the strict recursive goal;
the pending loop Source facts are supplied at its actual normalized context. -/
inductive LoopRecipe (diagnosticPolicy : AssignmentDiagnosticPolicy)
    (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop) :
    SourceSemantics.Context → Scope → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Ty → Expr → Prop where
  | mk {context scope condition conditionNode post statements expected type conditionCode bodyCode postCode selfReason}
      (conditionFound : source.lookupExpression? condition = some conditionNode)
      (conditionType : conditionNode.type = .bool)
      (conditionTree : certificates context scope condition ⟨.bool, conditionCode⟩)
      (loopBody : GenericImperativeMatch.Tree layouts owner active frame globals onError values source expressionSyntax certificates ambient.definitions administrative
        context scope (.statements false statements) expected type bodyCode)
      (postTree : GenericForHeader.Tree layouts owner active frame globals onError values source certificates ambient.definitions administrative
        type (TypedForHeader.Fallthrough type) context scope post postCode)
      (postErrors : GenericForHeader.Tree.ErrorsFor diagnosticPolicy registry faults postTree)
      (nativeTyped : HasType (SourceCoreLocalCell.coreContext scope ++ administrative)
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason) (LocalLoop.resultType type) ambient.definitions)
      (child : goal context scope (.statements false statements) expected type bodyCode) :
      LoopRecipe diagnosticPolicy goal context scope condition post statements expected type
        (LocalLoop.iterate type conditionCode bodyCode postCode selfReason)
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedBoundedContracts (Below)
open RecursiveNamedHeaderContracts (AtMost)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records) (readiness : Readiness protocol)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  (headFacts : SourceSemantics.Context → StatementId → TypeSystem.Ty → Prop)
  (loopFacts : SourceSemantics.Context → ExpressionId → List ForItemForm → List StatementId → TypeSystem.Ty → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource} {expressionSyntax : ExpressionId → Prop}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} (validity : SourceSemantics.Context → Prop) (budget : Nat)
  (goal : SourceSemantics.Context → Scope → Position → TypeSystem.Ty → Ty → Expr → Prop)

def PreservingHeads : Prop :=
  ∀ {context scope id expected type code},
    HeadRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) goal context scope id expected type code →
    AtMost budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadPreservesAtWith protocol readiness conditionGate headFacts
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code)

def ReflectingHeads : Prop :=
  ∀ {context scope id expected type code},
    HeadRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) goal context scope id expected type code →
    Below budget (fun size => RecursiveNamedImperativeFor.Control.Stateful.WithReady.HeadReflectsAtWith protocol readiness conditionGate headFacts
      (validity := validity) functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) id expected type code)

def PreservingLoops (diagnosticPolicy : AssignmentDiagnosticPolicy) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults)
      diagnosticPolicy goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol readiness conditionGate (validity := validity)
      functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)

def ReflectingLoops (diagnosticPolicy : AssignmentDiagnosticPolicy) : Prop :=
  ∀ {context scope condition post statements expected type code},
    LoopRecipe (administrative := administrative) (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (values := values) (source := source) (expressionSyntax := expressionSyntax)
      (certificates := certificates) (ambient := ambient) (registry := registry) (faults := faults)
      diagnosticPolicy goal context scope condition post statements expected type code →
    loopFacts context condition post statements expected →
    AtMost budget (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol readiness conditionGate (validity := validity)
      functions program evidence (source := source) (context := context) (registry := registry)
      (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals)
      size (scope := scope) condition post statements expected type code)
end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady


namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
open TypedLexicalWhile (Scope ValuesContext)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {values : ValuesContext} {source : TypedSource} {context : SourceSemantics.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {administrative : Core.Context}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {validity : SourceSemantics.Context → Prop} {size : Nat} {scope : Scope}
  {condition : ExpressionId} {post : List ForItemForm} {statements : List StatementId}
  {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

theorem loop_preserves_of_true (meaning : ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped initial guarded _ready trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial reached⟩

theorem loop_preserves_forget_true (meaning : ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.LoopPreservesAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before after store ξ contextLocation native outcome
    environments heaps locals agrees typed reference read unmapped initial guarded trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded True.intro trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, reached.forget⟩

theorem loop_reflects_of_true (meaning : ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial guarded _ready evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, Reached.of_trivial reached⟩

theorem loop_reflects_forget_true (meaning : ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code) :
    ProtectedFor.Body.Stateful.LoopReflectsAtFor protocol conditionGate functions program evidence validity size
    (source := source) (context := context) (registry := registry) (faults := faults) (administrative := administrative) (frameLayout := frame) (globals := globals) (scope := scope) condition post statements expected type code := by
  intro valid mapping world actualContext environment canonical actual before store finalStore ξ contextLocation native value
    environments heaps locals agrees typed reference read unmapped initial guarded evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached⟩ :=
    meaning valid environments heaps locals agrees typed reference read unmapped initial guarded True.intro evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, reached.forget⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady

namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload
open TypedLexicalWhile (Scope ValuesContext)
open TypedImperativeFor (Position)
open RecursiveNamedLexicalContracts.Stateful.WithReady
open ProtectedStateTransition
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (conditionGate : Location → CallableIndexedHistory.NativeFrame → Prop)
  {administrative : Core.Context} {layouts : SourceCoreAllocationLayouts.Prepared}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
  {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error}
  {values : ValuesContext} {source : TypedSource}
  {certificates : SourceSemantics.Context → GenericExpressionMeaning.Certificate}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  (functions : FunctionModel values.checked.catalog ambient)
  {registry : SourceCoreRawMetadata.Registry} (program : Program) (evidence : Dynamic.EvidenceEnvironment)
  {faults : FunctionCalls.FaultRep} {validity : SourceSemantics.Context → Prop} {budget : Nat}
  {diagnosticPolicy : AssignmentDiagnosticPolicy} {context : SourceSemantics.Context} {scope : Scope}
  {position : Position} {expected : TypeSystem.Ty} {type : Ty} {code : Expr}

theorem preserves_goal_forget_true (meaning : RecursiveNamedImperativeFor.Stateful.WithReady.PreservesAtWith protocol (Readiness.trivial protocol) conditionGate
      (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code) :
    RecursiveNamedImperativeFor.Stateful.PreservesAtWith protocol conditionGate
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code := by
  cases position with
  | statements mode statements =>
    intro size within
    exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.PreservesAtWith.forget_true (protocol := protocol) (condition := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) (meaning size within)
  | initializers items condition post statements =>
    obtain ⟨tree, errors⟩ := meaning True.intro
    let convert := fun {nextContext nextScope nextCode} (certificate : True ∧ RecursiveNamedHeaderContracts.AtMost budget
      (fun size => ProtectedFor.Body.Stateful.WithReady.LoopPreservesAtFor protocol (Readiness.trivial protocol) conditionGate
        (validity := validity) functions program evidence size (source := source) (context := nextContext)
        (scope := nextScope) (registry := registry) (faults := faults) (frameLayout := frame)
        (globals := globals) (administrative := administrative) condition post statements expected type nextCode)) =>
      fun size within => loop_preserves_forget_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
        (certificate.2 size within)
    exact ⟨tree.mapContinuation convert, errors.mapContinuation convert⟩

theorem reflects_goal_forget_true (meaning : RecursiveNamedImperativeFor.Stateful.WithReady.ReflectsAtWith protocol (Readiness.trivial protocol) conditionGate
      (fun _ _ _ _ => True) (fun _ _ _ _ _ => True) (fun _ _ _ _ _ _ => True)
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code) :
    RecursiveNamedImperativeFor.Stateful.ReflectsAtWith protocol conditionGate
      (validity := validity) (diagnosticPolicy := diagnosticPolicy) (certificates := certificates)
      (layouts := layouts) (owner := owner) (active := active) (frame := frame) (globals := globals)
      (onError := onError) (source := source) (administrative := administrative) (registry := registry) (faults := faults)
      functions program evidence budget context scope position expected type code := by
  cases position with
  | statements mode statements =>
    intro size within
    exact RecursiveNamedImperativeFor.Control.Stateful.WithReady.ReflectsAtWith.forget_true (protocol := protocol) (condition := conditionGate)
      (functions := functions) (program := program) (evidence := evidence) (meaning size within)
  | initializers items condition post statements =>
    obtain ⟨tree, errors⟩ := meaning True.intro
    let convert := fun {nextContext nextScope nextCode} (certificate : True ∧ RecursiveNamedHeaderContracts.AtMost budget
      (fun size => ProtectedFor.Body.Stateful.WithReady.LoopReflectsAtFor protocol (Readiness.trivial protocol) conditionGate
        (validity := validity) functions program evidence size (source := source) (context := nextContext)
        (scope := nextScope) (registry := registry) (faults := faults) (frameLayout := frame)
        (globals := globals) (administrative := administrative) condition post statements expected type nextCode)) =>
      fun size within => loop_reflects_forget_true (protocol := protocol) (conditionGate := conditionGate) (functions := functions) (program := program) (evidence := evidence)
        (certificate.2 size within)
    exact ⟨tree.mapContinuation convert, errors.mapContinuation convert⟩

theorem InitializerSites.trivial (source : TypedSource) :
    InitializerSites (fun _ _ _ _ _ _ => True) (fun _ _ _ _ _ => True) source :=
  ⟨fun _ => True.intro, fun _ _ => True.intro, fun _ _ => True.intro,
    fun _ => True.intro, fun _ => True.intro, fun _ => True.intro⟩

theorem AssignmentSites.trivial (source : TypedSource) :
    AssignmentSites (fun _ _ _ => True) (fun _ _ _ _ => True) (fun _ _ => True) source :=
  ⟨fun _ _ _ => True.intro, fun _ _ _ => True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeCatalogReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
/-! Genuine imperative Source syntax supplies facts at actual statement and
expression sites. Tail facts follow the executed Source fallthrough prefix;
stopped branches need no facts for an unexecuted suffix. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
open Frontend SourceInference GenericImperativeMatch
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def Facts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId)
    (expected : TypeSystem.Ty) : Prop :=
  Syntax source expressionSyntax context (.statements mode statements) expected

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Facts source expressionSyntax context mode (id :: rest) expected

abbrev ExpressionFacts := ProtectedStateLexicalSourceSites.ExpressionFacts

theorem expression {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {child : ExpressionId} {node : ExpressionNode}
    (facts : HeadFacts source expressionSyntax context id expected)
    (slot : ExpressionSlot source id child)
    (found : source.lookupExpression? child = some node) :
    ExpressionFacts source context child node := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact ProtectedStateLexicalSourceSites.expression ⟨mode, rest, typed⟩ slot found
  all_goals cases slot <;> simp_all [ExpressionFacts, ProtectedStateLexicalSourceSites.ExpressionFacts]

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {statements : List StatementId}
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block statements) :
    Facts source expressionSyntax context false statements expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact .body (ProtectedStateLexicalSourceSites.block ⟨mode, rest, typed⟩ found form)
  all_goals simp_all [Facts]

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Facts source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, typedSyntax⟩ := facts
  cases typedSyntax
  case body typed =>
    exact .body (ProtectedStateLexicalSourceSites.branch boolean ⟨mode, rest, typed⟩ found form)
  all_goals cases boolean <;> simp_all [Facts]

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (unique : NodeOccurrencesUnique source)
    (typedSyntax : Facts source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Facts source expressionSyntax nextContext mode rest expected := by
  cases typedSyntax with
  | body typed =>
    exact .body (ProtectedStateLexicalSourceSites.tail unique typed found notTail executed)
  | uninitialized found form declaration monomorphic extended ordinary remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letUninitialized unique (lookupStatement?_sound found) form executed
    exact Dynamic.BinderExtends.functional extended actualExtension ▸ remaining
  | initialized found form declaration monomorphic extended ordinary initializerFound sourceType initializerTyped initializerSyntax remaining =>
    obtain ⟨actualExtension, _⟩ := ScalarStatementViews.letInitialized unique (lookupStatement?_sound found) form monomorphic executed
    exact Dynamic.BinderExtends.functional extended actualExtension ▸ remaining
  | discard found form guard sourceType expressionFound typed value remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.expression unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | block found form sourceType inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | ifThen found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.ifThen unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | breaking found form =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.breaking unique (lookupStatement?_sound found) form executed
    cases impossible
  | continuing found form =>
    obtain ⟨_, impossible, _⟩ := ScalarStatementViews.continuing unique (lookupStatement?_sound found) form executed
    cases impossible
  | whileLoop found form conditionFound conditionType typed conditionSyntax loopBody remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.whileLoop unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | assign found form sourceTyped writable rightTyped profile children remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.assignValue unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | forLoop found form sourceType initial remaining =>
    obtain ⟨same, _⟩ := ForSourceViews.success unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | bitNot found form writable bare profile remaining =>
    obtain ⟨same, _⟩ := CompatibleBitNotStatements.bitNot_view unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining
  | matchWith found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children remaining =>
    obtain ⟨same, _⟩ := DataMatchSourceTrace.of_outcome unique (lookupStatement?_sound found) form (.control executed)
    exact same.symm ▸ remaining
  | terminalBlock unique found form sourceType inner stops =>
    cases GenericLexicalStatements.block_terminates unique found form stops executed
  | terminalIf unique found form sourceType conditionFound conditionType typed conditionSyntax thenSyntax elseSyntax thenStops elseStops =>
    cases GenericLexicalStatements.conditional_terminates unique found form thenStops elseStops executed
  | terminalMatch unique found form sourceType scrutineeFound scrutineeTyped scrutineeSyntax casesTyped defaultTyped hiddenOrdinary armsOrdinary children stops =>
    cases ReachableMatchContinuations.DefaultStopped.terminates unique stops executed
  | scopedBlock found form inner remaining =>
    obtain ⟨same, _⟩ := ScalarStatementViews.block unique (lookupStatement?_sound found) form executed
    exact same.symm ▸ remaining

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (unique : NodeOccurrencesUnique source) :
    StaticSites (Facts source expressionSyntax) (HeadFacts source expressionSyntax)
      (ExpressionFacts source) program evidence source where
  head := fun typedSyntax => ⟨_, _, typedSyntax⟩
  expression := expression
  block := block
  branch := branch
  tail := tail unique

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeSourceSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
/-! Original Source statement typing accompanies compiler syntax at actual
sites. Assignment and loop judgments come from that Source receipt. Tail typing
is transported through the actual fallthrough context by the existing Source
context proof; no execution or compiler Tree fold is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
open Frontend SourceInference
open RecursiveNamedLexicalContracts.Stateful.WithReady

variable {source : TypedSource} {expressionSyntax : ExpressionId → Prop}

def Statements (source : TypedSource) (context : SourceSemantics.Context)
    (statements : List StatementId) : Prop :=
  ∃ control final facts, StatementsHaveType source control context statements final facts

def Head (source : TypedSource) (context : SourceSemantics.Context) (id : StatementId) : Prop :=
  ∃ control final facts, StatementHasType source control context id final facts

def Facts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (mode : Bool) (statements : List StatementId)
    (expected : TypeSystem.Ty) : Prop :=
  ProtectedStateImperativeSourceSites.Facts source expressionSyntax context mode statements expected ∧
    Statements source context statements

def HeadFacts (source : TypedSource) (expressionSyntax : ExpressionId → Prop)
    (context : SourceSemantics.Context) (id : StatementId) (expected : TypeSystem.Ty) : Prop :=
  ∃ mode rest, Facts source expressionSyntax context mode (id :: rest) expected

theorem head {context : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    (typed : Statements source context (id :: rest)) : Head source context id := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton typed => exact ⟨control, final, _, typed⟩
  | cons typed _ => exact ⟨control, _, _, typed⟩

private theorem actual_form {control : ControlContext} {context final : SourceSemantics.Context}
    {id : StatementId} {facts : StatementFacts} {node : StatementNode}
    (unique : NodeOccurrencesUnique source)
    (typed : StatementHasType source control context id final facts)
    (found : source.lookupStatement? id = some node) :
    Dynamic.StatementHasType.FormTyping source control context node.form final := by
  obtain ⟨original, contains, formTyped⟩ := Dynamic.StatementHasType.formTyping typed
  have same : original = node := Option.some.inj ((lookupStatement?_complete unique contains).symm.trans found)
  exact same ▸ formTyped

theorem assignment {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution} {operator : Syntax.ValueAssignOp} {rhs : ExpressionId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignValue assignment operator rhs) :
    SourceAssignmentHasType source context assignment operator rhs := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | assignValue typing => exact typing

theorem bit_not {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {assignment : AssignmentResolution}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .assignBitNot assignment) :
    SourceBitNotAssignmentValid source context assignment := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | assignBitNot typing => exact typing

theorem while_loop {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .whileLoop condition body) :
    ExpressionHasType source context condition .bool ∧ Statements source context body := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | whileLoop conditionTyped bodyTyped => exact ⟨conditionTyped, _, _, _, bodyTyped⟩

theorem for_loop {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {items post : List ForItemForm} {condition : ExpressionId} {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .forLoop items condition post body) :
    ∃ control loopContext postContext bodyFinal bodyFacts,
      ForItemsHaveType source control context items loopContext ∧
      ExpressionHasType source loopContext condition .bool ∧
      StatementsHaveType source control.enterLoop loopContext body bodyFinal bodyFacts ∧
      ForItemsHaveType source control.enterLoop loopContext post postContext := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | forLoop initializerTyped conditionTyped bodyTyped postTyped =>
    exact ⟨control, _, _, _, _, initializerTyped, conditionTyped, bodyTyped, postTyped⟩

theorem block_typed {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {body : List StatementId}
    (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body) :
    Statements source context body := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | block bodyTyped => exact ⟨control, _, _, bodyTyped⟩

theorem branch_typed {context : SourceSemantics.Context} {id : StatementId} {node : StatementNode}
    {condition : ExpressionId} {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (unique : NodeOccurrencesUnique source) (typed : Head source context id)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Statements source context (if boolean then thenBody else elseBody.getD []) := by
  obtain ⟨control, final, facts, typed⟩ := typed
  have original := actual_form unique typed found
  rw [form] at original
  cases original with
  | ifWithoutElse _ thenTyped =>
    cases boolean
    · exact ⟨control, context, _, .nil _ _⟩
    · exact ⟨control, _, _, thenTyped⟩
  | ifWithElse _ thenTyped elseTyped =>
    cases boolean
    · exact ⟨control, _, _, elseTyped⟩
    · exact ⟨control, _, _, thenTyped⟩

theorem tail_typed {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {id : StatementId} {rest : List StatementId}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (graph : OccurrenceGraphWellFormed source)
    (typed : Statements source context (id :: rest))
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Statements source nextContext rest := by
  obtain ⟨control, final, facts, typed⟩ := typed
  cases typed with
  | singleton _ => exact ⟨control, nextContext, _, .nil _ _⟩
  | cons headTyped tailTyped =>
    have same := executed.final_context_of_typing graph headTyped
    exact same.symm ▸ ⟨control, final, _, tailTyped⟩

theorem block {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {body : List StatementId}
    (unique : NodeOccurrencesUnique source)
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node) (form : node.form = .block body) :
    Facts source expressionSyntax context false body expected := by
  obtain ⟨mode, rest, compiledSyntax, typed⟩ := facts
  exact ⟨ProtectedStateImperativeSourceSites.block ⟨mode, rest, compiledSyntax⟩ found form,
    block_typed unique (head typed) found form⟩

theorem branch {context : SourceSemantics.Context} {id : StatementId}
    {expected : TypeSystem.Ty} {node : StatementNode} {condition : ExpressionId}
    {thenBody : List StatementId} {elseBody : Option (List StatementId)}
    (boolean : Bool) (unique : NodeOccurrencesUnique source)
    (facts : HeadFacts source expressionSyntax context id expected)
    (found : source.lookupStatement? id = some node)
    (form : node.form = .ifThen condition thenBody elseBody) :
    Facts source expressionSyntax context false (if boolean then thenBody else elseBody.getD []) expected := by
  obtain ⟨mode, rest, compiledSyntax, typed⟩ := facts
  exact ⟨ProtectedStateImperativeSourceSites.branch boolean ⟨mode, rest, compiledSyntax⟩ found form,
    branch_typed boolean unique (head typed) found form⟩

theorem tail {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {context nextContext : SourceSemantics.Context} {mode : Bool} {id : StatementId}
    {rest : List StatementId} {expected : TypeSystem.Ty} {node : StatementNode}
    {environment next : Dynamic.Environment} {before after : Dynamic.Heap}
    (graph : OccurrenceGraphWellFormed source)
    (facts : Facts source expressionSyntax context mode (id :: rest) expected)
    (found : source.lookupStatement? id = some node)
    (notTail : mode = true → rest = [] → ∀ expression, node.form ≠ .expression expression false)
    (executed : Dynamic.StatementExecutes program context evidence source environment before id
      nextContext (.fallthrough next) after) :
    Facts source expressionSyntax nextContext mode rest expected :=
  ⟨ProtectedStateImperativeSourceSites.tail graph.nodeOccurrencesUnique facts.1 found notTail executed,
    tail_typed graph facts.2 executed⟩

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (graph : OccurrenceGraphWellFormed source) :
    StaticSites (Facts source expressionSyntax) (HeadFacts source expressionSyntax)
      (ProtectedStateImperativeSourceSites.ExpressionFacts source) program evidence source where
  head := fun typed => ⟨_, _, typed⟩
  expression := fun ⟨mode, rest, compiledSyntax, _typed⟩ slot found =>
    ProtectedStateImperativeSourceSites.expression ⟨mode, rest, compiledSyntax⟩ slot found
  block := block graph.nodeOccurrencesUnique
  branch := fun boolean => branch boolean graph.nodeOccurrencesUnique
  tail := tail graph

end Solcore.SourceSemantics.CoreLowering.ProtectedStateImperativeTypedSourceSites
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites
/-! Original Source item typing supplies only the actual header slots. A
successful item identifies the next static context before tail facts are used. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites
open Frontend SourceInference
open ProtectedForHeader.Stateful.WithReady

variable {source : TypedSource} {control : ControlContext}

def Facts (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (items : List ForItemForm) : Prop :=
  ∃ final, ForItemsHaveType source control context items final

def ItemFacts (source : TypedSource) (control : ControlContext)
    (context : SourceSemantics.Context) (item : ForItemForm) : Prop :=
  ∃ final, ForItemHasType source control context item final

def ExpressionFacts (source : TypedSource) (context : SourceSemantics.Context)
    (id : ExpressionId) (node : ExpressionNode) : Prop :=
  ExpressionHasType source context id node.type

private theorem stored_expression {context : SourceSemantics.Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source) (typing : ExpressionHasType source context id type)
    (found : source.lookupExpression? id = some node) : ExpressionFacts source context id node := by
  obtain ⟨stored, contains, sourceType⟩ := typing.stored_type
  have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
  cases same
  change ExpressionHasType source context id node.type
  exact sourceType ▸ typing

private theorem key_typed {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (typed : SourceProjectionsHaveType source context root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ type, ExpressionHasType source context id type := by
  induction projections generalizing root leaf with
  | nil => cases typed; cases member
  | cons projection projections ih =>
    cases typed with
    | index head rest =>
      rcases List.mem_cons.mp member with rfl | tail
      · exact ⟨_, head⟩
      · exact ih rest tail
    | member _ rest => exact ih rest member

theorem expression {context : SourceSemantics.Context} {item : ForItemForm}
    {id : ExpressionId} {node : ExpressionNode} (unique : NodeOccurrencesUnique source)
    (facts : ItemFacts source control context item) (slot : ExpressionSlot item id)
    (found : source.lookupExpression? id = some node) : ExpressionFacts source context id node := by
  obtain ⟨final, typed⟩ := facts
  cases slot with
  | initialized mono =>
    cases typed with
    | letInitialized typing _ _ _ => exact stored_expression unique typing found
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | discard =>
    cases typed with
    | expression typing => exact stored_expression unique typing found
  | projectedBitNotKey member =>
    cases typed with
    | assignBitNot typing =>
      cases typing with
      | intro target _ =>
        cases target with
        | intro _ projections _ =>
          obtain ⟨type, keyTyped⟩ := key_typed projections member
          exact stored_expression unique keyTyped found

theorem item_context {program : Program} {context staticFinal runtimeFinal : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {environment next : Dynamic.Environment}
    {before after : Dynamic.Heap} {item : ForItemForm}
    (typing : ForItemHasType source control context item staticFinal)
    (executed : Dynamic.ForItemExecutes program context evidence source environment before item runtimeFinal next after) :
    runtimeFinal = staticFinal := by
  cases executed with
  | letUninitialized mono extended allocated =>
    cases typing with
    | letUninitialized _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
  | letInitialized evaluated mono extended allocated =>
    cases typing with
    | letInitialized _ _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
    | letInitializedGeneralized poly _ _ _ _ => exact False.elim (poly mono)
  | letInitializedGeneralized _ captures poly extended allocated =>
    cases typing with
    | letInitialized _ mono _ _ => exact False.elim (poly mono)
    | letInitializedGeneralized _ _ _ _ staticExtended => exact (Dynamic.BinderExtends.functional staticExtended extended).symm
  | expression | assignValue | assignBitNot => cases typing; rfl

theorem sites (program : Program) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (control : ControlContext) (unique : NodeOccurrencesUnique source) :
    StaticSites (Facts source control) (ItemFacts source control) (ExpressionFacts source)
      (SourceAssignmentHasType source) (SourceBitNotAssignmentValid source) program evidence source where
  head := by
    intro context item rest facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | cons head _ => exact ⟨_, head⟩
  expression := expression unique
  assignment := by
    intro context assignment operator rhs facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | assignValue typing => exact typing
  snapshot := by
    intro context assignment facts
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | assignBitNot typing => exact typing
  tail := by
    intro context nextContext item rest environment next before after facts executed
    obtain ⟨final, typed⟩ := facts
    cases typed with
    | cons head tail => exact item_context head executed ▸ ⟨_, tail⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateForHeaderSourceSites
end
