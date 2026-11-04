import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.CatalogAndSpecialization
import Solcore.SourceSemantics.CoreLowering.CellAllocationReadiness
import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.WellFormed

/-!
# Protected contracts: state transitions

`ProtectedStateTransition`, sequence bridges and producers, and operand typing of expressions.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
/-! Sized expression contracts return the actual reached protected state.
Compatibility adapters retain existing execution and heap results. Ordinary
administrative adapters preserve the complete record observation; dynamic
record production requires a separately proved transition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)

theorem AdministrativeTransport.toProtectedTransport (transport : AdministrativeTransport protocol) :
    ProtectedExpressionMeaning.Transport (entry protocol) where
  extend := by
    intro scope mapping world before store canonical futureMap futureWorld after futureStore
      installed maps worlds frame metadata
    obtain ⟨state⟩ := installed
    exact ⟨transport.extend state maps worlds frame metadata⟩

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
  (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

theorem PreservesAt.forget {size : Nat}
    (meaning : PreservesAt protocol model program context evidence source certificate faults size) :
    RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults (entry protocol) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed installed trace
  obtain ⟨initial⟩ := installed
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem ReflectsAt.forget {size : Nat}
    (meaning : ReflectsAt protocol model program context evidence source certificate faults size) :
    RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults (entry protocol) := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed installed evaluated
  obtain ⟨initial⟩ := installed
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩

/-- A proved legacy contract can extend its input witness through its certified
administrative effects. Its post-witness has the same record observation. -/
theorem PreservesAt.of_administrative (transport : AdministrativeTransport protocol) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults (entry protocol)) :
    PreservesAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial⟩ trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

theorem ReflectsAt.of_administrative (transport : AdministrativeTransport protocol) {size : Nat}
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults (entry protocol)) :
    ReflectsAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    meaning certified found environments heaps locals agrees typed ⟨initial⟩ evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    AdministrativeTransport.transition protocol transport initial maps worlds frame metadata⟩

end Expressions

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateSequenceBridge
/-! Exact-sized bridges between the recursive expression contract and the
protected ordered sequence contract. Both wrappers retain the original source
derivation; conversion preserves the concrete reached-state witness. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.SequenceBridge
open Core Frontend SourceInference GeneralHeap CoreProof ReadOnly
universe u v

theorem source_trace {program size context evidence source environment before id outcome after}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after) :
    ProtectedDataExpressionSequence.ExpressionTraceAt program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

theorem call_trace {program size context evidence source environment before id outcome after}
    (trace : ProtectedDataExpressionSequence.ExpressionTraceAt program size context evidence source environment before id outcome after) :
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after := by
  cases trace with
  | value trace => exact .value trace
  | fault trace => exact .fault trace

variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat}

theorem preserves_at
    (meaning : PreservesAt protocol model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt protocol size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  exact meaning certified found environments heaps locals agrees typed initial (call_trace trace)

theorem preserves_at_inv
    (meaning : ProtectedDataExpressionSequence.Stateful.ExpressionPreservesAt protocol size model program context evidence source certificate faults) :
    PreservesAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ outcome after
    environments heaps locals agrees typed initial trace
  exact meaning certified found environments heaps locals agrees typed initial (source_trace trace)

theorem reflects_at
    (meaning : ReflectsAt protocol model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt protocol size model program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, source_trace trace, rest⟩

theorem reflects_at_inv
    (meaning : ProtectedDataExpressionSequence.Stateful.ExpressionReflectsAt protocol size model program context evidence source certificate faults) :
    ReflectsAt protocol model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world admin environment canonical actual actualContext before store ξ value finalStore
    environments heaps locals agrees typed initial evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, call_trace trace, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.SequenceBridge
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateCellAllocationOrdinary
/-! The ordinary instance of the cell allocator uses the same actual marked
allocation and its original readiness condition. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion
universe u v

def MarkedAllocation.Producer.toCells {Records : Type v}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {protocol : Protocol.{u, v} Records}
    {layouts : SourceCoreAllocationLayouts.Prepared} {layout : SourceCoreCallableIndexedFrames.Layout}
    {model : GenericHeap.PayloadModel catalog projects definitions}
    (producer : MarkedAllocation.Producer protocol layouts layout model) :
    CellAllocation.Producer (catalog := catalog) protocol layouts layout (.ordinary model) where
  Ready := producer.Ready
  complete := by
    intro owner active request globals allocate allocation annotation same definitions registered
      mapping world administrative environment canonical actual before after store contextLocation native
      sourceCell payload sourceLocation environments agrees heaps reference read payloadAt cell allocated initial ready
    cases allocated with
    | ordinary allocated =>
      obtain ⟨captured, captures, typed, evaluated, finalHeaps, finalReference, preservation, transition⟩ :=
        producer.complete allocation annotation same definitions registered environments agrees
          (GenericHeap.ordinaryHeap_iff.mp heaps) reference read payloadAt cell allocated initial ready
      exact ⟨captured, captures, typed, evaluated, GenericHeap.ordinaryHeap_iff.mpr finalHeaps,
        finalReference, preservation, transition⟩
    | generalized allocated => cases cell

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
/-! Whole ordered sequence producers operate at one actual caller input.
Their outputs retain the full original result, effects and reached state.
Additional admission can be consumed before instantiation without changing
these neutral receipts or adding another sequence induction. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
open Core Frontend SourceInference GeneralHeap ReadOnly CoreProof
open DataExpressionSequence
open ProtectedDataExpressionSequence
universe u v
variable {Records : Type v} {protocol : ProtectedStateTransition.Protocol.{u,v} Records}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment}
  (model : GenericHeap.PayloadModel catalog projects definitions)
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {sourceTypes : List TypeSystem.Ty}
  {codes : List SourceCoreBasic.LoweredExpr} {faults : GenericExpressionMeaning.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment}
  {canonical actual : Environment} {before : Dynamic.Heap} {store : Store} {ξ : Renaming}
  (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)

/-- Inclusive Source sequence grades retain success and fault posts. -/
def Preserves (budget : Nat) : Prop :=
  ∀ {size outcome after},
    TraceAt program size context evidence source environment before ids outcome after → size ≤ budget →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

/-- Native sequence grades are strict; the reconstructed Source grade is
independent, and its actual successful or fault witness is retained. -/
def Reflects (budget : Nat) : Prop :=
  ∀ {size value finalStore},
    EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore →
    size < budget →
    ∃ sourceSize outcome after finalMap finalWorld,
      TraceAt program sourceSize context evidence source environment before ids outcome after ∧
      Result model finalMap finalWorld sourceTypes codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

variable {model}

/-- The existing Source fold supplies this provider at the same real input. -/
theorem Preserves.of_uniform (budget : Nat)
    (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → Stateful.ExpressionPreservesAt protocol size model
      program context evidence source certificate faults)
    {administrative actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    Preserves (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := ids) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget := by
  intro size outcome after trace bounded
  exact Stateful.preserves_bounded protocol budget tree meaning environments heaps locals agrees typed initial trace bounded

/-- The existing native fold supplies the independently graded Source trace
and same reached witness at this exact input. -/
theorem Reflects.of_uniform (budget : Nat)
    (tree : Tree source certificate scope ids sourceTypes codes)
    (meaning : ∀ size, size < budget → Stateful.ExpressionReflectsAt protocol size model
      program context evidence source certificate faults)
    {administrative actualContext : Core.Context}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : EnvironmentsAgree ξ canonical actual)
    (typed : RuntimeEnvironmentHasTypes world actual actualContext definitions) :
    Reflects (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := ids) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget := by
  intro size value finalStore completed bounded
  exact Stateful.reflects_bounded protocol budget tree meaning environments heaps locals agrees typed initial completed bounded

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionSequenceProducer
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionReady
/-! Readiness accompanies the same concrete expression state and is required
only after success. Source and native grades remain independent. These bridges
reuse the existing ordered sequence contracts and add no execution fold. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.WithReady
open Core Frontend SourceInference GeneralHeap ReadOnly CompatiblePayload CoreProof
universe u v
variable {Records : Type v} (protocol : Protocol.{u, v} Records)
  (ready : ∀ {index : Index}, protocol.State index → Prop)

def Reached (outcome : Dynamic.ExpressionOutcome) {initial : Index}
    (state : protocol.State initial) (final : Index) : Prop :=
  ∃ reached : protocol.State final,
    protocol.Relates state reached ∧ ∀ value, outcome = .value value → ready reached

theorem Reached.of_value {initial final : Index} {state : protocol.State initial}
    {value : Dynamic.Value} (transition : Reached protocol ready (.value value) state final)
    (outcome : Dynamic.ExpressionOutcome) : Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := transition
  exact ⟨reached, related, fun _ _ => successful _ rfl⟩

theorem Reached.continue {initial middle final : Index}
    {state : protocol.State initial} {middleState : protocol.State middle}
    {outcome : Dynamic.ExpressionOutcome} (first : protocol.Relates state middleState)
    (second : Reached protocol ready outcome middleState final) :
    Reached protocol ready outcome state final := by
  obtain ⟨reached, related, successful⟩ := second
  exact ⟨reached, protocol.trans first related, successful⟩

section Expressions
variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} (model : GenericHeap.PayloadModel catalog projects definitions)
  (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
  (source : TypedSource) (certificate : GenericExpressionMeaning.Certificate)
  (faults : GenericExpressionMeaning.FaultRep)

def PreservesAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ outcome after},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment before id outcome after →
    ∃ value finalStore finalMap finalWorld,
      Evaluates actual store (lowered.expression.rename ξ) value finalStore ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

def ReflectsAt (size : Nat) : Prop :=
  ∀ {scope id lowered}, certificate scope id lowered →
  ∀ {node}, source.lookupExpression? id = some node →
  ∀ {mapping world administrativeContext environment canonical actual actualContext before store ξ value finalStore},
    DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions →
    GenericHeap.HeapRepresents model mapping world before store →
    Dynamic.EnvironmentAgrees before context.locals environment →
    EnvironmentsAgree ξ canonical actual →
    RuntimeEnvironmentHasTypes world actual actualContext definitions →
  ∀ initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩,
    ready initial →
    EvaluationSize size actual store (lowered.expression.rename ξ) value finalStore →
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
      GenericExpressionMeaning.ResultRepresents model finalMap finalWorld node.type lowered.type faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      Reached protocol ready outcome initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩

end Expressions

variable {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
  {faults : GenericExpressionMeaning.FaultRep} {size : Nat}

theorem PreservesAt.to_sequence
    (meaning : PreservesAt protocol ready model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready size model
      program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial initialReady trace
  exact meaning certified found environments heaps locals agrees typed initial initialReady (SequenceBridge.call_trace trace)

theorem ReflectsAt.to_sequence
    (meaning : ReflectsAt protocol ready model program context evidence source certificate faults size) :
    ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready size model
      program context evidence source certificate faults := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, SequenceBridge.source_trace trace, rest⟩

theorem PreservesAt.of_sequence
    (meaning : ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionPreservesAt protocol ready size model
      program context evidence source certificate faults) :
    PreservesAt protocol ready model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial initialReady trace
  exact meaning certified found environments heaps locals agrees typed initial initialReady (SequenceBridge.source_trace trace)

theorem ReflectsAt.of_sequence
    (meaning : ProtectedDataExpressionSequence.Stateful.WithReady.ExpressionReflectsAt protocol ready size model
      program context evidence source certificate faults) :
    ReflectsAt protocol ready model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial initialReady evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    meaning certified found environments heaps locals agrees typed initial initialReady evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, SequenceBridge.call_trace trace, rest⟩

theorem PreservesAt.of_stateful
    (meaning : ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size) :
    PreservesAt protocol (fun _ => True) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ outcome after environments heaps locals agrees typed initial _ trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related⟩ := meaning certified found environments heaps locals agrees typed initial trace
  exact ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

theorem ReflectsAt.of_stateful
    (meaning : ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size) :
    ReflectsAt protocol (fun _ => True) model program context evidence source certificate faults size := by
  intro scope id lowered certified node found mapping world administrative environment canonical actual actualContext
    before store ξ value finalStore environments heaps locals agrees typed initial _ evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
      reached, related⟩ := meaning certified found environments heaps locals agrees typed initial evaluated
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata,
    reached, related, fun _ _ => True.intro⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition.WithReady
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
/-! The argument and value slots used by the composite, tuple, and builtin
adapters are exposed. Their full original
Source typing row comes from the parent's genuine typing judgment, independently
of native types or compiler projections. No execution or support fold is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
open Frontend SourceInference

/-- Ordered argument and value slots. Every call callee is excluded and handled
separately by its selected-call receipt; order and duplicates are retained. -/
def actualOperandIds : ExpressionForm → List ExpressionId
  | .group inner => [inner]
  | .tuple elements => elements
  | .unary _ operand => [operand]
  | .binary left _ right => [left, right]
  | .conditional condition thenBranch elseBranch => [condition, thenBranch, elseBranch]
  | .call _ arguments _ => arguments
  | .constructor _ arguments => arguments
  | .member base _ _ => [base]
  | .index base key => [base, key]
  | .literal _ | .integerLiteral _ _ | .reference _ _ | .lambda _ _ _ | .proxy _ => []

/-- One original typing inversion supplies every actual operand's Source row.
The row is retained in its original types, rather than identified with a native
parameter or projected type vector. -/
theorem operand_types {source : TypedSource} {context : Context}
    {id : ExpressionId} {node : ExpressionNode} {type : TypeSystem.Ty}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? id = some node)
    (typed : ExpressionHasType source context id type) :
    ∃ types, ExpressionsHaveTypes source context (actualOperandIds node.form) types := by
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ _ =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    generalize formEq : node.form = form at raw ⊢
    cases raw with
    | literal _ | integerLiteral _ | reference _ | proxy _ | lambda _ _ _ _ =>
      exact ⟨[], .nil context⟩
    | group child => exact ⟨_, .cons child (.nil context)⟩
    | tuple children => exact ⟨_, children⟩
    | unary child _ => exact ⟨_, .cons child (.nil context)⟩
    | binary first second _ => exact ⟨_, .cons first (.cons second (.nil context))⟩
    | conditional condition thenBranch elseBranch =>
      exact ⟨_, .cons condition (.cons thenBranch (.cons elseBranch (.nil context)))⟩
    | directCall _ _ children | builtinCall _ children | indirectCall _ children _ =>
      exact ⟨_, children⟩
    | constructor _ children => exact ⟨_, children⟩
    | member child _ => exact ⟨_, .cons child (.nil context)⟩
    | index base key => exact ⟨_, .cons base (.cons key (.nil context))⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedStateExpressionOperandTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedStateRebinding
/-! A snapshot evaluates in the same lexical scope with other canonical cells.
Lexical bindings already remove and prepend one scope binder; repeating this
over the whole scope rebinds its canonical values while every slot past the
scope stays fixed. Administrative transitions are the propositional part of an
administrative transport. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
open Core Frontend SourceInference GeneralHeap
universe u v

variable {Records : Type v} (protocol : Protocol.{u, v} Records)

/-- Every witness reaches each administrative extension of its index. -/
def AdministrativeTransitions : Prop :=
  ∀ {initial : Index} (_state : protocol.State initial) {mapping world heap store},
    LocationMap.Extends initial.mapping mapping → WorldExtends initial.world world →
    AdministrativePreserved initial.mapping initial.store mapping store →
    Dynamic.HeapMetadataExtend initial.heap heap →
    Transition protocol _state (initial.extend mapping world heap store)

theorem AdministrativeTransport.transitions (transport : AdministrativeTransport protocol) :
    AdministrativeTransitions protocol := by
  intro _ state _ _ _ _ maps worlds frame metadata
  exact AdministrativeTransport.transition protocol transport state maps worlds frame metadata

variable {protocol} (bindings : Bindings protocol)

include bindings in
/-- The scope binders are restored from the head and prepended again with the
new canonical values. -/
theorem Bindings.rebind :
    ∀ {index : Index} (state : protocol.State index) (canonical : Environment),
      index.scope.length ≤ index.canonical.length → index.scope.length ≤ canonical.length →
      (∀ slot, index.scope.length ≤ slot → canonical[slot]? = index.canonical[slot]?) →
      Transition protocol state { index with canonical := canonical } := by
  intro index
  obtain ⟨scope, mapping, world, heap, store, current⟩ := index
  induction scope generalizing current with
  | nil =>
    intro state canonical _ _ slots
    have same : canonical = current := List.ext_getElem? (fun slot => slots slot (Nat.zero_le _))
    subst same
    exact Transition.refl protocol state
  | cons head rest ih =>
    intro state canonical currentLength canonicalLength slots
    obtain ⟨id, type⟩ := head
    cases current with
    | nil => simp at currentLength
    | cons value tail =>
      cases canonical with
      | nil => simp at canonicalLength
      | cons replacement tail' =>
        have restored := bindings.restore_transition
          (index := ⟨rest, mapping, world, heap, store, tail⟩) (id := id) (type := type) (value := value) state
        refine Transition.then protocol restored (fun middle _ => ?_)
        have rebound := ih tail middle tail' (by simpa using currentLength) (by simpa using canonicalLength)
          (fun slot above => by
            dsimp only at above
            simpa using slots (slot + 1) (by dsimp only; simp only [List.length_cons]; omega))
        exact Transition.then protocol rebound (fun last _ => bindings.prepend_transition last id type replacement)

end Solcore.SourceSemantics.CoreLowering.ProtectedStateTransition
end
