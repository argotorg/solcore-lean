import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StatePlaceAssignments
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.Internal.RecursiveNamed.AssignmentContracts
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateExpressions
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceLayout
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
import Solcore.SourceSemantics.CoreLowering.Internal.Protected.StateAllocation
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceResolution
import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceWriteback
import Solcore.SourceSemantics.CoreLowering.CompatibleRenamedPlaceFaults
import Solcore.SourceSemantics.CoreLowering.AssignmentOperandDiagnostics
import Solcore.SourceSemantics.CoreLowering.CompatibleBareAssignmentMeaning

/-!
# Protected contracts: place assignments

Place keys, resolution and right-hand sides, and preservation of place assignments.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
/-! Protected ordered place keys reuse independent projection traces. Every
child receives the actual protected entry after previous key effects. Hidden
reference/payload slots are tracked by the real renaming and runtime typing;
no conditional meaning is converted into an unconditional child theorem. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPlaceKeyOrder
open GenericExpressionMeaning (FaultRep)
open SourceCoreLocalCell (Scope)

/- Index effects are evaluated exactly once in source projection order. The
generated values remain fully represented after later index effects. -/
namespace Stateful
universe u v

theorem preserves_bounded_with_sequence (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (meaning : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := sourceKeys projections) (sourceTypes := types) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) (bounded : size ≤ budget) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨sources, vectorSize, shaped, executed, vectorBound⟩ := RecursiveNamedPlaceKeyContracts.projections_values trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, post⟩ := meaning (.values executed) (Nat.le_trans vectorBound bounded)
  cases represented with
  | values represented =>
    exact ⟨sources, _, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
      finalHeaps, maps, worlds, frame, metadata, post⟩


theorem preserves_fault_bounded_with_sequence (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (meaning : ProtectedStateExpressionSequenceProducer.Preserves
      (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := sourceKeys projections) (sourceTypes := types) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨vectorSize, failed, vectorBound⟩ := RecursiveNamedPlaceKeyContracts.projections_fault trace
  obtain ⟨value, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, post⟩ := meaning (.fault failed) (Nat.le_trans vectorBound bounded)
  cases represented with
  | fault matched =>
    exact ⟨_, finalStore, finalMap, finalWorld, evaluated, matched, finalHeaps,
      maps, worlds, frame, metadata, post⟩


theorem reflects_bounded_with_sequence (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (meaning : ProtectedStateExpressionSequenceProducer.Reflects
      (program := program) (context := context) (evidence := evidence) (source := source)
      (ids := sourceKeys projections) (sourceTypes := types) (codes := codes) (faults := faults)
      (environment := environment) (actual := actual) (ξ := ξ) model initial budget)
    {size : Nat}
    (evaluated : CoreProof.EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedPlaceKeyContracts.OutcomeAt program sourceSize context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨vectorSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata, post⟩ := meaning evaluated bounded
  cases sourceTrace with
  | values trace =>
    obtain ⟨sourceSize, evaluated, shaped, sourceTrace⟩ := RecursiveNamedPlaceKeyContracts.values_projections trace
    exact ⟨sourceSize, _, after, finalMap, finalWorld, .values shaped sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, post⟩
  | fault trace =>
    obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedPlaceKeyContracts.fault_projections trace
    exact ⟨sourceSize, _, after, finalMap, finalWorld, .fault sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, post⟩


theorem preserves_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) (bounded : size ≤ budget) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_sequence budget protocol initial
    (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform initial budget tree
      (fun size bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bound))
      environments heaps locals layout actualTyped) trace bounded


theorem preserves_fault_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.PreservesAt protocol model program context evidence source certificate faults size))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_fault_bounded_with_sequence budget protocol initial
    (ProtectedStateExpressionSequenceProducer.Preserves.of_uniform initial budget tree
      (fun size bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bound))
      environments heaps locals layout actualTyped) trace bounded


theorem reflects_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.ReflectsAt protocol model program context evidence source certificate faults size))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    {size : Nat}
    (evaluated : CoreProof.EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedPlaceKeyContracts.OutcomeAt program sourceSize context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact reflects_bounded_with_sequence budget protocol initial
    (ProtectedStateExpressionSequenceProducer.Reflects.of_uniform initial budget tree
      (fun size bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning size bound))
      environments heaps locals layout actualTyped) evaluated bounded

end Stateful

theorem preserves_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before projections evaluated after) (bounded : size ≤ budget) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ := Stateful.preserves_bounded budget (ProtectedStatePlaceAssignment.legacyProtocol entry) tree
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
    environments heaps locals layout actualTyped ⟨installed⟩ trace bounded
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size model program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    {size : Nat}
    (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before projections reason after) (bounded : size ≤ budget) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ := Stateful.preserves_fault_bounded budget (ProtectedStatePlaceAssignment.legacyProtocol entry) tree
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
    environments heaps locals layout actualTyped ⟨installed⟩ trace bounded
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem reflects_bounded (budget : Nat) {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.ReflectsAt size model program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    {size : Nat}
    (evaluated : CoreProof.EvaluationSize size actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) (bounded : size < budget) :
    ∃ sourceSize outcome after finalMap finalWorld,
      RecursiveNamedPlaceKeyContracts.OutcomeAt program sourceSize context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, _⟩ := Stateful.reflects_bounded budget (ProtectedStatePlaceAssignment.legacyProtocol entry) tree
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_reflects transport (meaning size smaller))
    environments heaps locals layout actualTyped ⟨installed⟩ evaluated bounded
  exact ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact preserves_bounded size transport tree (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    environments heaps locals layout actualTyped installed sized (Nat.le_refl size)


theorem preserves_fault {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : ProtectedExpressionMeaning.Preserves model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsFault.has_size trace
  exact preserves_fault_bounded size transport tree (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size)
    environments heaps locals layout actualTyped installed sized (Nat.le_refl size)


theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : ProtectedExpressionMeaning.Reflects model program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (installed : entry scope mapping world before store canonical)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      OutcomeTrace program context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, rest⟩ :=
    reflects_bounded (size + 1) transport tree (RecursiveNamedBoundedContracts.reflects_below_of_unbounded meaning (size + 1))
      environments heaps locals layout actualTyped installed sized (by omega)
  exact ⟨outcome, after, finalMap, finalWorld, trace.sound, rest⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceKeys
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
/-! Typed child meanings for the actual CompatiblePlaceResolution phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot
open CompatiblePlaceResolution CompatibleRenamedPlace

private theorem path_length {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf) : steps.length = projections.length := by
  induction path with
  | nil => rfl
  | member _ _ _ _ ih | index _ _ _ ih => exact congrArg Nat.succ ih

private theorem shape_length {projections : List PlaceProjection} {sources : List Dynamic.Value}
    {resolved : List Dynamic.EvaluatedProjection} (shape : DataPlaceKeyOrder.Values projections sources resolved) :
    resolved.length = projections.length := by
  induction shape with
  | nil => rfl
  | member _ ih | index _ ih => exact congrArg Nat.succ ih

private theorem read_present {root : Dynamic.Value} {projections : List Dynamic.EvaluatedProjection}
    {selected : Option Dynamic.Value} (read : Dynamic.ProjectionsRead (some root) projections selected) :
    ∃ value, selected = some value := by
  generalize initialEq : some root = initial at read
  induction read generalizing root with
  | nil => exact ⟨root, initialEq.symm⟩
  | indexFound _ _ ih | indexDefault _ _ _ ih | member _ _ ih => exact ih rfl

/- Successful source resolution constructs the actual key and getter runs.
The protected child theorem receives the real entry at every key heap
and hidden reference slot. Independent writable-local typing and environment agreement
recover the exact raw root declaration type. -/
namespace Stateful
universe u v

theorem preserves_bounded_with_sequence (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place sourceTarget after) (bounded : size ≤ budget) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩ := by
  cases trace with
  | @intro _ _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata, keyPost⟩ :=
      ProtectedPlaceKeys.Stateful.preserves_bounded_with_sequence budget protocol initialState
        (sequenceMeaning target (agrees coreLookup) (.cons (.cellRef reference.typed) actualTyped)) evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments (renamedCodes codes ξ)).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using keyEvaluated
    obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
    obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
    have locationEq := lookup.functional staticLookupRuntime
    subst staticLocation
    have cellEq := initialRead.functional staticRead
    subst staticCell
    obtain ⟨updated, updatedRead, updatedType, _⟩ := metadata _ _ initialRead
    have currentEq := currentRead.functional updatedRead
    subst updated
    have rootType : currentCell.type = prepared.route.rootSourceType := updatedType.trans (staticCellType.trans bodyEq)
    have currentReference := reference.extend keyMaps keyWorlds
    have arguments := views.arguments shaped keysRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
    have keyLength : prepared.keyTypes.length = values.length := keyTypes ▸ keysRelated.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes keyWorld
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
          actualContext) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) (actualTyped.weaken keyWorlds))
    have resolvedNonempty : projections ≠ [] := by
      intro empty
      have length := (path_length path).trans (shape_length shaped).symm
      rw [empty, List.length_nil] at length
      exact nonempty (List.eq_nil_of_length_eq_zero length)
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases selection with | nil => exact (resolvedNonempty rfl).elim
    obtain ⟨sourceRoot, rfl⟩ := present
    obtain ⟨selectedValue, rfl⟩ := read_present selection
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions keyMap keyWorld prepared after keyStore sourceLocation target
          currentCell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keyHeaps currentReference currentRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keyHeaps currentReference currentRead (virtual key value rootType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have represented : ValueRep compilation.checked registry functions keyMap keyWorld
        prepared.route.rootSourceType sourceRoot rootValue prepared.route.rootType := by
      simpa only [← rootType] using root.payload
    have tree := arguments.readTree represented leafProjected selection prepared
    have tree : CompatibleMapping.MixedPaths.ReadTree compilation.checked registry functions keyMap keyWorld prepared values
        leaf prepared.route.leafType currentCell.type sourceRoot rootValue prepared.steps projections selectedValue
        (readCost compilation.checked prepared.steps) := by simpa only [rootType] using tree
    obtain ⟨snapshot, finalStore, administrative, _, _, related, evaluated, appended, _⟩ :=
      readTree_at root tree nonempty faithful observations keyLength
        (keysEnvironment prepared.route.rootType target (packValues values) coreEnvironment)
        (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
    obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
      evaluation_frame (mapping := keyMap) keyHeaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
    obtain ⟨keyState, keyRelated⟩ := keyPost
    refine ⟨{ target := target
              sources := sources
              values := values
              selected := selectedValue
              snapshot := snapshot
              keyStore := keyStore
              store := finalStore
              mapping := keyMap
              world := finalWorld
              selectedEq := rfl
              currentCell := currentCell
              currentRead := currentRead
              currentType := rootType
              reference := currentReference.extend (.refl _) extension
              shaped := shaped
              keysEvaluated := keyEvaluation
              snapshotEvaluated := by simpa only [packed_renamed_type] using evaluated
              keysRelated := by simpa only [renamedCodes_types] using keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, agrees coreLookup,
      transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after),
      protocol.trans keyRelated (transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after))⟩

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place sourceTarget after) (bounded : size ≤ budget) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, execution.mapping, execution.world, after, execution.store, canonical⟩ := by
  exact preserves_bounded_with_sequence budget path views keyTypes leafProjected virtual registryExtension
    nonempty getterTyped protocol transport faithful observations environments locals agrees actualTyped initialState
    (fun target _ prefixTyped => ProtectedStateExpressionSequenceProducer.Preserves.of_uniform initialState budget children
      (fun size smaller => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size smaller))
      environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees agrees [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) prefixTyped)
    slot rootTyped trace bounded

end Stateful

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceResolves program size context evidence source environment before place sourceTarget after) (bounded : size ≤ budget) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  obtain ⟨execution, selected, _⟩ := Stateful.preserves_bounded budget path views children keyTypes leafProjected virtual registryExtension nonempty getterTyped
    (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport)
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller)) faithful observations
    environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped trace bounded
  exact ⟨execution, selected⟩

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (path : PreparedPath compilation.checked source site prepared.route.rootSourceType place.projections
      0 prepared.steps prepared.keys leaf)
    (views : KeyViews path sourceTypes)
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (keyTypes : prepared.keyTypes = codes.map (·.type))
    (leafProjected : compilation.checked.catalog.project leaf = .ok prepared.route.leafType)
    (virtual : ∀ key value, prepared.route.rootSourceType = .mapping key value →
      CompatibleMapping.VirtualRoot.Generated compilation prepared.route key value)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (nonempty : prepared.steps ≠ [])
    (getterTyped : HasType ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext)
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution compilation.checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceResolves.has_size trace
  exact preserves_bounded size path views children keyTypes leafProjected virtual registryExtension nonempty getterTyped transport
    (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) faithful observations
    environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size)

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
open Core Frontend SourceInference GeneralHeap CompatiblePayload SourceCoreCompatibleDataPlaces

/-- Getter administrative allocations preserve the actual protected entry.
The canonical source environment has no getter temporaries. -/
theorem retained {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {prepared : Prepared} {codes : List SourceCoreBasic.LoweredExpr} {types : List TypeSystem.Ty}
    {place : PlaceResolution} {leaf : TypeSystem.Ty} {target : Dynamic.ResolvedPlace}
    {actual canonical : Core.Environment} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    {before after : Dynamic.Heap} {scope : Scope} {entry : ProtectedExpressionMeaning.Entry}
    (transport : ProtectedExpressionMeaning.Transport entry)
    (execution : CompatiblePlaceResolution.Execution checked registry functions prepared codes types place leaf target
      actual store mapping world before after)
    (installed : entry scope mapping world before store canonical) :
    entry scope execution.mapping execution.world after execution.store canonical :=
  transport.extend installed execution.maps execution.worlds execution.frame execution.metadata

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
/-! Protected child meaning runs under the actual snapshot, packed keys and
captured root reference. The post-getter entry is derived from its real frame,
world and heap metadata receipts, never from environment typing alone. Their typing is derived from resolution receipts and the
actual environment typing, rather than supplied as a child execution.
The result and latest-root relations are shared with unrestricted RHS meaning. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open CompatibleRenamedPlace
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceRhs

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Every hidden slot uses the post-getter world. Existing administrative
captures are transported by the exact world extension from resolution. -/
theorem snapshot_runtimeTyped {actualContext : Core.Context}
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions) :
    RuntimeEnvironmentHasTypes resolution.world
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      (OptionalCell.cellType prepared.route.leafType :: (SourceCoreCalls.packArguments (renamedCodes codes ξ)).type ::
        OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions :=
  .cons (.inRight resolution.snapshotRelated.runtime_hasType)
    (.cons (CompatiblePlaceResolution.values_typed resolution.keysRelated)
      (.cons (.cellRef resolution.reference.typed) (actualTyped.weaken resolution.worlds)))

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

universe u v

/-- Pack the actual RHS execution and reached state under the real saved slots. -/
theorem rhs_of_expression {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap} {value : Value}
    {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after)
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store)
    (represented : ResultRepresents (payloadModel checked registry functions) mapping world node.type lowered.type faults outcome value)
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (frame : AdministrativePreserved resolution.mapping resolution.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after)
    (post : ProtectedStateTransition.Transition protocol initial ⟨scope, mapping, world, after, store, canonical⟩) :
    Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, mapping, world, after, store, canonical⟩ :=
  ⟨⟨trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩, post⟩

/-- Source RHS meaning at one actual getter state, with a strict child budget. -/
def Preserves {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {size outcome after}, size < budget →
    RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment targetHeap id outcome after →
    ∃ value store mapping world,
      Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
        resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, mapping, world, after, store, canonical⟩

/-- Native RHS meaning at the same getter state retains an independent Source grade. -/
def Reflects {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {size value store}, size < budget →
    CoreProof.EvaluationSize size
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
        (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store →
    ∃ sourceSize outcome after mapping world,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment targetHeap id outcome after ∧
      Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
        resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
      ProtectedStateTransition.Transition protocol initial ⟨scope, mapping, world, after, store, canonical⟩

/-- Choose Source RHS meaning only after the genuine resolution and its actual post. -/
def PreservesAfter {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, initialMap, initialWorld, before, initialStore, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {sourceTarget targetHeap},
    Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap →
    ∀ (execution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment initialStore initialMap initialWorld before targetHeap)
      (reached : protocol.State ⟨scope, execution.mapping, execution.world, targetHeap, execution.store, canonical⟩),
    protocol.Relates initial reached →
    Preserves (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      execution protocol reached budget

/-- Choose native RHS meaning at that same genuine resolution and actual post. -/
def ReflectsAfter {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (initial : protocol.State ⟨scope, initialMap, initialWorld, before, initialStore, canonical⟩)
    (budget : Nat) : Prop :=
  ∀ {sourceTarget targetHeap},
    Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap →
    ∀ (execution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ)
      sourceTypes place leaf sourceTarget coreEnvironment initialStore initialMap initialWorld before targetHeap)
      (reached : protocol.State ⟨scope, execution.mapping, execution.world, targetHeap, execution.store, canonical⟩),
    protocol.Relates initial reached →
    Reflects (program := program) (context := context) (evidence := evidence) (source := source)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      execution protocol reached budget

/- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
namespace Stateful

theorem preserves_at (size : Nat)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : ProtectedStateTransition.PreservesAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initialState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, mapping, world, after, store, canonical⟩ := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata, post⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped initialState trace
  refine ⟨value, store, mapping, world,
    rhs_of_expression resolution protocol initialState trace.sound ?_ represented heaps maps worlds frame metadata post⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem reflects_at (size : Nat)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : ProtectedStateTransition.ReflectsAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initialState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    {value : Value} {store : Store}
    (evaluated : CoreProof.EvaluationSize size
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ sourceSize outcome after mapping world,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment targetHeap id outcome after ∧
      Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, mapping, world, after, store, canonical⟩ := by
  have snapshotTyped := snapshot_runtimeTyped resolution actualTyped
  obtain ⟨sourceSize, outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata, post⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees agrees
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) snapshotTyped
      initialState
      (by simpa only [DataPlaceChildExpressions.rename_prefix, renamed, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨sourceSize, outcome, after, mapping, world, trace,
    rhs_of_expression resolution protocol initialState trace.sound evaluated.sound represented heaps maps worlds frame metadata post⟩

end Stateful

/-- Compatibility supplies the old uniform child family only at the real getter post. -/
theorem PreservesAfter.of_uniform (budget : Nat)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol
      (payloadModel checked registry functions) program context evidence source certificate faults size))
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, initialMap, initialWorld, before, initialStore, canonical⟩) :
    PreservesAfter (checked := checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initial budget := by
  intro target targetHeap _ execution reached _ size outcome after bounded trace
  exact Stateful.preserves_at execution size protocol (meaning size bounded) generated found
    environments agrees actualTyped locals reached trace

/-- Native compatibility keeps the original independently measured child grades. -/
theorem ReflectsAfter.of_uniform (budget : Nat)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.ReflectsAt protocol
      (payloadModel checked registry functions) program context evidence source certificate faults size))
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog)
      initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (initial : protocol.State ⟨scope, initialMap, initialWorld, before, initialStore, canonical⟩) :
    ReflectsAfter (checked := checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := id) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initial budget := by
  intro target targetHeap _ execution reached _ size value store bounded evaluated
  exact Stateful.reflects_at execution size protocol (meaning size bounded) generated found
    environments agrees actualTyped locals reached evaluated


theorem preserves_at (size : Nat)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨value, store, mapping, world, result, _⟩ := Stateful.preserves_at resolution size (ProtectedStatePlaceAssignment.legacyProtocol entry)
    (ProtectedStatePlaceAssignment.legacy_preserves transport meaning) generated found environments agrees actualTyped locals
    ⟨transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata⟩ trace
  exact ⟨value, store, mapping, world, result⟩

theorem reflects_at (size : Nat)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.ReflectsAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {value : Value} {store : Store}
    (evaluated : CoreProof.EvaluationSize size
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ sourceSize outcome after mapping world,
      RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment targetHeap id outcome after ∧
      Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨sourceSize, outcome, after, mapping, world, measured, result, _⟩ := Stateful.reflects_at resolution size (ProtectedStatePlaceAssignment.legacyProtocol entry)
    (ProtectedStatePlaceAssignment.legacy_reflects transport meaning) generated found environments agrees actualTyped locals
    ⟨transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata⟩ evaluated
  exact ⟨sourceSize, outcome, after, mapping, world, measured, result⟩

theorem preserves
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨size, sized⟩ := RecursiveNamedCallBounds.ExpressionOutcome.has_size trace
  exact preserves_at resolution size transport (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size)
    generated found environments agrees actualTyped locals installed sized

theorem reflects
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults entry)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 (lowered.expression.rename ξ)) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node (renamed lowered ξ) environment outcome after value store mapping world := by
  obtain ⟨size, sized⟩ := CoreProof.evaluation_has_size evaluated
  obtain ⟨sourceSize, outcome, after, mapping, world, _, result⟩ :=
    reflects_at resolution size transport (RecursiveNamedBoundedContracts.reflects_at_of_unbounded meaning size)
      generated found environments agrees actualTyped locals installed sized
  exact ⟨outcome, after, mapping, world, result⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload SourceCoreCompatibleDataPlaces CompatiblePlaceRhs

/-- The RHS result's real post-prefix map/world/protection receipts transport
all installed observations. Its three hidden slots never alter canonical
source scope or native captured closure environments. -/
theorem retained {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {types : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {target : Dynamic.ResolvedPlace} {actual canonical : Environment} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes types place leaf target
      actual initialStore initialMap initialWorld before targetHeap)
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    {environment : Dynamic.Environment} {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world)
    {scope : Scope} {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (installed : entry scope initialMap initialWorld before initialStore canonical) :
    entry scope mapping world after store canonical :=
  transport.extend (transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata)
    result.maps result.worlds result.frame result.metadata

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceRhs

namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceWriteback
open Core Frontend SourceInference GeneralHeap DataPatternValues DataEquality
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces

/-- The already-closed setter reconstruction and mapped write supply their
actual effects. The protected entry survives those exact effects; neither a
child evaluation nor a body semantics premise is supplied for writeback. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {prepared : Prepared} {heap after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {target : Location} {cell : Dynamic.Cell} {optional rootValue : Value}
    {sourceRoot : Dynamic.Value}
    (root : RootRead checked registry functions mapping world prepared heap store location target cell optional sourceRoot rootValue)
    (heaps : HeapRepresents checked registry functions mapping world heap store)
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} {leaf : TypeSystem.Ty}
    {sourceProjections : List PlaceProjection} {position : Nat} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site cell.type sourceProjections position prepared.steps keySites leaf}
    {keys : List Value} {projections : List Dynamic.EvaluatedProjection}
    (arguments : Arguments checked registry functions mapping world source site keys path projections)
    {replacementSource updated : Dynamic.Value} {replacement : Value}
    (replacementRep : ValueRep checked registry functions mapping world leaf replacementSource replacement prepared.route.leafType)
    (changed : Dynamic.ProjectionsUpdate (fun _ value => value = replacementSource) (some sourceRoot) projections updated)
    (written : Dynamic.Heap.Writes heap location (some updated) after)
    (nonempty : prepared.steps ≠ [])
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations checked.catalog functions identities) (keyLength : prepared.keyTypes.length = keys.length)
    {environment canonical : Environment} {actualContext : Core.Context} {keyType : Ty}
    {referenceExpression keyExpression replacementExpression : Expr}
    (environmentTyped : RuntimeEnvironmentHasTypes world environment actualContext ambient.definitions)
    (setterTyped : HasType actualContext
      (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
      (LanguageResult.resultType prepared.route.rootType) ambient.definitions)
    (referenceSelected : Selects environment referenceExpression (.cellRef (OptionalCell.cellType prepared.route.rootType) target))
    (keysSelected : Selects environment keyExpression (packValues keys))
    (replacementSelected : Selects environment replacementExpression replacement)
    {scope : Scope} {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (installed : entry scope mapping world heap store canonical) :
    ∃ native helperStore finalStore futureWorld,
      ValueRep checked registry functions mapping futureWorld cell.type updated native prepared.route.rootType ∧
      Evaluates environment store
        (.apply (setter prepared keyType) (.pair (.loadCell referenceExpression) (.pair keyExpression replacementExpression)))
        (.inRight .word native) helperStore ∧
      helperStore.read? target = some optional ∧
      helperStore.write? target (.inRight .unit native) = some finalStore ∧
      HeapRepresents checked registry functions mapping futureWorld after finalStore ∧
      WorldExtends world futureWorld ∧ AdministrativePreserved mapping store mapping finalStore ∧
      Dynamic.HeapMetadataExtend heap after ∧ entry scope mapping futureWorld after finalStore canonical := by
  obtain ⟨native, helperStore, finalStore, futureWorld, related, evaluated, read, write, finalHeaps,
    worlds, frame, metadata⟩ := CompatiblePlaceWriteback.preserves root heaps arguments replacementRep changed written
      nonempty faithful observations keyLength environmentTyped setterTyped referenceSelected keysSelected replacementSelected
  exact ⟨native, helperStore, finalStore, futureWorld, related, evaluated, read, write, finalHeaps, worlds, frame,
    metadata, transport.extend installed (.refl _) worlds frame metadata⟩

end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceWriteback
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentPreservation
/-! Typed child meanings for the actual CompatiblePlaceTargetKeys phase.
The existing semantic output receipts and static compiler layouts are reused.
All temporary slot types come from represented payloads and mapped references. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution
open CompatiblePlaceTargetKeys CompatibleRenamedPlace

/- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
namespace Stateful
universe u v

theorem preserves_bounded_with_sequence (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (_children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget) :
    ∃ keys : Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index),
      ProtectedStateTransition.Transition protocol initialState ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩ := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata, post⟩ :=
    ProtectedPlaceKeys.Stateful.preserves_bounded_with_sequence budget protocol initialState
      (sequenceMeaning target (agrees selected) (.cons (.cellRef reference.typed) actualTyped)) trace bounded
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, agrees selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, List.length_cons, List.length_nil,
      packed_renamed_expression, List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    by simpa only [renamedCodes_types] using related, keyHeaps, maps, worlds, frame, metadata⟩, post⟩

theorem preserves_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget) :
    ∃ keys : Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index),
      ProtectedStateTransition.Transition protocol initialState ⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩ := by
  exact preserves_bounded_with_sequence    (budget := budget)
    (_children := children)
    (protocol := protocol)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (lookup := lookup)
    (initialRead := initialRead)
    (trace := trace)
    (bounded := bounded)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))

end Stateful

theorem preserves_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget) :
    Nonempty (Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index)) := by
  obtain ⟨keys, _⟩ := Stateful.preserves_bounded budget children (ProtectedStatePlaceAssignment.legacyProtocol entry) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
    environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped lookup initialRead trace bounded
  exact ⟨keys⟩

theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place (renamedCodes codes ξ) sourceTypes location resolved coreEnvironment before after store mapping world (ξ index)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact preserves_bounded size
    children transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size)


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetKeys


/-! Typed successful assignment prefixes expose their seven real temporary
values. Getter/setter typing and represented payloads type those slots in the
post-write world; no arbitrary slot list is assumed to be safe for captures. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentSuccess
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning CoreProof
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceAssignmentSuccess

def writtenContext (prepared : Prepared) (keyType : Ty) (context : Core.Context) : Core.Context :=
  .unit :: prepared.route.rootType :: prepared.route.leafType :: prepared.route.leafType ::
    prepared.optionalLeaf :: keyType :: OptionalCell.referenceType prepared.route.rootType :: context

private theorem resolved_nonempty {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    {sources : List Dynamic.Value} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved) (nonempty : steps ≠ []) : resolved ≠ [] := by
  have lengths : steps.length = resolved.length := by
    clear nonempty
    induction path generalizing sources resolved with
    | nil => cases shaped; rfl
    | member _ _ _ _ ih => cases shaped with | member tail => exact congrArg Nat.succ (ih tail)
    | index _ _ _ ih => cases shaped with | index tail => exact congrArg Nat.succ (ih tail)
  intro empty
  rw [empty, List.length_nil] at lengths
  exact nonempty (List.eq_nil_of_length_eq_zero lengths)

private theorem none_update {modify : Option Dynamic.Value → Dynamic.Value → Prop}
    {projections : List Dynamic.EvaluatedProjection} {updated : Dynamic.Value}
    (changed : Dynamic.ProjectionsUpdate modify none projections updated) : projections = [] := by
  cases changed
  rfl

/- An independent successful transaction constructs every native phase.
Raw metadata and duplicate entries are retained by the full payload relation;
the native store additionally contains tracked administrative helper cells. -/
namespace Stateful
universe u v

theorem preserves_prefix_bounded_with_producers (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (rhsMeaning : ProtectedPlaceRhs.PreservesAfter (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := rhs) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (bounded : size ≤ budget)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        (∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ))) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  cases trace with
  | @intro _ _ _ _ _ _ _ _ targetHeap rhsHeap _ _ sourceTarget _ right _ resolve evaluate written =>
    obtain ⟨resolution, coreLookup, resolutionPost⟩ := ProtectedPlaceResolution.Stateful.preserves_bounded_with_sequence budget layout.path layout.views layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped protocol transport faithful observations
      environments locals agrees actualTyped initialState sequenceMeaning slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨resolutionState, resolutionRelated⟩ := resolutionPost
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
      rhsMeaning resolve.sound resolution resolutionState resolutionRelated (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      obtain ⟨rhsState, rhsRelated⟩ := rhsPost
      have snapshotRep := rhsResult.saved_snapshot
      have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
        simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
      have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
      have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
      obtain ⟨latest⟩ := rhsResult.latest
      cases written with
      | @intro _ _ cell initial _ sourceRead _ initialValue update sourceWrite =>
        have cellEq := sourceRead.functional latest.read
        have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
        obtain ⟨replacement, applies, changed⟩ := DataPlaceAssignmentWriteBack.replacement_of_update update
        rw [resolution.selectedEq] at applies
        obtain ⟨replacementValue, replacementRep, modifiedEvaluated, _⟩ :=
          CompatiblePlaceModifier.preserves observations operatorProfile snapshotRep rightRep applies
            (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
            (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
        have present : ∃ sourceRoot, initial = some sourceRoot := by
          cases initial with
          | some value => exact ⟨value, rfl⟩
          | none => exact (resolved_nonempty layout.path resolution.shaped layout.nonempty (none_update changed)).elim
        obtain ⟨sourceRoot, rfl⟩ := present
        have rootExists : ∃ optional rootValue,
            RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
              cell optional sourceRoot rootValue := by
          cases initialValue with
          | initialized =>
            obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
            exact ⟨_, value, root⟩
          | emptyMapping key value =>
            obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
              (layout.virtual key value cellType.symm) registryExtension
            exact ⟨_, native, root⟩
        obtain ⟨optional, rootValue, root⟩ := rootExists
        have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
        have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
            (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
              (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
            (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
              OptionalCell.referenceType prepared.route.rootType :: actualContext)
            ambient.definitions :=
          .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
            (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
              (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
        have currentPath : PreparedPath compilation.checked source site cell.type place.projections
            0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
        have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
            currentPath sourceTarget.projections := by simpa only [cellType] using arguments
        obtain ⟨updatedValue, helperStore, finalStore, finalWorld, updatedRep, setterEvaluated,
          helperRead, coreWritten, finalHeaps, extension, frame, metadata⟩ :=
          CompatiblePlaceWriteback.preserves root rhsResult.heaps currentArguments replacementRep changed sourceWrite layout.nonempty
            faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
        refine ⟨updatedValue, finalStore, rhsMap, finalWorld,
          by simpa only [cellType] using updatedRep, finalHeaps, resolution.maps.trans rhsResult.maps,
          (resolution.worlds.trans rhsResult.worlds).trans extension, (resolution.frame.trans rhsResult.frame).trans frame,
          (resolution.metadata.trans rhsResult.metadata).trans metadata,
          [.unit, updatedValue, replacementValue, rightValue, .inRight .unit resolution.snapshot,
            packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target], rfl, ?_, ?_,
          transport.extend rhsState (.refl _) extension frame metadata,
          protocol.trans (protocol.trans resolutionRelated rhsRelated)
            (transport.related rhsState (.refl _) extension frame metadata)⟩
        · exact .cons .unit (.cons updatedRep.runtime_hasType (typedEnvironment.weaken extension))
        · intro next outputType
          rw [execute_rename layout.path closed]
          simp only [renamed_packed, Expr.rename]
          unfold execute
          simp only [packed_renamed_type]
          have snapshotEvaluated := resolution.snapshotEvaluated
          simp only [packed_renamed_type] at snapshotEvaluated
          exact (ContinuationAgreement.letE (.var coreLookup)).trans
            ((ContinuationAgreement.bind resolution.keysEvaluated).trans
              ((ContinuationAgreement.bind snapshotEvaluated).trans
                ((ContinuationAgreement.bind rhsResult.evaluated).trans
                  ((ContinuationAgreement.bind modifiedEvaluated).trans
                    ((ContinuationAgreement.bind setterEvaluated).trans
                      (ContinuationAgreement.letE (.storeCell (.var rfl) helperRead (.inRight (.var rfl)) coreWritten)))))))

theorem preserves_prefix_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (bounded : size ≤ budget)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        (∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ))) ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_prefix_bounded_with_producers    (budget := budget)
    (layout := layout)
    (ordinary := ordinary)
    (registryExtension := registryExtension)
    (protocol := protocol)
    (transport := transport)
    (faithful := faithful)
    (observations := observations)
    (_rhsGenerated := rhsGenerated)
    (_found := found)
    (rhsView := rhsView)
    (rhsCoreType := rhsCoreType)
    (operatorProfile := operatorProfile)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (trace := trace)
    (bounded := bounded)
    (invalidOperand := invalidOperand)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget layout.children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))
    (rhsMeaning := (ProtectedPlaceRhs.PreservesAfter.of_uniform budget protocol meaning rhsGenerated found
      environments agrees actualTyped locals initialState))

end Stateful

theorem preserves_prefix_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignment program size context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after) (bounded : size ≤ budget)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨updatedValue, finalStore, finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation, _⟩ := Stateful.preserves_prefix_bounded budget layout ordinary registryExtension
    (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport)
    (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller)) faithful observations
    rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped trace bounded invalidOperand
  exact ⟨updatedValue, finalStore, finalMap, finalWorld, related, finalHeaps, maps, worlds, frame, metadata, slots, count, typed, continuation⟩

theorem preserves_prefix {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat} {updatedRoot : Dynamic.Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceAssignment program context evidence source (Dynamic.AssignmentValueApplies operator)
      environment before place rhs updatedRoot after)
    (invalidOperand : Word) :
    ∃ updatedValue finalStore finalMap finalWorld,
      ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType updatedRoot updatedValue prepared.route.rootType ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ∃ slots : Environment, slots.length = 7 ∧
        RuntimeEnvironmentHasTypes finalWorld (slots ++ coreEnvironment)
          (writtenContext prepared (SourceCoreCalls.packArguments codes).type
            actualContext) ambient.definitions ∧
        ∀ next outputType, ContinuationAgreement coreEnvironment store
          ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
            (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand).rename ξ)
          (slots ++ coreEnvironment) finalStore (shift 7 (next.rename ξ)) := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignment.has_size trace
  exact preserves_prefix_bounded size
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) faithful observations rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentSuccess



/-! Whole emitted assignments short-circuit on key and RHS faults, retaining
all preceding source effects. The executions of children are obtained from the
protected expression theorem; neither phase accepts a child evaluation as its
static compiler contract. Structural missing-default guards are separate. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFailures
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

namespace Stateful
universe u v

theorem keys_bounded_with_sequence (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (_children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents checked registry functions mapping world before store)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before place.projections reason after) (bounded : size ≤ budget)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    ProtectedPlaceKeys.Stateful.preserves_fault_bounded_with_sequence budget protocol initialState
      (sequenceMeaning target (agrees coreLookup) (.cons (.cellRef reference.typed) actualTyped)) trace bounded
  refine ⟨token, finalStore, finalMap, finalWorld, .target (.projectionExpression lookup read trace.sound), ?_,
    tokenRep, finalHeaps, maps, worlds, frame, metadata, post⟩
  apply execute_key_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
    (.cellRef (OptionalCell.cellType prepared.route.rootType) target) (.var (agrees coreLookup))
  simpa only [DataPlaceChildExpressions.rename_prefix, packed_renamed_expression, packed_renamed_type, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

theorem keys_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before place.projections reason after) (bounded : size ≤ budget)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact keys_bounded_with_sequence    (budget := budget)
    (_children := children)
    (protocol := protocol)
    (environments := environments)
    (_heaps := heaps)
    (_locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (lookup := lookup)
    (read := read)
    (trace := trace)
    (bounded := bounded)
    (operator := operator)
    (rhsId := rhsId)
    (rhs := rhs)
    (next := next)
    (outputType := outputType)
    (invalid := invalid)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))

end Stateful

theorem keys_bounded (budget : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry))
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsFault program size context evidence source environment before place.projections reason after) (bounded : size ≤ budget)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, sourceFault, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.keys_bounded budget children (ProtectedStatePlaceAssignment.legacyProtocol entry) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
      environments heaps locals agrees actualTyped ⟨installed⟩ slot lookup read trace bounded operator rhsId rhs next outputType invalid
  exact ⟨token, finalStore, finalMap, finalWorld, sourceFault, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩

theorem keys {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    {environment : Dynamic.Environment} {canonical coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {index : Nat} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (lookup : Dynamic.Environment.LooksUp environment place.root sourceLocation)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before place.projections reason after)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsFault.has_size trace
  exact keys_bounded size
    children transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot lookup read sized (Nat.le_refl size) operator rhsId rhs next outputType invalid


/- This composition consumes a semantic resolution result, produced by
ProtectedPlaceResolution.preserves, and the independent RHS fault. It derives
the actual RHS run and suppresses modifier, setter, write and continuation. -/
namespace Stateful
universe u v

theorem rhs_at_with_rhs (size : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (_generated : certificate scope id lowered) (_found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (_environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (_agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (_actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (rhsMeaning : ∀ {outcome after},
      RecursiveNamedCallBounds.ExpressionOutcome program size context evidence source environment targetHeap id outcome after →
      ∃ value store mapping world,
        CompatiblePlaceRhs.Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
          resolution id node (renamed lowered ξ) environment outcome after value store mapping world ∧
        ProtectedStateTransition.Transition protocol initialState ⟨scope, mapping, world, after, store, canonical⟩)
    (_locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨value, store, mapping, world, result, post⟩ :=
    rhsMeaning (.fault failed)
  cases represented : result.represented with
  | @fault _ token tokenRep =>
    refine ⟨token, store, mapping, world, .rhs resolved failed.sound, ?_, tokenRep, result.heaps,
      resolution.maps.trans result.maps, resolution.worlds.trans result.worlds,
      resolution.frame.trans result.frame, resolution.metadata.trans result.metadata, post⟩
    apply SourceCoreCompatibleDataPlaces.execute_rhs_failure prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ))
      (lowered.expression.rename ξ) next outputType (binaryOperator (prepared.route.leafType = .integer) operator) false invalid token
      (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target) (packValues resolution.values)
      (.inRight .unit resolution.snapshot) (.var reference) resolution.keysEvaluated resolution.snapshotEvaluated
    simpa only [renamed, coreType, snapshotEnvironment, keysEnvironment, referenceEnvironment] using result.evaluated

theorem rhs_at (size : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : ProtectedStateTransition.PreservesAt protocol (payloadModel checked registry functions) program context evidence source certificate faults size)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, resolution.mapping, resolution.world, targetHeap, resolution.store, canonical⟩)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact rhs_at_with_rhs    (size := size)
    (resolution := resolution)
    (protocol := protocol)
    (_generated := generated)
    (_found := found)
    (coreType := coreType)
    (_environments := environments)
    (_agrees := agrees)
    (_actualTyped := actualTyped)
    (initialState := initialState)
    (_locals := locals)
    (resolved := resolved)
    (reference := reference)
    (failed := failed)
    (operator := operator)
    (next := next)
    (outputType := outputType)
    (invalid := invalid)
    (rhsMeaning := by
      intro outcome after trace
      exact ProtectedPlaceRhs.Stateful.preserves_at resolution size protocol meaning generated found
        environments agrees actualTyped locals initialState trace)

end Stateful

theorem rhs_at (size : Nat) {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.PreservesAt size (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : SourceExecutionSize.ExpressionFaults program size context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, sourceFault, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.rhs_at size resolution (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacy_preserves transport meaning)
      generated found coreType environments agrees actualTyped
      ⟨transport.extend installed resolution.maps resolution.worlds resolution.frame resolution.metadata⟩
      locals resolved reference failed operator next outputType invalid
  exact ⟨token, finalStore, finalMap, finalWorld, sourceFault, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩

theorem rhs {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {sourceTarget : Dynamic.ResolvedPlace} {canonical coreEnvironment : Environment} {ξ : Renaming} {initialStore : Store}
    {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap after : Dynamic.Heap}
    (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared (renamedCodes codes ξ) sourceTypes place leaf sourceTarget
      coreEnvironment initialStore initialMap initialWorld before targetHeap)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults entry)
    {administrativeContext actualContext : Core.Context} {environment : Dynamic.Environment}
    {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (coreType : lowered.type = prepared.route.leafType)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment canonical)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes initialWorld coreEnvironment actualContext ambient.definitions)
    (installed : entry scope initialMap initialWorld before initialStore canonical)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (resolved : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    {index : Nat} (reference : coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target))
    {reason : Dynamic.SemanticFault}
    (failed : Dynamic.ExpressionFaults program context evidence source environment targetHeap id reason after)
    (operator : Syntax.ValueAssignOp) (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator id reason after ∧
      Evaluates coreEnvironment initialStore
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid)
        (.inLeft outputType (.word token)) finalStore ∧
      faults reason token ∧ HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends initialMap finalMap ∧ WorldExtends initialWorld finalWorld ∧
      AdministrativePreserved initialMap initialStore finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.ExpressionFaults.has_size failed
  exact rhs_at size
    resolution transport (RecursiveNamedBoundedContracts.preserves_at_of_unbounded meaning size) generated found coreType environments agrees actualTyped installed locals resolved reference sized operator next outputType invalid


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFailures


/-! Target-resolution faults before the RHS. The actual key runs are derived
from the protected expression theorem. The getter uses the live root after
those effects, preserving exact raw missing-default tokens and administrative
allocations. An absent ordinary root fails without allocating a helper. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {compilation : SourceCoreCompatibleDataPlaces.Context}
  {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
  {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {administrativeContext actualContext : Core.Context} {ξ : Renaming}
  {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
  {before after : Dynamic.Heap} {store : Store} {index : Nat}
  {location : Dynamic.Location} {initialCell currentCell : Dynamic.Cell}
  {resolved : List Dynamic.EvaluatedProjection}

/- Independent structural failure determines the actual whole emitted
assignment's failure before its RHS, modifier, setter or continuation starts. -/
namespace Stateful
universe u v

theorem projection_bounded_with_sequence_with_receipt (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ reason token := by
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨keys, keyPost⟩ := ProtectedPlaceAssignmentTargetKeys.Stateful.preserves_bounded_with_sequence budget layout.children protocol environments _heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead trace bounded
  obtain ⟨keyState, keyStateRelated⟩ := keyPost
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have present : ∃ sourceRoot, initial = some sourceRoot := by
    cases initial with
    | some value => exact ⟨value, rfl⟩
    | none => cases fault
  obtain ⟨sourceRoot, rfl⟩ := present
  have rootExists : ∃ optional rootValue,
      RootRead compilation.checked registry functions keys.keyMap keys.keyWorld prepared after keys.keyStore location keys.target
        currentCell optional sourceRoot rootValue := by
    cases initialValue with
    | initialized =>
      obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root keys.heaps keys.reference currentRead
      exact ⟨_, value, root⟩
    | emptyMapping key value =>
      obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root keys.heaps keys.reference currentRead
        (layout.virtual key value cellType.symm) registryExtension
      exact ⟨_, native, root⟩
  obtain ⟨optional, rootValue, root⟩ := rootExists
  have keyRelated : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) keys.keyMap keys.keyWorld sourceTypes (codes.map (·.type)) keys.sources keys.values := by
    simpa only [renamedCodes_types] using keys.related
  have arguments := layout.views.arguments keys.shaped keyRelated (fun _ _ found => by simpa only [Nat.zero_add] using found)
  have currentPath : PreparedPath compilation.checked source site currentCell.type place.projections
      0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
  have currentArguments : Arguments compilation.checked registry functions keys.keyMap keys.keyWorld source site keys.values
      currentPath resolved := by simpa only [cellType] using arguments
  obtain ⟨token, count, receipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
  have keyLength : prepared.keyTypes.length = keys.values.length := layout.keyTypes ▸ keyRelated.length.2
  obtain ⟨finalStore, administrative, _, _, evaluated, appended, _⟩ :=
    faultTree_at root tree layout.nonempty faithful observations keyLength
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      (SourceCoreCalls.packArguments codes).type (.var 1) (.var 0) (.var rfl) (.var rfl)
  have typedEnvironment : RuntimeEnvironmentHasTypes keys.keyWorld
      (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      ((SourceCoreCalls.packArguments codes).type :: OptionalCell.referenceType prepared.route.rootType ::
        actualContext) ambient.definitions :=
    .cons (CompatiblePlaceResolution.values_typed keyRelated)
      (.cons (.cellRef keys.reference.typed) (actualTyped.weaken keys.worlds))
  obtain ⟨finalWorld, extension, typedStore, _, frame⟩ :=
    evaluation_frame (mapping := keys.keyMap) keys.heaps.runtime_hasTypes typedEnvironment getterTyped evaluated appended
  let reached := transport.extend keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  have phaseRelated := transport.related keyState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl after)
  refine ⟨token, count, sourceRoot, finalStore, keys.keyMap, finalWorld,
    .target (.projectionRead lookup initialRead trace.sound currentRead initialValue fault), initialValue, receipt, ?_,
    CompatibleHeap.HeapRepresents.after_snapshot keys.heaps extension typedStore appended,
    keys.maps, keys.worlds.trans extension, keys.frame.trans frame, keys.metadata,
    reached, protocol.trans keyStateRelated phaseRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, location, keys.target,
      currentCell, optional, sourceRoot, rootValue, keys.values, resolved, count, currentPath,
      keyStateRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType, currentArguments, fault, receipt, tree⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))


theorem projection_bounded_with_sequence (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, present, receipt,
    evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    projection_bounded_with_sequence_with_receipt budget layout ordinary protocol transport environments _heaps
      locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead trace bounded currentRead
      registryExtension faithful observations initialValue fault operator rhsId rhs next outputType invalidOperand
  exact ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, present, receipt,
    evaluated, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem projection_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact projection_bounded_with_sequence    (budget := budget)
    (layout := layout)
    (ordinary := ordinary)
    (protocol := protocol)
    (transport := transport)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (lookup := lookup)
    (initialRead := initialRead)
    (trace := trace)
    (bounded := bounded)
    (currentRead := currentRead)
    (registryExtension := registryExtension)
    (faithful := faithful)
    (observations := observations)
    (initialValue := initialValue)
    (fault := fault)
    (operator := operator)
    (rhsId := rhsId)
    (rhs := rhs)
    (next := next)
    (outputType := outputType)
    (invalidOperand := invalidOperand)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget layout.children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))

end Stateful

theorem projection_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, initial, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.projection_bounded budget layout ordinary (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
      environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped lookup initialRead trace bounded currentRead
      registryExtension faithful observations initialValue fault operator rhsId rhs next outputType invalidOperand
  exact ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, initial, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩

theorem projection
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (initialValue : Dynamic.RootInitialValue currentCell initial)
    (fault : Dynamic.ProjectionsFaults initial resolved reason)
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId reason after ∧
      Dynamic.RootInitialValue currentCell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps resolved reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact projection_bounded size
    layout ordinary transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size) currentRead registryExtension faithful observations initialValue fault operator rhsId rhs next outputType invalidOperand


/- Actual describe supplies `ordinary`. It is a static route fact, not a
claim that native type equality recovers the source declaration. -/
namespace Stateful
universe u v

theorem uninitialized_bounded_with_sequence_with_receipt (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedPlaceReachedDiagnostics.UninitializedPost compilation.checked registry functions protocol environment place prepared initialState
        ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ location := by
  obtain ⟨keys, post⟩ := ProtectedPlaceAssignmentTargetKeys.Stateful.preserves_bounded_with_sequence budget layout.children protocol environments _heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead trace bounded
  have cellEq := currentRead.functional keys.read
  have cellType : currentCell.type = prepared.route.rootSourceType := cellEq ▸ keys.type
  have noVirtual : prepared.route.rootMapping = none := ordinary (fun key value same => notMapping ⟨key, value, cellType.trans same⟩)
  obtain ⟨optional, native, represented⟩ := CompatibleHeap.HeapRepresents.read_at keys.heaps keys.reference currentRead
  have absent : optional = .inLeft prepared.route.rootType .unit := by
    cases represented with
    | uninitialized => rfl
    | initialized => cases empty
  rw [absent] at native
  have evaluated : Evaluates (keysEnvironment prepared.route.rootType keys.target (packValues keys.values) coreEnvironment)
      keys.keyStore (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inLeft prepared.optionalLeaf (.word prepared.invalidProjection)) keys.keyStore := by
    apply Evaluates.apply .lambda (.pair (.loadCell (.var rfl) native) (.var rfl))
    cases steps : prepared.steps with
    | nil => exact (layout.nonempty steps).elim
    | cons head tail =>
      simp only [normalizeRoot, noVirtual, LanguageResult.failure]
      exact .caseLeft (.first (.var rfl)) (.inLeft .word)
  obtain ⟨keyState, keyRelated⟩ := post
  refine ⟨keys.keyStore, keys.keyMap, keys.keyWorld,
    .target (.uninitialized lookup initialRead trace.sound currentRead empty notMapping hasProjection), ?_,
    keys.heaps, keys.maps, keys.worlds, keys.frame, keys.metadata,
    keyState, keyRelated,
    ⟨⟨scope, keys.keyMap, keys.keyWorld, after, keys.keyStore, canonical⟩, keyState, keys.target, currentCell,
      .inLeft prepared.route.rootType .unit, keys.sources, resolved, keyRelated, protocol.refl keyState, rfl, rfl, rfl,
      .refl _, .refl _ _, lookup, currentRead, keys.reference, native, absent ▸ represented, cellType, empty, notMapping, layout.nonempty, keys.shaped, hasProjection⟩⟩
  unfold execute
  simp only [packed_renamed_type]
  exact .letE (.var keys.selected)
    (LanguageResult.bind_success _ keys.evaluated (LanguageResult.bind_failure _ evaluated))


theorem uninitialized_bounded_with_sequence (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  obtain ⟨finalStore, finalMap, finalWorld, sourceFault, evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    uninitialized_bounded_with_sequence_with_receipt budget layout protocol environments _heaps locals agrees actualTyped
      initialState sequenceMeaning slot rootTyped lookup initialRead trace bounded currentRead ordinary empty notMapping
      hasProjection operator rhsId rhs next outputType invalidOperand
  exact ⟨finalStore, finalMap, finalWorld, sourceFault, evaluated, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem uninitialized_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact uninitialized_bounded_with_sequence    (budget := budget)
    (layout := layout)
    (protocol := protocol)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (lookup := lookup)
    (initialRead := initialRead)
    (trace := trace)
    (bounded := bounded)
    (currentRead := currentRead)
    (ordinary := ordinary)
    (empty := empty)
    (notMapping := notMapping)
    (hasProjection := hasProjection)
    (operator := operator)
    (rhsId := rhsId)
    (rhs := rhs)
    (next := next)
    (outputType := outputType)
    (invalidOperand := invalidOperand)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget layout.children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))

end Stateful

theorem uninitialized_bounded (budget : Nat)
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {size : Nat} (trace : SourceExecutionSize.SourceProjectionsEvaluate program size context evidence source environment before place.projections resolved after) (bounded : size ≤ budget)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨finalStore, finalMap, finalWorld, sourceFault, evaluated, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.uninitialized_bounded budget layout (ProtectedStatePlaceAssignment.legacyProtocol entry) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
      environments heaps locals agrees actualTyped ⟨installed⟩ slot rootTyped lookup initialRead trace bounded currentRead
      ordinary empty notMapping hasProjection operator rhsId rhs next outputType invalidOperand
  exact ⟨finalStore, finalMap, finalWorld, sourceFault, evaluated, finalHeaps, maps, worlds, frame, metadata⟩

theorem uninitialized
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
    (currentRead : Dynamic.Heap.Reads after location currentCell)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (empty : currentCell.value = none)
    (notMapping : ¬ ∃ key value, currentCell.type = .mapping key value)
    (hasProjection : resolved ≠ [])
    (operator : Syntax.ValueAssignOp) (rhsId : ExpressionId) (rhs next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhsId
        (.uninitializedLocation location) after ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) rhs next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word prepared.invalidProjection)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourceProjectionsEvaluate.has_size trace
  exact uninitialized_bounded size
    layout transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) environments heaps locals agrees actualTyped installed slot rootTyped lookup initialRead sized (Nat.le_refl size) currentRead ordinary empty notMapping hasProjection operator rhsId rhs next outputType invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentTargetFaults


/-! Structural missing-default failure after the RHS. The source specification
traverses the latest root before applying the modifier. For authenticated equal
or scalar numeric operands, the generated earlier modifier is total; therefore
the same structural fault wins and neither source nor native final write runs.
Exact raw key guards come from the source fault, not native projection equality.
-/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentStructuralFault
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys CompatiblePlaceLiveRoot
open SourceCoreCompatibleDataPlaces DataPlaceExecution

/- All key/RHS native evaluations come from their protected child theorem. The fault
receipt retains the raw mapping header and ordered selection where traversal
stopped; no decoder or source evaluator supplies the semantic result. -/
namespace Stateful
universe u v

theorem preserves_bounded_with_producers_with_receipt (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (rhsMeaning : ProtectedPlaceRhs.PreservesAfter (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := rhs) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {resolveSize rhsSize : Nat}
    (resolve : SourceExecutionSize.SourcePlaceResolves program resolveSize context evidence source environment before place sourceTarget targetHeap)
    (evaluate : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right rhsHeap)
    (resolveBound : resolveSize ≤ budget) (rhsBound : rhsSize < budget)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap ∧
      ProtectedPlaceReachedDiagnostics.MissingPost compilation.checked registry functions protocol source site place prepared leaf initialState
        ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩ reason token := by
  have closed := virtual_closed layout ordinary
  have respects := environment_respects environments.runtime_hasTypes actualTyped agrees
  have getterTyped := getter_typed layout closed respects
  have setterTyped := setter_typed layout closed respects
  have sourceFault := Dynamic.SourcePlaceAssignmentFaults.structuralUpdate (operator := operator) resolve.sound evaluate.sound sourceRead rootType initialValue fault
  obtain ⟨resolution, coreLookup, resolutionPost⟩ := ProtectedPlaceResolution.Stateful.preserves_bounded_with_sequence budget layout.path layout.views layout.keyTypes
    layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped protocol transport faithful observations
    environments locals agrees actualTyped initialState sequenceMeaning slot rootTyped resolve resolveBound
  obtain ⟨resolutionState, resolutionRelated⟩ := resolutionPost
  obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult, rhsPost⟩ :=
    rhsMeaning resolve.sound resolution resolutionState resolutionRelated rhsBound (.value evaluate)
  cases represented : rhsResult.represented with
  | @value _ rightValue rightRep =>
    obtain ⟨rhsState, rhsRelated⟩ := rhsPost
    have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf right rightValue prepared.route.leafType :=
      .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
    have snapshotRep := rhsResult.saved_snapshot
    have keyRep : DataExpressionSequence.Values (payloadModel compilation.checked registry functions) rhsMap rhsWorld sourceTypes (codes.map (·.type)) resolution.sources resolution.values := by
      simpa only [renamedCodes_types] using resolution.keysRelated.extend rhsResult.maps rhsResult.worlds
    have reference := resolution.reference.extend rhsResult.maps rhsResult.worlds
    have arguments := layout.views.arguments resolution.shaped keyRep (fun _ _ _found => by simpa only [Nat.zero_add] using _found)
    obtain ⟨latest⟩ := rhsResult.latest
    have cellEq := sourceRead.functional latest.read
    have cellType : cell.type = prepared.route.rootSourceType := cellEq ▸ latest.type
    obtain ⟨replacement, replacementValue, replacementRep, _, modifiedEvaluated, valid⟩ :=
      CompatiblePlaceModifier.initialized_success observations operatorProfile snapshotRep rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalidOperand
    have present : ∃ sourceRoot, initial = some sourceRoot := by
      cases initial with
      | some value => exact ⟨value, rfl⟩
      | none => cases fault
    obtain ⟨sourceRoot, rfl⟩ := present
    have rootExists : ∃ optional rootValue,
        RootRead compilation.checked registry functions rhsMap rhsWorld prepared rhsHeap rhsStore sourceTarget.location resolution.target
          cell optional sourceRoot rootValue := by
      cases initialValue with
      | initialized =>
        obtain ⟨value, root⟩ := CompatibleHeap.HeapRepresents.initialized_root rhsResult.heaps reference sourceRead
        exact ⟨_, value, root⟩
      | emptyMapping key value =>
        obtain ⟨native, root⟩ := CompatibleHeap.HeapRepresents.virtual_root rhsResult.heaps reference sourceRead
          (layout.virtual key value cellType.symm) registryExtension
        exact ⟨_, native, root⟩
    obtain ⟨optional, rootValue, root⟩ := rootExists
    have keyLength : prepared.keyTypes.length = resolution.values.length := layout.keyTypes ▸ keyRep.length.2
    have typedEnvironment : RuntimeEnvironmentHasTypes rhsWorld
        (modifiedEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue replacementValue coreEnvironment)
        (prepared.route.leafType :: prepared.route.leafType :: prepared.optionalLeaf :: (SourceCoreCalls.packArguments codes).type ::
          OptionalCell.referenceType prepared.route.rootType :: actualContext)
        ambient.definitions :=
      .cons replacementRep.runtime_hasType (.cons rightRep.runtime_hasType (.cons (.inRight snapshotRep.runtime_hasType)
        (.cons (CompatiblePlaceResolution.values_typed keyRep) (.cons (.cellRef reference.typed)
          (actualTyped.weaken (resolution.worlds.trans rhsResult.worlds))))))
    have currentPath : PreparedPath compilation.checked source site cell.type place.projections
        0 prepared.steps prepared.keys leaf := cellType ▸ layout.path
    have currentArguments : Arguments compilation.checked registry functions rhsMap rhsWorld source site resolution.values
        currentPath sourceTarget.projections := by simpa only [cellType] using arguments
    obtain ⟨token, count, finalStore, administrative, finalWorld, receipt, setterEvaluated,
      finalHeaps, extension, frame, _, _, _⟩ :=
      CompatiblePlaceSetterFault.preserves root rhsResult.heaps currentArguments fault layout.nonempty
        faithful observations keyLength typedEnvironment setterTyped (.var rfl) (.var rfl) (.var rfl)
    obtain ⟨otherToken, otherCount, otherReceipt, tree⟩ := currentArguments.faultTree root.payload fault prepared
    obtain ⟨rfl, rfl⟩ := receipt.functional otherReceipt
    let reached := transport.extend rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    have phaseRelated := transport.related rhsState (.refl _) extension frame (Dynamic.HeapMetadataExtend.refl rhsHeap)
    refine ⟨token, count, sourceRoot, finalStore, rhsMap, finalWorld, sourceFault, initialValue, receipt, ?_, finalHeaps,
      resolution.maps.trans rhsResult.maps, (resolution.worlds.trans rhsResult.worlds).trans extension,
      (resolution.frame.trans rhsResult.frame).trans frame, resolution.metadata.trans rhsResult.metadata,
      reached, protocol.trans (protocol.trans resolutionRelated rhsRelated) phaseRelated,
      ⟨⟨scope, rhsMap, rhsWorld, rhsHeap, rhsStore, canonical⟩, rhsState, sourceTarget.location, resolution.target,
        cell, optional, sourceRoot, rootValue, resolution.values, sourceTarget.projections, count, currentPath,
        protocol.trans resolutionRelated rhsRelated, phaseRelated, rfl, rfl, rfl, extension, frame, root, cellType,
        currentArguments, fault, receipt, tree⟩⟩
    unfold execute
    simp only [packed_renamed_type]
    have snapshotEvaluated := resolution.snapshotEvaluated
    simp only [packed_renamed_type] at snapshotEvaluated
    exact .letE (.var coreLookup)
      (LanguageResult.bind_success _ resolution.keysEvaluated
        (LanguageResult.bind_success _ snapshotEvaluated
          (LanguageResult.bind_success _ rhsResult.evaluated
            (LanguageResult.bind_success _ modifiedEvaluated
              (LanguageResult.bind_failure _ setterEvaluated)))))


theorem preserves_bounded_with_producers (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (rhsMeaning : ProtectedPlaceRhs.PreservesAfter (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := rhs) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {resolveSize rhsSize : Nat}
    (resolve : SourceExecutionSize.SourcePlaceResolves program resolveSize context evidence source environment before place sourceTarget targetHeap)
    (evaluate : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right rhsHeap)
    (resolveBound : resolveSize ≤ budget) (rhsBound : rhsSize < budget)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩ := by
  obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, present, receipt,
    evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
    preserves_bounded_with_producers_with_receipt budget layout ordinary registryExtension protocol transport faithful observations
      _rhsGenerated _found rhsView rhsCoreType operatorProfile environments _heaps locals agrees actualTyped initialState
      sequenceMeaning rhsMeaning slot rootTyped resolve evaluate resolveBound rhsBound sourceRead rootType initialValue fault next outputType invalidOperand
  exact ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, present, receipt,
    evaluated, finalHeaps, maps, worlds, frame, metadata, post.forget⟩

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {resolveSize rhsSize : Nat}
    (resolve : SourceExecutionSize.SourcePlaceResolves program resolveSize context evidence source environment before place sourceTarget targetHeap)
    (evaluate : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right rhsHeap)
    (resolveBound : resolveSize ≤ budget) (rhsBound : rhsSize < budget)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, rhsHeap, finalStore, canonical⟩ := by
  exact preserves_bounded_with_producers    (budget := budget)
    (layout := layout)
    (ordinary := ordinary)
    (registryExtension := registryExtension)
    (protocol := protocol)
    (transport := transport)
    (faithful := faithful)
    (observations := observations)
    (_rhsGenerated := rhsGenerated)
    (_found := found)
    (rhsView := rhsView)
    (rhsCoreType := rhsCoreType)
    (operatorProfile := operatorProfile)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (resolve := resolve)
    (evaluate := evaluate)
    (resolveBound := resolveBound)
    (rhsBound := rhsBound)
    (sourceRead := sourceRead)
    (rootType := rootType)
    (initialValue := initialValue)
    (fault := fault)
    (next := next)
    (outputType := outputType)
    (invalidOperand := invalidOperand)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget layout.children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))
    (rhsMeaning := (ProtectedPlaceRhs.PreservesAfter.of_uniform budget protocol meaning rhsGenerated found
      environments agrees actualTyped locals initialState))

end Stateful

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {resolveSize rhsSize : Nat}
    (resolve : SourceExecutionSize.SourcePlaceResolves program resolveSize context evidence source environment before place sourceTarget targetHeap)
    (evaluate : SourceExecutionSize.ExpressionEvaluates program rhsSize context evidence source environment targetHeap rhs right rhsHeap)
    (resolveBound : resolveSize ≤ budget) (rhsBound : rhsSize < budget)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, initial, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_bounded budget layout ordinary registryExtension (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
      faithful observations rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped ⟨installed⟩
      slot rootTyped resolve evaluate resolveBound rhsBound sourceRead rootType initialValue fault next outputType invalidOperand
  exact ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, sourceFault, initial, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr} {node : ExpressionNode}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before targetHeap rhsHeap : Dynamic.Heap} {store : Store} {index : Nat}
    {sourceTarget : Dynamic.ResolvedPlace} {right : Dynamic.Value} {cell : Dynamic.Cell} {initial : Option Dynamic.Value} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (resolve : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget targetHeap)
    (evaluate : Dynamic.ExpressionEvaluates program context evidence source environment targetHeap rhs right rhsHeap)
    (sourceRead : Dynamic.Heap.Reads rhsHeap sourceTarget.location cell)
    (rootType : cell.type = sourceTarget.rootType)
    (initialValue : Dynamic.RootInitialValue cell initial)
    (fault : Dynamic.ProjectionsFaults initial sourceTarget.projections reason)
    (next : Expr) (outputType : Ty) (invalidOperand : Word) :
    ∃ token count sourceRoot finalStore finalMap finalWorld,
      Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason rhsHeap ∧
      Dynamic.RootInitialValue cell (some sourceRoot) ∧
      FaultToken compilation.checked registry sourceRoot prepared.steps sourceTarget.projections reason token count ∧
      Evaluates coreEnvironment store
        (execute prepared (.var (ξ index)) (SourceCoreCalls.packArguments (renamedCodes codes ξ)) (lowered.expression.rename ξ) next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalidOperand)
        (.inLeft outputType (.word token)) finalStore ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld rhsHeap finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before rhsHeap := by
  obtain ⟨resolveSize, resolveSized⟩ := SourceExecutionSize.SourcePlaceResolves.has_size resolve
  obtain ⟨rhsSize, rhsSized⟩ := SourceExecutionSize.ExpressionEvaluates.has_size evaluate
  exact preserves_bounded (resolveSize + rhsSize + 1)
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning (resolveSize + rhsSize + 1)) faithful observations rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped resolveSized rhsSized (by omega) (by omega) sourceRead rootType initialValue fault next outputType invalidOperand


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentStructuralFault


/-! Every independently specified assignment fault in the nonempty equal or
numeric profile is preserved. Unbound/dangling roots contradict actual lexical
and heap agreement. Invalid operands contradict the represented snapshot and
RHS values; neither exclusion is inferred from native type equality alone. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFaults
open CompatibleRenamedPlace
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

namespace Stateful
universe u v

theorem preserves_bounded_with_producers_with_diagnostics (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      source site place prepared leaf initialState faults)
    (uninitializedFor : ProtectedPlaceReachedDiagnostics.UninitializedFor compilation.checked registry functions protocol
      environment place prepared initialState faults)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (rhsMeaning : ProtectedPlaceRhs.PreservesAfter (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := rhs) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  simp only [execute_rename layout.path (virtual_closed layout ordinary), renamed_packed, Expr.rename]
  have getterTyped := getter_typed layout (virtual_closed layout ordinary) (environment_respects environments.runtime_hasTypes actualTyped agrees)
  obtain ⟨scheme, staticLookup, _, _, _⟩ := rootTyped.scheme
  obtain ⟨sourceLocation, sourceCell, sourceLookup, sourceRead, _, _⟩ := locals.lookup staticLookup
  cases trace with
  | target fault =>
    cases fault with
    | unbound missing => exact (missing.excludes_lookup sourceLookup).elim
    | dangling lookup missing =>
      have same := lookup.functional sourceLookup
      cases same
      exact (missing.excludes_read sourceRead).elim
    | projectionExpression lookup read fault =>
      obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
        ProtectedPlaceAssignmentFailures.Stateful.keys_bounded_with_sequence budget layout.children protocol environments _heaps locals agrees actualTyped initialState sequenceMeaning slot lookup read fault (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
          operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, post⟩
    | danglingAfterProjections lookup read evaluated missing =>
      obtain ⟨keys, _⟩ := ProtectedPlaceAssignmentTargetKeys.Stateful.preserves_bounded_with_sequence budget layout.children protocol environments _heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup read evaluated (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
      exact (missing.excludes_read keys.read).elim
    | projectionRead lookup initialRead evaluate currentRead initialValue fault =>
      obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
        ProtectedPlaceAssignmentTargetFaults.Stateful.projection_bounded_with_sequence_with_receipt budget layout ordinary protocol transport environments _heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead
          registryExtension faithful observations initialValue fault operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      obtain ⟨reached, related, witness⟩ := post
      exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingFor reached related witness, finalHeaps, maps, worlds, frame, metadata, reached, related⟩
    | uninitialized lookup initialRead evaluate currentRead empty notMapping projected =>
      obtain ⟨finalStore, finalMap, finalWorld, _, evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
        ProtectedPlaceAssignmentTargetFaults.Stateful.uninitialized_bounded_with_sequence_with_receipt budget layout protocol environments _heaps locals agrees actualTyped initialState sequenceMeaning slot rootTyped lookup initialRead evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead
          ordinary empty notMapping projected operator rhs (lowered.expression.rename ξ) (next.rename ξ) outputType invalid
      obtain ⟨reached, related, witness⟩ := post
      exact ⟨prepared.invalidProjection, finalStore, finalMap, finalWorld, evaluated, uninitializedFor reached related witness, finalHeaps, maps, worlds, frame, metadata, reached, related⟩
  | rhs resolve fault =>
    obtain ⟨resolution, coreLookup, resolutionPost⟩ := ProtectedPlaceResolution.Stateful.preserves_bounded_with_sequence budget layout.path layout.views layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped protocol transport faithful observations
      environments locals agrees actualTyped initialState sequenceMeaning slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨resolutionState, resolutionRelated⟩ := resolutionPost
    obtain ⟨token, finalStore, finalMap, finalWorld, _, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedPlaceAssignmentFailures.Stateful.rhs_at_with_rhs _ resolution protocol _rhsGenerated _found rhsCoreType environments agrees actualTyped resolutionState
        (rhsMeaning resolve.sound resolution resolutionState resolutionRelated (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)) locals resolve.sound coreLookup fault
        operator (next.rename ξ) outputType invalid
    obtain ⟨reached, related⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, reached, protocol.trans resolutionRelated related⟩
  | operands resolve evaluate _ _ _ _ invalidOperands =>
    obtain ⟨resolution, coreLookup, resolutionPost⟩ := ProtectedPlaceResolution.Stateful.preserves_bounded_with_sequence budget layout.path layout.views layout.keyTypes
      layout.leafProjected layout.virtual registryExtension layout.nonempty getterTyped protocol transport faithful observations
      environments locals agrees actualTyped initialState sequenceMeaning slot rootTyped resolve (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega)
    obtain ⟨resolutionState, resolutionRelated⟩ := resolutionPost
    obtain ⟨rightResult, rhsStore, rhsMap, rhsWorld, rhsResult, _⟩ :=
      rhsMeaning resolve.sound resolution resolutionState resolutionRelated (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) (.value evaluate)
    cases represented : rhsResult.represented with
    | @value _ rightValue rightRep =>
      have rightRep : ValueRep compilation.checked registry functions rhsMap rhsWorld leaf _ rightValue prepared.route.leafType :=
        .compatible rhsView (by simpa only [payloadModel, renamed, rhsCoreType] using rightRep)
      obtain ⟨_, _, _, _, _, valid⟩ := CompatiblePlaceModifier.initialized_success observations operatorProfile
        rhsResult.saved_snapshot rightRep
        (environment := rhsEnvironment prepared.route.rootType resolution.target (packValues resolution.values)
          (.inRight .unit resolution.snapshot) rightValue coreEnvironment)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rw [resolution.selectedEq] at invalidOperands
      exact (valid invalidOperands).elim
  | structuralUpdate resolve evaluate currentRead sameType initialValue fault =>
    obtain ⟨token, count, sourceRoot, finalStore, finalMap, finalWorld, _, _, receipt, evaluated, finalHeaps, maps, worlds, frame, metadata, post⟩ :=
      ProtectedPlaceAssignmentStructuralFault.Stateful.preserves_bounded_with_producers_with_receipt budget layout ordinary registryExtension protocol transport faithful observations _rhsGenerated _found rhsView rhsCoreType
        operatorProfile environments _heaps locals agrees actualTyped initialState sequenceMeaning rhsMeaning slot rootTyped resolve evaluate (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) (by simp only [SourceExecutionSize.stepSize, List.sum_cons, List.sum_nil] at bounded; omega) currentRead sameType initialValue fault (next.rename ξ) outputType invalid
    obtain ⟨reached, related, witness⟩ := post
    exact ⟨token, finalStore, finalMap, finalWorld, evaluated, missingFor reached related witness, finalHeaps, maps, worlds, frame, metadata, reached, related⟩


theorem preserves_bounded_with_producers (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (_rhsGenerated : certificate scope rhs lowered) (_found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (_heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (sequenceMeaning : ∀ target,
      coreEnvironment[ξ index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target) →
      RuntimeEnvironmentHasTypes world
        (.cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (OptionalCell.referenceType prepared.route.rootType :: actualContext) ambient.definitions →
      ProtectedStateExpressionSequenceProducer.Preserves
        (program := program) (context := context) (evidence := evidence) (source := source)
        (ids := DataPlaceKeyOrder.sourceKeys place.projections) (sourceTypes := sourceTypes) (codes := codes) (faults := faults)
        (environment := environment) (actual := .cellRef (OptionalCell.cellType prepared.route.rootType) target :: coreEnvironment)
        (ξ := DataPlaceChildExpressions.prefixRenaming 1 ξ)
        (payloadModel compilation.checked registry functions) initialState budget)
    (rhsMeaning : ProtectedPlaceRhs.PreservesAfter (checked := compilation.checked) (registry := registry) (functions := functions)
      (program := program) (context := context) (evidence := evidence) (source := source)
      (prepared := prepared) (place := place) (codes := codes) (sourceTypes := sourceTypes) (leaf := leaf)
      (faults := faults) (id := rhs) (node := node) (lowered := lowered) (environment := environment)
      (coreEnvironment := coreEnvironment) (ξ := ξ) protocol initialState budget)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_producers_with_diagnostics budget layout ordinary registryExtension protocol transport faithful observations
    _rhsGenerated _found rhsView rhsCoreType operatorProfile environments _heaps locals agrees actualTyped initialState
    (ProtectedPlaceReachedDiagnostics.MissingFor.of_uniform missingTokens)
    (ProtectedPlaceReachedDiagnostics.UninitializedFor.of_uniform invalidTokens)
    sequenceMeaning rhsMeaning slot rootTyped trace bounded next outputType invalid

theorem preserves_bounded_with_diagnostics (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (missingFor : ProtectedPlaceReachedDiagnostics.MissingFor compilation.checked registry functions protocol
      source site place prepared leaf initialState faults)
    (uninitializedFor : ProtectedPlaceReachedDiagnostics.UninitializedFor compilation.checked registry functions protocol
      environment place prepared initialState faults)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_producers_with_diagnostics    (budget := budget)
    (layout := layout)
    (ordinary := ordinary)
    (registryExtension := registryExtension)
    (protocol := protocol)
    (transport := transport)
    (faithful := faithful)
    (observations := observations)
    (missingFor := missingFor)
    (uninitializedFor := uninitializedFor)
    (_rhsGenerated := rhsGenerated)
    (_found := found)
    (rhsView := rhsView)
    (rhsCoreType := rhsCoreType)
    (operatorProfile := operatorProfile)
    (environments := environments)
    (_heaps := heaps)
    (locals := locals)
    (agrees := agrees)
    (actualTyped := actualTyped)
    (initialState := initialState)
    (slot := slot)
    (rootTyped := rootTyped)
    (trace := trace)
    (bounded := bounded)
    (next := next)
    (outputType := outputType)
    (invalid := invalid)
    (sequenceMeaning := (by
      intro target _ hiddenTyped
      exact ProtectedStateExpressionSequenceProducer.Preserves.of_uniform (initial := initialState) budget layout.children
        (fun size bounded => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bounded))
        environments heaps locals (DataPlaceChildExpressions.prefix_agrees agrees
          [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) hiddenTyped))
    (rhsMeaning := (ProtectedPlaceRhs.PreservesAfter.of_uniform budget protocol meaning rhsGenerated found
      environments agrees actualTyped locals initialState))


theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
    (transport : ProtectedStateTransition.AdministrativeTransport protocol)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => ProtectedStateTransition.PreservesAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (initialState : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after ∧
      ProtectedStateTransition.Transition protocol initialState ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩ := by
  exact preserves_bounded_with_diagnostics budget layout ordinary registryExtension protocol transport meaning faithful observations
    rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped initialState
    (ProtectedPlaceReachedDiagnostics.MissingFor.of_uniform missingTokens)
    (ProtectedPlaceReachedDiagnostics.UninitializedFor.of_uniform invalidTokens)
    slot rootTyped trace bounded next outputType invalid

end Stateful

theorem preserves_bounded (budget : Nat) {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size => RecursiveNamedBoundedContracts.PreservesAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    {size : Nat} (trace : SourceExecutionSize.SourcePlaceAssignmentFaults program size context evidence source environment before place operator rhs reason after) (bounded : size ≤ budget)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata, _⟩ :=
    Stateful.preserves_bounded budget layout ordinary registryExtension (ProtectedStatePlaceAssignment.legacyProtocol entry) (ProtectedStatePlaceAssignment.legacyTransport transport) (fun size smaller => ProtectedStatePlaceAssignment.legacy_preserves transport (meaning size smaller))
      faithful observations missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped ⟨installed⟩
      slot rootTyped trace bounded next outputType invalid
  exact ⟨token, finalStore, finalMap, finalWorld, evaluated, tokenRep, finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext actualContext : Core.Context} {ξ : Renaming}
    (layout : CompatiblePlaceAssignmentSuccess.Layout (definitions := ambient.definitions) compilation source certificate scope site place prepared codes sourceTypes leaf administrativeContext)
    (ordinary : (∀ key value, prepared.route.rootSourceType ≠ .mapping key value) → prepared.route.rootMapping = none)
    (registryExtension : SourceCoreRawMetadata.Extends compilation.registry registry)
    {entry : ProtectedExpressionMeaning.Entry} (transport : ProtectedExpressionMeaning.Transport entry)
    (meaning : ProtectedExpressionMeaning.Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (missingTokens : ∀ {root resolved reason token count},
      FaultToken compilation.checked registry root prepared.steps resolved reason token count → faults reason token)
    (invalidTokens : ∀ location, faults (.uninitializedLocation location) prepared.invalidProjection)
    {rhs : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
    (rhsGenerated : certificate scope rhs lowered) (found : source.lookupExpression? rhs = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCoreType : lowered.type = prepared.route.leafType)
    {operator : Syntax.ValueAssignOp}
    (operatorProfile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType leaf = .word ∨
      SourceCoreRawMetadata.runtimeType leaf = .integer ∧ operator.wordOnly = false)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {canonical coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical coreEnvironment)
    (actualTyped : RuntimeEnvironmentHasTypes world coreEnvironment actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {reason : Dynamic.SemanticFault}
    (trace : Dynamic.SourcePlaceAssignmentFaults program context evidence source environment before place operator rhs reason after)
    (next : Expr) (outputType : Ty) (invalid : Word) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates coreEnvironment store
        ((execute prepared (.var index) (SourceCoreCalls.packArguments codes) lowered.expression next outputType
          (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ)
        (.inLeft outputType (.word token)) finalStore ∧ faults reason token ∧
      HeapRepresents compilation.checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨size, sized⟩ := SourceExecutionSize.SourcePlaceAssignmentFaults.has_size trace
  exact preserves_bounded size
    layout ordinary registryExtension transport (RecursiveNamedBoundedContracts.preserves_below_of_unbounded meaning size) faithful observations missingTokens invalidTokens rhsGenerated found rhsView rhsCoreType operatorProfile environments heaps locals agrees actualTyped installed slot rootTyped sized (Nat.le_refl size) next outputType invalid


end Solcore.SourceSemantics.CoreLowering.ProtectedPlaceAssignmentFaults
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignmentReflection
/-! Completed bare assignment code reconstructs the independent source
transaction or fault. RHS meaning is typed and instantiated in the actual
three temporary slots; successful continuation typing names its seven values.
A concrete expression-tree consumer discharges the child interface separately. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution CoreProof
open CompatibleBareAssignment
universe u v

variable {compilation : SourceCoreCompatibleDataPlaces.Context} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions compilation.checked.catalog.definitions} {functions : FunctionModel compilation.checked.catalog ambient}
  {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
  {prepared : Prepared} {place : PlaceResolution} {environment : Dynamic.Environment} {canonical actual : Environment}
  {before : Dynamic.Heap} {store : Store} {mapping : LocationMap} {world : StoreTyping} {index : Nat} {ξ : Renaming}
  {scope : Scope} {administrativeContext actualContext : Core.Context} {certificate : Certificate} {faults : FaultRep}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}
  {operator : Syntax.ValueAssignOp} {identities : Dynamic.Value → Word → Prop}
  {entry : ProtectedExpressionMeaning.Entry}

/- Finite reflection needs no source RHS trace and no chosen child execution.
The actual completed code is the sole runtime premise. -/
namespace Stateful
variable {Records : Type v} (protocol : ProtectedStateTransition.Protocol.{u, v} Records)
  (transport : ProtectedStateTransition.AdministrativeTransport protocol)

include transport in
theorem reflects_reachable_bounded_with_rhs (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (rhsMeaning : ∀ (snapshot : Snapshot compilation.checked registry functions prepared place environment actual before store mapping world (ξ index))
      (child : Nat), child < budget → ∀ {value : Value} {finalStore : Store},
      EvaluationSize child (snapshotEnvironment prepared.route.rootType snapshot.target .unit snapshot.value actual)
        store (shift 3 (lowered.expression.rename ξ)) value finalStore →
      ∃ sourceSize outcome after finalMap finalWorld,
        RecursiveNamedCallBounds.ExpressionOutcome program sourceSize context evidence source environment before id outcome after ∧
        RhsResult (program := program) (context := context) (evidence := evidence) (source := source)
          (faults := faults) (id := id) (node := node) (lowered := lowered) snapshot outcome after value finalStore finalMap finalWorld ∧
        ProtectedStateTransition.Transition protocol initial ⟨scope, finalMap, finalWorld, after, finalStore, canonical⟩)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (_generated : certificate scope id lowered) (_found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateBareAssignment.ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
      id actual actualContext ξ initial next outputType value finalStore := by
  obtain ⟨snapshot⟩ := snapshot_of_heap layout extension environments heaps locals agrees slot rootTyped
  have phase :=  snapshot_prefix layout snapshot lowered.expression next outputType
    (binaryOperator (prepared.route.leafType = .integer) operator) invalid
  obtain ⟨prefixSize, prefixBound, remaining⟩ := RecursiveNamedBareAssignmentContracts.snapshot_prefix_sized layout snapshot completed
  cases remaining with
  | caseLeft evaluated _ =>
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, rhsPost⟩ :=
      rhsMeaning snapshot _ (by omega) evaluated
    cases related : result.represented with
    | fault token =>
      have failed := phase.wrap (LanguageResult.bind_failure outputType result.evaluated)
      obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound failed
      cases sourceTrace with
      | fault fault =>
        exact .fault (.rhs (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) fault) rfl token result.heaps result.maps result.worlds result.frame result.metadata rhsPost
  | caseRight evaluated remaining =>
    rename_i rhsStore rightValue
    obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, sourceTrace, result, rhsPost⟩ :=
      rhsMeaning snapshot _ (by omega) evaluated
    cases related : result.represented with
    | value payload =>
      rename_i right
      rename_i rhsStore
      have rightRep : ValueRep compilation.checked registry functions finalMap finalWorld prepared.route.rootSourceType right rightValue prepared.route.rootType :=
        .compatible rhsView (by simpa only [payloadModel, rhsCore, ← layout.sameType] using payload)
      have saved := snapshot.represented.extend result.maps result.worlds
      have modifier := modifier_total observations profile saved rightRep
        (environment := rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual)
        (.var (index := 1) rfl) (.var (index := 0) rfl) rhsStore invalid
      rcases modifier with ⟨invalidOperands, failed⟩ | ⟨updated, updatedValue, replacement, applied, modified⟩
      · have failed : Evaluates (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
            (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
            (.inLeft prepared.route.leafType (.word invalid)) rhsStore := by
          simpa only [layout.sameType] using failed
        have evaluation := phase.wrap (LanguageResult.bind_success outputType result.evaluated
          (LanguageResult.bind_failure outputType failed))
        obtain ⟨rfl, rfl⟩ := evaluation_deterministic completed.sound evaluation
        obtain ⟨latest⟩ := result.latest
        obtain ⟨initial, initialized⟩ := cell_initial latest.related
        cases sourceTrace with
        | value rhsTrace =>
          exact .fault (.operands (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) rhsTrace latest.read
            (latest.type.trans snapshot.type.symm) initialized .nil invalidOperands) rfl (invalidToken _ _ invalidOperands)
            result.heaps result.maps result.worlds result.frame result.metadata rhsPost
      · cases sourceTrace with
        | value rhsTrace =>
          obtain ⟨latest⟩ := result.latest
          obtain ⟨initial, initialValue⟩ := cell_initial latest.related
          have nativeModified : Evaluates
              (rhsEnvironment prepared.route.rootType snapshot.target .unit snapshot.value rightValue actual) rhsStore
              (SourceCoreCompatibleDataPlaces.modified prepared.route.leafType (binaryOperator (prepared.route.leafType = .integer) operator) false (.var 1) (.var 0) invalid)
              (.inRight .word updatedValue) rhsStore := by simpa only [layout.sameType] using modified
          obtain ⟨after, commitStore, _, written, finalHeaps, frame, metadata, typed, writeFrame, writeMetadata, agreement⟩ :=
            commit_with_write layout snapshot bare result rightRep replacement applied nativeModified actualTyped
          have terminal := (agreement .unit outputType).wrap
            (by simpa [shift, Expr.rename, List.range, List.range.loop, List.foldl, Expr.weakenAt] using
              (Evaluates.unit (environment := writtenEnvironment prepared.route.rootType snapshot.target .unit
                snapshot.value rightValue updatedValue updatedValue actual) (store := commitStore)))
          obtain ⟨remainingSize, remainingBound, remaining⟩ :=
            RecursiveNamedBareAssignmentContracts.continuation_sized layout snapshot result.evaluated nativeModified
              latest.nativeRead terminal completed
          obtain ⟨rhsState, rhsRelated⟩ := rhsPost
          exact .success (.intro (RecursiveNamedBareAssignmentContracts.resolves_sized snapshot bare) rhsTrace
              (.intro latest.read (latest.type.trans snapshot.type.symm) initialValue (.leaf applied) written))
            replacement finalHeaps result.maps result.worlds frame metadata
            (slots := [.unit, updatedValue, updatedValue, rightValue, snapshot.value, .unit,
              .cellRef (OptionalCell.cellType prepared.route.rootType) snapshot.target]) rfl typed remainingBound remaining
            ⟨transport.extend rhsState (.refl _) (.refl _) writeFrame writeMetadata,
              protocol.trans rhsRelated (transport.related rhsState (.refl _) (.refl _) writeFrame writeMetadata)⟩

include transport in
theorem reflects_reachable_bounded (budget : Nat)
    (initial : protocol.State ⟨scope, mapping, world, before, store, canonical⟩)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      ProtectedStateTransition.ReflectsAt protocol (payloadModel compilation.checked registry functions) program context evidence source certificate faults size))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    ProtectedStateBareAssignment.ResultAt protocol size compilation registry functions program context evidence source faults prepared place operator scope canonical environment before store mapping world
      id actual actualContext ξ initial next outputType value finalStore := by
  exact reflects_reachable_bounded_with_rhs protocol transport budget initial layout bare extension
    (fun snapshot child smaller {_ _} evaluated => Stateful.rhs_reflects_at snapshot protocol child (meaning child smaller)
      generated found environments heaps locals agrees actualTyped initial evaluated)
    observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped invalidToken completed bounded

end Stateful

theorem reflects_reachable_bounded (budget : Nat)
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : RecursiveNamedBoundedContracts.Below budget (fun size =>
      RecursiveNamedBoundedContracts.ReflectsAt size (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry))
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    {size : Nat} (completed : EvaluationSize size actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) (bounded : size ≤ budget) :
    RecursiveNamedBareAssignmentContracts.ResultAt size compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  exact (Stateful.reflects_reachable_bounded_with_rhs (scope := scope) (canonical := canonical)
    ProtectedStateBareAssignment.unitProtocol ProtectedStateBareAssignment.unitTransport budget () layout bare extension
    (fun snapshot child smaller {_ _} evaluated => by
      obtain ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result⟩ := rhs_reflects_at snapshot child (meaning child smaller)
        generated found environments heaps locals agrees actualTyped installed evaluated
      exact ⟨sourceSize, outcome, after, finalMap, finalWorld, trace, result, (), trivial⟩)
    observations generated found rhsView rhsCore profile environments heaps locals agrees actualTyped slot rootTyped invalidToken completed bounded).forget

theorem reflects_reachable
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : AssignmentOperandDiagnostics.OperandsLaw faults operator invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    CompatibleBareAssignment.Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  obtain ⟨size, sized⟩ := evaluation_has_size completed
  exact (reflects_reachable_bounded size layout bare extension
    (RecursiveNamedBoundedContracts.reflects_below_of_unbounded meaning size) observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped invalidToken sized (Nat.le_refl size)).erase

/-- Compatibility entry point retaining the original operand-token premise. -/
theorem reflects
    (layout : Layout compilation prepared) (bare : place.projections = [])
    (extension : SourceCoreRawMetadata.Extends compilation.registry registry)
    (meaning : ProtectedExpressionMeaning.Reflects (payloadModel compilation.checked registry functions) program context evidence source certificate faults entry)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (rhsView : SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = SourceCoreRawMetadata.runtimeType node.type)
    (rhsCore : lowered.type = prepared.route.leafType)
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .word ∨
      SourceCoreRawMetadata.runtimeType prepared.route.rootSourceType = .integer ∧ operator.wordOnly = false)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog)
      mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (agrees : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (installed : entry scope mapping world before store canonical)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    {next : Expr} {outputType : Ty} {invalid : Word} {value : Value} {finalStore : Store}
    (invalidToken : faults (.invalidAssignmentOperands operator) invalid)
    (completed : Evaluates actual store
      ((execute prepared (.var index) (SourceCoreCalls.packArguments []) lowered.expression next outputType
        (binaryOperator (prepared.route.leafType = .integer) operator) false invalid).rename ξ) value finalStore) :
    CompatibleBareAssignment.Result compilation registry functions program context evidence source faults prepared place operator environment before store mapping world
      id actual actualContext ξ next outputType value finalStore := by
  exact reflects_reachable layout bare extension meaning observations generated found rhsView rhsCore profile
    environments heaps locals agrees actualTyped installed slot rootTyped
    (AssignmentOperandDiagnostics.of_unconditional invalidToken) completed

end Solcore.SourceSemantics.CoreLowering.ProtectedBareAssignment
end
