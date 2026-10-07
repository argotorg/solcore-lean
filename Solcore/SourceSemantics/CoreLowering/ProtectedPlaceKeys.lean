import Solcore.SourceSemantics.CoreLowering.ProtectedStatePlaceAssignment
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPlaceKeyContracts

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
  obtain ⟨sources, vectorSize, shaped, executed, vectorBound⟩ := RecursiveNamedPlaceKeyContracts.projections_values trace
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata, post⟩ := ProtectedDataExpressionSequence.Stateful.preserves_values_bounded protocol budget tree
      (fun size bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bound))
      environments heaps locals layout actualTyped initial executed (Nat.le_trans vectorBound bounded)
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata, post⟩


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
  obtain ⟨vectorSize, failed, vectorBound⟩ := RecursiveNamedPlaceKeyContracts.projections_fault trace
  exact ProtectedDataExpressionSequence.Stateful.preserves_fault_bounded protocol budget tree
    (fun size bound => ProtectedStateTransition.SequenceBridge.preserves_at protocol (meaning size bound))
    environments heaps locals layout actualTyped initial failed (Nat.le_trans vectorBound bounded)


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
  obtain ⟨vectorSize, outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata, post⟩ := ProtectedDataExpressionSequence.Stateful.reflects_bounded protocol budget tree
      (fun size bound => ProtectedStateTransition.SequenceBridge.reflects_at protocol (meaning size bound))
      environments heaps locals layout actualTyped initial evaluated bounded
  cases sourceTrace with
  | values trace =>
    obtain ⟨sourceSize, evaluated, shaped, sourceTrace⟩ := RecursiveNamedPlaceKeyContracts.values_projections trace
    exact ⟨sourceSize, _, after, finalMap, finalWorld, .values shaped sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, post⟩
  | fault trace =>
    obtain ⟨sourceSize, sourceTrace⟩ := RecursiveNamedPlaceKeyContracts.fault_projections trace
    exact ⟨sourceSize, _, after, finalMap, finalWorld, .fault sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata, post⟩


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
