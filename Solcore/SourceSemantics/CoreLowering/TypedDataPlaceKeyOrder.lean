import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.TypedDataExpressionSequence

/-! Typed argument packing for place keys reuses the independent projection
traces and their established ordering. Actual inserted operands may include
closures; their runtime types come from the complete represented payloads. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder
open Core Frontend SourceInference GeneralHeap DataPatternValues DataPlaceKeyOrder
open GenericExpressionMeaning (FaultRep)
open SourceCoreLocalCell (Scope)

/-- Index effects are evaluated exactly once in source projection order. The
generated values remain fully represented after later index effects. -/
theorem preserves {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {evaluated : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections evaluated after) :
    ∃ sources values finalStore finalMap finalWorld,
      Values projections sources evaluated ∧
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (packValues values)) finalStore ∧
      DataExpressionSequence.Values model finalMap finalWorld types (codes.map (·.type)) sources values ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, shaped, executed⟩ := projections_values trace
  obtain ⟨values, finalStore, finalMap, finalWorld, evaluated, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := TypedDataExpressionSequence.preserves_values tree meaning environments heaps locals layout actualTyped executed
  exact ⟨sources, values, finalStore, finalMap, finalWorld, shaped, evaluated, represented,
    finalHeaps, maps, worlds, frame, metadata⟩

theorem preserves_fault {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {reason : Dynamic.SemanticFault}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (trace : Dynamic.SourceProjectionsFault program context evidence source environment before projections reason after) :
    ∃ token finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inLeft (SourceCoreCalls.packArguments codes).type (.word token)) finalStore ∧
      faults reason token ∧ GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after :=
  TypedDataExpressionSequence.preserves_fault tree meaning environments heaps locals layout actualTyped (projections_fault trace)

theorem reflects {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection} {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {certificate : GenericExpressionMeaning.Certificate} {faults : FaultRep}
    {projections : List PlaceProjection} {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope (sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Reflects model program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store finalStore : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents catalog mapping world administrativeContext scope environment canonical definitions)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext definitions)
    (evaluated : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value finalStore) :
    ∃ outcome after finalMap finalWorld,
      OutcomeTrace program context evidence source environment before projections outcome after ∧
      DataExpressionSequence.Result model finalMap finalWorld types codes faults outcome value ∧
      GenericHeap.HeapRepresents model finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps,
    maps, worlds, frame, metadata⟩ := TypedDataExpressionSequence.reflects tree meaning environments heaps locals layout actualTyped evaluated
  refine ⟨outcome, after, finalMap, finalWorld, ?_, represented, finalHeaps, maps, worlds, frame, metadata⟩
  cases sourceTrace with
  | values trace => obtain ⟨evaluated, shaped, sourceTrace⟩ := values_projections trace; exact .values shaped sourceTrace
  | fault trace => exact .fault (fault_projections trace)

end Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder
