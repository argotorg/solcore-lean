import Solcore.SourceSemantics.CoreLowering.CallableIndexedParameters
import Solcore.SourceSemantics.CoreLowering.CallableIndexedBodyFrames

/-! The real accepted parameter compiler reaches a closure-producing body.
The returned closure captures the actual temporary environment, while the
independent source parameter cells and previous context/snapshots are retained.
This tests both directions without exact closure equality under weakening. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedParameters
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

theorem accepted_closure_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {bindings : List Binding} {code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source [] bindings (.function .unit .unit) SourceCoreFunctions.argumentProjection
        (LanguageResult.success (.lambda .unit .unit (.var 0))) = .ok code)
    (inputs : source.inputs = bindings.map Prod.fst)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects}
    (definitions : layouts.definitions = catalog.definitions)
    (registered : layout.Registered catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame}
    {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    {owned : CallableAncestryPairedLookup.Inputs base} {table : CallableAncestryPairedLookup.Table}
    {records : List CallableIndexedSnapshots.Record}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues values :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (caller : CellState owned table layout contextLocation native ghost store)
    (snapshots : CallableIndexedSnapshots.All owned table layout mapping store records)
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalActual finalStore finalMap finalWorld,
      Dynamic.BindersAllocate [] heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      Evaluates actual store (code.rename ξ)
        (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore ∧
      CellState owned table layout contextLocation native ghost finalStore ∧
      CallableIndexedSnapshots.All owned table layout finalMap finalStore records ∧
      (∀ result finished, Evaluates actual store (code.rename ξ) result finished →
        result = .inRight .word (.closure .unit .unit (.var 0) finalActual) ∧ finished = finalStore) := by
  obtain ⟨finalEnvironment, finalHeap, _, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, _, finalHeaps, _, _, frame, _, agreement⟩ :=
    CallableIndexedParameters.named_prefix onError accepted inputs definitions registered represented
      environments heaps actualLayout reference caller.read unmapped
  have child : Evaluates finalActual finalStore
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).rename finalEmbedding)
      (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore := .inRight .lambda
  have evaluated := agreement.wrap child
  refine ⟨finalEnvironment, finalHeap, finalActual, finalStore, finalMap, finalWorld, allocated,
    finalHeaps, evaluated, CallableIndexedBodyFrames.body_current unmapped caller frame,
    snapshots.transport frame, ?_⟩
  intro result finished evaluated'
  have child' := agreement.unwrap evaluated'
  exact evaluation_deterministic child' child

/-- Argument payloads need no first-order restriction. The two copies may be
closures sharing the same mutable capture, and packing preserves their value. -/
example {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects} {mapping : LocationMap} {world : StoreTyping}
    (left right : SourceInference.TypedBinder) (type : Ty) (source : Dynamic.Value) (value : Value)
    (first : model.Represents mapping world left.scheme.body source value type)
    (second : model.Represents mapping world right.scheme.body source value type) :
    RuntimeValueHasType world (.pair value value) (.product type type) catalog.definitions := by
  have arguments : Arguments model mapping world [(left, type), (right, type)] [source, source] [value, value] :=
    .cons first (.cons second .nil)
  exact CallableIndexedParameters.Arguments.pack_typed arguments

end Solcore.Test.SourceCoreCallableIndexedParameters
