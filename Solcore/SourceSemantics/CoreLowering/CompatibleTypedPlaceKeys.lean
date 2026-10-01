import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys
import Solcore.SourceSemantics.CoreLowering.TypedDataPlaceKeyOrder

/-! Typed key computations produce the existing authenticated path Arguments.
Raw source type views stay explicit and are never inferred from native equality.
The unrestricted key API remains unchanged. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatibleMixedRoute CompatibleHeap CompatiblePlaceKeys

/-- Universal expression preservation constructs the key executions and their
intervening live heaps. This theorem adds path Arguments to the shared result. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {resolved : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues values)) finalStore ∧
      Arguments checked registry functions finalMap finalWorld source site values path resolved ∧
      HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, values, finalStore, finalMap, finalWorld, shaped, ran, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.preserves tree meaning environments heaps locals layout actualTyped trace
  exact ⟨values, finalStore, finalMap, finalWorld, ran,
    views.arguments shaped represented (fun _ _ found => by simpa only [Nat.zero_add] using found), finalHeaps, maps, worlds, frame, metadata⟩

/-- Every completed packed-key computation reconstructs either the ordered
source key trace and authenticated path arguments, or its exact source fault. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : GenericExpressionMeaning.Certificate} {faults : GenericExpressionMeaning.FaultRep}
    {site : SourceCoreElaboration.ErrorSite} {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections 0 steps keySites leaf}
    {types : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    (views : KeyViews path types)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes)
    (meaning : TypedGenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext actualContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store after : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext ambient.definitions)
    (completed : Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ) value after) :
    ∃ sourceAfter finalMap finalWorld,
      ((∃ values resolved,
        Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved sourceAfter ∧
        Arguments checked registry functions finalMap finalWorld source site values path resolved ∧
        value = .inRight .word (DataPatternValues.packValues values)) ∨
       (∃ reason token,
        Dynamic.SourceProjectionsFault program context evidence source environment before projections reason sourceAfter ∧
        faults reason token ∧ value = .inLeft (SourceCoreCalls.packArguments codes).type (.word token))) ∧
      HeapRepresents checked registry functions finalMap finalWorld sourceAfter after ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap after ∧ Dynamic.HeapMetadataExtend before sourceAfter := by
  obtain ⟨outcome, sourceAfter, finalMap, finalWorld, trace, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    TypedDataPlaceKeyOrder.reflects tree meaning environments heaps locals layout actualTyped completed
  refine ⟨sourceAfter, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | values shaped sourceTrace => cases represented with
    | values related => exact .inl ⟨_, _, sourceTrace,
        views.arguments shaped related (fun _ _ found => by simpa only [Nat.zero_add] using found), rfl⟩
  | fault sourceTrace => cases represented with
    | fault token => exact .inr ⟨_, _, sourceTrace, token, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleTypedPlaceKeys
