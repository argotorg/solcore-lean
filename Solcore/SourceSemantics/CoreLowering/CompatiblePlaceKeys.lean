import Solcore.SourceSemantics.CoreLowering.CompatibleHeap
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder

/-! Effectful compatible index expressions reuse the common sequence theorem.
The static key-type view is explicit: native projection equality alone does
not justify changing a source type. Full ordered payloads at the resulting
heap/world construct the path's semantic Arguments, without assuming native
child or helper evaluations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces CompatibleMixedRoute CompatibleHeap

/-- Static source-type agreement at each index occurrence. This receipt is
separate from actual route/preparation success, which only checks native types. -/
inductive KeyViews {checked : Checked} {source : TypedSource} {site : SourceCoreElaboration.ErrorSite} :
    {root : TypeSystem.Ty} → {projections : List PlaceProjection} → {position : Nat} →
    {steps : List PreparedStep} → {keys : List (ExpressionId × Ty)} → {leaf : TypeSystem.Ty} →
    PreparedPath checked source site root projections position steps keys leaf → List TypeSystem.Ty → Prop where
  | nil {type position} : KeyViews (PreparedPath.nil (type := type) (position := position)) []
  | member {root field leaf : TypeSystem.Ty} {name : String} {index : Nat}
      {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {identity : DataTypeId}
      {branches : List MemberBranch} {fieldType : Ty} {projections : List PlaceProjection}
      {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments)}
      {selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature]}
      {certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root) field signature arguments index identity branches fieldType}
      {tail : PreparedPath checked source site field projections position steps keys leaf} {types : List TypeSystem.Ty}
      (rest : KeyViews tail types) :
      KeyViews (.member (name := name) nominal selected certificate tail) types
  | index {root keySource valueSource leaf : TypeSystem.Ty} {key : ExpressionId} {layout : OrderedMapping.Layout}
      {projections : List PlaceProjection} {steps : List PreparedStep} {position : Nat} {keys : List (ExpressionId × Ty)}
      {comparison : Expr} {missing : Word}
      {certificate : IndexSite checked source root keySource valueSource key layout}
      {generated : CompatibleMapping.Index checked ⟨layout, key, position, comparison, missing⟩}
      {tail : PreparedPath checked source site valueSource projections (position + 1) steps keys leaf}
      {type : TypeSystem.Ty} {types : List TypeSystem.Ty}
      (view : SourceCoreRawMetadata.runtimeType keySource = SourceCoreRawMetadata.runtimeType type)
      (rest : KeyViews tail types) :
      KeyViews (.index certificate generated tail) (type :: types)

/-- The ordered semantic values returned by the real argument packing theorem
supply every mapping key, including aliases retaining distinct raw metadata. -/
theorem KeyViews.arguments {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keySites : List (ExpressionId × Ty)}
    {path : PreparedPath checked source site root projections position steps keySites leaf} {types : List TypeSystem.Ty}
    (views : KeyViews path types)
    {sources : List Dynamic.Value} {values allKeys : List Value} {nativeTypes : List Ty} {resolved : List Dynamic.EvaluatedProjection}
    (shaped : DataPlaceKeyOrder.Values projections sources resolved)
    (represented : DataExpressionSequence.Values (payloadModel checked registry functions) mapping world types nativeTypes sources values)
    (positions : ∀ index value, values[index]? = some value → allKeys[position + index]? = some value) :
    Arguments checked registry functions mapping world source site allKeys path resolved := by
  induction views generalizing sources values nativeTypes resolved with
  | nil => cases shaped; cases represented; exact .nil
  | @member root field leaf name index signature arguments identity branches fieldType projections steps position keys nominal selected certificate tail types rest ih => cases shaped with
    | member shapedTail => exact .member (nominal := nominal) (selected := selected) (certificate := certificate) (ih shapedTail represented positions)
  | @index root keySource valueSource leaf key layout projections steps position keySites comparison missing certificate generated tail type types view rest ih =>
    cases shaped with
    | index tailShape => cases represented with
      | cons head restValues =>
        have keyRelated : ValueRep checked registry functions mapping world keySource _ _ _ := .compatible view head
        have sameType := Except.ok.inj (keyRelated.projection.symm.trans certificate.keyProjection)
        rw [sameType] at keyRelated
        refine Arguments.index (certificate := certificate) (generated := generated) (tail := tail) (by simpa using positions 0 _ rfl) keyRelated ?_
        apply ih tailShape restValues
        intro index value found
        have selected := positions (index + 1) value found
        simpa only [Nat.add_assoc, Nat.add_comm 1 index] using selected

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
    (meaning : GenericExpressionMeaning.Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before after : Dynamic.Heap}
    {store : Store} {ξ : Renaming} {resolved : List Dynamic.EvaluatedProjection}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before projections resolved after) :
    ∃ values finalStore finalMap finalWorld,
      Evaluates actual store ((SourceCoreCalls.packArguments codes).expression.rename ξ)
        (.inRight .word (DataPatternValues.packValues values)) finalStore ∧
      Arguments checked registry functions finalMap finalWorld source site values path resolved ∧
      HeapRepresents checked registry functions finalMap finalWorld after finalStore ∧
      LocationMap.Extends mapping finalMap ∧ WorldExtends world finalWorld ∧
      AdministrativePreserved mapping store finalMap finalStore ∧ Dynamic.HeapMetadataExtend before after := by
  obtain ⟨sources, values, finalStore, finalMap, finalWorld, shaped, ran, represented, finalHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceKeyOrder.preserves tree meaning environments heaps locals layout trace
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
    (meaning : GenericExpressionMeaning.Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment} {before : Dynamic.Heap}
    {store after : Store} {ξ : Renaming} {value : Value}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment canonical)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (layout : ReadOnly.EnvironmentsAgree ξ canonical actual)
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
    DataPlaceKeyOrder.reflects tree meaning environments heaps locals layout completed
  refine ⟨sourceAfter, finalMap, finalWorld, ?_, finalHeaps, maps, worlds, frame, metadata⟩
  cases trace with
  | values shaped sourceTrace => cases represented with
    | values related => exact .inl ⟨_, _, sourceTrace,
        views.arguments shaped related (fun _ _ found => by simpa only [Nat.zero_add] using found), rfl⟩
  | fault sourceTrace => cases represented with
    | fault token => exact .inr ⟨_, _, sourceTrace, token, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys
