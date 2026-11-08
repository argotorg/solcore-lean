import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.SourceSemantics.Internal.Substitution.StructuralLaws
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceExecution
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceReflection
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.Frontend.SourceCore.Compatible

/-!
# Compatible places: keys and resolution

Keys and their typing, resolution, right-hand sides and missing-diagnostic rows.
-/

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys
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
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
/-! Independent place typing authenticates the source views of compiled keys.
The proof uses retained expression nodes and the actual member compiler rows;
equality of native projected types is never used to identify source types. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces CompatibleMixedRoute
open CompatiblePlaceKeys CompatibleConstructorMetadata

private theorem lookup_zip_map (parameters : List TypeSystem.TypeParameterId)
    (values : TypeSystem.TypeParameterId → TypeSystem.Ty) (unique : parameters.Nodup)
    (parameter : TypeSystem.TypeParameterId) :
    TypeSystem.ParameterSubstitution.lookup? (parameters.zip (parameters.map values)) parameter =
      if parameter ∈ parameters then some (values parameter) else none := by
  induction parameters with
  | nil => simp [TypeSystem.ParameterSubstitution.lookup?]
  | cons head tail ih =>
    simp only [List.nodup_cons] at unique
    by_cases same : head = parameter
    · subst parameter
      simp [TypeSystem.ParameterSubstitution.lookup?]
    · simp [TypeSystem.ParameterSubstitution.lookup?, same, ih unique.2, Ne.symm same]

/-- Exact source substitutions may be permuted. The compiler's canonical zip
has the same normalized action without identifying either raw substitution. -/
theorem canonical_substitution_view {substitution : TypeSystem.ParameterSubstitution}
    {parameters : List TypeSystem.TypeParameterId}
    (exact : SourceSemantics.ParameterSubstitution.Exact substitution parameters)
    (type : TypeSystem.Ty) :
    SourceCoreRawMetadata.runtimeType
      (TypeSystem.ParameterSubstitution.apply (parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution parameters).map
        SourceCoreRawMetadata.runtimeType)) type) =
      SourceCoreRawMetadata.runtimeType (substitution.apply type) := by
  apply substitution_apply_congr
  intro parameter
  simp only [SourceSemantics.ParameterSubstitution.orderedArguments, List.map_map]
  rw [lookup_zip_map _ _ exact.parameters_nodup]
  by_cases member : parameter ∈ parameters
  · obtain ⟨value, _, found⟩ := StructuralSubstitution.ParameterSubstitution.exists_lookup?_eq_some exact member
    simp [member, found, SourceCoreRawMetadata.runtimeType_idempotent]
  · have absent : parameter ∉ SourceSemantics.ParameterSubstitution.domain substitution :=
      fun found => member ((exact.mem_domain_iff parameter).mp found)
    rw [StructuralSubstitution.ParameterSubstitution.lookup?_eq_none_of_not_mem_domain absent]
    simp [member]

private theorem row_member {α β : Type} {relation : α → β → Prop} {inputs : List α} {outputs : List β}
    (rows : DataPatternValues.ListRel relation inputs outputs) {input : α} (member : input ∈ inputs) :
    ∃ output, relation input output := by
  induction rows with
  | nil => cases member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, head⟩
    · exact ih member

/-- The retained source member judgment and actual generated member rows
agree after staging erasure, including permuted semantic substitutions. -/
theorem member_view {checked : Checked} {context : SourceSemantics.Context}
    (signatures : context.signatures = checked.signatures)
    {site : SourceCoreElaboration.ErrorSite} {root sourceRoot field sourceField : TypeSystem.Ty}
    {signature : ProgramDataSignature} {arguments : List TypeSystem.Ty} {index : Nat}
    {identity : DataTypeId} {branches : List MemberBranch} {fieldType : Ty}
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType root) = some (signature.id, arguments))
    (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
    (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType root)
      field signature arguments index identity branches fieldType)
    (typed : UniformMemberProjection context sourceRoot index sourceField) :
    SourceCoreRawMetadata.runtimeType field = SourceCoreRawMetadata.runtimeType sourceField := by
  cases typed with
  | @intro _ _ dataType substitution member exact base _ _ nonempty uniform _ =>
    rw [view, base, runtimeType_nominal, DataPatternAuthenticity.nominalParts_nominal] at nominal
    obtain ⟨sameId, sameArguments⟩ := Prod.mk.inj (Option.some.inj nominal)
    have selectedMember : dataType ∈ checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) := by
      apply List.mem_filter.mpr
      exact ⟨signatures ▸ member, by simpa using sameId⟩
    rw [selected] at selectedMember
    have sameSignature : dataType = signature := List.mem_singleton.mp selectedMember
    subst dataType
    rw [← sameArguments] at certificate
    obtain ⟨constructor, constructorMember⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨position, constructorFound⟩ := List.mem_iff_getElem?.mp constructorMember
    have zipped : (constructor, position) ∈ signature.constructors.zipIdx :=
      List.mk_mem_zipIdx_iff_getElem?.mpr constructorFound
    obtain ⟨branch, row⟩ := row_member certificate.rows zipped
    obtain ⟨actual, found, actualView⟩ := row.fieldLookup
    have sourceFound := uniform constructor constructorMember
    have lists :
        (constructor.payloadTypes.map
          (TypeSystem.ParameterSubstitution.apply (signature.parameters.zip ((SourceSemantics.ParameterSubstitution.orderedArguments substitution signature.parameters).map
            SourceCoreRawMetadata.runtimeType)))).map SourceCoreRawMetadata.runtimeType =
        (constructor.payloadTypes.map substitution.apply).map SourceCoreRawMetadata.runtimeType := by
      simp only [List.map_map]
      apply List.map_congr_left
      intro type _
      exact canonical_substitution_view exact type
    have same := congrArg (fun types : List TypeSystem.Ty => types[index]?) lists
    simp only [List.getElem?_map, found, sourceFound, Option.map_some, Option.some.injEq] at same
    exact actualView.symm.trans same

/-- Exact retained nodes of the production argument vector. -/
private theorem tree_nodes {source : TypedSource} {certificate : GenericExpressionMeaning.Certificate}
    {scope : SourceCoreLocalCell.Scope} {ids : List ExpressionId} {types : List TypeSystem.Ty}
    {codes : List SourceCoreBasic.LoweredExpr}
    (tree : DataExpressionSequence.Tree source certificate scope ids types codes) :
    DataPatternValues.ListRel (fun id type => ∃ node,
      source.lookupExpression? id = some node ∧ node.type = type) ids types := by
  induction tree with
  | nil => exact .nil
  | single found _ => exact .cons ⟨_, found, rfl⟩ .nil
  | cons found _ _ ih => exact .cons ⟨_, found, rfl⟩ ih

/-- Place typing determines every key view and the final leaf view. Actual
lookup receipts, rather than projected Core type equality, align key nodes. -/
theorem of_nodes {checked : Checked} {context : SourceSemantics.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = checked.signatures)
    {root leaf sourceRoot sourceLeaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)} {types : List TypeSystem.Ty}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (typed : SourceProjectionsHaveType source context sourceRoot projections sourceLeaf)
    (nodes : DataPatternValues.ListRel (fun id type => ∃ node,
      source.lookupExpression? id = some node ∧ node.type = type) (DataPlaceKeyOrder.sourceKeys projections) types) :
    KeyViews path types ∧ SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType sourceLeaf := by
  induction path generalizing sourceRoot sourceLeaf types with
  | nil => cases typed; cases nodes; exact ⟨.nil, view⟩
  | @member root field leaf name index signature arguments identity branches fieldType projections steps position keys nominal selected certificate tail ih =>
    cases typed with
    | member selectedType tailType =>
      have fieldView := member_view signatures view nominal selected certificate selectedType
      obtain ⟨views, leafView⟩ := ih fieldView tailType nodes
      exact ⟨.member (nominal := nominal) (selected := selected) (certificate := certificate) views, leafView⟩
  | @index root keySource valueSource leaf key layout projections steps position keys comparison missing certificate generated tail ih =>
    cases typed with
    | @index _ _ keyType valueType _ _ keyTyped tailTyped =>
      simp only [DataPlaceKeyOrder.sourceKeys] at nodes
      cases nodes with
      | cons head rest =>
        obtain ⟨node, found, nodeType⟩ := head
        obtain ⟨typedNode, contains, typedType⟩ := keyTyped.stored_type
        have typedFound := lookupExpression?_complete unique contains
        have nodesEqual := Option.some.inj (found.symm.trans typedFound)
        have keyNode : node.type = keyType := by simpa only [nodesEqual] using typedType
        have mappingView := certificate.view.symm.trans view
        simp only [SourceCoreRawMetadata.runtimeType, TypeSystem.Ty.mapping.injEq] at mappingView
        have keyView : SourceCoreRawMetadata.runtimeType keySource = SourceCoreRawMetadata.runtimeType node.type := by
          rw [mappingView.1, SourceCoreRawMetadata.runtimeType_idempotent, keyNode]
        rw [nodeType] at keyView
        have valueView : SourceCoreRawMetadata.runtimeType valueSource = SourceCoreRawMetadata.runtimeType valueType := by
          rw [mappingView.2, SourceCoreRawMetadata.runtimeType_idempotent]
        obtain ⟨views, leafView⟩ := ih valueView tailTyped rest
        exact ⟨.index (certificate := certificate) (generated := generated) keyView views, leafView⟩

/-- The real packed-key tree and independent checked place typing supply the
formerly explicit KeyViews receipt, for arbitrary mixed and nested paths. -/
theorem of_typing {checked : Checked} {context : SourceSemantics.Context}
    {source : TypedSource} {site : SourceCoreElaboration.ErrorSite}
    (unique : NodeOccurrencesUnique source) (signatures : context.signatures = checked.signatures)
    {root leaf sourceRoot sourceLeaf : TypeSystem.Ty} {projections : List PlaceProjection} {position : Nat}
    {steps : List PreparedStep} {keys : List (ExpressionId × Ty)} {types : List TypeSystem.Ty}
    {certificate : GenericExpressionMeaning.Certificate} {scope : SourceCoreLocalCell.Scope}
    {codes : List SourceCoreBasic.LoweredExpr}
    (path : PreparedPath checked source site root projections position steps keys leaf)
    (view : SourceCoreRawMetadata.runtimeType root = SourceCoreRawMetadata.runtimeType sourceRoot)
    (typed : SourceProjectionsHaveType source context sourceRoot projections sourceLeaf)
    (tree : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys projections) types codes) :
    KeyViews path types ∧ SourceCoreRawMetadata.runtimeType leaf = SourceCoreRawMetadata.runtimeType sourceLeaf :=
  of_nodes unique signatures path view typed (tree_nodes tree)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyTyping
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
/-! Effectful key evaluation and the actual compatible live getter implement
target resolution before the RHS starts. The common heap is transported over
the getter's real administrative allocations; virtual mapping roots remain
uninitialized. No child or helper execution is a static premise. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute CompatiblePlaceKeys
open SourceCoreCompatibleDataPlaces DataPlaceExecution CompatiblePlaceLiveRoot

private theorem packed_type (codes : List SourceCoreBasic.LoweredExpr) :
    SourceCoreDataMatches.bundleType (codes.map (·.type)) = (SourceCoreCalls.packArguments codes).type := by
  induction codes with
  | nil => rfl
  | cons code codes ih => cases codes with
    | nil => rfl
    | cons => exact congrArg (Ty.product code.type) ih

theorem values_typed {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {definitions : DataEnvironment} {model : GenericHeap.PayloadModel catalog projects definitions} {mapping : LocationMap} {world : StoreTyping}
    {sourceTypes : List TypeSystem.Ty} {codes : List SourceCoreBasic.LoweredExpr}
    {sources : List Dynamic.Value} {values : List Value}
    (represented : DataExpressionSequence.Values model mapping world sourceTypes (codes.map (·.type)) sources values) :
    RuntimeValueHasType world (packValues values) (SourceCoreCalls.packArguments codes).type definitions := by
  rw [← packed_type]
  generalize typesEq : codes.map (·.type) = types at represented ⊢
  clear typesEq codes
  induction represented with
  | nil => exact .unit
  | cons head tail ih => cases tail with
    | nil => exact model.runtime_hasType head
    | cons => exact .pair (model.runtime_hasType head) ih

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

/-- The source selected value and exact key/snapshot native runs are outputs
of resolution. The source heap is unchanged by snapshot helper allocation. -/
structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (prepared : Prepared)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (leaf : TypeSystem.Ty) (sourceTarget : Dynamic.ResolvedPlace)
    (environment : Environment) (initialStore : Store) (initialMap : LocationMap)
    (initialWorld : StoreTyping) (before after : Dynamic.Heap) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  selected : Dynamic.Value
  snapshot : Value
  keyStore : Store
  store : Store
  mapping : LocationMap
  world : StoreTyping
  selectedEq : sourceTarget.selected = some selected
  currentCell : Dynamic.Cell
  currentRead : Dynamic.Heap.Reads after sourceTarget.location currentCell
  currentType : currentCell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  shaped : DataPlaceKeyOrder.Values place.projections sources sourceTarget.projections
  keysEvaluated : Evaluates (referenceEnvironment prepared.route.rootType target environment) initialStore
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  snapshotEvaluated : Evaluates (keysEnvironment prepared.route.rootType target (packValues values) environment) keyStore
    (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
    (.inRight .word (.inRight .unit snapshot)) store
  keysRelated : DataExpressionSequence.Values (payloadModel checked registry functions) mapping world
    sourceTypes (codes.map (·.type)) sources values
  snapshotRelated : ValueRep checked registry functions mapping world leaf selected snapshot prepared.route.leafType
  heaps : HeapRepresents checked registry functions mapping world after store
  maps : LocationMap.Extends initialMap mapping
  worlds : WorldExtends initialWorld world
  frame : AdministrativePreserved initialMap initialStore mapping store
  metadata : Dynamic.HeapMetadataExtend before after

/-- Successful source resolution constructs the actual key and getter runs.
The universal child theorem covers every intermediate key heap and hidden
reference slot. Independent writable-local typing and environment agreement
recover the exact raw root declaration type. -/
theorem preserves {compilation : SourceCoreCompatibleDataPlaces.Context}
    {registry : SourceCoreRawMetadata.Registry} {ambient : AmbientDefinitions compilation.checked.catalog.definitions}
    {functions : FunctionModel compilation.checked.catalog ambient}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {source : TypedSource} {scope : Scope} {site : SourceCoreElaboration.ErrorSite}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
    {administrativeContext : Core.Context}
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
        (SourceCoreLocalCell.coreContext scope ++ administrativeContext))
      (.apply (getter prepared (SourceCoreCalls.packArguments codes).type) (.pair (.loadCell (.var 1)) (.var 0)))
      (LanguageResult.resultType prepared.optionalLeaf) ambient.definitions)
    (meaning : Preserves (payloadModel compilation.checked registry functions) program context evidence source certificate faults)
    {identities : Dynamic.Value → Word → Prop} (faithful : DataEquality.IdentityFaithful identities)
    (observations : FunctionObservations compilation.checked.catalog functions identities)
    {mapping : LocationMap} {world : StoreTyping} {environment : Dynamic.Environment} {coreEnvironment : Environment}
    {before after : Dynamic.Heap} {store : Store} {sourceTarget : Dynamic.ResolvedPlace} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog compilation.checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents compilation.checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (trace : Dynamic.SourcePlaceResolves program context evidence source environment before place sourceTarget after) :
    ∃ execution : Execution compilation.checked registry functions prepared codes sourceTypes place leaf sourceTarget
      coreEnvironment store mapping world before after,
      coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) execution.target) := by
  cases trace with
  | @intro _ _ _ _ _ _ _ sourceLocation initialCell currentCell projections initial selected
      lookup initialRead evaluate currentRead initialValue selection =>
    obtain ⟨target, coreLookup, reference⟩ := environments.lookup_visible lookup slot
    have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by
      intro _ _ found; exact found
    obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, keyEvaluated, keysRelated,
      keyHeaps, keyMaps, keyWorlds, keyFrame, metadata⟩ :=
      DataPlaceKeyOrder.preserves children meaning environments heaps locals
        (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) evaluate
    have keyEvaluation : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore := by
      simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
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
          (SourceCoreLocalCell.coreContext scope ++ administrativeContext)) ambient.definitions :=
      .cons (values_typed keysRelated)
        (.cons (.cellRef currentReference.typed) ((environments.extend keyMaps keyWorlds).runtime_hasTypes))
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
              snapshotEvaluated := evaluated
              keysRelated := keysRelated.extend (.refl _) extension
              snapshotRelated := related.extend (.refl _) (.refl _) extension
              heaps := CompatibleHeap.HeapRepresents.after_snapshot keyHeaps extension typedStore appended
              maps := keyMaps
              worlds := keyWorlds.trans extension
              frame := keyFrame.trans frame
              metadata := metadata }, coreLookup⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceResolution
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
/-! RHS execution uses the previously selected snapshot but returns the live
root in the post-RHS heap. Both directions instantiate the universal expression
IH under execute's real three hidden slots. None of the fields below is an
input to a compiler certificate; they are semantic output witnesses. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap CompatibleMixedRoute
open SourceCoreCompatibleDataPlaces DataPlaceExecution

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
  {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
  {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty} {leaf : TypeSystem.Ty}
  {sourceTarget : Dynamic.ResolvedPlace} {coreEnvironment : Environment} {initialStore : Store}
  {initialMap : LocationMap} {initialWorld : StoreTyping} {before targetHeap : Dynamic.Heap}

/-- The original reference is read against the actual post-RHS store.
The source cell's raw declared type survives; its value may have changed. -/
structure Latest (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (mapping : LocationMap) (world : StoreTyping)
    (prepared : Prepared) (sourceTarget : Dynamic.ResolvedPlace) (target : Location)
    (heap : Dynamic.Heap) (store : Store) where
  cell : Dynamic.Cell
  optional : Value
  read : Dynamic.Heap.Reads heap sourceTarget.location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents mapping world sourceTarget.location target prepared.route.rootType
  nativeRead : store.read? target = some optional
  related : GenericHeap.CellRepresents (payloadModel checked registry functions) mapping world cell optional prepared.route.rootType

variable (resolution : CompatiblePlaceResolution.Execution checked registry functions prepared codes sourceTypes place leaf sourceTarget
  coreEnvironment initialStore initialMap initialWorld before targetHeap)

/-- Snapshot, keys, and RHS all retain their own source/native identities.
The latest-root receipt refers to the new heap, not the saved snapshot heap. -/
structure Result (id : ExpressionId) (node : ExpressionNode) (lowered : SourceCoreBasic.LoweredExpr)
    (environment : Dynamic.Environment) (outcome : Dynamic.ExpressionOutcome) (after : Dynamic.Heap)
    (value : Value) (store : Store) (mapping : LocationMap) (world : StoreTyping) : Prop where
  trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after
  evaluated : Evaluates
    (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
    resolution.store (shift 3 lowered.expression) value store
  represented : ResultRepresents (payloadModel checked registry functions) mapping world node.type lowered.type faults outcome value
  heaps : HeapRepresents checked registry functions mapping world after store
  maps : LocationMap.Extends resolution.mapping mapping
  worlds : WorldExtends resolution.world world
  frame : AdministrativePreserved resolution.mapping resolution.store mapping store
  metadata : Dynamic.HeapMetadataExtend targetHeap after
  latest : Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store)

private theorem latest_of_heap {mapping : LocationMap} {world : StoreTyping} {after : Dynamic.Heap} {store : Store}
    (heaps : HeapRepresents checked registry functions mapping world after store)
    (maps : LocationMap.Extends resolution.mapping mapping) (worlds : WorldExtends resolution.world world)
    (metadata : Dynamic.HeapMetadataExtend targetHeap after) :
    Nonempty (Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) := by
  obtain ⟨cell, read, sameType, _⟩ := metadata _ _ resolution.currentRead
  have reference := resolution.reference.extend maps worlds
  obtain ⟨optional, nativeRead, represented⟩ := CompatibleHeap.HeapRepresents.read_at heaps reference read
  exact ⟨⟨cell, optional, read, sameType.trans resolution.currentType, reference, nativeRead, represented⟩⟩

variable {administrativeContext : Core.Context} {environment : Dynamic.Environment}
  {id : ExpressionId} {node : ExpressionNode} {lowered : SourceCoreBasic.LoweredExpr}

/-- Every source RHS outcome executes under the actual saved snapshot slots.
The returned live-root receipt is derived from the IH's new heap. -/
theorem preserves
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment targetHeap id outcome after) :
    ∃ value store mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨value, store, mapping, world, evaluated, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target]) trace
  refine ⟨value, store, mapping, world, trace, ?_, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩
  simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
    List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
    SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated

/-- Completed RHS code reconstructs the independent source outcome and the
post-RHS live root, without supplying a source execution or child evaluation IH
at one preselected runtime environment. -/
theorem reflects
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    (generated : certificate scope id lowered) (found : source.lookupExpression? id = some node)
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) initialMap initialWorld administrativeContext scope environment coreEnvironment)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    {value : Value} {store : Store}
    (evaluated : Evaluates
      (snapshotEnvironment prepared.route.rootType resolution.target (packValues resolution.values) (.inRight .unit resolution.snapshot) coreEnvironment)
      resolution.store (shift 3 lowered.expression) value store) :
    ∃ outcome after mapping world, Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world := by
  have layout : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨outcome, after, mapping, world, trace, represented, heaps, maps, worlds, frame, metadata⟩ :=
    meaning generated found (environments.extend resolution.maps resolution.worlds) resolution.heaps (locals.mono resolution.metadata)
      (DataPlaceChildExpressions.prefix_agrees layout
        [.inRight .unit resolution.snapshot, packValues resolution.values, .cellRef (OptionalCell.cellType prepared.route.rootType) resolution.target])
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, snapshotEnvironment, keysEnvironment, referenceEnvironment,
        SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  exact ⟨outcome, after, mapping, world, trace, evaluated, represented, heaps, maps, worlds, frame, metadata,
    latest_of_heap resolution heaps maps worlds metadata⟩

/-- RHS effects preserve the previous snapshot as a related value. It is not
replaced by the value obtained when the root is read again for writeback. -/
theorem Result.saved_snapshot {outcome : Dynamic.ExpressionOutcome} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment outcome after value store mapping world) :
    ValueRep checked registry functions mapping world leaf resolution.selected resolution.snapshot prepared.route.leafType :=
  resolution.snapshotRelated.extend (.refl _) result.maps result.worlds

/-- A successful source RHS cannot turn an initialized root into an absent
one. This fact comes from the independent trace, not the heap metadata law. -/
theorem Result.initialized {right : Dynamic.Value} {after : Dynamic.Heap}
    {value : Value} {store : Store} {mapping : LocationMap} {world : StoreTyping}
    (result : Result (program := program) (context := context) (evidence := evidence) (source := source) (faults := faults)
      resolution id node lowered environment (.value right) after value store mapping world)
    (wasInitialized : resolution.currentCell.value ≠ none)
    (latest : Latest checked registry functions mapping world prepared sourceTarget resolution.target after store) :
    latest.cell.value ≠ none := by
  cases result.trace with
  | value trace =>
    obtain ⟨cell, read, initialized⟩ := trace.initialization_extends _ _ resolution.currentRead wasInitialized
    exact latest.read.functional read ▸ initialized

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceRhs
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetKeys
/-! The common target prefix evaluates every key once and then reads the live
source root metadata. It does not assume that structural selection succeeds.
The receipt below is a semantic output; compiler certificates remain static. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetKeys
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

structure Execution (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (prepared : Prepared) (place : PlaceResolution)
    (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (location : Dynamic.Location) (resolved : List Dynamic.EvaluatedProjection)
    (coreEnvironment : Environment) (before after : Dynamic.Heap) (store : Store)
    (mapping : LocationMap) (world : StoreTyping) (index : Nat) where
  target : Location
  sources : List Dynamic.Value
  values : List Value
  keyStore : Store
  keyMap : LocationMap
  keyWorld : StoreTyping
  cell : Dynamic.Cell
  read : Dynamic.Heap.Reads after location cell
  type : cell.type = prepared.route.rootSourceType
  reference : ReferenceRepresents keyMap keyWorld location target prepared.route.rootType
  selected : coreEnvironment[index]? = some (.cellRef (OptionalCell.cellType prepared.route.rootType) target)
  shaped : DataPlaceKeyOrder.Values place.projections sources resolved
  evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
    (shift 1 (SourceCoreCalls.packArguments codes).expression) (.inRight .word (packValues values)) keyStore
  related : DataExpressionSequence.Values (payloadModel checked registry functions) keyMap keyWorld sourceTypes (codes.map (·.type)) sources values
  heaps : HeapRepresents checked registry functions keyMap keyWorld after keyStore
  maps : LocationMap.Extends mapping keyMap
  worlds : WorldExtends world keyWorld
  frame : AdministrativePreserved mapping store keyMap keyStore
  metadata : Dynamic.HeapMetadataExtend before after

/-- Successful key expressions supply the current root after all their effects.
Exact declared source type comes from WritableLocal and environment agreement. -/
theorem preserves {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {prepared : Prepared} {place : PlaceResolution}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : Preserves (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before after : Dynamic.Heap} {store : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {resolved : List Dynamic.EvaluatedProjection} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after) :
    Nonempty (Execution checked registry functions prepared place codes sourceTypes location resolved coreEnvironment before after store mapping world index) := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  obtain ⟨sources, values, keyStore, keyMap, keyWorld, shaped, evaluated, related, keyHeaps, maps, worlds, frame, metadata⟩ :=
    DataPlaceKeyOrder.preserves children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target]) trace
  obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
  obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
  have locationEq := lookup.functional staticLookupRuntime
  subst staticLocation
  have cellEq := initialRead.functional staticRead
  subst staticCell
  obtain ⟨currentCell, currentRead, currentType, _⟩ := metadata _ _ initialRead
  exact ⟨⟨target, sources, values, keyStore, keyMap, keyWorld, currentCell, currentRead,
    currentType.trans (staticCellType.trans bodyEq), reference.extend maps worlds, selected, shaped,
    by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
      List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated,
    related, keyHeaps, maps, worlds, frame, metadata⟩⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceTargetKeys
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
/-! Compatible payloads retain raw source metadata while numeric modifiers
operate on their scalar runtime view. Total initialized primitives justify
computing the modifier before latest-root traversal: it cannot hide a later
structural source fault. This module reuses the existing primitive semantics. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
open Core Frontend SourceInference GeneralHeap DataEquality CompatiblePayload CompatibleEquality
open SourceCoreCompatibleDataPlaces

variable {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
  {ambient : AmbientDefinitions checked.catalog.definitions}
  {functions : FunctionModel checked.catalog ambient} {mapping : LocationMap} {world : StoreTyping}
  {identities : Dynamic.Value → Word → Prop}

theorem word_fields (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value .word) :
    ∃ word, source = .word word ∧ value = .word word := by
  cases CompatibleEquality.ValueRep.observation observations related with
  | word word => exact ⟨word, rfl, rfl⟩

theorem integer_fields (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value}
    (related : ValueRep checked registry functions mapping world sourceType source value .integer) :
    ∃ integer, source = .integer integer ∧ value = .integer integer := by
  cases CompatibleEquality.ValueRep.observation observations related with
  | integer integer => exact ⟨integer, rfl, rfl⟩

/-- Plain assignment supports every authenticated payload. Numeric compound
assignment also accepts staged type views, without changing their metadata. -/
theorem initialized_success
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {left right : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer ∧ operator.wordOnly = false)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ result value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Dynamic.AssignmentValueApplies operator (some left) right result ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  rcases profile with rfl | word | ⟨integer, notWordOnly⟩
  · exact ⟨right, rightCore, rightRep, .equal _ _, .inRight (rightSelected.evaluates store),
      DataPlaceModifier.assignment_excludes_invalid (.equal _ _)⟩
  · have projected : checked.catalog.project sourceType = .ok .word := by
      rw [← checked.catalog.project_runtimeType sourceType, word]; rfl
    have same := Except.ok.inj (leftRep.projection.symm.trans projected)
    subst type
    obtain ⟨left, rfl, rfl⟩ := word_fields observations leftRep
    obtain ⟨right, rfl, rfl⟩ := word_fields observations rightRep
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.word_success operator left right snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .word) word (.word result), applied, evaluated, DataPlaceModifier.assignment_excludes_invalid applied⟩
  · have projected : checked.catalog.project sourceType = .ok .integer := by
      rw [← checked.catalog.project_runtimeType sourceType, integer]; rfl
    have same := Except.ok.inj (leftRep.projection.symm.trans projected)
    subst type
    obtain ⟨left, rfl, rfl⟩ := integer_fields observations leftRep
    obtain ⟨right, rfl, rfl⟩ := integer_fields observations rightRep
    obtain ⟨result, applied, evaluated⟩ := DataPlaceModifier.integer_success operator notWordOnly left right snapshotSelected rightSelected store invalid
    exact ⟨_, _, .compatible (actual := .integer) integer (.integer result), applied, evaluated, DataPlaceModifier.assignment_excludes_invalid applied⟩

/-- The source operation determines the same result as the actual native
modifier, including division/modulo by zero and unbounded Integer arithmetic. -/
theorem preserves
    (observations : FunctionObservations checked.catalog functions identities)
    {sourceType : TypeSystem.Ty} {type : Ty} {left right result : Dynamic.Value} {leftCore rightCore : Value}
    {operator : Syntax.ValueAssignOp}
    (profile : operator = .equal ∨ SourceCoreRawMetadata.runtimeType sourceType = .word ∨
      SourceCoreRawMetadata.runtimeType sourceType = .integer ∧ operator.wordOnly = false)
    (leftRep : ValueRep checked registry functions mapping world sourceType left leftCore type)
    (rightRep : ValueRep checked registry functions mapping world sourceType right rightCore type)
    (applied : Dynamic.AssignmentValueApplies operator (some left) right result)
    {environment : Environment} {snapshot rhs : Expr}
    (snapshotSelected : Selects environment snapshot (.inRight .unit leftCore))
    (rightSelected : Selects environment rhs rightCore) (store : Store) (invalid : Word) :
    ∃ value, ValueRep checked registry functions mapping world sourceType result value type ∧
      Evaluates environment store (modified type (binaryOperator (type = .integer) operator) false snapshot rhs invalid)
        (.inRight .word value) store ∧ ¬ Dynamic.AssignmentOperandsInvalid operator (some left) right := by
  obtain ⟨result', value, related, applied', evaluated, valid⟩ :=
    initialized_success observations profile leftRep rightRep snapshotSelected rightSelected store invalid
  have same := DataPlaceModifier.assignment_functional applied' applied
  subst result'
  exact ⟨value, related, evaluated, valid⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceModifier
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyReflection
/-! Reflection of the actual emitted reference/key prefix. The universal
child theorem recovers each source index trace. Success exposes the real
remaining getter subtree as an output witness, not a compiler-certificate
premise. Interpreting that subtree is the separate live-root reflection step. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyReflection
open Core Frontend SourceInference GeneralHeap DataPatternValues GenericExpressionMeaning
open CompatiblePayload CompatibleEquality CompatibleHeap SourceCoreCompatibleDataPlaces DataPlaceExecution

/-- The exact subtree after the packed keys binder in `execute`. -/
def remainder (prepared : Prepared) (keyType : Ty) (rhs next : Expr) (outputType : Ty)
    (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) : Expr :=
  LanguageResult.bind outputType
    (.apply (getter prepared keyType) (.pair (.loadCell (.var 1)) (.var 0)))
    (LanguageResult.bind outputType (shift 3 rhs)
      (LanguageResult.bind outputType
        (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalid)
        (LanguageResult.bind outputType
          (.apply (setter prepared keyType) (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
          (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next)))))

theorem execute_eq (prepared : Prepared) (reference : Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word) :
    execute prepared reference keys rhs next outputType operator bitNot invalid =
      .letE reference (LanguageResult.bind outputType (shift 1 keys.expression)
        (remainder prepared keys.type rhs next outputType operator bitNot invalid)) := rfl

inductive Result (checked : Checked) (registry : SourceCoreRawMetadata.Registry)
    {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (program : Program) (context : SourceSemantics.Context)
    (evidence : Dynamic.EvidenceEnvironment) (source : TypedSource) (faults : FaultRep)
    (prepared : Prepared) (codes : List SourceCoreBasic.LoweredExpr) (sourceTypes : List TypeSystem.Ty)
    (place : PlaceResolution) (environment : Dynamic.Environment) (coreEnvironment : Environment)
    (before : Dynamic.Heap) (store : Store) (mapping : LocationMap) (world : StoreTyping) (index : Nat)
    (rhs next : Expr) (outputType : Ty) (operator : Option BinaryOp) (bitNot : Bool) (invalid : Word)
    (result : Value) (finalStore : Store) : Prop where
  | fault {reason : Dynamic.SemanticFault} {token : Word} {after : Dynamic.Heap}
      {finalMap : LocationMap} {finalWorld : StoreTyping}
      (sourceFault : Dynamic.SourcePlaceFaults program context evidence source environment before place reason after)
      (resultEq : result = .inLeft outputType (.word token)) (tokenRep : faults reason token)
      (heaps : HeapRepresents checked registry functions finalMap finalWorld after finalStore)
      (maps : LocationMap.Extends mapping finalMap) (worlds : WorldExtends world finalWorld)
      (frame : AdministrativePreserved mapping store finalMap finalStore) (metadata : Dynamic.HeapMetadataExtend before after) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore
  | keys {location : Dynamic.Location} {resolved : List Dynamic.EvaluatedProjection} {after : Dynamic.Heap}
      (lookup : Dynamic.Environment.LooksUp environment place.root location)
      (trace : Dynamic.SourceProjectionsEvaluate program context evidence source environment before place.projections resolved after)
      (execution : CompatiblePlaceTargetKeys.Execution checked registry functions prepared place codes sourceTypes location resolved
        coreEnvironment before after store mapping world index)
      (continuation : Evaluates (keysEnvironment prepared.route.rootType execution.target (packValues execution.values) coreEnvironment)
        execution.keyStore (remainder prepared (SourceCoreCalls.packArguments codes).type rhs next outputType operator bitNot invalid) result finalStore) :
      Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
        coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore

/-- Completed emitted code supplies the key runs to the universal reflection
IH. No source projection trace or child runtime execution is an input. -/
theorem reflects {checked : Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions}
    {functions : FunctionModel checked.catalog ambient} {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource} {scope : Scope}
    {certificate : Certificate} {faults : FaultRep} {place : PlaceResolution} {prepared : Prepared}
    {codes : List SourceCoreBasic.LoweredExpr} {sourceTypes : List TypeSystem.Ty}
    (children : DataExpressionSequence.Tree source certificate scope (DataPlaceKeyOrder.sourceKeys place.projections) sourceTypes codes)
    (meaning : Reflects (payloadModel checked registry functions) program context evidence source certificate faults)
    {mapping : LocationMap} {world : StoreTyping} {administrativeContext : Core.Context}
    {environment : Dynamic.Environment} {coreEnvironment : Environment} {before : Dynamic.Heap} {store finalStore : Store}
    {location : Dynamic.Location} {initialCell : Dynamic.Cell} {index : Nat}
    (environments : DataHeap.EnvRepresents (definitions := ambient.definitions) (storageCatalog checked.catalog) mapping world administrativeContext scope environment coreEnvironment)
    (heaps : HeapRepresents checked registry functions mapping world before store)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (slot : SourceCoreLocalCell.lookup? scope place.root = some (index, prepared.route.rootType))
    (rootTyped : WritableLocal context place.root prepared.route.rootSourceType)
    (lookup : Dynamic.Environment.LooksUp environment place.root location)
    (initialRead : Dynamic.Heap.Reads before location initialCell)
    {rhs next : Expr} {outputType : Ty} {operator : Option BinaryOp} {bitNot : Bool} {invalid : Word} {result : Value}
    (completed : Evaluates coreEnvironment store
      (execute prepared (.var index) (SourceCoreCalls.packArguments codes) rhs next outputType operator bitNot invalid) result finalStore) :
    Result checked registry functions program context evidence source faults prepared codes sourceTypes place environment
      coreEnvironment before store mapping world index rhs next outputType operator bitNot invalid result finalStore := by
  obtain ⟨target, selected, reference⟩ := environments.lookup_visible lookup slot
  have sameEnvironment : ReadOnly.EnvironmentsAgree Renaming.id coreEnvironment coreEnvironment := by intro _ _ found; exact found
  have reflectKeys := fun {keyValue : Value} {keyStore : Store}
      (evaluated : Evaluates (referenceEnvironment prepared.route.rootType target coreEnvironment) store
        (shift 1 (SourceCoreCalls.packArguments codes).expression) keyValue keyStore) =>
    DataPlaceKeyOrder.reflects children meaning environments heaps locals
      (DataPlaceChildExpressions.prefix_agrees sameEnvironment [.cellRef (OptionalCell.cellType prepared.route.rootType) target])
      (by simpa only [DataPlaceChildExpressions.rename_prefix, Expr.rename_id, List.length_cons, List.length_nil,
        List.cons_append, List.nil_append, referenceEnvironment, SourceCoreDataPlaces.shift, shift, Nat.zero_add] using evaluated)
  cases completed with
  | letE referenceEvaluated tail =>
    obtain ⟨rfl, rfl⟩ := evaluation_deterministic referenceEvaluated (Evaluates.var selected)
    cases tail with
    | caseLeft keysEvaluated failed =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | fault tokenRep =>
        cases sourceTrace with
        | fault sourceTrace =>
          cases failed with
          | inLeft valueEvaluated =>
            cases valueEvaluated with
            | var found =>
              simp only [List.getElem?_cons_zero, Option.some.injEq] at found
              subst_vars
              exact .fault (.projectionExpression lookup initialRead sourceTrace) rfl tokenRep finalHeaps maps worlds frame metadata
    | caseRight keysEvaluated tail =>
      obtain ⟨outcome, after, finalMap, finalWorld, sourceTrace, represented, finalHeaps, maps, worlds, frame, metadata⟩ := reflectKeys keysEvaluated
      cases represented with
      | @values sources values related =>
        cases sourceTrace with
        | @values _ resolved _ shaped sourceTrace =>
          obtain ⟨scheme, staticLookup, _, _, bodyEq⟩ := rootTyped.scheme
          obtain ⟨staticLocation, staticCell, staticLookupRuntime, staticRead, staticCellType, _⟩ := locals.lookup staticLookup
          have locationEq := lookup.functional staticLookupRuntime
          subst staticLocation
          have cellEq := initialRead.functional staticRead
          subst staticCell
          obtain ⟨cell, read, type, _⟩ := metadata _ _ initialRead
          exact .keys lookup sourceTrace
            ⟨target, sources, values, _, finalMap, finalWorld, cell, read,
              type.trans (staticCellType.trans bodyEq), reference.extend maps worlds, selected, shaped,
              keysEvaluated, related, finalHeaps, maps, worlds, frame, metadata⟩ tail

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeyReflection
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
/-! Static receipts from the real compatible place description. The declared
root type and the selected source type remain distinct: only the compiler's
explicit runtime-type check relates the selected type to the assignment type.
Virtual mapping roots retain the actual encoder and quote receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
open Core Frontend SourceInference SourceCoreCompatibleDataPlaces
open DataEqualityGeneration CompatibleMixedRoute

structure Description (context : SourceCoreCompatibleDataPlaces.Context) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution) (route : Route) (binder : TypedBinder) (selected : TypeSystem.Ty) : Prop where
  binding : rootBinder source assignment.target.root = .ok binder
  rootSource : route.rootSourceType = binder.scheme.body
  rootProjected : context.checked.catalog.project binder.scheme.body = .ok route.rootType
  leafProjected : context.checked.catalog.project assignment.target.type = .ok route.leafType
  selectedType : SourceCoreRawMetadata.runtimeType selected = SourceCoreRawMetadata.runtimeType assignment.target.type
  routed : routeSteps context.checked context.checked.signatures source site assignment.target.root
    binder.scheme.body assignment.target.projections = .ok (route.steps, selected)
  virtual : ∀ key value, binder.scheme.body = .mapping key value →
    CompatibleMapping.VirtualRoot.Generated context route key value
  ordinary : (∀ key value, binder.scheme.body ≠ .mapping key value) → route.rootMapping = none

private theorem project_facts {checked : Checked} {site : SourceCoreElaboration.ErrorSite}
    {source : TypeSystem.Ty} {type : Ty} (accepted : project checked site source = .ok type) :
    checked.catalog.project source = .ok type ∧ type.WellFormed checked.catalog.definitions := by
  unfold project SourceCoreCompatibleDataExpressions.projectType SourceCoreCompatibleCatalog.Checked.project at accepted
  cases generated : checked.catalog.project source with
  | error error => simp [generated, bind, Except.bind, Except.map, Except.mapError] at accepted
  | ok native =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · rename_i valid
      simp only [pure, Except.pure, Except.map, Except.mapError, Except.ok.injEq] at accepted
      subst type
      exact ⟨rfl, Ty.isWellFormed_sound valid⟩
    · cases accepted

/-- Actual description success supplies both source metadata and every route
step. No helper execution or semantic conclusion is assumed. -/
theorem of_describe {context : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    (accepted : describe context context.checked.signatures source site assignment = .ok route) :
    ∃ binder selected, Description context source site assignment route binder selected := by
  have original := accepted
  unfold describe at accepted
  dsimp only at accepted
  split at accepted <;> try cases accepted
  obtain ⟨binder, binding, accepted⟩ := bind_ok accepted
  obtain ⟨rootType, rootProjected, accepted⟩ := bind_ok accepted
  obtain ⟨⟨steps, selected⟩, routed, accepted⟩ := bind_ok accepted
  split at accepted <;> try cases accepted
  rename_i selectedType
  have finish : ∀ rootMapping leafType,
      route = ⟨binder.scheme.body, rootType, leafType, steps, rootMapping⟩ →
      project context.checked site assignment.target.type = .ok leafType →
      ((∀ key value, binder.scheme.body ≠ .mapping key value) → rootMapping = none) →
      ∃ binder selected, Description context source site assignment route binder selected := by
    intro rootMapping leafType routeEq leafProjected ordinary
    subst route
    refine ⟨binder, selected, ⟨binding, rfl, (project_facts rootProjected).1,
      (project_facts leafProjected).1, selectedType, routed, ?_, ordinary⟩⟩
    intro key value declared
    exact CompatibleMapping.VirtualRoot.generated_of_describe binding declared original
  split at accepted
  · rename_i key value declared
    cases identity : context.checked.catalog.identity? binder.scheme.body with
    | none => simp [identity, throw, pure, Except.pure, bind, Except.bind] at accepted
    | some identityValue =>
      simp only [identity, pure, Except.pure, bind, Except.bind] at accepted
      obtain ⟨coreKey, _, accepted⟩ := bind_ok accepted
      obtain ⟨coreValue, _, accepted⟩ := bind_ok accepted
      split at accepted <;> try cases accepted
      obtain ⟨carrier, _, accepted⟩ := bind_ok accepted
      split at accepted <;> try cases accepted
      cases quoted : SourceCoreCompatibleDataExpressions.quote carrier.value with
      | none => simp [quoted, throw] at accepted
      | some expression =>
        simp only [quoted] at accepted
        obtain ⟨leafType, leafProjected, accepted⟩ := bind_ok accepted
        cases accepted
        exact finish (some expression) leafType rfl leafProjected (fun impossible => (impossible key value declared).elim)
  · simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨leafType, leafProjected, accepted⟩ := bind_ok accepted
    cases accepted
    exact finish none leafType rfl leafProjected (fun _ => rfl)

/-- Description and preparation compose without re-proving or approximating
member authentication, mapping layout lookup, or comparison generation. -/
theorem Description.prepared {context : SourceCoreCompatibleDataPlaces.Context} {source : TypedSource}
    {site : SourceCoreElaboration.ErrorSite} {assignment : AssignmentResolution} {route : Route}
    {binder : TypedBinder} {selected : TypeSystem.Ty}
    (description : Description context source site assignment route binder selected)
    {fuel : Nat} {invalid : Word} {missing : TypeSystem.Ty → Word} {prepared : Prepared}
    (accepted : prepare context fuel route invalid missing = .ok prepared) :
    prepared.route = route ∧ prepared.invalidProjection = invalid ∧
      PreparedPath context.checked source site binder.scheme.body assignment.target.projections
        0 prepared.steps prepared.keys selected :=
  prepared_of_success description.routed accepted

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceDescription
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
/-! Static provenance of the actual expanded missing-diagnostic rows.
Each returned row retains its real public site and raw owning metadata.
Duplicate tokens keep the original producer's first row. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites

/-- A row actually emitted for a matching raw mapping header. -/
def MissingRow (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (row : Word × Diagnostic) : Prop :=
  ∃ site, site ∈ sites ∧ ∃ index rawKey rawValue,
    (SourceCoreRawMetadata.Metadata.mapping rawKey rawValue, index) ∈ registry.entries.zipIdx ∧
    SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
    SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType ∧
    Word.ofNat? (site.base.val + index + 1) = some row.1 ∧
    row.2 = { error := .typeMismatch rawValue none, site := site.site, span := some site.span }

private def RowsSound (registry : SourceCoreRawMetadata.Registry) (sites : List MissingSite)
    (rows : List (Word × Diagnostic)) : Prop := ∀ row, row ∈ rows → MissingRow registry sites row

private theorem bind_ok {α β ε : Type} {value : Except ε α} {next : α → Except ε β} {result : β}
    (accepted : (value >>= next) = .ok result) :
    ∃ middle, value = .ok middle ∧ next middle = .ok result := by
  cases value with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem forIn_contains {α β ε : Type} {items : List α} {initial final : β}
    {step : α → β → Except ε (ForInStep β)} {property : β → Prop} {selected : α}
    (accepted : forIn items initial step = .ok final) (member : selected ∈ items)
    (each : ∀ item, item ∈ items → ∀ state outcome, step item state = .ok outcome →
      ∃ updated, outcome = .yield updated ∧ (property state → property updated) ∧
        (item = selected → property updated)) : property final := by
  have contains : selected ∈ items → property final := by
    apply CompatibleMemberCertificates.forIn_preserves accepted
      (fun seen state => selected ∈ seen → property state)
    · simp
    · intro seen item remaining state outcome split previous ran
      have member : item ∈ items := by rw [split]; simp
      obtain ⟨updated, rfl, keeps, obtains⟩ := each item member state outcome ran
      refine ⟨updated, rfl, ?_⟩
      intro appeared
      rcases List.mem_append.mp appeared with before | current
      · exact keeps (previous before)
      · have same := List.mem_singleton.mp current
        exact obtains same.symm
  exact contains member

private theorem contains_append {reason : Word} {rows suffix : List (Word × Diagnostic)}
    (present : ∃ row, row ∈ rows ∧ row.1 = reason) :
    ∃ row, row ∈ rows ++ suffix ∧ row.1 = reason := by
  obtain ⟨row, member, same⟩ := present
  exact ⟨row, List.mem_append_left _ member, same⟩

/-- Soundness follows the actual two finite inventory loops. -/
theorem missingDiagnostics_rows {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows) :
    ∀ row, row ∈ rows → MissingRow registry sites row := by
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    have same := Except.ok.inj finished
    subst updated
    apply CompatibleMemberCertificates.forIn_preserves loop (fun _ output => RowsSound registry sites output)
    · intro row member
      cases member
    · intro seen site remaining state outcome split previous ran
      have member : site ∈ sites := by rw [split]; simp
      obtain ⟨updated, inner, finished⟩ := bind_ok ran
      refine ⟨updated, (Except.ok.inj finished).symm, ?_⟩
      apply CompatibleMemberCertificates.forIn_preserves inner (fun _ output => RowsSound registry sites output) previous
      intro seen entry remaining state outcome split previous ran
      obtain ⟨metadata, index⟩ := entry
      dsimp only at ran
      have stored : (metadata, index) ∈ registry.entries.zipIdx := by rw [split]; simp
      cases metadata with
      | proxy inner =>
        exact ⟨state, (Except.ok.inj ran).symm, previous⟩
      | constructor instantiation =>
        exact ⟨state, (Except.ok.inj ran).symm, previous⟩
      | mapping rawKey rawValue =>
        dsimp only at ran
        split at ran
        · rename_i matched
          have views : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
              SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType := by
            simpa only [Bool.and_eq_true, decide_eq_true_eq] using matched
          obtain ⟨reason, generated, finished⟩ := bind_ok ran
          have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
            change (match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason at generated
            split at generated
            · cases generated; assumption
            · cases generated
          split at finished
          · exact ⟨state, (Except.ok.inj finished).symm, previous⟩
          · refine ⟨_, (Except.ok.inj finished).symm, ?_⟩
            intro row rowMember
            rcases List.mem_append.mp rowMember with old | fresh
            · exact previous row old
            · have same := List.mem_singleton.mp fresh
              subst row
              exact ⟨site, member, index, rawKey, rawValue, stored, views.1, views.2, converted, rfl⟩
        · exact ⟨state, (Except.ok.inj ran).symm, previous⟩
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- A genuine matching public site and authenticated header are covered by
an actual returned token. A duplicate token retains its earlier diagnostic. -/
theorem missingDiagnostics_contains {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows)
    {site : MissingSite} (member : site ∈ sites) {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (reserved : site.base.val + header.val < wordModulus) :
    ∃ row, row ∈ rows ∧ row.1 = site.base.add header := by
  have positive : header.val ≠ 0 := by
    intro zero
    apply metadata.nonzero
    exact Fin.ext zero
  have stored : (.mapping rawKey rawValue, header.val - 1) ∈ registry.entries.zipIdx := by
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simpa [SourceCoreRawMetadata.Registry.lookup, positive] using metadata.lookup
  unfold missingDiagnostics at accepted
  split at accepted
  · obtain ⟨updated, loop, finished⟩ := bind_ok accepted
    have same := Except.ok.inj finished
    subst updated
    apply forIn_contains loop member
    intro current currentMember state outcome ran
    obtain ⟨updated, inner, finished⟩ := bind_ok ran
    refine ⟨updated, (Except.ok.inj finished).symm, ?_, ?_⟩
    · intro present
      apply CompatibleMemberCertificates.forIn_preserves inner (fun _ output =>
        ∃ row, row ∈ output ∧ row.1 = site.base.add header) present
      intro seen entry remaining state outcome split present ran
      obtain ⟨rawMetadata, index⟩ := entry
      dsimp only at ran
      cases rawMetadata with
      | proxy _ | constructor _ => exact ⟨state, (Except.ok.inj ran).symm, present⟩
      | mapping _ _ =>
        dsimp only at ran
        split at ran
        · obtain ⟨reason, _, finished⟩ := bind_ok ran
          split at finished
          · exact ⟨state, (Except.ok.inj finished).symm, present⟩
          · exact ⟨_, (Except.ok.inj finished).symm, contains_append present⟩
        · exact ⟨state, (Except.ok.inj ran).symm, present⟩
    · intro same
      subst current
      apply forIn_contains inner stored
      intro entry entryMember state outcome ran
      obtain ⟨rawMetadata, index⟩ := entry
      dsimp only at ran
      cases rawMetadata with
      | proxy _ | constructor _ =>
        refine ⟨state, (Except.ok.inj ran).symm, fun present => present, ?_⟩
        intro same
        cases same
      | mapping key value =>
        dsimp only at ran
        split at ran
        · obtain ⟨reason, generated, finished⟩ := bind_ok ran
          have converted : Word.ofNat? (site.base.val + index + 1) = some reason := by
            change (match Word.ofNat? (site.base.val + index + 1) with
              | some value => Except.ok value
              | none => Except.error SourceCoreCompatibleDataPlaceFaultSites.Error.reasonSpaceExhausted) = .ok reason at generated
            split at generated
            · cases generated; assumption
            · cases generated
          have tokenEq (same : (SourceCoreRawMetadata.Metadata.mapping key value, index) =
              (.mapping rawKey rawValue, header.val - 1)) : reason = site.base.add header := by
            have indexEq := congrArg Prod.snd same
            have number : reason.val = site.base.val + index + 1 := by
              unfold Word.ofNat? at converted
              split at converted
              · exact congrArg Fin.val (Option.some.inj converted).symm
              · cases converted
            apply Fin.ext
            rw [token_nonWrapping site.base header header.val reserved (Nat.le_refl _)]
            omega
          split at finished
          · rename_i already
            refine ⟨state, (Except.ok.inj finished).symm, fun present => present, ?_⟩
            intro same
            obtain ⟨row, rowMember, equal⟩ := List.any_eq_true.mp already
            exact ⟨row, rowMember, (of_decide_eq_true equal).trans (tokenEq same)⟩
          · refine ⟨_, (Except.ok.inj finished).symm, contains_append, ?_⟩
            intro same
            exact ⟨_, List.mem_append_right _ (List.mem_singleton_self _), tokenEq same⟩
        · rename_i unmatched
          refine ⟨state, (Except.ok.inj ran).symm, fun present => present, ?_⟩
          intro same
          have types := congrArg Prod.fst same
          cases types
          have contradiction : (decide (SourceCoreRawMetadata.runtimeType rawKey =
              SourceCoreRawMetadata.runtimeType site.keyType) &&
              decide (SourceCoreRawMetadata.runtimeType rawValue =
                SourceCoreRawMetadata.runtimeType site.valueType)) = true := by simp [keyView, valueView]
          exact False.elim (unmatched contradiction)
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error
      (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- The producer's budget check applies to its actual output registry. -/
theorem missingDiagnostics_budget {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {rows : List (Word × Diagnostic)} (accepted : missingDiagnostics registry sites = .ok rows) :
    registry.length ≤ registry.limits.maxEntries := by
  unfold missingDiagnostics at accepted
  split at accepted
  · assumption
  · change (Except.error .registryBudgetExceeded : Except SourceCoreCompatibleDataPlaceFaultSites.Error (List (Word × Diagnostic))) = .ok rows at accepted
    cases accepted

/-- Recover the actual one-based raw header and the same nonwrapping token. -/
theorem MissingRow.metadata {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {row : Word × Diagnostic} (rowOrigin : MissingRow registry sites row) :
    ∃ site, site ∈ sites ∧ ∃ rawKey rawValue header,
      MetadataRep registry (.mapping rawKey rawValue) header ∧
      SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType ∧
      SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType ∧
      row.1 = site.base.add header ∧ site.base.val + header.val < wordModulus ∧
      row.2 = { error := .typeMismatch rawValue none, site := site.site, span := some site.span } := by
  obtain ⟨site, member, index, rawKey, rawValue, stored, keyView, valueView, converted, diagnostic⟩ := rowOrigin
  have number : row.1.val = site.base.val + index + 1 := by
    unfold Word.ofNat? at converted
    split at converted
    · exact congrArg Fin.val (Option.some.inj converted).symm
    · cases converted
  have bounded : index + 1 < wordModulus := by have := row.1.isLt; omega
  let header : Word := ⟨index + 1, bounded⟩
  have lookup : registry.lookup header = some (.mapping rawKey rawValue) := by
    have stored := List.mk_mem_zipIdx_iff_getElem?.mp stored
    simpa [SourceCoreRawMetadata.Registry.lookup, header] using stored
  have reserved : site.base.val + header.val < wordModulus := by
    have := row.1.isLt
    dsimp [header]
    omega
  refine ⟨site, member, rawKey, rawValue, header, ⟨lookup⟩, keyView, valueView, ?_, reserved, diagnostic⟩
  apply Fin.ext
  rw [token_nonWrapping site.base header header.val reserved (Nat.le_refl _)]
  simpa [header, Nat.add_assoc] using number

/-- Authentication gives a real one-based registry position. -/
theorem metadata_headerBound {registry : SourceCoreRawMetadata.Registry}
    {metadata : SourceCoreRawMetadata.Metadata} {header : Word}
    (represented : MetadataRep registry metadata header) : header.val ≤ registry.length := by
  have lookup := represented.lookup
  unfold SourceCoreRawMetadata.Registry.lookup at lookup
  split at lookup
  · cases lookup
  · rename_i positive
    have bounded := (List.getElem?_eq_some_iff.mp lookup).1
    change header.val ≤ registry.entries.length
    omega

/-- A successful extension table checks its actual registry's budget. -/
theorem tableForRegistry_budget {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table) :
    registry.length ≤ registry.limits.maxEntries := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, _⟩ := bind_ok accepted
  exact missingDiagnostics_budget built

/-- Real site membership, an authenticated extended-registry header and its
reserved range give a row in the actual rebuilt public table. -/
theorem tableForRegistry_contains {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (reserved : site.base.val + registry.limits.maxEntries < wordModulus) :
    ∃ row, row ∈ table.additional ∧ row.1 = site.base.add header ∧
      MissingRow registry program.missing row := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst table
  have budget := missingDiagnostics_budget built
  have bounded := metadata_headerBound metadata
  have within : site.base.val + header.val < wordModulus := by omega
  obtain ⟨row, rowMember, tokenEq⟩ := missingDiagnostics_contains built member metadata keyView valueView within
  exact ⟨row, List.mem_append_right _ rowMember, tokenEq, missingDiagnostics_rows built row rowMember⟩

/-- Extension tables contain only actual fixed rows or expanded missing rows. -/
theorem tableForRegistry_rows {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    {row : Word × Diagnostic} (member : row ∈ table.additional) :
    row ∈ program.fixed ∨ MissingRow registry program.missing row := by
  unfold SourceCoreCompatibleDataPlaceFaultSites.Program.tableForRegistry at accepted
  obtain ⟨extra, built, finished⟩ := bind_ok accepted
  have same := Except.ok.inj finished
  subst table
  rcases List.mem_append.mp member with fixed | missing
  · exact .inl fixed
  · exact .inr (missingDiagnostics_rows built row missing)

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticRows
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation
/-! Actual expanded rows are interpreted using their owning ranges and raw
metadata. A duplicate row may retain a different public span; its error is
identified only by the same nonwrapping header in the authentic registry. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticRows

/-- Numeric separation is a static receipt for the actual issued inventory. -/
structure Ranges (capacity : Nat) (sites : List MissingSite) : Prop where
  reserved : ∀ site, site ∈ sites → site.base.val + capacity < wordModulus
  separated : ∀ left, left ∈ sites → ∀ right, right ∈ sites →
    left.base = right.base ∨ left.base.val + capacity < right.base.val ∨
      right.base.val + capacity < left.base.val

/-- Same-token rows in separated real ranges have the same raw owning header,
and hence the same semantic error. No requested span is reconstructed. -/
theorem row_error {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    (ranges : Ranges registry.limits.maxEntries sites)
    (budget : registry.length ≤ registry.limits.maxEntries)
    {site : MissingSite} (member : site ∈ sites)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    {row : Word × Diagnostic} (origin : MissingRow registry sites row)
    (same : row.1 = site.base.add header) : row.2.error = .typeMismatch rawValue none := by
  obtain ⟨actual, actualMember, actualKey, actualValue, actualHeader, actualMetadata,
    _, _, actualToken, _, actualDiagnostic⟩ := origin.metadata
  have leftBound := Nat.le_trans (metadata_headerBound metadata) budget
  have rightBound := Nat.le_trans (metadata_headerBound actualMetadata) budget
  have leftReserved := ranges.reserved site member
  have rightReserved := ranges.reserved actual actualMember
  have tokens : site.base.add header = actual.base.add actualHeader := same.symm.trans actualToken
  rcases ranges.separated site member actual actualMember with bases | before | after
  · have numbers := congrArg Fin.val tokens
    rw [token_nonWrapping _ _ _ leftReserved leftBound,
      token_nonWrapping _ _ _ rightReserved rightBound] at numbers
    have headers : header = actualHeader := by
      apply Fin.ext
      have bases := congrArg Fin.val bases
      omega
    have sameMetadata := Option.some.inj (metadata.lookup.symm.trans (headers.symm ▸ actualMetadata.lookup))
    have sameValue : rawValue = actualValue := (SourceCoreRawMetadata.Metadata.mapping.inj sameMetadata).2
    simp only [actualDiagnostic, sameValue]
  · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ leftReserved rightReserved leftBound rightBound before tokens)
  · exact False.elim (token_ranges_disjoint _ _ _ _ _ _ rightReserved leftReserved rightBound leftBound after tokens.symm)

/-- A fixed row outside the selected reserved interval cannot shadow its
positive authenticated header. -/
theorem fixed_different {registry : SourceCoreRawMetadata.Registry} {site : MissingSite}
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (budget : registry.length ≤ registry.limits.maxEntries)
    (reserved : site.base.val + registry.limits.maxEntries < wordModulus)
    {row : Word × Diagnostic}
    (separate : row.1.val ≤ site.base.val ∨ site.base.val + registry.limits.maxEntries < row.1.val) :
    row.1 ≠ site.base.add header := by
  intro same
  have positive : 0 < header.val := by
    have nonzero := metadata.nonzero
    by_cases zero : header.val = 0
    · exact False.elim (nonzero (Fin.ext zero))
    · omega
  have bounded := Nat.le_trans (metadata_headerBound metadata) budget
  have number := congrArg Fin.val same
  rw [token_nonWrapping _ _ _ reserved bounded] at number
  rcases separate with before | after <;> omega

/-- Decode the actual first matching row. Coverage, range separation and fixed
row separation are static table facts; no universal fault relation is used. -/
theorem table_diagnostic {context : SourceCoreCompatibleDataPlaceFaultSites.Context}
    {program : SourceCoreCompatibleDataPlaceFaultSites.Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table)
    (ranges : Ranges registry.limits.maxEntries program.missing)
    {site : MissingSite} (member : site ∈ program.missing)
    {rawKey rawValue : TypeSystem.Ty} {header : Word}
    (metadata : MetadataRep registry (.mapping rawKey rawValue) header)
    (keyView : SourceCoreRawMetadata.runtimeType rawKey = SourceCoreRawMetadata.runtimeType site.keyType)
    (valueView : SourceCoreRawMetadata.runtimeType rawValue = SourceCoreRawMetadata.runtimeType site.valueType)
    (fixed : ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + registry.limits.maxEntries < row.1.val)
    (positive : site.base.add header ≠ Word.zero)
    (ordinary : site.base.add header ≠ table.escapedReason) :
    ∃ diagnostic, table.diagnostic? (site.base.add header) = some diagnostic ∧
      diagnostic.error = .typeMismatch rawValue none := by
  have budget := tableForRegistry_budget accepted
  obtain ⟨row, rowMember, same, _⟩ := tableForRegistry_contains accepted member metadata keyView valueView
    (ranges.reserved site member)
  have covered : (table.additional.find? (fun candidate => decide (candidate.1 = site.base.add header))).isSome := by
    apply List.find?_isSome.mpr
    exact ⟨row, rowMember, by simp only [same, decide_true]⟩
  cases found : table.additional.find? (fun candidate => decide (candidate.1 = site.base.add header)) with
  | none => simp only [found, Option.isSome_none, Bool.false_eq_true] at covered
  | some selected =>
    have selectedMember := List.mem_of_find?_eq_some found
    have selectedToken : selected.1 = site.base.add header := of_decide_eq_true (List.find?_some (p := fun candidate : Word × Diagnostic => decide (candidate.1 = site.base.add header)) found)
    have error : selected.2.error = .typeMismatch rawValue none := by
      rcases tableForRegistry_rows accepted selectedMember with old | missing
      · exact False.elim (fixed_different metadata budget (ranges.reserved site member) (fixed selected old) selectedToken)
      · exact row_error ranges budget member metadata missing selectedToken
    exact ⟨selected.2, by simp only [SourceCoreFaultSites.Table.diagnostic?, positive, ordinary, found, if_false], error⟩

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingDiagnosticAssociation
end

section
-- leanmerge: from Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts
/-! Proof receipts for the actual compatible diagnostic preparation. These
retain the original base and final rows, numeric bounds and read separation.
Source occurrence ownership and index priority require independent receipts. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts
open Core Frontend SourceInference CompatiblePayload
open SourceCoreCompatibleDataPlaceFaultSites CompatiblePlaceMissingDiagnosticAssociation

/-- Original reads remain separate from every actually issued fixed row. -/
def ReadSafe (reads : List SourceCoreFaultSites.ReadSite) (fixed : List (Word × Diagnostic)) : Prop :=
  ∀ read, read ∈ reads → ∀ row, row ∈ fixed → read.reason ≠ row.1

/-- The actual fresh fixed token lies above every original read. -/
theorem ReadSafe.append {reads : List SourceCoreFaultSites.ReadSite}
    {fixed : List (Word × Diagnostic)} (safe : ReadSafe reads fixed)
    {next : Nat} (below : ∀ read, read ∈ reads → read.reason.val < next)
    {reason : Word} (number : reason.val = next) (diagnostic : Diagnostic) :
    ReadSafe reads (fixed ++ [(reason, diagnostic)]) := by
  intro read member row rowMember
  rcases List.mem_append.mp rowMember with old | fresh
  · exact safe read member row old
  · have sameRow := List.mem_singleton.mp fresh
    subst row
    intro same
    have equal := congrArg Fin.val same
    have bounded := below read member
    change read.reason.val = reason.val at equal
    omega

/-- All fields refer to the one accepted base and the actual final rows. -/
structure ReservedAt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (plan : Plan) (root : Key) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context)
    (base : SourceCoreProgramFaultSites.Program) (extra : List (Word × Diagnostic)) : Prop where
  baseAccepted : SourceCoreProgramFaultSites.prepare plan root = .ok base
  sameBase : program.program.base = base
  sameExpressionBase : program.program.expressions.base = base
  sameRoot : program.program.rootTable = {base.rootTable with additional := program.fixed ++ extra}
  sameExpressionRoot : program.program.expressions.rootTable =
    {base.rootTable with additional := program.fixed ++ extra}
  extraAccepted : missingDiagnostics context.registry program.missing = .ok extra
  legacy : Ranges context.registry.limits.maxEntries program.missing ∧
    (∀ site, site ∈ program.missing → 0 < site.base.val) ∧
    (∀ site, site ∈ program.missing → ∀ row, row ∈ program.fixed →
      row.1.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < row.1.val) ∧
    (∀ site, site ∈ program.missing →
      program.program.rootTable.escapedReason.val ≤ site.base.val ∨
        site.base.val + context.registry.limits.maxEntries < program.program.rootTable.escapedReason.val)
  positive : 0 < program.nextReason
  missingBelow : ∀ site, site ∈ program.missing →
    site.base.val + context.registry.limits.maxEntries < program.nextReason
  fixedBelow : ∀ row, row ∈ program.fixed → row.1.val < program.nextReason
  readsBelow : ∀ read, read ∈ base.rootTable.reads → read.reason.val < program.nextReason
  escapedBelow : base.rootTable.escapedReason.val < program.nextReason
  readsOutside : ∀ site, site ∈ program.missing → ∀ read, read ∈ base.rootTable.reads →
    read.reason.val ≤ site.base.val ∨ site.base.val + context.registry.limits.maxEntries < read.reason.val
  readSafe : ReadSafe base.rootTable.reads program.fixed

/-- The base and extra rows are retained as proof witnesses. -/
def ReservedReceipt (context : SourceCoreCompatibleDataPlaceFaultSites.Context)
    (plan : Plan) (root : Key) (program : SourceCoreCompatibleDataPlaceFaultSites.Program context) : Prop :=
  ∃ base extra, ReservedAt context plan root program base extra

end Solcore.SourceSemantics.CoreLowering.CompatiblePlaceMissingReservedReceipts
end
