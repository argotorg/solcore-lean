import Solcore.SourceSemantics.CoreLowering.CompatiblePlaceKeys
import Solcore.SourceSemantics.SubstitutionProperties

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
