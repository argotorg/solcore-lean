import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMemberLayouts

/-! Independent member-expression traces, including the exact base failure
and invalid projection rules. Authenticated static layouts exclude invalid
shapes and positions only after the base's meaning has been established. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
open Core Frontend SourceInference CompatibleExpressionPrimitives CompatiblePayload GeneralHeap DataPatternValues

inductive Layout (checked : SourceCoreCompatibleCatalog.Checked) (site : SourceCoreElaboration.ErrorSite)
    (base field : TypeSystem.Ty) (index : Nat) (identity : DataTypeId) (branches : List Expr) (result : Ty) : Prop where
  | intro {signature arguments infos}
      (nominal : SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType base) = some (signature.id, arguments))
      (selected : checked.signatures.dataTypes.filter (fun data => decide (data.id = signature.id)) = [signature])
      (certificate : CompatibleMemberCertificates.Certificate checked site (SourceCoreRawMetadata.runtimeType base)
        field signature arguments index identity infos result)
      (generated : branches = infos.map (branchCode index)) : Layout checked site base field index identity branches result

private theorem source_constructor {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world sourceType source value type) :
    ∀ {owner arguments}, SourceCoreDataCatalog.nominalParts (SourceCoreRawMetadata.runtimeType sourceType) = some (owner, arguments) →
      ∃ metadata payloads, source = .constructed metadata payloads := by
  induction related using CompatiblePayload.ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy | mappingValue => intro _ _ impossible; cases impossible
  | constructed => intro _ _ _; exact ⟨_, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

/-- Row selection authenticates both the original source field view and the
actual projected payload expression. This statement has no evaluation input. -/
theorem Layout.select {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {site : SourceCoreElaboration.ErrorSite}
    {base field : TypeSystem.Ty} {index : Nat} {identity : DataTypeId} {branches : List Expr} {result : Ty}
    (layout : Layout checked site base field index identity branches result)
    {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world base source value type) :
    ∃ metadata sources tag header payloads types child native,
      source = .constructed metadata sources ∧
      value = .constructed tag (.pair (.word header) (packValues payloads)) ∧
      tag.owner = identity ∧
      branches[tag.index]? = some (LanguageResult.success (SourceCoreDataExpressions.projectPacked index types (.second (.var 0)))) ∧
      types.length = payloads.length ∧ payloads[index]? = some native ∧
      Dynamic.ValueAt sources index child ∧ ValueRep checked registry functions mapping world field child native result := by
  cases layout with
  | intro nominal selected certificate generated =>
    obtain ⟨metadata, sources, rfl⟩ := source_constructor related nominal
    obtain ⟨tag, header, payloads, types, rfl, typeEq, fields⟩ := constructor_fields related rfl
    obtain ⟨owner, branch, actual, child, native, branchAt, tagEq, typesEq, sourceAt, view, coreAt, selectedAt, nativeAt, childRelated⟩ :=
      certificate.select nominal selected fields
    refine ⟨metadata, sources, tag, header, payloads, types, child, native, rfl, rfl, owner, ?_, ?_, nativeAt, selectedAt,
      .compatible view.symm childRelated⟩
    · simp only [generated, List.getElem?_map, branchAt, Option.map_some, branchCode, typesEq]
    · exact fields.payloads.length.2.2.symm.trans fields.payloads.length.2.1

inductive SourceMember (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base : ExpressionId)
    (index : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {metadata arguments selected after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.constructed metadata arguments) after)
      (field : Dynamic.ValueAt arguments index selected) : SourceMember program context evidence source environment before base index (.value selected) after
  | failure {reason after}
      (baseTrace : Dynamic.ExpressionFaults program context evidence source environment before base reason after) :
      SourceMember program context evidence source environment before base index (.fault reason) after
  | shape {value after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base value after)
      (invalid : ¬ Dynamic.ConstructedValue value) : SourceMember program context evidence source environment before base index (.fault .invalidProjection) after
  | position {metadata arguments after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.constructed metadata arguments) after)
      (missing : Dynamic.ValueIndexMissing arguments index) : SourceMember program context evidence source environment before base index (.fault .invalidProjection) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id base : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {name : String} {index : Nat}

theorem member_inv (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceMember program context evidence source environment before base index outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | member _ base field => exact .value base field
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | memberBase _ base => exact .failure base
    | memberShape _ base invalid => exact .shape base invalid
    | memberIndex _ base missing => exact .position base missing

theorem member_intro (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index)
    (trace : SourceMember program context evidence source environment before base index outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | value base field =>
    apply Dynamic.ExpressionEvaluatesOutcome.value
    apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .member rfl base field
    · rw [metadata.coercions]; exact .nil
  | failure base =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberBase rfl base
  | shape base invalid =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberShape rfl base invalid
  | position base missing =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault
    apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]
    exact .memberIndex rfl base missing

theorem member_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .member base name index) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ baseType, ExpressionHasType source context base baseType ∧ UniformMemberProjection context baseType index node.type := by
  generalize typeEq : node.type = type at typed
  cases typed with
  | @intro _ _ actualNode rawType plan contains raw _ _ _ valid =>
    have same := Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
    subst actualNode
    have path := valid.outputPath
    rw [coercions] at path
    cases path
    rw [form] at raw
    generalize resultEq : node.type = result at raw
    cases raw with
    | member baseTyped projection => exact ⟨_, baseTyped, projection⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionMembers
