import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndexLookup

/-! Independent index traces retain base-before-key evaluation, exact raw
mapping headers and default availability. The scalar restriction is static;
it does not identify source metadata using equal native representations. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
open Core Frontend SourceInference GeneralHeap CompatiblePayload CompatibleMapping
open CompatibleExpressionReads CompatibleExpressionPrimitives

inductive SourceScalar : TypeSystem.Ty → Prop where
  | bool : SourceScalar .bool
  | word : SourceScalar .word
  | integer : SourceScalar .integer

theorem SourceScalar.projected {checked : SourceCoreCompatibleCatalog.Checked} {sourceType : TypeSystem.Ty} {type : Ty}
    (scalar : SourceScalar sourceType) (projected : checked.catalog.project sourceType = .ok type) : Scalar type := by
  cases scalar <;> cases projected
  · exact .bool
  · exact .word
  · exact .integer

theorem source_mapping {checked : SourceCoreCompatibleCatalog.Checked} {registry : SourceCoreRawMetadata.Registry}
    {ambient : AmbientDefinitions checked.catalog.definitions} {functions : FunctionModel checked.catalog ambient}
    {mapping : LocationMap} {world : StoreTyping} {expected : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : ValueRep checked registry functions mapping world expected source value type) :
    ∀ {key result}, SourceCoreRawMetadata.runtimeType expected = .mapping key result →
      ∃ sourceKey sourceValue sources, source = .mapping sourceKey sourceValue sources := by
  induction related using ValueRep.rec (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True) (motive_4 := fun _ _ _ _ => True) with
  | unit | bool | word | integer | product | function | proxy => intro _ _ impossible; cases impossible
  | constructed metadata =>
    intro key result view
    have facts := CompatibleConstructorMetadata.facts metadata.authenticated
    cases facts with
    | mk signature constructor arguments _ _ _ _ _ resultType =>
      rw [resultType, CompatibleConstructorMetadata.runtimeType_nominal] at view
      have impossible := congrArg SourceCoreDataCatalog.nominalParts view
      simp only [DataPatternAuthenticity.nominalParts_nominal, SourceCoreDataCatalog.nominalParts, reduceCtorEq] at impossible
  | mappingValue => intro _ _ _; exact ⟨_, _, _, rfl⟩
  | compatible same _ ih => intro _ _ view; exact ih (by rw [← same]; exact view)
  | nil | cons | empty | entry | absent | present => trivial

inductive SourceIndex (program : Program) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base key : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | found {sourceKey sourceValue entries lookup value middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (located : Dynamic.MappingLookup lookup entries value) :
      SourceIndex program context evidence source environment before base key (.value value) after
  | default {sourceKey sourceValue entries lookup value middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue sourceValue value) :
      SourceIndex program context evidence source environment before base key (.value value) after
  | baseFailure {reason after}
      (failed : Dynamic.ExpressionFaults program context evidence source environment before base reason after) :
      SourceIndex program context evidence source environment before base key (.fault reason) after
  | keyFailure {baseValue reason middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
      (failed : Dynamic.ExpressionFaults program context evidence source environment middle key reason after) :
      SourceIndex program context evidence source environment before base key (.fault reason) after
  | shape {baseValue lookup middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base baseValue middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (invalid : ¬ Dynamic.MappingValue baseValue) :
      SourceIndex program context evidence source environment before base key (.fault .invalidProjection) after
  | keyType {sourceKey sourceValue entries lookup actual middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeType lookup actual)
      (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey) :
      SourceIndex program context evidence source environment before base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual))) after
  | unavailable {sourceKey sourceValue entries lookup middle after}
      (baseTrace : Dynamic.ExpressionEvaluates program context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : Dynamic.ExpressionEvaluates program context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeTypeMatches lookup sourceKey)
      (absent : Dynamic.MappingAbsent lookup entries) (missing : ¬ Dynamic.Defaultable sourceValue) :
      SourceIndex program context evidence source environment before base key (.fault (.missingMappingDefault sourceValue)) after

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id base key : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome}

theorem index_inv (metadata : CompatibleExpressionReads.Metadata checked source id node type)
    (form : node.form = .index base key) (unique : NodeOccurrencesUnique source)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    SourceIndex program context evidence source environment before base key outcome after := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexFound _ base key found => exact .found base key found
    | indexDefault _ base key absent defaulted => exact .default base key absent defaulted
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexBase _ failed => exact .baseFailure failed
    | indexKey _ base failed => exact .keyFailure base failed
    | indexShape _ base key shape => exact .shape base key shape
    | indexKeyType _ base key typed mismatch => exact .keyType base key typed mismatch
    | indexDefaultUnavailable _ base key typed absent missing => exact .unavailable base key typed absent missing

theorem index_intro (metadata : CompatibleExpressionReads.Metadata checked source id node type) (form : node.form = .index base key)
    (trace : SourceIndex program context evidence source environment before base key outcome after) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases trace with
  | found base key found =>
    apply Dynamic.ExpressionEvaluatesOutcome.value; apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .indexFound rfl base key found
    · rw [metadata.coercions]; exact .nil
  | default base key absent defaulted =>
    apply Dynamic.ExpressionEvaluatesOutcome.value; apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
    · rw [form, metadata.requirements, metadata.coercions]; exact .indexDefault rfl base key absent defaulted
    · rw [metadata.coercions]; exact .nil
  | baseFailure failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexBase rfl failed
  | keyFailure base failed =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexKey rfl base failed
  | shape base key shape =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexShape rfl base key shape
  | keyType base key typed mismatch =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexKeyType rfl base key typed mismatch
  | unavailable base key typed absent missing =>
    apply Dynamic.ExpressionEvaluatesOutcome.fault; apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
    rw [form, metadata.requirements, metadata.coercions]; exact .indexDefaultUnavailable rfl base key typed absent missing

theorem index_source_types (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .index base key) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    ∃ keyType, ExpressionHasType source context base (.mapping keyType node.type) ∧ ExpressionHasType source context key keyType := by
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
    | index baseTyped keyTyped => exact ⟨_, baseTyped, keyTyped⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionIndices
