import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConditionalMeaning
import Solcore.SourceSemantics.CoreLowering.CompatibleEncodingFacts

/-! Constructor source traces use independent metadata validity and preserve
left-to-right argument effects. Native type projection alone is not a proof
of the original constructor metadata. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
open Core Frontend SourceInference CompatibleExpressionPrimitives

private theorem mismatch_irrefl {types : List TypeSystem.Ty} {expected actual : TypeSystem.Ty}
    (mismatch : Dynamic.TypesFirstMismatch types types expected actual) : False := by
  induction types with
  | nil => cases mismatch
  | cons head tail ih =>
    cases mismatch with
    | head different => exact different rfl
    | tail failed => exact ih failed

theorem metadata_fault_excluded {context : SourceSemantics.Context} {metadata : DataConstructorInstantiation}
    {reason : Dynamic.SemanticFault} (valid : SourceSemantics.DataConstructorInstantiation.Valid context metadata)
    (fault : Dynamic.ConstructorMetadataFaults context metadata reason) : False := by
  cases valid with
  | intro dataType signature dataMember signatureMember owner constructor exact range payloads result =>
    cases fault with
    | missing absent => exact absent dataType dataMember signature signatureMember constructor.symm
    | owner entry different =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact different owner
    | payloadArity entry mismatch =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact mismatch (by simp [payloads])
    | payloadType entry mismatch =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      rw [payloads] at mismatch
      exact mismatch_irrefl mismatch
    | resultType entry different =>
      obtain ⟨rfl, rfl⟩ := entry.unique dataType signature dataMember signatureMember constructor.symm
      exact different result

inductive PacksOutcome (metadata : DataConstructorInstantiation) :
    DataExpressionSequence.Outcome → Dynamic.ExpressionOutcome → Prop where
  | values (values : List Dynamic.Value) : PacksOutcome metadata (.ok values) (.value (.constructed metadata values))
  | fault (reason : Dynamic.SemanticFault) : PacksOutcome metadata (.error reason) (.fault reason)

theorem PacksOutcome.functional {metadata : DataConstructorInstantiation} {sequence : DataExpressionSequence.Outcome}
    {first second : Dynamic.ExpressionOutcome} (left : PacksOutcome metadata sequence first)
    (right : PacksOutcome metadata sequence second) : first = second := by
  cases left <;> cases right <;> rfl

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId}

theorem constructor_inv (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments) (unique : NodeOccurrencesUnique source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (trace : Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after) :
    ∃ sequence, DataExpressionSequence.Trace program context evidence source environment before arguments sequence after ∧
      PacksOutcome instantiation sequence outcome := by
  cases trace with
  | value evaluated =>
    have raw := evaluation_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructor _ _ children => exact ⟨_, .values children, .values _⟩
  | fault failed =>
    have raw := fault_raw unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructorArgument _ children => exact ⟨_, .fault children, .fault _⟩
    | constructorMetadata _ badMetadata => exact False.elim (metadata_fault_excluded valid badMetadata)

theorem constructor_intro (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    {sequence : DataExpressionSequence.Outcome}
    (trace : DataExpressionSequence.Trace program context evidence source environment before arguments sequence after)
    (packed : PacksOutcome instantiation sequence outcome) :
    Dynamic.ExpressionEvaluatesOutcome program context evidence source environment before id outcome after := by
  cases packed with
  | values values =>
    cases trace with
    | values children =>
      apply Dynamic.ExpressionEvaluatesOutcome.value
      apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound metadata.found)
      · rw [form, metadata.requirements, metadata.coercions]
        exact .constructor rfl valid children
      · rw [metadata.coercions]; exact .nil
  | fault reason =>
    cases trace with
    | fault failed =>
      apply Dynamic.ExpressionEvaluatesOutcome.fault
      apply Dynamic.ExpressionFaults.form (lookupExpression?_sound metadata.found)
      rw [form, metadata.requirements, metadata.coercions]
      exact .constructorArgument rfl failed

theorem constructor_source_types
    (unique : NodeOccurrencesUnique source) (found : source.lookupExpression? id = some node)
    (form : node.form = .constructor instantiation arguments) (coercions : node.coercions = [])
    (typed : ExpressionHasType source context id node.type) :
    SourceSemantics.DataConstructorInstantiation.Admissible context instantiation ∧
      ExpressionsHaveTypes source context arguments instantiation.payloadTypes ∧ node.type = instantiation.resultType := by
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
    | constructor constructorValid children => exact ⟨constructorValid, children, rfl⟩

end Solcore.SourceSemantics.CoreLowering.CompatibleExpressionConstructors
