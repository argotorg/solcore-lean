import Solcore.SourceSemantics.CoreLowering.RecursiveNamedExpressionSourceBounds
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionCallTree

/-! Original constructor arguments and member/index operands retain their
source costs and order. The mapping terminal remains the existing independent
lookup/default judgment; it adds no expression child or body execution law. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
open Core Frontend SourceInference GeneralHeap CompatiblePayload CoreProof
open CompatibleExpressionPrimitives CompatibleExpressionMembers CompatibleExpressionIndices
open RecursiveNamedCallBounds RecursiveNamedExpressionSourceBounds

variable {checked : SourceCoreCompatibleCatalog.Checked} {source : TypedSource} {id : ExpressionId}
  {node : ExpressionNode} {type : Ty} {program : Program} {context : SourceSemantics.Context}
  {evidence : Dynamic.EvidenceEnvironment} {environment : Dynamic.Environment} {before after : Dynamic.Heap}
  {outcome : Dynamic.ExpressionOutcome} {size : Nat}

theorem constructor_inv {instantiation : DataConstructorInstantiation} {arguments : List ExpressionId} (metadata : Metadata checked source id node type)
    (form : node.form = .constructor instantiation arguments) (unique : NodeOccurrencesUnique source)
    (valid : SourceSemantics.DataConstructorInstantiation.Valid context instantiation)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    ∃ child sequence, ProtectedDataExpressionSequence.TraceAt program child context evidence source environment before arguments sequence after ∧
      CompatibleExpressionConstructors.PacksOutcome instantiation sequence outcome ∧ child < size := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructor _ _ children => exact ⟨_, _, .values children, .values _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found)
      (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | constructorArgument _ children => exact ⟨_, _, .fault children, .fault _, Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller⟩
    | constructorMetadata _ badMetadata => exact False.elim (CompatibleExpressionConstructors.metadata_fault_excluded valid badMetadata)

inductive SourceMember (program : Program) (size : Nat) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base : ExpressionId)
    (index : Nat) : Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | value {baseSize metadata arguments selected after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.constructed metadata arguments) after)
      (field : Dynamic.ValueAt arguments index selected)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.value selected) after
  | failure {baseSize reason after}
      (baseTrace : SourceExecutionSize.ExpressionFaults program baseSize context evidence source environment before base reason after)
      (baseSizeSmaller : baseSize < size) :
      SourceMember program size context evidence source environment before base index (.fault reason) after
  | shape {baseSize value after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base value after)
      (invalid : ¬ Dynamic.ConstructedValue value)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.fault .invalidProjection) after
  | position {baseSize metadata arguments after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.constructed metadata arguments) after)
      (missing : Dynamic.ValueIndexMissing arguments index)
      (baseSizeSmaller : baseSize < size) : SourceMember program size context evidence source environment before base index (.fault .invalidProjection) after

theorem member_inv {base : ExpressionId} {name : String} {index : Nat} (metadata : Metadata checked source id node type)
    (form : node.form = .member base name index) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceMember program size context evidence source environment before base index outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | member _ base field => refine .value base field ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | memberBase _ base => refine .failure base ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | memberShape _ base invalid => refine .shape base invalid ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | memberIndex _ base missing => refine .position base missing ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller


inductive SourceIndex (program : Program) (size : Nat) (context : SourceSemantics.Context) (evidence : Dynamic.EvidenceEnvironment)
    (source : TypedSource) (environment : Dynamic.Environment) (before : Dynamic.Heap) (base key : ExpressionId) :
    Dynamic.ExpressionOutcome → Dynamic.Heap → Prop where
  | found {baseSize keySize sourceKey sourceValue entries lookup value middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (located : Dynamic.MappingLookup lookup entries value)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.value value) after
  | default {baseSize keySize sourceKey sourceValue entries lookup value middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (absent : Dynamic.MappingAbsent lookup entries) (defaulted : Dynamic.DefaultValue sourceValue value)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.value value) after
  | baseFailure {baseSize reason after}
      (failed : SourceExecutionSize.ExpressionFaults program baseSize context evidence source environment before base reason after)
      (baseSizeSmaller : baseSize < size) :
      SourceIndex program size context evidence source environment before base key (.fault reason) after
  | keyFailure {baseSize keySize baseValue reason middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base baseValue middle)
      (failed : SourceExecutionSize.ExpressionFaults program keySize context evidence source environment middle key reason after)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault reason) after
  | shape {baseSize keySize baseValue lookup middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base baseValue middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (invalid : ¬ Dynamic.MappingValue baseValue)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault .invalidProjection) after
  | keyType {baseSize keySize sourceKey sourceValue entries lookup actual middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeType lookup actual)
      (mismatch : Dynamic.runtimeType actual ≠ Dynamic.runtimeType sourceKey)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault (.typeMismatch sourceKey (Dynamic.runtimeType actual))) after
  | unavailable {baseSize keySize sourceKey sourceValue entries lookup middle after}
      (baseTrace : SourceExecutionSize.ExpressionEvaluates program baseSize context evidence source environment before base (.mapping sourceKey sourceValue entries) middle)
      (keyTrace : SourceExecutionSize.ExpressionEvaluates program keySize context evidence source environment middle key lookup after)
      (typed : Dynamic.ValueRuntimeTypeMatches lookup sourceKey)
      (absent : Dynamic.MappingAbsent lookup entries) (missing : ¬ Dynamic.Defaultable sourceValue)
      (baseSizeSmaller : baseSize < size)
      (keySizeSmaller : keySize < size) :
      SourceIndex program size context evidence source environment before base key (.fault (.missingMappingDefault sourceValue)) after

theorem index_inv {base key : ExpressionId} (metadata : CompatibleExpressionReads.Metadata checked source id node type)
    (form : node.form = .index base key) (unique : NodeOccurrencesUnique source)
    (trace : ExpressionOutcome program size context evidence source environment before id outcome after) :
    SourceIndex program size context evidence source environment before base key outcome after := by
  cases trace with
  | value evaluated =>
    obtain ⟨_, raw, smaller⟩ := evaluation_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions evaluated
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexFound _ base key found => refine .found base key found ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexDefault _ base key absent defaulted => refine .default base key absent defaulted ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
  | fault failed =>
    obtain ⟨_, raw, smaller⟩ := fault_raw_sized unique (lookupExpression?_sound metadata.found) (by intros; simp [form]) metadata.coercions failed
    rw [form, metadata.requirements, metadata.coercions] at raw
    cases raw with
    | indexBase _ failed => refine .baseFailure failed ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexKey _ base failed => refine .keyFailure base failed ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexShape _ base key shape => refine .shape base key shape ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexKeyType _ base key typed mismatch => refine .keyType base key typed mismatch ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller
    | indexDefaultUnavailable _ base key typed absent missing => refine .unavailable base key typed absent missing ?_ ?_ <;> exact Nat.lt_trans (SourceExecutionSize.child_lt_stepSize (by simp)) smaller


theorem SourceIndex.split {base key : ExpressionId}
    (trace : SourceIndex program size context evidence source environment before base key outcome after) :
    (∃ reason child, outcome = .fault reason ∧
      SourceExecutionSize.ExpressionFaults program child context evidence source environment before base reason after ∧ child < size) ∨
    (∃ baseValue middle first, SourceExecutionSize.ExpressionEvaluates program first context evidence source environment before base baseValue middle ∧ first < size ∧
      ((∃ reason second, outcome = .fault reason ∧ SourceExecutionSize.ExpressionFaults program second context evidence source environment middle key reason after ∧ second < size) ∨
       (∃ keyValue second, SourceExecutionSize.ExpressionEvaluates program second context evidence source environment middle key keyValue after ∧ second < size ∧ Terminal baseValue keyValue outcome))) := by
  cases trace with
  | baseFailure failed smaller => exact .inl ⟨_, _, rfl, failed, smaller⟩
  | keyFailure base failed firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inl ⟨_, _, rfl, failed, secondSmaller⟩⟩
  | found base key found firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .found rfl found⟩⟩
  | default base key absent defaulted firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .default rfl absent defaulted⟩⟩
  | shape base key invalid firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .shape invalid⟩⟩
  | keyType base key typed mismatch firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .keyType rfl typed mismatch⟩⟩
  | unavailable base key typed absent missing firstSmaller secondSmaller => exact .inr ⟨_, _, _, base, firstSmaller, .inr ⟨_, _, key, secondSmaller, .unavailable rfl typed absent missing⟩⟩

end Solcore.SourceSemantics.CoreLowering.RecursiveNamedDataExpressionSourceBounds
