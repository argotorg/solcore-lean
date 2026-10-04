import Solcore.Core.Correspondence
import Solcore.SourceSemantics.Dynamic.Evaluation
import Solcore.Resolved.LocalScope
import Solcore.SourceSemantics.CoreLowering.SourceStagedClosedEvaluationMeaning
import Solcore.Resolved.Typing
import Solcore.Resolved.Eval
import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerLetMeaning
import Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerStatementsMeaning

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Parameter allocation retains all reads, including unused original cells. -/
theorem preserves_read {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    {location : Location} {cell : Cell} (read : Heap.Reads before location cell) :
    Heap.Reads after location cell := by
  induction allocated with
  | nil => exact read
  | cons allocation _ ih => exact ih (allocation.preserves_read read)

theorem allocation_length {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after) :
    inputs.length = values.length := by
  induction allocated with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

/-- A fresh parameter sequence preserves the original first-match lookup. -/
theorem preserves_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    {id : Resolved.LocalId} {location : Location}
    (fresh : ∀ input, input ∈ inputs → input.id ≠ id)
    (found : Dynamic.Environment.LooksUp initial id location) :
    Dynamic.Environment.LooksUp final id location := by
  induction allocated with
  | nil => exact found
  | cons allocation tail ih =>
      exact ih (fun input member => fresh input (by simp [member]))
        (.tail (fresh _ (by simp)) found)

/-- Forward input order selects the actual source address, even though the
completed lexical environment lists the last allocated parameter first. -/
theorem allocated_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    (unique : (inputs.map (·.id)).Nodup)
    {index : Nat} {input : TypedBinder} {value : Dynamic.Value}
    (inputAt : inputs[index]? = some input) (valueAt : values[index]? = some value) :
    ∃ location : Location, location.index = before.cells.length + index ∧
      Dynamic.Environment.LooksUp final input.id location ∧
      Heap.Reads after location { type := input.scheme.body, value := some value } := by
  induction allocated generalizing index input value with
  | nil => simp at inputAt
  | @cons initial final before middle after head rest headValue tailValues location allocation tail ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at inputAt valueAt
          subst input
          subst value
          refine ⟨location, by simpa using allocation.location_fresh, ?_, ?_⟩
          · apply preserves_lookup tail ?_ Dynamic.Environment.LooksUp.head
            intro candidate member same
            exact unique.1 (List.mem_map.mpr ⟨candidate, member, same⟩)
          · exact preserves_read tail allocation.reads_new
      | succ index =>
          obtain ⟨actual, address, found, read⟩ := ih unique.2 inputAt valueAt
          refine ⟨actual, ?_, found, read⟩
          rw [allocation.length_eq_succ] at address
          omega

/-- Scalar input values are represented directly by the pure Core ABI.
This relation supplies no Core store allocation or callable authority. -/
inductive ScalarRep : Dynamic.Value → Core.Value → Prop where
  | word (value : Core.Word) : ScalarRep (.word value) (.word value)
  | bool (value : Bool) : ScalarRep (.bool value) (.bool value)

inductive ScalarValuesRep : List Dynamic.Value → List Core.Value → Prop where
  | nil : ScalarValuesRep [] []
  | cons {value : Dynamic.Value} {native : Core.Value}
      {values : List Dynamic.Value} {natives : List Core.Value}
      (head : ScalarRep value native) (tail : ScalarValuesRep values natives) :
      ScalarValuesRep (value :: values) (native :: natives)

theorem ScalarValuesRep.length_eq {values : List Dynamic.Value} {native : List Core.Value}
    (represented : ScalarValuesRep values native) : values.length = native.length := by
  induction represented with
  | nil => rfl
  | cons _ _ ih => exact congrArg Nat.succ ih

theorem scalar_at {values : List Dynamic.Value} {native : List Core.Value}
    (represented : ScalarValuesRep values native)
    {index : Nat} {result : Core.Value} (atNative : native[index]? = some result) :
    ∃ value, values[index]? = some value ∧ ScalarRep value result := by
  induction represented generalizing index with
  | nil => simp at atNative
  | cons head tail ih =>
      cases index with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at atNative
          subst result
          exact ⟨_, rfl, head⟩
      | succ index => exact ih atNative

/-- The pure positional ABI keeps the original forward parameter order. -/
def inputEnvironment (inputs : List TypedBinder) (native : List Core.Value) :
    Resolved.LocalScope Core.Value := (inputs.map (·.id)).zip native

/-- An actual scalar ABI lookup is authenticated by the actual source
parameter allocator. Neither the initial environment nor unused cells are
filtered; this theorem does not allocate any Core store cells. -/
theorem allocated_native_lookup {initial final : Dynamic.Environment} {before after : Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    (allocated : BindersAllocate initial before inputs values final after)
    (unique : (inputs.map (·.id)).Nodup)
    (represented : ScalarValuesRep values native)
    {id : Resolved.LocalId} {result : Core.Value}
    (found : Resolved.LocalScope.Lookup (inputEnvironment inputs native) id result) :
    ∃ location cell value,
      Dynamic.Environment.LooksUp final id location ∧ Heap.Reads after location cell ∧
      cell.generalized = none ∧ cell.value = some value ∧ ScalarRep value result := by
  have arity : (inputs.map (·.id)).length = native.length := by
    rw [List.length_map]
    exact (allocation_length allocated).trans represented.length_eq
  have idsEq : Resolved.LocalScope.ids (inputEnvironment inputs native) = inputs.map (·.id) :=
    List.map_fst_zip (Nat.le_of_eq arity)
  have valuesEq : Resolved.LocalScope.values (inputEnvironment inputs native) = native :=
    List.map_snd_zip (Nat.le_of_eq arity.symm)
  obtain ⟨index, indexed, nativeAt⟩ := found.indexed
  rw [idsEq] at indexed
  rw [valuesEq] at nativeAt
  have inputIdAt := indexed.getElem?
  rw [List.getElem?_map] at inputIdAt
  obtain ⟨input, inputAt, sameId⟩ := Option.map_eq_some_iff.mp inputIdAt
  obtain ⟨value, valueAt, scalar⟩ := scalar_at represented nativeAt
  obtain ⟨location, _, lookup, read⟩ := allocated_lookup allocated unique inputAt valueAt
  exact ⟨location, _, value, sameId ▸ lookup, read, rfl, rfl, scalar⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Frontend SourceInference SourceCoreElaboration.Internal.Staged

/-- Only the two scalar carriers used by this pure residual fragment. -/
inductive ScalarTyped : Core.Value → Core.Ty → Prop where
  | word (value : Core.Word) : ScalarTyped (.word value) .word
  | bool (value : Bool) : ScalarTyped (.bool value) .bool

/-- Every actual native first-match lookup observes the same ordinary Source cell. -/
def RuntimeEnvironmentRep (native : Resolved.Environment) (source : Dynamic.Environment)
    (heap : Dynamic.Heap) : Prop :=
  ∀ id value, Resolved.LocalScope.Lookup native id value → ∃ location cell sourceValue,
    Dynamic.Environment.LooksUp source id location ∧ Dynamic.Heap.Reads heap location cell ∧
    cell.generalized = none ∧ cell.value = some sourceValue ∧ ScalarRep sourceValue value

/-- Context entries have actual native scalar values of their assigned types. -/
def RuntimeEnvironmentTyped (scope : Resolved.Context) (native : Resolved.Environment) : Prop :=
  ∀ id type, Resolved.LocalScope.Lookup scope id type → ∃ value,
    Resolved.LocalScope.Lookup native id value ∧ ScalarTyped value type

private theorem scalar_of_raw {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {source : TypedSource}
    {environment : Dynamic.Environment} {heap : Dynamic.Heap} {id : ExpressionId}
    {node : ExpressionNode} {value : Dynamic.Value}
    (found : source.lookupExpression? id = some node) (empty : node.coercions = [])
    (raw : Dynamic.ExpressionFormEvaluates program context evidence source environment heap
      node.form node.requirements node.coercions value heap) :
    Dynamic.ExpressionEvaluates program context evidence source environment heap id value heap := by
  apply Dynamic.ExpressionEvaluates.intro (lookupExpression?_sound found) raw
  rw [empty]
  exact .nil

/-- One induction on the static receipt constructs independent Source and
Resolved evaluations. Both keep their full initial states. A native store is
independent of the Source heap and no Core allocation is inferred here. -/
theorem expression_meaning {program : Program} {context : SourceSemantics.Context}
    {evidence : Dynamic.EvidenceEnvironment} {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : SourceCoreElaboration.Internal.Staged.Environment}
    {fuel : Nat} {id : ExpressionId} {result : SourceCoreElaboration.LoweredExpression}
    {expected : Core.Ty} {sourceEnv : Dynamic.Environment} {sourceHeap : Dynamic.Heap}
    {nativeEnv : Resolved.Environment} {coreStore : Core.Store}
    (checked : Residual.ExpressionChecked solved source scope staged fuel id result)
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : SourceStagedClosedEvaluationMeaning.UsedValid context solved result.consumedRequirements)
    (stagedRep : SourceStagedClosedEvaluationMeaning.EnvironmentRep staged sourceEnv sourceHeap)
    (runtimeRep : RuntimeEnvironmentRep nativeEnv sourceEnv sourceHeap)
    (typedEnv : RuntimeEnvironmentTyped scope nativeEnv) :
    ∃ sourceValue nativeValue,
      Dynamic.ExpressionEvaluates program context evidence source sourceEnv sourceHeap id sourceValue sourceHeap ∧
      Resolved.Evaluates nativeEnv coreStore result.resolved nativeValue coreStore ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected := by
  induction checked generalizing expected with
  | @literal fuel id node literal value found form requirements coercions interpreted =>
    cases typed
    have modulo : Core.Word.ofNatModulo value.val = value := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt value.isLt
    have constructs : Dynamic.LiteralConstructs literal (.word value) := by
      rw [← modulo]
      exact .word (interpretWordLiteral?_sound interpreted)
    refine ⟨.word value, .word value, ?_, .word, .word value, .word value⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .literal rfl constructs
  | @stagedWord fuel id result checked =>
    cases typed
    exact ⟨.word result.value, .word result.value,
      (SourceStagedClosedEvaluationMeaning.checked_meaning ledger stagedRep fuel).2.1 checked valid,
      .word, .word result.value, .word result.value⟩
  | @stagedBool fuel id result checked =>
    cases typed
    exact ⟨.bool result.value, .bool result.value,
      (SourceStagedClosedEvaluationMeaning.checked_meaning ledger stagedRep fuel).2.2 checked valid,
      .bool, .bool result.value, .bool result.value⟩
  | @«local» fuel id node name binder found form requirements coercions _ =>
    cases typed with
    | var atType =>
      obtain ⟨nativeValue, atValue, valueTyped⟩ := typedEnv _ _ atType
      obtain ⟨location, cell, sourceValue, lookup, read, ordinary, initialized, scalar⟩ := runtimeRep _ _ atValue
      refine ⟨sourceValue, nativeValue, ?_, .var atValue, scalar, valueTyped⟩
      apply scalar_of_raw found coercions
      rw [form, requirements, coercions]
      exact .local rfl lookup read ordinary initialized
  | @boolean fuel id node name value found form requirements coercions =>
    cases typed
    refine ⟨.bool value, .bool value, ?_, .bool, .bool value, .bool value⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .builtinBoolean rfl
  | @group fuel id node inner result found form requirements coercions child ih =>
    obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := ih typed valid
    refine ⟨sourceValue, nativeValue, ?_, native, scalar, valueTyped⟩
    apply scalar_of_raw found coercions
    rw [form, requirements, coercions]
    exact .group rfl evaluated
  | @conditional fuel id node condition yes no guard left right found form requirements coercions _ _ _ guardIH yesIH noIH =>
    cases typed with
    | ifE guardTyped yesTyped noTyped =>
      have guardValid := valid.mono (by intro child member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have yesValid := valid.mono (by intro child member; exact List.mem_append_left _ (List.mem_append_right _ member))
      have noValid := valid.mono (by intro child member; exact List.mem_append_right _ member)
      obtain ⟨guardSource, guardNative, guardSourceEval, guardNativeEval, guardScalar, guardType⟩ := guardIH guardTyped guardValid
      cases guardType with
      | bool truth =>
        cases guardScalar
        cases truth with
        | false =>
          obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := noIH noTyped noValid
          refine ⟨sourceValue, nativeValue, ?_, .ifFalse guardNativeEval native, scalar, valueTyped⟩
          apply scalar_of_raw found coercions
          rw [form, requirements, coercions]
          exact .conditionalFalse rfl guardSourceEval evaluated
        | true =>
          obtain ⟨sourceValue, nativeValue, evaluated, native, scalar, valueTyped⟩ := yesIH yesTyped yesValid
          refine ⟨sourceValue, nativeValue, ?_, .ifTrue guardNativeEval native, scalar, valueTyped⟩
          apply scalar_of_raw found coercions
          rw [form, requirements, coercions]
          exact .conditionalTrue rfl guardSourceEval evaluated

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics
open SourceCoreElaboration SourceCoreElaboration.Internal
open SourceStagingHeapRelation
local notation "Closed" => SourceStagedClosedEvaluationMeaning.EnvironmentRep

/-- Root lexical rows may omit only an actual staged Integer binding. Captured
closure environments continue to use the unchanged full EnvironmentRel. -/
inductive MixedEnvironment (mapping : LocationMap) (heap : Dynamic.Heap) :
    Dynamic.Environment → Dynamic.Environment → Staged.Environment → Prop where
  | nil : MixedEnvironment mapping heap [] [] []
  | keep {id source target left right staged}
      (mapped : Maps mapping source target)
      (tail : MixedEnvironment mapping heap left right staged) :
      MixedEnvironment mapping heap ((id, source) :: left) ((id, target) :: right) staged
  | erase {binding location left right staged}
      (dropped : mapping[location.index]? = some none)
      (read : Dynamic.Heap.Reads heap location
        { type := .integer, value := some (.integer (SourceStagedClosedEvaluationMeaning.bindingValue binding)) })
      (tail : MixedEnvironment mapping heap left right staged) :
      MixedEnvironment mapping heap
        ((SourceStagedIntegerStatementsMeaning.bindingId binding, location) :: left)
        right (binding :: staged)

namespace MixedEnvironment

theorem of_retained {mapping : LocationMap} {heap : Dynamic.Heap}
    {left right : Dynamic.Environment} (related : EnvironmentRel mapping left right) :
    MixedEnvironment mapping heap left right [] := by
  induction related with
  | nil => exact .nil
  | cons mapped tail ih => exact .keep mapped ih

/-- All old rows survive the original source allocation, including shadowed
and unused entries. The new mapping position is accounted for separately. -/
theorem allocated {mapping : LocationMap} {before after : Dynamic.Heap}
    {left right : Dynamic.Environment} {staged : Staged.Environment}
    (related : MixedEnvironment mapping before left right staged)
    {type : TypeSystem.Ty} {value : Option Dynamic.Value} {location : Dynamic.Location}
    (allocation : Dynamic.Heap.Allocates before type value location after)
    (suffix : LocationMap) : MixedEnvironment (mapping ++ suffix) after left right staged := by
  induction related with
  | nil => exact .nil
  | keep mapped tail ih => exact .keep (extends_append _ _ _ _ mapped) ih
  | erase dropped read tail ih =>
      apply MixedEnvironment.erase ?_ (allocation.preserves_read read) ih
      simpa only [List.getElem?_append_left (List.getElem?_eq_some_iff.mp dropped).1] using dropped

theorem erase_allocated {mapping : LocationMap} {before residual after : Dynamic.Heap}
    {left right : Dynamic.Environment} {staged : Staged.Environment}
    (related : MixedEnvironment mapping before left right staged)
    (heaps : HeapRel mapping before residual) (binding : Staged.Binding)
    {location : Dynamic.Location}
    (allocation : Dynamic.Heap.Allocates before .integer
      (some (.integer (SourceStagedClosedEvaluationMeaning.bindingValue binding))) location after) :
    MixedEnvironment (mapping ++ [none]) after
      ((SourceStagedIntegerStatementsMeaning.bindingId binding, location) :: left)
      right (binding :: staged) := by
  apply MixedEnvironment.erase ?_ allocation.reads_new (related.allocated allocation [none])
  rw [allocation.location_fresh, ← heaps.length]
  exact List.getElem?_concat_length

end MixedEnvironment

/-- Independent typing of the actual final artifact follows from its own
positional lowering receipt and Core type reconstruction. -/
theorem artifact_typed (artifact : ElaboratedFunction) :
    Resolved.HasType artifact.inputs artifact.resolved artifact.returnType :=
  (Resolved.Expr.lower?_sound artifact.resolvedLowered).reflects_type
    (Core.infer_sound artifact.coreTypeChecked)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal

/-- Source typing is an independent premise; actual projection only selects
the matching scalar carrier for the pure ABI. -/
theorem scalar_typed_of_source {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {value : Dynamic.Value} {native : Core.Value} {sourceType : TypeSystem.Ty}
    {type : Core.Ty} {site : ErrorSite}
    (represented : ScalarRep value native) (typed : Dynamic.ValueHasType context heap value sourceType)
    (projected : lowerType site sourceType = .ok type) : ScalarTyped native type := by
  cases represented <;> cases typed <;> cases projected <;> constructor

/-- The source Integer allocation preserves every runtime-variable observation;
its new identity is absent from the actual native input scope. -/
theorem RuntimeEnvironmentRep.bind {native : Resolved.Environment} {scope : Resolved.Context}
    {source : Dynamic.Environment} {before after : Dynamic.Heap}
    (related : RuntimeEnvironmentRep native source before)
    (sameIds : native.ids = scope.ids) (binder : TypedBinder)
    (fresh : scope.ids.contains binder.id = false)
    {value : Int} {location : Dynamic.Location}
    (allocated : Dynamic.Heap.Allocates before .integer (some (.integer value)) location after) :
    RuntimeEnvironmentRep native ((binder.id, location) :: source) after := by
  intro id value found
  obtain ⟨index, indexed, _⟩ := found.indexed
  have member : id ∈ scope.ids := by
    rw [← sameIds]
    exact List.mem_of_getElem? indexed.getElem?
  have different : binder.id ≠ id := by
    intro same
    subst id
    have absent : binder.id ∉ scope.ids := by simpa using fresh
    exact absent member
  obtain ⟨oldLocation, cell, sourceValue, lookup, read, ordinary, initialized, scalar⟩ := related _ _ found
  exact ⟨oldLocation, cell, sourceValue, .tail different lookup, allocated.preserves_read read,
    ordinary, initialized, scalar⟩

theorem inputs_ids {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope) : scope.ids = inputs.map (·.id) := by
  induction checked with
  | nil => rfl
  | cons fresh mono projected tail ih => simpa only [Resolved.LocalScope.ids, List.map_cons] using congrArg (List.cons _) ih

theorem inputs_unique_aux {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope) :
    (inputs.map (·.id)).Nodup ∧ ∀ id, id ∈ inputs.map (·.id) → id ∉ seen := by
  induction checked with
  | nil => exact ⟨by simp, by simp⟩
  | @cons seen binder rest type scope fresh mono projected tail ih =>
    have absent : binder.id ∉ seen := by simpa using fresh
    refine ⟨?_, ?_⟩
    · simp only [List.map_cons, List.nodup_cons]
      exact ⟨fun member => (ih.2 _ member) (by simp), ih.1⟩
    · intro id member
      rcases List.mem_cons.mp member with same | member
      · simpa only [same] using absent
      · exact fun inSeen => (ih.2 _ member) (List.mem_cons_of_mem _ inSeen)

/-- Scalar values are typed using the original source parameter types and the
actual ordered lowerInputs receipt, not from native payloads alone. -/
theorem inputs_typed {seen : List Resolved.LocalId} {inputs : List TypedBinder} {scope : Resolved.Context}
    (checked : Staged.Residual.InputsChecked seen inputs scope)
    {context : SourceSemantics.Context} {heap : Dynamic.Heap}
    {values : List Dynamic.Value} {native : List Core.Value}
    (typed : Dynamic.ValuesHaveTypes context heap values (inputs.map (fun binder => binder.scheme.body)))
    (represented : ScalarValuesRep values native) :
    RuntimeEnvironmentTyped scope (inputEnvironment inputs native) := by
  induction checked generalizing values native with
  | nil =>
    cases typed
    cases represented
    intro id type found
    cases found
  | cons fresh mono projected tail ih =>
    cases typed with
    | cons headTyped tailTyped =>
      cases represented with
      | cons headRep tailRep =>
        have tailEnv := ih tailTyped tailRep
        intro id type found
        cases found with
        | head => exact ⟨_, .head, scalar_typed_of_source headRep headTyped projected⟩
        | tail different found =>
          obtain ⟨value, foundValue, valueTyped⟩ := tailEnv _ _ found
          exact ⟨value, .tail different foundValue, valueTyped⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagingHeapRelation

theorem scalar_identity {mapping : LocationMap} {value : Dynamic.Value} {native : Core.Value}
    (represented : ScalarRep value native) : ValueRel mapping value value := by
  cases represented with
  | word value => exact .word value
  | bool value => exact .bool value

/-- Runtime input cells are kept by the two actual Source allocators. This
statement supplies no Core store allocation. -/
theorem inputs_heaps {mapping : LocationMap}
    {before residual after afterResidual : Dynamic.Heap}
    {initial initialResidual final finalResidual : Dynamic.Environment}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    (heaps : HeapRel mapping before residual)
    (environments : MixedEnvironment mapping before initial initialResidual [])
    (allocated : Dynamic.BindersAllocate initial before inputs values final after)
    (residualAllocated : Dynamic.BindersAllocate initialResidual residual inputs values finalResidual afterResidual)
    (represented : ScalarValuesRep values native) :
    ∃ finalMap, HeapRel finalMap after afterResidual ∧
      MixedEnvironment finalMap after final finalResidual [] := by
  induction allocated generalizing mapping residual initialResidual finalResidual afterResidual native with
  | nil =>
    cases residualAllocated
    exact ⟨mapping, heaps, environments⟩
  | @cons initial final before middle after binder rest value values location allocation tail ih =>
    cases residualAllocated with
    | @cons _ _ _ residualMiddle _ _ _ _ _ residualLocation residualAllocation residualTail =>
      cases represented with
      | cons headRep tailRep =>
        have nextHeaps := heaps.keep_allocated (scalar_identity headRep) allocation residualAllocation
        have oldEnvironments := environments.allocated allocation [some residualLocation]
        have mapped : Maps (mapping ++ [some residualLocation]) location residualLocation := by
          unfold Maps
          rw [allocation.location_fresh, ← heaps.length]
          exact List.getElem?_concat_length
        exact ih nextHeaps (.keep mapped oldEnvironments) residualTail tailRep

theorem input_environment_ids {initial final : Dynamic.Environment} {before after : Dynamic.Heap}
    {inputs : List TypedBinder} {values : List Dynamic.Value} {native : List Core.Value}
    {scope : Resolved.Context}
    (allocated : Dynamic.BindersAllocate initial before inputs values final after)
    (represented : ScalarValuesRep values native)
    (checked : Staged.Residual.InputsChecked [] inputs scope) :
    (inputEnvironment inputs native).ids = scope.ids := by
  rw [inputs_ids checked]
  apply List.map_fst_zip
  simpa only [List.length_map] using Nat.le_of_eq ((allocation_length allocated).trans represented.length_eq)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

/-! Independent source typing supplies lexical extensions on the actual
residual statement receipt, including both conditional branches. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Core Frontend SourceInference
open SourceCoreElaboration SourceCoreElaboration.Internal

inductive BindingsFormed (solved : List SolvedRequirement) (source : TypedSource)
    (scope : Resolved.Context) : SourceSemantics.Context →
    {actual : Staged.Environment} → {fuel : Nat} → {roots : List StatementId} →
    {result : LoweredExpression} →
    Staged.Residual.StatementsChecked solved source scope actual fuel roots result → Prop where
  | letValue {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {rest : List StatementId} {node : StatementNode}
      {binder : TypedBinder} {initializer : ExpressionId}
      {initial : StagedIntegerEvaluation} {result : LoweredExpression}
      {context next : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .letDecl binder (some initializer)) (unit : node.type = .unit)
      (scopeFresh : scope.ids.contains binder.id = false)
      (environmentFresh : Staged.IntegerLet.contains actual binder.id = false)
      (owned : binder.id.owner = source.owner) (monomorphic : binder.scheme.quantified = [])
      (binderType : binder.scheme.body = .integer)
      (initialChecked : Staged.IntegerChecked solved source actual true fuel initializer initial)
      (bodyChecked : Staged.Residual.StatementsChecked solved source scope
        (Staged.Statements.bind binder initial.value :: actual) fuel rest result)
      (extension : BinderExtends source.owner context binder next)
      (bodyFormed : BindingsFormed solved source scope next bodyChecked) :
      BindingsFormed solved source scope context
        (.letValue found form unit scopeFresh environmentFresh owned monomorphic binderType initialChecked bodyChecked)
  | returnValue {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {value : ExpressionId}
      {result : LoweredExpression} {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .returnStmt (some value))
      (valueChecked : Staged.Residual.ExpressionChecked solved source scope actual fuel value result) :
      BindingsFormed solved source scope context (.returnValue found form valueChecked)
  | conditional {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {condition : ExpressionId}
      {yes no : List StatementId} {guard left right : LoweredExpression}
      {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node)
      (form : node.form = .ifThen condition yes (some no))
      (conditionChecked : Staged.Residual.ExpressionChecked solved source scope actual fuel condition guard)
      (thenChecked : Staged.Residual.StatementsChecked solved source scope actual fuel yes left)
      (elseChecked : Staged.Residual.StatementsChecked solved source scope actual fuel no right)
      (thenFormed : BindingsFormed solved source scope context thenChecked)
      (elseFormed : BindingsFormed solved source scope context elseChecked) :
      BindingsFormed solved source scope context (.conditional found form conditionChecked thenChecked elseChecked)
  | block {actual : Staged.Environment} {fuel : Nat}
      {statement : StatementId} {node : StatementNode} {body : List StatementId}
      {result : LoweredExpression} {context : SourceSemantics.Context}
      (found : source.lookupStatement? statement = some node) (form : node.form = .block body)
      (bodyChecked : Staged.Residual.StatementsChecked solved source scope actual fuel body result)
      (bodyFormed : BindingsFormed solved source scope context bodyChecked) :
      BindingsFormed solved source scope context (.block found form bodyChecked)

theorem checked_nonempty {solved source scope actual fuel roots result}
    (checked : Staged.Residual.StatementsChecked solved source scope actual fuel roots result) :
    roots ≠ [] := by
  cases checked <;> simp

/-- Source typing and the original unique node lookup identify the same binders
in the accepted tree. The residual scope and staged environment remain fixed. -/
theorem bindingsFormed_of_typing {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {actual : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression}
    (checked : Staged.Residual.StatementsChecked solved source scope actual fuel roots result)
    (unique : NodeOccurrencesUnique source) {control : ControlContext}
    {context final : SourceSemantics.Context} {facts : BodyFacts}
    (typed : StatementsHaveType source control context roots final facts) :
    BindingsFormed solved source scope context checked := by
  induction checked generalizing context final facts with
  | letValue found form unit scopeFresh environmentFresh owned mono binderType initial body ih =>
      obtain ⟨next, headFacts, tailFacts, head, tail⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_cons typed (checked_nonempty body)
      exact .letValue found form unit scopeFresh environmentFresh owned mono binderType initial body
        (SourceStagedIntegerStatementsMeaning.StaticViews.typed_let unique found form mono head) (ih tail)
  | returnValue found form value => exact .returnValue found form value
  | conditional found form condition yes no ihYes ihNo =>
      obtain ⟨headFacts, head⟩ := SourceStagedIntegerStatementsMeaning.StaticViews.typed_singleton typed
      obtain ⟨yesFinal, noFinal, yesFacts, noFacts, yesTyped, noTyped⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_if unique found form head
      exact .conditional found form condition yes no (ihYes yesTyped) (ihNo noTyped)
  | block found form body ih =>
      obtain ⟨headFacts, head⟩ := SourceStagedIntegerStatementsMeaning.StaticViews.typed_singleton typed
      obtain ⟨inner, innerFacts, bodyTyped⟩ :=
        SourceStagedIntegerStatementsMeaning.StaticViews.typed_block unique found form head
      exact .block found form body (ih bodyTyped)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal
open SourceStagedClosedEvaluationMeaning SourceStagedIntegerStatementsMeaning
open SourceStagingHeapRelation

/-- The sole structural statement proof executes only the selected Source
branch, records every Integer cell in order, and evaluates the actual residual
expression in an independent unchanged Core store. Expression meaning is
closed by expression_meaning; there is no caller or body execution premise. -/
theorem formed_meaning {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression}
    {checked : Staged.Residual.StatementsChecked solved source scope staged fuel roots result}
    {context : SourceSemantics.Context} (formed : BindingsFormed solved source scope context checked)
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment residualEnvironment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : LocationMap} {native : Resolved.Environment} {store : Core.Store} {expected : Core.Ty}
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : UsedValid context solved result.consumedRequirements)
    (stagedRep : EnvironmentRep staged environment before)
    (runtimeRep : RuntimeEnvironmentRep native environment before)
    (typedEnv : RuntimeEnvironmentTyped scope native) (sameIds : native.ids = scope.ids)
    (heaps : HeapRel mapping before residual)
    (mixed : MixedEnvironment mapping before environment residualEnvironment staged) :
    ∃ final after added sourceValue nativeValue,
      Dynamic.StatementsExecute program context evidence source environment before roots final (.returned sourceValue) after ∧
      Resolved.Evaluates native store result.resolved nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected ∧
      SourceStagedIntegerStatementsMeaning.Extends before after added ∧
      HeapRel (mapping ++ List.replicate added.length none) after residual := by
  induction formed generalizing environment before mapping with
  | @letValue staged fuel statement rest node binder initializer initial result context next found form unit scopeFresh environmentFresh owned mono binderType initialChecked bodyChecked extension bodyFormed ih =>
    have initialValid : UsedValid context solved initial.consumedRequirements := valid.mono (by
      intro id member; exact List.mem_append_left _ member)
    have evaluated := (SourceStagedClosedEvaluationMeaning.checked_meaning (program := program)
      (evidence := evidence) ledger stagedRep fuel).1 initialChecked initialValid
    let location : Dynamic.Location := ⟨before.cells.length⟩
    let middle : Dynamic.Heap := ⟨before.cells ++ [SourceStagedIntegerStatementsMeaning.integerCell initial.value]⟩
    let nextEnvironment : Dynamic.Environment := (binder.id, location) :: environment
    have allocation : Dynamic.Heap.Allocates before .integer (some (.integer initial.value)) location middle := .append
    have binding : Dynamic.Binds environment before (bindingId (Staged.Statements.bind binder initial.value)) .integer
        (some (.integer (bindingValue (Staged.Statements.bind binder initial.value)))) nextEnvironment middle := by
      simpa only [bindingId, bindingValue, Staged.Statements.bind] using Dynamic.Binds.intro allocation
    have nextStaged := EnvironmentRep.bind (Staged.Statements.bind binder initial.value) stagedRep binding
    have nextRuntime := runtimeRep.bind sameIds binder scopeFresh allocation
    have nextMixed := mixed.erase_allocated heaps (Staged.Statements.bind binder initial.value) allocation
    have nextHeaps := heaps.erase_allocated allocation
    have nextLedger := extension.context_fields.2.2.2.2.trans ledger
    have nextValid := usedValid_extend extension (valid.mono (by intro id member; exact List.mem_append_right _ member))
    obtain ⟨final, after, added, sourceValue, nativeValue, bodyEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      ih typed nextLedger nextValid nextStaged nextRuntime nextHeaps nextMixed
    have actualAllocation : Dynamic.Heap.Allocates before binder.scheme.body (some (.integer initial.value)) location middle := by
      rw [binderType]; exact allocation
    have headEval : Dynamic.StatementExecutes program context evidence source environment before statement next
        (.fallthrough nextEnvironment) middle :=
      .letInitialized (lookupStatement?_sound found) form evaluated mono extension actualAllocation
    refine ⟨final, after, initial.value :: added, sourceValue, nativeValue, .cons headEval bodyEval,
      nativeEval, scalar, scalarTyped, ?_, ?_⟩
    · exact ((SourceStagedIntegerStatementsMeaning.Extends.refl before).allocate allocation).trans cells
    · simpa only [List.length_cons, List.replicate_succ, List.append_assoc, List.singleton_append] using heapResult
  | returnValue found form valueChecked =>
    obtain ⟨sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped⟩ :=
      expression_meaning valueChecked typed ledger valid stagedRep runtimeRep typedEnv
    refine ⟨_, before, [], sourceValue, nativeValue,
      .terminal (.returnValue (lookupStatement?_sound found) form sourceEval) (.returned _),
      nativeEval, scalar, scalarTyped, .refl before, ?_⟩
    simpa using heaps
  | @conditional staged fuel statement node condition yes no guard left right context found form conditionChecked thenChecked elseChecked thenFormed elseFormed ihYes ihNo =>
    cases typed with
    | ifE guardTyped yesTyped noTyped =>
      have guardValid := valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_left _ member))
      have yesValid := valid.mono (by intro id member; exact List.mem_append_left _ (List.mem_append_right _ member))
      have noValid := valid.mono (by intro id member; exact List.mem_append_right _ member)
      obtain ⟨guardSource, guardNative, sourceGuard, nativeGuard, scalarGuard, typedGuard⟩ :=
        expression_meaning conditionChecked guardTyped ledger guardValid stagedRep runtimeRep typedEnv
      cases typedGuard with
      | bool truth =>
        cases scalarGuard
        cases truth with
        | false =>
          obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
            ihNo noTyped ledger noValid stagedRep runtimeRep heaps mixed
          have headEval := Dynamic.StatementExecutes.ifFalseWithElse (lookupStatement?_sound found) form sourceGuard sourceEval
          refine ⟨context, after, added, sourceValue, nativeValue, ?_, .ifFalse nativeGuard nativeEval,
            scalar, scalarTyped, cells, heapResult⟩
          simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
        | true =>
          obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
            ihYes yesTyped ledger yesValid stagedRep runtimeRep heaps mixed
          have headEval := Dynamic.StatementExecutes.ifTrue (lookupStatement?_sound found) form sourceGuard sourceEval
          refine ⟨context, after, added, sourceValue, nativeValue, ?_, .ifTrue nativeGuard nativeEval,
            scalar, scalarTyped, cells, heapResult⟩
          simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)
  | @block staged fuel statement node body result context found form bodyChecked bodyFormed ih =>
    obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      ih typed ledger valid stagedRep runtimeRep heaps mixed
    have headEval := Dynamic.StatementExecutes.block (lookupStatement?_sound found) form sourceEval
    refine ⟨context, after, added, sourceValue, nativeValue, ?_, nativeEval, scalar, scalarTyped, cells, heapResult⟩
    simpa only [Dynamic.restoreControl] using Dynamic.StatementsExecute.terminal headEval (.returned _)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- Exact original statement identities in their source order. -/
def statementRoots (source : TypedSource) : List StatementId :=
  source.roots.filterMap fun root => match root with
    | .statement statement => some statement | .expression _ => none

private theorem roots_eq {source : TypedSource} {roots : List StatementId}
    (same : roots.map NodeId.statement = source.roots) : statementRoots source = roots := by
  unfold statementRoots
  rw [← same]
  clear same
  induction roots with
  | nil => rfl
  | cons head tail ih => simpa using congrArg (List.cons head) ih

/-- Actual default acceptance and independent typing close the statement proof.
Only its static finite syntax test is an additional compiler-side condition. -/
theorem statements_of_accepted {solved : List SolvedRequirement} {source : TypedSource}
    {scope : Resolved.Context} {staged : Staged.Environment} {fuel : Nat}
    {roots : List StatementId} {result : LoweredExpression} {expected : Core.Ty}
    {site : ErrorSite} {reason : ErrorReason} {control : ControlContext} {facts : BodyFacts}
    {context finalTyped : SourceSemantics.Context}
    {program : Program} {evidence : Dynamic.EvidenceEnvironment}
    {environment residualEnvironment : Dynamic.Environment} {before residual : Dynamic.Heap}
    {mapping : LocationMap} {native : Resolved.Environment} {store : Core.Store}
    (supported : Staged.Residual.statementsSupported source fuel roots = true)
    (accepted : Staged.IntegerLet.lower solved source scope staged fuel expected site reason roots = .ok result)
    (unique : NodeOccurrencesUnique source)
    (sourceTyped : StatementsHaveType source control context roots finalTyped facts)
    (typed : Resolved.HasType scope result.resolved expected)
    (ledger : context.solvedRequirements = solved)
    (valid : UsedValid context solved result.consumedRequirements)
    (stagedRep : EnvironmentRep staged environment before)
    (runtimeRep : RuntimeEnvironmentRep native environment before)
    (typedEnv : RuntimeEnvironmentTyped scope native) (sameIds : native.ids = scope.ids)
    (heaps : HeapRel mapping before residual)
    (mixed : MixedEnvironment mapping before environment residualEnvironment staged) :
    ∃ final after added sourceValue nativeValue,
      Dynamic.StatementsExecute program context evidence source environment before roots final (.returned sourceValue) after ∧
      Resolved.Evaluates native store result.resolved nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue expected ∧
      SourceStagedIntegerStatementsMeaning.Extends before after added ∧
      HeapRel (mapping ++ List.replicate added.length none) after residual :=
  formed_meaning (bindingsFormed_of_typing (Staged.Residual.statements_checked supported accepted) unique sourceTyped)
    typed ledger valid stagedRep runtimeRep typedEnv sameIds heaps mixed

/-- The actual compatibility elaborator and its finalized artifact have the
same scalar result. Source input allocations remain in a logical residual
Source heap, selected Integer lets are omitted there, and the actual pure Core
code preserves its separate input store. This is not a statement about the
public unified compiler's callable entry or its physical Source-cell ABI. -/
theorem elaborateFunction_at_allocations {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial environment residualEnvironment : Dynamic.Environment}
    {before residualBefore bound residualBound : Dynamic.Heap} {mapping : LocationMap} {store : Core.Store}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (allocated : Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound)
    (residualAllocated : Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs
      arguments residualEnvironment residualBound)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial) :
    ∃ inputMap final after added sourceValue nativeValue,
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved nativeValue store ∧
      Core.Evaluates nativeArguments store artifact.core nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  obtain ⟨draft, lowered, finalized⟩ := Staged.Residual.elaborated_body accepted
  obtain ⟨_, artifactInputs, artifactResolved, artifactReturn, _⟩ := Staged.Residual.finalized_fields finalized
  cases Staged.IntegerLet.function_of_accepted lowered with
  | intro owned rootsAccepted rootsSame nonempty inputsAccepted expectedAccepted bodyAccepted reconciled declaration inputEq resolved returnType rootOccurrence =>
    rename_i roots head tail inputs expected body
    have rootsSame' := roots_eq rootsSame
    have inputsChecked := Staged.Residual.inputs_checked inputsAccepted
    have sameIds := input_environment_ids allocated scalarArguments inputsChecked
    have typedEnv := inputs_typed inputsChecked argumentsTyped scalarArguments
    have runtimeRep : RuntimeEnvironmentRep (inputEnvironment function.typedBody.inputs nativeArguments) environment bound :=
      fun _ _ found => allocated_native_lookup allocated (inputs_unique_aux inputsChecked).1 scalarArguments found
    have stagedRep : EnvironmentRep [] environment bound := by intro id binding found; cases found
    obtain ⟨inputMap, inputHeaps, inputEnvironments⟩ := inputs_heaps initialHeaps
      (MixedEnvironment.of_retained initialEnvironments) allocated residualAllocated scalarArguments
    have typed := artifact_typed artifact
    rw [artifactInputs, inputEq, artifactResolved, resolved, artifactReturn, returnType] at typed
    obtain ⟨finalTyped, bodyTyped, _, _⟩ := sourceTyped
    change StatementsHaveType function.typedBody _ context (statementRoots function.typedBody) _ _ at bodyTyped
    rw [rootsSame'] at bodyTyped supported
    have used : UsedValid context function.solvedRequirements body.consumedRequirements := by
      intro row proof member consumed actual
      exact valid row proof member (List.mem_map.mpr ⟨row, member, rfl⟩) actual
    obtain ⟨final, after, added, sourceValue, nativeValue, sourceEval, nativeEval, scalar, scalarTyped, cells, heapResult⟩ :=
      statements_of_accepted supported bodyAccepted unique bodyTyped typed ledger used stagedRep runtimeRep typedEnv sameIds inputHeaps inputEnvironments
    have actualNative : Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments)
        store artifact.resolved nativeValue store := by
      rw [artifactResolved, resolved]
      exact nativeEval
    have actualLowered := Resolved.Expr.lower?_sound artifact.resolvedLowered
    have loweringIds : (inputEnvironment function.typedBody.inputs nativeArguments).ids = artifact.inputs.ids := by
      rw [artifactInputs, inputEq]
      exact sameIds
    rw [← loweringIds] at actualLowered
    have core := actualNative.toCore actualLowered
    have arity := (allocation_length allocated).trans scalarArguments.length_eq
    have valueIds : (inputEnvironment function.typedBody.inputs nativeArguments).values = nativeArguments := by
      apply List.map_snd_zip
      simpa only [List.length_map] using Nat.le_of_eq arity.symm
    rw [valueIds] at core
    refine ⟨inputMap, final, after, added, sourceValue, nativeValue, inputHeaps, inputEnvironments,
      ?_, actualNative, core, scalar, ?_, cells, heapResult⟩
    · rwa [rootsSame']
    · rwa [artifactReturn, returnType]

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- Construct the original ordered parameter allocation from its exact arity.
All initial cells and lexical entries remain in the actual allocation trace. -/
theorem allocate_inputs (inputs : List TypedBinder) (values : List Dynamic.Value)
    (arity : inputs.length = values.length) (initial : Dynamic.Environment) (before : Dynamic.Heap) :
    ∃ environment after, Dynamic.BindersAllocate initial before inputs values environment after := by
  induction inputs generalizing values initial before with
  | nil =>
    cases values with
    | nil => exact ⟨initial, before, .nil _ _⟩
    | cons head tail => simp at arity
  | cons binder rest ih =>
    cases values with
    | nil => simp at arity
    | cons value values =>
      let location : Dynamic.Location := ⟨before.cells.length⟩
      let middle : Dynamic.Heap := ⟨before.cells ++ [{type := binder.scheme.body, value := some value}]⟩
      have allocation : Dynamic.Heap.Allocates before binder.scheme.body (some value) location middle := .append
      obtain ⟨environment, after, tail⟩ := ih values (Nat.succ.inj arity) ((binder.id, location) :: initial) middle
      exact ⟨environment, after, .cons allocation tail⟩

/-- Public accepted elaboration constructs both actual ordered Source input
allocations before using the closed body theorem. Runtime scalar cells are
kept; only selected Integer lets are omitted from the logical residual heap.
The resulting Core expression uses the unchanged independent pure store. -/
theorem elaborateFunction_sound {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store : Core.Store}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial) :
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue nativeValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved nativeValue store ∧
      Core.Evaluates nativeArguments store artifact.core nativeValue store ∧
      ScalarRep sourceValue nativeValue ∧ ScalarTyped nativeValue artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  have arity : function.typedBody.inputs.length = arguments.length := by
    simpa only [List.length_map] using argumentsTyped.length_eq.symm
  obtain ⟨environment, bound, allocated⟩ := allocate_inputs function.typedBody.inputs arguments arity initial before
  obtain ⟨residualEnvironment, residualBound, residualAllocated⟩ :=
    allocate_inputs function.typedBody.inputs arguments arity residualInitial residualBefore
  obtain ⟨inputMap, final, after, added, sourceValue, nativeValue, meaning⟩ :=
    elaborateFunction_at_allocations accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments
      allocated residualAllocated initialHeaps initialEnvironments
  exact ⟨environment, bound, residualEnvironment, residualBound, inputMap, final, after, added, sourceValue, nativeValue,
    allocated, residualAllocated, meaning⟩

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning

set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
open Solcore Frontend SourceInference SourceSemantics SourceCoreElaboration
open SourceCoreElaboration.Internal SourceStagedClosedEvaluationMeaning SourceStagingHeapRelation

/-- An original Core completion identifies the value and complete Core store
of the accepted scalar artifact. Both Source input allocations and the complete
logical residual heap relation remain those of the closed Source witness. -/
theorem elaborateFunction_reflects {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store finalStore : Core.Store} {value : Core.Value}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial)
    (completed : Core.Evaluates nativeArguments store artifact.core value finalStore) :
    finalStore = store ∧
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved value store ∧
      ScalarRep sourceValue value ∧ ScalarTyped value artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound := by
  obtain ⟨environment, bound, residualEnvironment, residualBound, inputMap, final, after, added,
    sourceValue, expectedValue, allocated, residualAllocated, inputHeaps, inputEnvironments,
    sourceEvaluation, residualEvaluation, coreEvaluation, represented, typed, suffix, finalHeaps⟩ :=
    elaborateFunction_sound accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments initialHeaps initialEnvironments
  obtain ⟨rfl, rfl⟩ := Core.evaluation_deterministic completed coreEvaluation
  exact ⟨rfl, environment, bound, residualEnvironment, residualBound, inputMap, final, after, added,
    sourceValue, allocated, residualAllocated, inputHeaps, inputEnvironments,
    sourceEvaluation, residualEvaluation, represented, typed, suffix, finalHeaps⟩

/-- Finite completion of the actual initial machine state supplies the original
Core derivation. The pure Core store remains separate from the Source heaps. -/
theorem elaborateFunction_runStateful_reflects {function : CheckedFunction} {artifact : ElaboratedFunction}
    {program : Program} {context : SourceSemantics.Context} {evidence : Dynamic.EvidenceEnvironment}
    {facts : BodyFacts} {arguments : List Dynamic.Value} {nativeArguments : List Core.Value}
    {initial residualInitial : Dynamic.Environment} {before residualBefore : Dynamic.Heap}
    {mapping : LocationMap} {store finalStore : Core.Store} {value : Core.Value} {fuel : Nat}
    (accepted : elaborateFunction function = .ok artifact)
    (supported : Staged.Residual.statementsSupported function.typedBody (function.typedBody.nodes.length + 1)
      (statementRoots function.typedBody) = true)
    (unique : NodeOccurrencesUnique function.typedBody)
    (sourceTyped : BodyHasType function.typedBody context function.inferredBodyType facts)
    (ledger : context.solvedRequirements = function.solvedRequirements)
    (valid : UsedValid context function.solvedRequirements (function.solvedRequirements.map (·.id)))
    (argumentsTyped : Dynamic.ValuesHaveTypes context before arguments
      (function.typedBody.inputs.map (fun binder => binder.scheme.body)))
    (scalarArguments : ScalarValuesRep arguments nativeArguments)
    (initialHeaps : HeapRel mapping before residualBefore)
    (initialEnvironments : EnvironmentRel mapping initial residualInitial)
    (completed : Core.runStateful fuel (Core.State.initial artifact.core nativeArguments store) =
      .done value finalStore) :
    finalStore = store ∧
    ∃ environment bound residualEnvironment residualBound inputMap final after added sourceValue,
      Dynamic.BindersAllocate initial before function.typedBody.inputs arguments environment bound ∧
      Dynamic.BindersAllocate residualInitial residualBefore function.typedBody.inputs arguments residualEnvironment residualBound ∧
      HeapRel inputMap bound residualBound ∧ MixedEnvironment inputMap bound environment residualEnvironment [] ∧
      Dynamic.StatementsExecute program context evidence function.typedBody environment bound
        (statementRoots function.typedBody) final (.returned sourceValue) after ∧
      Resolved.Evaluates (inputEnvironment function.typedBody.inputs nativeArguments) store artifact.resolved value store ∧
      ScalarRep sourceValue value ∧ ScalarTyped value artifact.returnType ∧
      SourceStagedIntegerStatementsMeaning.Extends bound after added ∧
      HeapRel (inputMap ++ List.replicate added.length none) after residualBound :=
  elaborateFunction_reflects accepted supported unique sourceTyped ledger valid argumentsTyped scalarArguments initialHeaps initialEnvironments
    (Core.runStateful_evaluation_sound completed)

end Solcore.SourceSemantics.CoreLowering.SourceStagedIntegerResidualMeaning
