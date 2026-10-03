import Solcore.SourceSemantics.CoreLowering.CompatibleEncodedDataTyping

/-! Consumers retain the actual compatible encoder equations and definition
prefix. Negative cases distinguish structural data from annotation validity
and exclude closures, references and newly appended constructor identities.
These are static proof consumers; the existing encoder remains unchanged. -/
set_option autoImplicit false
namespace Solcore.Tests.SourceCoreCompatibleEncodedDataTyping
open Core Frontend SourceSemantics.CoreLowering
open CompatibleEncodedDataTyping

theorem actual_raw_typing {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {carrier : SourceCoreDataValues.Value} {encoded : SourceCoreCompatibleValues.Extended registry Value}
    {world : StoreTyping} {type : Ty} {future : DataEnvironment}
    (accepted : SourceCoreCompatibleValues.encodeRaw fuel checked registry expected carrier = .ok encoded)
    (projected : checked.catalog.project expected = .ok type)
    (extension : checked.catalog.definitions.Extends future)
    (typed : RuntimeValueHasType world encoded.value type future) :
    RuntimeValueHasType world encoded.value type checked.catalog.definitions :=
  encodeRaw_restrict_typing accepted projected extension typed

theorem actual_payloads {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {types : List TypeSystem.Ty}
    {carriers : List SourceCoreDataValues.Value} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodePayloadsRaw fuel checked registry types carriers index = .ok encoded) :
    DataOnly encoded.value := encodePayloadsRaw_dataOnly accepted

theorem actual_ordered_entries {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {key value : TypeSystem.Ty} {layout : OrderedMapping.Layout}
    {carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value)} {index : Nat}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodeEntriesRaw fuel checked registry key value layout carriers index = .ok encoded) :
    DataOnly encoded.value := encodeEntriesRaw_dataOnly accepted

theorem actual_default {fuel : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {sourceType : TypeSystem.Ty} {type : Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Value}
    (accepted : SourceCoreCompatibleValues.encodeDefaultRaw fuel checked registry sourceType type = .ok encoded) :
    DataOnly encoded.value := encodeDefaultRaw_dataOnly accepted

theorem closure_not_data {parameter result : Ty} {body : Expr} {captured : Environment} :
    ¬ DataOnly (.closure parameter result body captured) := by
  intro data
  cases data

theorem reference_not_data {type : Ty} {location : Location} :
    ¬ DataOnly (.cellRef type location) := by
  intro data
  cases data

/-- Runtime sum typing omits the unused annotation check. The prefix theorem
requires the independently projected well formed annotation for this reason. -/
theorem data_runtime_does_not_certify_annotation :
    DataOnly (.inLeft (.namedData ⟨0⟩) .unit) ∧
    RuntimeValueHasType [] (.inLeft (.namedData ⟨0⟩) .unit) (.sum .unit (.namedData ⟨0⟩)) [] ∧
    ¬ Ty.WellFormed [] (.sum .unit (.namedData ⟨0⟩)) := by
  refine ⟨.inLeft .unit, .inLeft .unit, ?_⟩
  intro annotation
  cases annotation with
  | sum _ right => cases right with
    | namedData found => cases found

private def base : DataEnvironment := [⟨[.unit]⟩]
private def suffix : DataEnvironment := [⟨[.word]⟩]
private def firstConstructor : ConstructorId := ⟨⟨0⟩, 0⟩

/-- The appended definition differs from the selected original definition.
The helper recovers the same owner and payload from the real prefix lookup. -/
theorem original_named_payload :
    RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) base := by
  apply DataOnly.restrict_definitions (future := base ++ suffix) (.constructed .unit)
    (DataEnvironment.isWellFormed_sound (by decide)) (.append base suffix)
    (.namedData (by rfl))
  exact .constructed (by rfl) .unit

/-- Structural data at a fresh appended owner cannot be cast into an empty
base. The independent projection/prefix annotation is essential. -/
theorem fresh_named_owner_does_not_restrict :
    DataOnly (.constructed firstConstructor .unit) ∧
    RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) base ∧
    ¬ RuntimeValueHasType [] (.constructed firstConstructor .unit) (.namedData ⟨0⟩) [] := by
  refine ⟨.constructed .unit, .constructed (by rfl) .unit, ?_⟩
  intro typed
  cases typed with
  | constructed selected _ => cases selected

end Solcore.Tests.SourceCoreCompatibleEncodedDataTyping
