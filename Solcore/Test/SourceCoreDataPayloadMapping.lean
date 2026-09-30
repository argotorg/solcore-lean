import Solcore.SourceSemantics.CoreLowering.DataPayloadMapping

/-! Non-reflexive mapping keys append even when structurally identical. The
actual helper retains the complete contents of both old and appended keys. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 2000000
namespace Tests.SourceCoreDataPayloadMapping
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering DataPayload DataPatternValues
private def innerType : TypeSystem.Ty := .mapping .integer .integer
private def innerLayout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def outerLayout : Core.OrderedMapping.Layout := ⟨innerLayout.type, .integer, ⟨1⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := innerType, definition := some innerLayout.definition },
  { sourceType := .mapping innerType .integer, definition := some outerLayout.definition }] }
private def checked : SourceCoreDataCatalog.Checked := ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def functions : GenericHeap.PayloadModel catalog where
  Represents := fun _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  extend := fun impossible _ _ => False.elim impossible
private theorem observations : FunctionObservations catalog signatures functions (fun _ _ => False) :=
  fun impossible => False.elim impossible
private theorem faithful : DataEquality.IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private theorem comparisonExists : (SourceCoreDataEquality.prepare 20 checked innerType).toOption.isSome = true := by cbv
private def comparison := (SourceCoreDataEquality.prepare 20 checked innerType).toOption.get comparisonExists
private theorem comparisonGenerated : SourceCoreDataEquality.prepare 20 checked innerType = .ok comparison := by
  generalize result : SourceCoreDataEquality.prepare 20 checked innerType = outcome
  have positive := comparisonExists
  rw [result] at positive
  cases outcome with
  | error => simp [Except.toOption] at positive
  | ok prepared => simp [comparison, result]; rfl
private theorem comparisonType : outerLayout.keyType = comparison.type := by
  have projected := comparison.projection
  rw [DataPlaceMappingPreparation.comparison_sourceType comparisonGenerated] at projected
  exact Except.ok.inj projected
private def sourceKey : Dynamic.Value := .mapping .integer .integer [(.integer 2, .integer 3)]
private def key : Value := Core.OrderedMapping.encode innerLayout [(.integer 2, .integer 3)]
private def original : Core.OrderedMapping.Entries := [(key, .integer 11)]
private def sources : List (Dynamic.Value × Dynamic.Value) := [(sourceKey, .integer 11)]
private def updated : List (Dynamic.Value × Dynamic.Value) := [(sourceKey, .integer 11), (sourceKey, .integer 22)]
private theorem keyRep : ValueRep catalog signatures functions [] [] innerType sourceKey key innerLayout.type :=
  .mapping rfl rfl rfl ⟨.integer, .integer, rfl⟩ (.prepend (.integer 2) (.integer 3) (.empty _ _ _ _))
private theorem entriesRep : EntriesRep catalog signatures functions [] [] innerType .integer outerLayout.keyType .integer sources original :=
  .prepend keyRep (.integer 11) (.empty _ _ _ _)
private theorem inserted : Dynamic.MappingInsert sourceKey (.integer 22) sources updated := by
  apply Dynamic.MappingInsert.append
  apply Dynamic.MappingAbsent.cons
  · intro equivalent
    have impossible := equivalent.2
    cases impossible
  · exact .nil
private def expression : Expr := Core.OrderedMapping.insert outerLayout comparison.expression (.var 0) (.var 1) (.var 2)
private def environment : Environment := [Core.OrderedMapping.encode outerLayout original, key, .integer 22]
private def initialStore : Store := [.integer 900]

/-- Full payload preservation comes from the actual compiled comparator and
insert code; it is not inferred from weak equality observations of keys. -/
example : ∃ output required,
    ValueRep catalog signatures functions [] [] (.mapping innerType .integer)
      (.mapping innerType .integer updated) output outerLayout.type ∧
    ∀ fuel, required ≤ fuel → runStateful fuel (.initial expression environment initialStore) =
      .done (.inRight .word output)
        (DataMappingComparison.insertStore comparison outerLayout environment initialStore original key (.integer 22)) := by
  obtain ⟨output, represented, evaluated⟩ := DataPayload.insert_preserves observations faithful comparison outerLayout comparisonType
    rfl rfl rfl ⟨.namedData (by rfl), .integer, rfl⟩ keyRep (.integer 22) entriesRep inserted
    environment initialStore (.var 0) (.var 1) (.var 2) (.var rfl) (.var rfl) (.var rfl)
  obtain ⟨required, complete⟩ := evaluation_runStateful_complete_with_sufficient_fuel evaluated
  exact ⟨output, required, represented, complete⟩

/-- The finite run appends a second identical mapping key; it preserves the
old value and both keys' nested data, and the administrative prefix. -/
example : ∃ store, runStateful 1000 (.initial expression environment initialStore) =
    .done (.inRight .word (Core.OrderedMapping.encode outerLayout [(key, .integer 11), (key, .integer 22)])) store ∧
    store.read? 0 = some (.integer 900) := by
  refine ⟨DataMappingComparison.insertStore comparison outerLayout environment initialStore original key (.integer 22), ?_, ?_⟩
  · cbv
  · rfl

end Tests.SourceCoreDataPayloadMapping
