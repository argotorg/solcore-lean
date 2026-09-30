import Solcore.SourceSemantics.CoreLowering.DataPlaceMappingHelpers
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap

/-! Actual preparation receipts, independent mapping read/update semantics,
finite helper execution, and preservation of an existing source heap frame.
Runtime regressions exercise the same emitted code and its checker. -/
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1500000
namespace Tests.SourceCoreDataPlaceMappingProofs
open Solcore Solcore.Core Solcore.Frontend Solcore.Frontend.SourceInference
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open SourceCoreDataPlaces DataPlaceMappingIndex DataPlaceMappingHelpers DataEquality DataEqualityValues

private def moduleId : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"mapping_place_proofs", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨moduleId, 0⟩
private def keyId : ExpressionId := ⟨⟨owner, 0⟩⟩
private def signatures : ProgramSignatures := ⟨[], [], [], [], [], []⟩
private def layout : Core.OrderedMapping.Layout := ⟨.integer, .integer, ⟨0⟩⟩
private def catalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .integer .integer, definition := some layout.definition }]
}
private def checked : SourceCoreDataCatalog.Checked :=
  ⟨catalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def route : Route := ⟨.mapping .integer .integer, layout.type, .integer,
  [.index layout keyId .integer], some layout⟩
private def missing : TypeSystem.Ty → Word := fun _ => Word.zero
private theorem noIdentities : IdentityFaithful (fun _ _ => False) := by
  constructor <;> intros <;> contradiction
private abbrev ValueRep := DataPatternTypedValues.TypedValueRep catalog signatures .integer
private def sources : List (Dynamic.Value × Dynamic.Value) :=
  [(.integer 7, .integer 11), (.integer 7, .integer 22), (.integer 9, .integer 33)]
private def entries : Core.OrderedMapping.Entries :=
  [(.integer 7, .integer 11), (.integer 7, .integer 22), (.integer 9, .integer 33)]
private def root : Value := Core.OrderedMapping.encode layout entries
private def getterArgument : Value := .pair (.inRight .unit root) (.integer 7)
private def getterArgumentType : Core.Ty := .product (.sum .unit layout.type) .integer
private def sentinelHeap : Dynamic.Heap := ⟨[⟨.integer, some (.integer 900), none⟩]⟩
private def sentinelStore : Store := [.inRight .unit (.integer 900)]
private def sentinelWorld : StoreTyping := [.sum .unit .integer]
private def model := GenericHeap.finitePayload catalog signatures
private theorem sentinelRelated : GenericHeap.HeapRepresents model [0] sentinelWorld sentinelHeap sentinelStore := by
  have empty : GenericHeap.HeapRepresents model [] [] ⟨[]⟩ [] := .empty
  have represented : model.Represents [] [] .integer (.integer 900) (.integer 900) .integer :=
    ⟨rfl, .integer 900⟩
  exact (empty.allocate (.initialized represented) .append).1
private theorem layoutRegistered : layout.Registered catalog.definitions := ⟨.integer, .integer, rfl⟩
private theorem argumentTyped : RuntimeValueHasType sentinelWorld getterArgument getterArgumentType catalog.definitions := by
  apply RuntimeValueHasType.pair (RuntimeValueHasType.inRight ?_) RuntimeValueHasType.integer
  apply Core.OrderedMapping.encode_hasType layoutRegistered entries
  intro key value member
  simp only [entries, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same | same <;> cases same <;> exact ⟨.integer, .integer⟩

/-- Preparation supplies all comparison/default programs. The checker premise
is the real final helper check, rather than an assumed semantic evaluation.
All existing source cells and their aliases survive the new helper cells. -/
example (prepared : Prepared)
    (accepted : prepare checked 20 route Word.zero missing = .ok prepared)
    (checkedGetter : infer? [getterArgumentType] (.apply (getter prepared .integer) (.var 0)) catalog.definitions =
      some (.sum .word (.sum .unit .integer))) :
    ∃ finalStore futureWorld administrative,
      Dynamic.ProjectionsRead (some (.mapping .integer .integer sources)) [.index (.integer 7)] (some (.integer 11)) ∧
      WorldExtends sentinelWorld futureWorld ∧
      GenericHeap.HeapRepresents model [0] futureWorld sentinelHeap finalStore ∧
      GeneralHeap.AdministrativePreserved [0] sentinelStore [0] finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 ∧
      (∃ required, ∀ fuel, required ≤ fuel → runStateful fuel
        (.initial (.apply (getter prepared .integer) (.var 0)) [getterArgument] sentinelStore) =
          .done (.inRight .word (.inRight .unit (.integer 11))) finalStore) ∧
      (∀ fuel value actualStore, runStateful fuel
        (.initial (.apply (getter prepared .integer) (.var 0)) [getterArgument] sentinelStore) =
          .done value actualStore → value = .inRight .word (.inRight .unit (.integer 11)) ∧ actualStore = finalStore) := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep (n : Int) : KeyRep certificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer n
  have related : OrderedMapping.EntriesRel (KeyRep certificate signatures (fun _ _ => False)) ValueRep sources entries :=
    .cons (keyRep 7) (.integer 11) (.cons (keyRep 7) (.integer 22) (.cons (keyRep 9) (.integer 33) .nil))
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, some (.mapping .integer .integer sources), none⟩
      (.inRight .unit root) sources entries := by simpa only [root, indexLayout] using RootInput.initialized related
  obtain ⟨value, finalStore, administrative, _, projections, represented, evaluated, extension, count⟩ :=
    getter_preserves certificate prepared steps rootMapping noIdentities input (keyRep 7)
      (.found (.head ⟨rfl, .integer 7⟩)) [getterArgument] sentinelStore .integer [.integer 7] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  have valueSame : value = .integer 11 := by
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; rfl
    · cases tree
  subst value
  obtain ⟨futureWorld, worlds, heap, _, administrativeFrame⟩ := DataMappingHeap.evaluation_preserves_frame
    sentinelRelated (.cons argumentTyped .nil) (infer_sound checkedGetter) evaluated extension
  refine ⟨finalStore, futureWorld, administrative, projections, worlds, heap, administrativeFrame,
    extension, count, evaluation_runStateful_complete_with_sufficient_fuel evaluated, ?_⟩
  intro fuel value actualStore ran
  exact evaluation_deterministic (runStateful_evaluation_sound ran) evaluated

private def updatedSources : List (Dynamic.Value × Dynamic.Value) :=
  [(.integer 7, .integer 55), (.integer 7, .integer 22), (.integer 9, .integer 33)]

/-- Duplicate keys keep their order; only the first equivalent occurrence is
replaced. The supplied root is the latest root passed into the setter. -/
example (prepared : Prepared) (accepted : prepare checked 20 route Word.zero missing = .ok prepared) :
    ∃ output finalStore administrative,
      Dynamic.ProjectionsUpdate (fun _ value => value = .integer 55)
        (some (.mapping .integer .integer sources)) [.index (.integer 7)] (.mapping .integer .integer updatedSources) ∧
      Evaluates [.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))] sentinelStore
        (.apply (setter prepared .integer) (.var 0)) (.inRight .word output) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 4 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep (n : Int) : KeyRep certificate signatures (fun _ _ => False) (.integer n) (.integer n) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer n
  have related : OrderedMapping.EntriesRel (KeyRep certificate signatures (fun _ _ => False)) ValueRep sources entries :=
    .cons (keyRep 7) (.integer 11) (.cons (keyRep 7) (.integer 22) (.cons (keyRep 9) (.integer 33) .nil))
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, some (.mapping .integer .integer sources), none⟩
      (.inRight .unit root) sources entries := by simpa only [root, indexLayout] using RootInput.initialized related
  obtain ⟨output, finalStore, administrative, _, updated, _, evaluated, extension, count⟩ :=
    setter_preserves certificate prepared steps rootMapping noIdentities input (keyRep 7) (DataPatternTypedValues.TypedValueRep.integer 55)
      (.found (.head ⟨rfl, .integer 7⟩)) (.update (.head ⟨rfl, .integer 7⟩))
      [.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))] sentinelStore .integer [.integer 7] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  exact ⟨output, finalStore, administrative, updated, evaluated, extension, count⟩

/-- An uninitialized root is read as the empty mapping without writing that
virtual value into the source cell. The scalar default is derived automatically. -/
example (prepared : Prepared) (accepted : prepare checked 20 route Word.zero missing = .ok prepared) :
    ∃ finalStore administrative,
      Dynamic.RootInitialValue ⟨.mapping .integer .integer, none, none⟩ (some (.mapping .integer .integer [])) ∧
      Dynamic.ProjectionsRead (some (.mapping .integer .integer [])) [.index (.integer 8)] (some (.integer 0)) ∧
      Evaluates [.pair (.inLeft layout.type .unit) (.integer 8)] sentinelStore
        (.apply (getter prepared .integer) (.var 0)) (.inRight .word (.inRight .unit (.integer 0))) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, _⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep : KeyRep certificate signatures (fun _ _ => False) (.integer 8) (.integer 8) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer 8
  have input : RootInput index.layout .integer .integer (KeyRep certificate signatures (fun _ _ => False)) ValueRep
      ⟨.mapping .integer .integer, none, none⟩ (.inLeft layout.type .unit) [] [] := by
    simpa only [indexLayout] using (RootInput.absent (layout := index.layout))
  obtain ⟨value, finalStore, administrative, initial, projections, represented, evaluated, extension, count⟩ :=
    getter_preserves certificate prepared steps rootMapping noIdentities input keyRep (.default .nil .integer)
      [.pair (.inLeft layout.type .unit) (.integer 8)] sentinelStore .integer [.integer 8] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  have valueSame : value = .integer 0 := by
    rcases represented with represented | ⟨_, tree⟩
    · cases represented; rfl
    · cases tree; rfl
  subst value
  exact ⟨finalStore, administrative, initial, projections, evaluated, extension, count⟩

private def functionLayout : Core.OrderedMapping.Layout := ⟨.integer, TaggedFunction.functionType .unit .unit, ⟨0⟩⟩
private def functionCatalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .integer (.function .unit .unit), definition := some functionLayout.definition }]
}
private def functionChecked : SourceCoreDataCatalog.Checked :=
  ⟨functionCatalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def functionRoute : Route := ⟨.mapping .integer (.function .unit .unit), functionLayout.type,
  functionLayout.valueType, [.index functionLayout keyId (.function .unit .unit)], some functionLayout⟩
private def anonymous : Value := .pair (.inLeft .word .unit)
  (.closure .unit (.sum .word .unit) (.inRight .word .unit) [])

/-- Missing function defaults remain source language faults. In particular the
setter does not insert the supplied closure or allocate insertion helpers. -/
example (prepared : Prepared)
    (accepted : prepare functionChecked 20 functionRoute Word.zero missing = .ok prepared) :
    ∃ finalStore administrative,
      Dynamic.ProjectionsFaults (some (.mapping .integer (.function .unit .unit) [])) [.index (.integer 8)]
        (.missingMappingDefault (.function .unit .unit)) ∧
      Evaluates [.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous)] sentinelStore
        (.apply (setter prepared .integer) (.var 0)) (.inLeft functionLayout.type (.word Word.zero)) finalStore ∧
      finalStore = sentinelStore ++ administrative ∧ administrative.length = 2 := by
  obtain ⟨index, ⟨certificate⟩, steps, keys, indexLayout, position, reason⟩ :=
    single_index_of_prepare accepted rfl (by rfl) (by rfl) (by rfl) (by rfl)
  have routeSame := (DataPlaceMappingPreparation.steps_of_prepare accepted).1
  have rootMapping : prepared.route.rootMapping = some index.layout := by rw [routeSame, indexLayout]; rfl
  have keyRep : KeyRep certificate signatures (fun _ _ => False) (.integer 8) (.integer 8) := by
    change Observation _ _ _ certificate.comparison.type _ _
    rw [← certificate.keyType, indexLayout]
    exact .integer 8
  have input : RootInput index.layout .integer (.function .unit .unit)
      (KeyRep certificate signatures (fun _ _ => False)) (fun _ _ => False)
      ⟨.mapping .integer (.function .unit .unit), none, none⟩ (.inLeft functionLayout.type .unit) [] [] := by
    simpa only [indexLayout] using (RootInput.absent (layout := index.layout))
  obtain ⟨finalStore, administrative, _, failed, evaluated, extension, count⟩ :=
    setter_missing certificate prepared steps rootMapping noIdentities input keyRep (.integer 8) .nil (by intro impossible; cases impossible)
      [.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous)] sentinelStore .integer [.integer 8] (.var 0)
      (by simp [Prepared.keyTypes, keys]) (by simp [position]) (.var rfl)
  exact ⟨finalStore, administrative, failed, by simpa only [indexLayout, reason, missing] using evaluated, extension, count⟩

private def assertTrue (condition : Bool) (message : String) : IO Unit := do
  unless condition do throw (IO.userError message)
private def checkResult (expected : Value) (adminCount : Nat) (result : StatefulRunResult) : IO Unit := do
  match result with
  | .done value store =>
    assertTrue (value == expected) "generated mapping helper returned wrong value or entry order"
    assertTrue (store.length == sentinelStore.length + adminCount) "generated mapping helper has wrong allocation count"
    assertTrue (store.take sentinelStore.length == sentinelStore) "generated mapping helper overwrote an existing source cell"
  | other => throw (IO.userError s!"generated mapping helper did not finish: {reprStr other}")
private def checkHelper (layout : Core.OrderedMapping.Layout) (catalog : SourceCoreDataCatalog.Catalog)
    (prepared : Prepared) (write : Bool) (argument expected : Value) (adminCount : Nat) : IO Unit := do
  let helper := if write then setter prepared layout.keyType else getter prepared layout.keyType
  let argumentType := if write then .product (.sum .unit layout.type) (.product layout.keyType layout.valueType)
    else .product (.sum .unit layout.type) layout.keyType
  let resultType := if write then layout.type else .sum .unit layout.valueType
  let expression := .apply helper (.var 0)
  assertTrue (infer? [argumentType] expression catalog.definitions == some (.sum .word resultType)) "generated mapping helper failed Core checker"
  let initial := Core.State.initial expression [argument] sentinelStore
  checkResult expected adminCount (runStateful 5000 initial)
  match runStateful 8 initial with
  | .outOfFuel checkpoint => checkResult expected adminCount (runStateful 5000 checkpoint)
  | other => throw (IO.userError s!"mapping helper checkpoint unexpectedly finished: {reprStr other}")

private def checkRun := checkHelper layout catalog

private def wordLayout : Core.OrderedMapping.Layout := ⟨.word, .integer, ⟨0⟩⟩
private def wordCatalog : SourceCoreDataCatalog.Catalog := { entries := [
  { sourceType := .mapping .word .integer, definition := some wordLayout.definition }]
}
private def wordChecked : SourceCoreDataCatalog.Checked :=
  ⟨wordCatalog, Core.DataEnvironment.isWellFormed_sound (by decide)⟩
private def wordRoute : Route := ⟨.mapping .word .integer, wordLayout.type, .integer,
  [.index wordLayout keyId .integer], some wordLayout⟩

def run : IO Unit := do
  let prepared ← match prepare checked 20 route Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"actual mapping preparation rejected: {reprStr error}")
  checkRun prepared false getterArgument (.inRight .word (.inRight .unit (.integer 11))) 2
  checkRun prepared false (.pair (.inRight .unit root) (.integer 8)) (.inRight .word (.inRight .unit (.integer 0))) 2
  checkRun prepared false (.pair (.inLeft layout.type .unit) (.integer 8)) (.inRight .word (.inRight .unit (.integer 0))) 2
  let updated := Core.OrderedMapping.encode layout [(.integer 7, .integer 55), (.integer 7, .integer 22), (.integer 9, .integer 33)]
  checkRun prepared true (.pair (.inRight .unit root) (.pair (.integer 7) (.integer 55))) (.inRight .word updated) 4
  let appended := Core.OrderedMapping.encode layout (entries ++ [(.integer 8, .integer 55)])
  checkRun prepared true (.pair (.inRight .unit root) (.pair (.integer 8) (.integer 55))) (.inRight .word appended) 4
  let fresh := Core.OrderedMapping.encode layout [(.integer 8, .integer 55)]
  checkRun prepared true (.pair (.inLeft layout.type .unit) (.pair (.integer 8) (.integer 55))) (.inRight .word fresh) 4
  let functionPrepared ← match prepare functionChecked 20 functionRoute Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"function mapping preparation rejected: {reprStr error}")
  checkHelper functionLayout functionCatalog functionPrepared false
    (.pair (.inLeft functionLayout.type .unit) (.integer 8))
    (.inLeft (.sum .unit functionLayout.valueType) (.word Word.zero)) 2
  checkHelper functionLayout functionCatalog functionPrepared true
    (.pair (.inLeft functionLayout.type .unit) (.pair (.integer 8) anonymous))
    (.inLeft functionLayout.type (.word Word.zero)) 2
  let wordPrepared ← match prepare wordChecked 20 wordRoute Word.zero missing with
    | .ok value => pure value
    | .error error => throw (IO.userError s!"Word mapping preparation rejected: {reprStr error}")
  let wordEntries := [(.word Word.zero, .integer 11), (.word Word.zero, .integer 22)]
  let wordRoot := Core.OrderedMapping.encode wordLayout wordEntries
  checkHelper wordLayout wordCatalog wordPrepared false (.pair (.inRight .unit wordRoot) (.word Word.zero))
    (.inRight .word (.inRight .unit (.integer 11))) 2
  checkHelper wordLayout wordCatalog wordPrepared true
    (.pair (.inRight .unit wordRoot) (.pair (.word Word.zero) (.integer 55)))
    (.inRight .word (Core.OrderedMapping.encode wordLayout [(.word Word.zero, .integer 55), (.word Word.zero, .integer 22)])) 4
  IO.println "source Core mapping place proof consumers GREEN"

end Tests.SourceCoreDataPlaceMappingProofs
