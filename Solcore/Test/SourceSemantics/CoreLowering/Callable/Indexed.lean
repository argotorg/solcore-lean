import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedAllocation
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.Paths
import Solcore.SourceSemantics.CoreLowering.Internal.Compatible.MappingsAndEquality
import Solcore.SourceSemantics.CoreLowering.Internal.Data.PlaceMappings
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.Frontend.ProgramChecking
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaTyping
import Solcore.Test.SourceSemantics.CoreLowering.Callable.Ancestry
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaOrigins
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedLambdaValues
import Solcore.Test.Frontend.Source.CompilerFeatureSupport
import Solcore.Frontend.SourceCore.Internal.CallableOutputs
import Solcore.SourceSemantics.CoreLowering.Internal.Owned.FunctionValuesAndState
import Solcore.Core.Safety
import Solcore.SourceSemantics.CoreLowering.Internal.Callable.IndexedParameters
import Solcore.Frontend.SourceCore.Internal.CallablePaired
import Solcore.Test.SourceSemantics.CoreLowering.Callable.IndexedLambda

/-!
# Indexed callable tests

Indexed callables: frames, history, outputs, owned values, parameters, programs and snapshots.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedAmbient
/-! The actual indexed compiler supplies the administrative definition suffix.
Base source metadata and represented payloads retain their identity under this
suffix. Comparators and their heap extension use the full environment; the
runtime test also exercises actual emitted closures without claiming their
source authenticity from native typing alone. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedAmbient
open Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload

private def noFunctions {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    FunctionModel checked.catalog (CallableIndexedAmbient.ambientDefinitions prepared) where
  Represents := fun _ _ _ _ _ _ _ => False
  projection := False.elim
  runtime_hasType := False.elim
  source_function := False.elim
  extend := fun impossible _ _ _ => False.elim impossible

private def model {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :=
  CompatibleAmbientHeap.payloadModel checked checked.staticRegistry (noFunctions prepared)

/-- The real frame value is typed in the actual final definitions. -/
theorem frame_typed {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) (world : StoreTyping) :
    RuntimeValueHasType world
      (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty)
      prepared.ancestry.layout.frame.type prepared.layouts.definitions :=
  SourceCoreCallableIndexedFrames.encode_runtime_typed world
    (CallableIndexedAmbient.frame_registered prepared) .empty

/-- The sequence representation uses the same full-definitions model, and
retains the raw staged type rather than deducing a source equality from Core. -/
theorem keys_represented {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (mapping : LocationMap) (world : StoreTyping) (a b : Word) :
    DataExpressionSequence.Values (model prepared) mapping world [.comptime .word, .word]
      [.word, .word] [.word a, .word b] [.word a, .word b] :=
  .cons (.compatible (actual := .word) rfl (.word a)) (.cons (.word b) .nil)

theorem staged_runtime_view {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) (value : Word) :
    Dynamic.ValueRuntimeTypeMatches (.word value) (.comptime .word) :=
  ValueRep.source_runtimeView (functions := noFunctions prepared) (fun impossible => False.elim impossible)
    (mapping := []) (world := []) (registry := checked.staticRegistry) (.compatible (actual := .word) rfl (.word value))

/-- Actual generated comparison code preserves a pre-existing common heap
under the real frame/marker suffix. Every newly installed comparator cell is
administrative; old source cells and raw staged metadata remain unchanged. -/
theorem comparison_preserves_heap {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)
    (comparator : SourceCoreCompatibleDataEquality.Prepared checked) (wordType : comparator.type = .word)
    {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}
    (heaps : GenericHeap.HeapRepresents (model prepared) mapping world heap store) (a b : Word) :
    ∃ result futureWorld,
      (result = true ↔ Dynamic.ValueEquivalent (.word a) (.word b)) ∧
      Evaluates [.word a, .word b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [.word a, .word b] store) ∧
      WorldExtends world futureWorld ∧
      GenericHeap.HeapRepresents (model prepared) mapping futureWorld heap
        (CompatibleEquality.preparedStore comparator [.word a, .word b] store) ∧
      RuntimeValueHasType futureWorld (.bool result) .bool prepared.layouts.definitions ∧
      AdministrativePreserved mapping store mapping (CompatibleEquality.preparedStore comparator [.word a, .word b] store) := by
  have left : ValueRep checked checked.staticRegistry (noFunctions prepared) mapping world
      (.comptime .word) (.word a) (.word a) comparator.type := by
    rw [wordType]; exact .compatible (actual := .word) rfl (.word a)
  have right : ValueRep checked checked.staticRegistry (noFunctions prepared) mapping world
      .word (.word b) (.word b) comparator.type := by rw [wordType]; exact .word b
  have faithful : DataEquality.IdentityFaithful (fun _ _ => False) :=
    ⟨fun impossible => False.elim impossible, fun impossible _ => False.elim impossible⟩
  obtain ⟨result, meaning, evaluated⟩ := CompatibleEquality.represented_compare_preserves comparator faithful
    (fun impossible => False.elim impossible) left right [.word a, .word b] store (.var 0) (.var 1) (.var rfl) (.var rfl)
  have code : HasType [.word, .word] (CompatibleEquality.comparison comparator (.var 0) (.var 1)) .bool
      prepared.layouts.definitions := by
    have generated := comparator.typed.extend_definitions (CallableIndexedAmbient.ambientDefinitions prepared).basePrefix
    have callable : HasType [.word, .word] comparator.expression (.function (.product .word .word) .bool)
        prepared.layouts.definitions := by
      simpa only [SourceCoreDataEquality.comparatorType, wordType, Expr.rename_id, CallableIndexedAmbient.ambient_definitions] using
        (generated.rename (mapping := Renaming.id) (target := [.word, .word]) (by intro index type found; cases found))
    simpa only [CompatibleEquality.comparison, Expr.weakenAt, Nat.zero_le, ↓reduceIte] using
      (HasType.letE callable (HasType.apply (.var rfl) (.pair (.var (index := 1) rfl) (.var (index := 2) rfl))))
  obtain ⟨future, worlds, related, typed, frame⟩ := DataMappingHeap.evaluation_preserves_frame heaps
    (RuntimeEnvironmentHasTypes.cons .word (.cons .word .nil)) code evaluated (show CompatibleEquality.preparedStore comparator [.word a, .word b] store =
      store ++ _ from rfl)
  exact ⟨result, future, meaning, evaluated, worlds, related, typed, frame⟩

private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "type F = function(Word) returns (Word);",
    "function main(seed: Word) returns (Word) {",
    " let cache: mapping(Word => Word); cache[0] = seed;",
    " let f: F = lam(item: Word) -> Word { seed += item; return seed; };",
    " f(3); return f(4); }"
  ]}] }

/-- Actual preparation, suspension/resumption, and comparator installation in
its completed store. These checks use the native compiler only. -/
def run : IO Unit := do
  let program ← get "ambient source checker" (checkProgram workspace)
  let key ← match program.signatures.functions.filter (·.name == "main") with
    | [signature] => pure (⟨signature.id, []⟩ : SourceSpecialization.SpecializationKey)
    | _ => throw (IO.userError "ambient fixture missing main")
  let plan ← match SourceSpecializationWorklist.run program [⟨key.declaration, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ambient worklist: {reprStr other}")
  let automatic ← get "ambient compatible base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "ambient actual indexed compiler" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  assertTrue (!automatic.checked.catalog.definitions.isEmpty) "ambient fixture lacks a source data prefix"
  assertTrue (!prepared.layouts.entries.isEmpty) "actual compiler produced no source markers"
  assertTrue (prepared.layouts.definitions == automatic.checked.catalog.definitions ++
    (prepared.ancestry.layout.frame.definition :: prepared.layouts.entries.map (·.layout.definition)))
    "actual frame/marker suffix changed catalog identities"
  let first ← get "ambient suspended start" (prepared.runSource key [.word (Word.ofNatModulo 2)] 7 500)
  assertTrue (match first.result.native.observation with | .outOfFuel _ => true | _ => false)
    "ambient fixture did not exercise a checkpoint"
  let completion := first.resume 100000
  -- Closures capture by value: both calls of `f` start again from `seed = 2`,
  -- so the second returns 2 + 4.
  match completion.result.native.observation with
  | .succeeded (.word result) _ =>
    assertTrue (result == Word.ofNatModulo 6) "ambient closure did not restart its call from the captured creation-time value"
  | other => throw (IO.userError s!"ambient invocation: {reprStr other}")
  let initialStore := SourceCoreCallableIndexedLedger.store completion
  let comparator ← get "ambient real comparator" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked .word)
  for right in [9, 10] do
    let expression := CompatibleEquality.comparison comparator (.word (Word.ofNatModulo 9)) (.word (Word.ofNatModulo right))
    assertTrue (infer? [] expression prepared.layouts.definitions == some .bool) "comparison failed full-definition checker"
    match runStateful 100000 (.initial expression [] initialStore) with
    | .done (.bool value) finalStore =>
      assertTrue (initialStore.length < finalStore.length) "comparison did not allocate its helper cells"
      assertTrue (value == (right == 9)) "ambient comparison changed source Word equality"
      assertTrue (finalStore == CompatibleEquality.preparedStore comparator [] initialStore)
        "comparator changed existing heap or administrative allocation order"
    | other => throw (IO.userError s!"ambient comparator: {reprStr other}")
  IO.println "source core indexed ambient tests passed"

end Solcore.Test.SourceCoreCallableIndexedAmbient
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedAppliedStageOrigins
/-! Actual metadata factories supply the applied header and descriptor origin.
The indexed consumer requires the same full rewritten source. These tests do
not turn a substitution-only source receipt into an applied one, nor construct
body typing from history. The existing recipe fixture checks distinct caller
and lexical contexts, original witnesses and the observable source export. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedAppliedStageOrigins
open Solcore Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableAppliedViewProvenance CallableIndexedAppliedStageOrigins
open SourceCoreCallableAncestryReadRecipes

abbrev actual_view := @Recipe.of_view
abbrev actual_header := @header_of_prepared
abbrev actual_code := @code_origin
abbrev actual_scope := @selected
abbrev original_source_receipt := @LambdaSourceAlignment.SourceReceipt.original

section Recipe
variable {checked : Checked} {base : Base checked} {inputs : Inputs base}
  {callerFrame lexicalFrame : Frame} {caller lexical : MetadataState} {view target : Core.Word}
  (recipe : Recipe inputs callerFrame lexicalFrame caller lexical view target)
  {contract : SourceCoreStageContracts.Contract}
  (canonical : CanonicalHeader inputs recipe.read.template contract)

include canonical in
theorem actual_bound {function : Dynamic.Closure}
    (retained : recipe.read.descriptor.contract = some contract)
    (aligned : Alignment recipe function) :
    CallableLedger.Binds base.plan (.closure function) (CallContractCertificates.semanticContract contract) :=
  (origin recipe canonical retained aligned).binds

include canonical in
theorem ordered_parameters : contract.parameters =
    recipe.applied.parameters.map (TypedBinder.applySubstitution recipe.read.substitution) :=
  recipe.contract_parameters canonical

include canonical in
theorem source_result : contract.stagedResult =
    SourceCompilationPlan.sourceTypeIsComptimeOnly (recipe.read.substitution.apply recipe.applied.resultType) :=
  recipe.contract_result canonical

theorem separate_contexts :
    (recipe.read.after lexical).metadata.active = recipe.read.substitution.compose lexical.metadata.active ∧
    (recipe.read.after lexical).nativeActive = recipe.read.entry.view.cumulative :=
  ⟨recipe.semantic_active, recipe.native_active⟩

theorem full_lexical_source : (recipe.read.after lexical).metadata.source =
    SourceTypedRuntime.rewriteLocalRequirements recipe.read.witnesses
      (lexical.metadata.source.applySubstitution recipe.read.substitution) := recipe.full_source

theorem actual_rewritten_node :
    (recipe.read.after lexical).metadata.source.lookupExpression? recipe.read.entry.view.principal.initializer =
      some (SourceTypedRuntime.rewriteExpressionLocalRequirements recipe.read.witnesses
        (recipe.applied.node.applySubstitution recipe.read.substitution)) := recipe.source_node

theorem original_witness_order (captured : SourceTypedRuntime.Environment)
    (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    recipe.applied.sourceValue captured evidence =
      .instantiated recipe.read.substitution recipe.read.witnesses
        (.closure recipe.applied.parameters recipe.applied.resultType recipe.applied.body
          lexical.metadata.source lexical.metadata.owner captured evidence) := recipe.source_value _ _

theorem authenticated_after : CallableAncestryPairedLookup.Authenticates inputs
    (.appliedView view target callerFrame lexicalFrame) (some (recipe.read.after lexical)) := recipe.authenticated
end Recipe

section Original
variable {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
  {table : SourceCoreStageCodebook.Table} {function : Dynamic.Closure} {scope : Staging.Recursive.Scope}

theorem selected_original (selected : RecursiveStageRegistry.Selected program plan table function scope) :
    ∃ sidecar active, SourceCoreStageContracts.prepareSidecar plan sidecar.caller.key = .ok sidecar ∧
      scope = RecursiveStageRegistry.scope sidecar active function ∧
      scope.origin.declaration = sidecar.caller.key.declaration := selected.original
end Original

/-- Fresh recipe execution; the whole native callable fixture remains in its
existing test module and is not duplicated here. -/
def run : IO Unit := Tests.SourceCoreCallableAncestryReadRecipes.run

end Tests.SourceCoreCallableIndexedAppliedStageOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedAuthorityPool
/-! Formal protocol consumers. No body grammar or indirect-call semantics is
asserted here; registered snapshots are the exact retained record domain. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedAuthorityPool
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableAncestryPairedLookup
open RecursiveNamedCatalog CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedAuthorityPool

variable {checked : Checked} {base : Base checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : ValuesContext}
  {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  {headers : Inventory prepared values ambient.definitions program}
  {keys : List (Key prepared values ambient.definitions program)}
  {key otherKey : Key prepared values ambient.definitions program}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- Real prepared recipe, exact original heap and catalogue entry. -/
abbrev actual_initial_pool := @CallableIndexedAuthorityPool.initial_entry

/-- Actual allocator receipts produce the exact three-cell append and its
record registration; no final separation law is supplied. -/
abbrev actual_snapshot_registration := @Pool.completed_snapshot

/-- The actual fresh allocator and full initialized entry close registration. -/
abbrev actual_fresh_frame_registration := @Pool.register_fresh_frame
abbrev actual_fresh_frame_history := @fresh_frame_state

/-- The concrete native allocator initializes an empty frame at its exact
fresh location. A decoder is not part of this construction. -/
theorem actual_empty_frame_append :
    CellState prepared.graph.inputs prepared.graph.table prepared.layout.frame store.length .empty .empty
      (store ++ [encode prepared.layout.frame .empty]) :=
  fresh_frame_state (.stable .empty) rfl

/-- Registration consumes that actual one-cell append and an independently
initialized complete catalogue; its cross-separation is proved internally. -/
def actual_fresh_empty_registration (pool : Pool headers keys mapping world heap store)
    {futureWorld : StoreTyping} (worlds : WorldExtends world futureWorld)
    (entry : EntryValid headers key mapping futureWorld heap (store ++ [encode prepared.layout.frame .empty]))
    (fresh : key.frameLocation = store.length)
    (records : ∀ record ∈ entry.authority.records, pool.Registered record) :
    Pool headers (keys ++ [key]) mapping futureWorld heap (store ++ [encode prepared.layout.frame .empty]) :=
  pool.register_fresh_frame rfl worlds entry fresh records

/-- Restoration promises the original key domain, keeping final body effects. -/
abbrev actual_original_pool_restore := @Pool.restore

/-- The exact code and every original captured value survive the real write. -/
abbrev full_capture_after_write := @Pool.install_capture_read

def duplicate_key (pool : Pool headers keys mapping world heap store) (i : Fin keys.length) :
    Pool headers (keys ++ [keys[i.val]]) mapping world heap store := pool.duplicate i

theorem shared_frame_update (pool : Pool headers keys mapping world heap store)
    (i j : Fin keys.length) (same : keys[j.val].frameLocation = keys[i.val].frameLocation)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    ((pool.install i history).rows i).authority.current = next ∧
    ((pool.install i history).rows j).authority.current = next := by
  constructor <;> rw [Pool.install_current] <;> simp [same]

theorem other_frame_keeps_history (pool : Pool headers keys mapping world heap store)
    (i j : Fin keys.length) (different : keys[j.val].frameLocation ≠ keys[i.val].frameLocation)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    ((pool.install i history).rows j).authority.current = (pool.rows j).authority.current ∧
    ((pool.install i history).rows j).authority.ghost = (pool.rows j).authority.ghost ∧
    ((pool.install i history).rows j).authority.records = (pool.rows j).authority.records := by
  exact ⟨by rw [Pool.install_current]; simp [different],
    by rw [Pool.install_ghost]; simp [different], pool.install_records i j history⟩

theorem different_catalogue_global (left : EntryValid headers key mapping world heap store)
    (right : EntryValid headers otherKey mapping world heap store)
    {header : Header prepared values ambient.definitions program} (member : header ∈ headers) :
    key.locations header ≠ otherKey.frameLocation := left.global_ne_frame right member

theorem old_record_protected_after_install (pool : Pool headers keys mapping world heap store)
    (i selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (member : record ∈ (pool.rows i).authority.records)
    {next : NativeFrame} {ghost : GhostFrame}
    (history : Current prepared.graph.inputs prepared.graph.table next ghost) :
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame mapping
      (store.set keys[selected.val].frameLocation (encode prepared.layout.frame next)) record :=
  ((pool.install selected history).rows i).authority.snapshots record (by simpa only [Pool.install_records] using member)

section CrossBoundary
/-- Two different physical cells, both with actual initialized empty frames. -/
def keyAt (location : Location) : Key prepared values ambient.definitions program :=
  ⟨fun _ => 7, 0, location⟩

def twoStore : Store := [encode prepared.layout.frame .empty, encode prepared.layout.frame .empty]
def twoWorld : StoreTyping := [prepared.layout.frame.type, prepared.layout.frame.type]
def snapshotAt (location : Location) : CallableIndexedSnapshots.Record := ⟨location, .empty, .empty, none⟩

/-- Each individual authority can have self-distinct records while its
snapshot is the other authority's mutable frame. The cross invariant is real. -/
def firstAuthority : Authority ([] : Inventory prepared values ambient.definitions program)
    (keyAt (prepared := prepared) (values := values) (ambient := ambient) (program := program) 0).locations
    0 [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) where
  frameLocation := 0
  unmapped := by simp
  typed := rfl
  current := .empty
  ghost := .empty
  frame := ⟨rfl, .stable .empty⟩
  records := [snapshotAt 1]
  snapshots := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    exact ⟨rfl, by simp, .empty⟩
  distinct := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    decide
  captures := by intro header member; simp at member

def secondAuthority : Authority ([] : Inventory prepared values ambient.definitions program)
    (keyAt (prepared := prepared) (values := values) (ambient := ambient) (program := program) 1).locations
    0 [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) where
  frameLocation := 1
  unmapped := by simp
  typed := rfl
  current := .empty
  ghost := .empty
  frame := ⟨rfl, .stable .empty⟩
  records := [snapshotAt 0]
  snapshots := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    exact ⟨rfl, by simp, .empty⟩
  distinct := by
    intro record member
    have same := List.mem_singleton.mp member; subst record
    decide
  captures := by intro header member; simp at member

theorem self_distinct_does_not_supply_cross :
    ¬ ∃ pool : Pool ([] : Inventory prepared values ambient.definitions program)
        [keyAt 0, keyAt 1] [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)),
      (pool.rows 0).authority.records = [snapshotAt 1] := by
  rintro ⟨pool, records⟩
  have member : snapshotAt 1 ∈ (pool.rows 0).authority.records := by rw [records]; exact List.mem_singleton_self _
  have impossible := pool.separated 0 1 (snapshotAt 1) member
  exact impossible rfl

/-- Duplicating the actual first authority is valid: both rows share frame 0
and the retained snapshot at 1 remains separated from both rows. -/
def concrete_duplicate :
    Pool ([] : Inventory prepared values ambient.definitions program)
      [keyAt 0, keyAt 0] [] (twoWorld (prepared := prepared)) ⟨[]⟩ (twoStore (prepared := prepared)) :=
  (Pool.singleton (EntryValid.of_authority (firstAuthority (prepared := prepared) (values := values)
    (ambient := ambient) (program := program)))).duplicate 0

theorem concrete_frames_different :
    (firstAuthority (prepared := prepared) (values := values) (ambient := ambient) (program := program)).frameLocation ≠
      (secondAuthority (prepared := prepared) (values := values) (ambient := ambient) (program := program)).frameLocation := by change (0 : Nat) ≠ 1; decide
end CrossBoundary

end Solcore.Test.SourceCoreCallableIndexedAuthorityPool
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedBodyMeaning
/-! A mapped source update survives a language failure inside the context
wrapper. Installation/restoration preserve the general payload model and the
original caller. No child Core execution is supplied to the regression. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedBodyMeaning
open Core Frontend SourceSemantics SourceSemantics.CoreLowering GeneralHeap
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects} {layout : Layout}
    {world : StoreTyping} {before after : Dynamic.Heap} {store : Store}
    {current next : NativeFrame} {currentGhost nextGhost : GhostFrame}
    {sourceLocation : Dynamic.Location} {cell : Dynamic.Cell} {reason : Word}
    (registered : layout.Registered catalog.definitions)
    (heaps : GenericHeap.HeapRepresents model [1] world before store)
    (contextTyped : world[0]? = some layout.type)
    (caller : CellState inputs table layout 0 current currentGhost store)
    (nextHistory : Current inputs table next nextGhost)
    (reference : ReferenceRepresents [1] world sourceLocation 1 .bool)
    (read : Dynamic.Heap.Reads before sourceLocation cell)
    (represented : model.Represents [1] world cell.type (.bool true) (.bool true) .bool)
    (written : Dynamic.Heap.Writes before sourceLocation (some (.bool true)) after) :
    ∃ finalStore,
      Evaluates [.cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] store
        (withFrame (.var 1) (SourceCoreCallableIndexedDispatch.literal layout next)
          (.letE (.storeCell (.var 0) (.inRight .unit (.bool true)))
            (LanguageResult.failure .unit (.word reason))))
        (.inLeft .unit (.word reason)) finalStore ∧
      GenericHeap.HeapRepresents model [1] world after finalStore ∧
      AdministrativePreserved [1] store [1] finalStore ∧
      CellState inputs table layout 0 current currentGhost finalStore ∧
      finalStore.read? 1 = some (.inRight .unit (.bool true)) := by
  have unmapped : (0 : Nat) ∉ ([1] : LocationMap) := by decide
  obtain ⟨installedHeaps, installedCurrent⟩ := CallableIndexedBodyFrames.install
    registered heaps unmapped contextTyped caller nextHistory
  obtain ⟨updated, nativeWrite, updatedHeaps, sourceFrame⟩ :=
    installedHeaps.write_initialized reference read represented written
  obtain ⟨old, oldRead, _⟩ := installedHeaps.runtime_hasTypes.lookup reference.typed
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0]
      (store.set 0 (encode layout next))
      (((Expr.letE (.storeCell (.var 0) (.inRight .unit (.bool true)))
        (LanguageResult.failure .unit (.word reason))).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason)) updated := by
    simpa [Expr.weakenAt, LanguageResult.failure] using
      (show Evaluates
        [.unit, encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0]
        (store.set 0 (encode layout next))
        (.letE (.storeCell (.var 2) (.inRight .unit (.bool true))) (.inLeft .unit (.word reason)))
        (.inLeft .unit (.word reason)) updated from
        .letE (.storeCell (.var rfl) oldRead (.inRight .bool) nativeWrite) (.inLeft .word))
  have nextEvaluation : Evaluates
      [encode layout current, .cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] store
      ((SourceCoreCallableIndexedDispatch.literal layout next).weakenAt 0) (encode layout next) store := by
    rw [← Expr.rename_insertion, CallableIndexedRenaming.literal]
    exact CallableIndexedContextFrames.literal_evaluates _ _ _ _
  have evaluated := CallableContextFrames.withFrame_evaluates (.var (show
      ([.cellRef (OptionalCell.cellType .bool) 1, .cellRef layout.type 0] : Environment)[1]? = some (.cellRef layout.type 0) from rfl))
    caller.read nextEvaluation bodyEvaluation
  have _innerCurrent := CallableIndexedBodyFrames.body_current unmapped installedCurrent sourceFrame
  obtain ⟨finalHeaps, finalFrame, finalCaller⟩ := CallableIndexedBodyFrames.restore
    registered unmapped contextTyped caller updatedHeaps (WorldExtends.refl _) sourceFrame
  refine ⟨_, evaluated, finalHeaps, finalFrame, finalCaller, ?_⟩
  have restoreWrite : updated.write? 0 (encode layout current) = some (updated.set 0 (encode layout current)) :=
    Store.write?_eq_some_iff.mpr ⟨updatedHeaps.runtime_hasTypes.location_lt contextTyped, rfl⟩
  exact (Store.write?_preserves_other restoreWrite (by decide)).trans (Store.write?_reads_written nativeWrite)

/-- Repeated nested body frames preserve the same installed history before
the enclosing wrapper restores its caller. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : Layout} {firstMap middleMap finalMap : LocationMap} {first middle final : Store}
    {location : Location} {native : NativeFrame} {ghost : GhostFrame}
    (unmapped : location ∉ firstMap)
    (current : CellState inputs table layout location native ghost first)
    (firstFrame : AdministrativePreserved firstMap first middleMap middle)
    (secondFrame : AdministrativePreserved middleMap middle finalMap final) :
    CellState inputs table layout location native ghost final :=
  CallableIndexedBodyFrames.body_current unmapped current (firstFrame.trans secondFrame)

end Solcore.Test.SourceCoreCallableIndexedBodyMeaning
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedBuiltinValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
/-! Actual builtin references under a sealed indexed artifact supply all
function-leaf laws. Native captures include the artifact's new nominal frame;
equality observes source builtin identity, independently of capture contents. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedBuiltinValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedBuiltinValues CompatiblePayload GeneralHeap

/-- Fresh nominal frame captures are typed under the actual definition suffix. -/
theorem captured_frame {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (world : StoreTyping) : RuntimeEnvironmentHasTypes world
      [SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty]
      [prepared.ancestry.layout.frame.type] prepared.layouts.definitions :=
  .cons (SourceCoreCallableIndexedFrames.encode_runtime_typed world (CallableIndexedAmbient.frame_registered prepared) .empty) .nil

theorem leaves_extend {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {registry futureRegistry : SourceCoreRawMetadata.Registry} {mapping futureMap : LocationMap}
    {world futureWorld : StoreTyping} {sourceType : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : (model prepared profile).Represents registry mapping world sourceType source value type)
    (registries : SourceCoreRawMetadata.Extends registry futureRegistry) (maps : LocationMap.Extends mapping futureMap)
    (worlds : WorldExtends world futureWorld) :
    (model prepared profile).Represents futureRegistry futureMap futureWorld sourceType source value type :=
  (model prepared profile).extend related registries maps worlds

/-- The real comparator is supplied with proved model laws, not caller law
assumptions. Its result uses the independent source equality relation. -/
theorem comparison_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

section ActualReference
variable {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
  (profile : checked.catalog.callableContracts = true)
  {active : TypeSystem.Substitution} {compilation : SourceCoreFunctions.Context}
  {source : TypedSource} {node : ExpressionNode} {name : String} {function : BuiltinFunctionId}
  {lowered : SourceCoreBasic.LoweredExpr}
  (globals : compilation.globals = prepared.base.globals)
  (accepted : SourceCoreFunctions.builtinReference
    (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) active)
    compilation source node name function = .ok lowered)
  {world : StoreTyping} {actual : Environment} {actualContext : Core.Context}
  (typed : RuntimeEnvironmentHasTypes world actual actualContext prepared.layouts.definitions)

include globals accepted typed in
theorem reference_supplies_laws (store : Store) (registry : SourceCoreRawMetadata.Registry) (mapping : LocationMap) :
    ∃ value, Evaluates actual store lowered.expression (.inRight .word value) store ∧
      (model prepared profile).Represents registry mapping world node.type (.builtin ⟨function⟩) value lowered.type ∧
      CompatibleEquality.Observation checked.catalog registry (Identity prepared) lowered.type (.builtin ⟨function⟩) value := by
  obtain ⟨value, evaluated, related⟩ := formation_of_accepted prepared profile globals accepted typed store registry mapping
  exact ⟨value, evaluated, related, observations prepared profile related⟩
end ActualReference

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function sub(a: integer, b: integer) returns (integer) { return integerSub(a, b); }",
    "function add(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function mul(a: integer, b: integer) returns (integer) { return integerMul(a, b); }",
    "function eq(a: integer, b: integer) returns (Bool) { return integerEq(a, b); }",
    "function lt(a: integer, b: integer) returns (Bool) { return integerLt(a, b); }",
    "function from(a: integer) returns (Word) { return wordFromInteger(a); }",
    "function to(a: Word) returns (integer) { return wordToInteger(a); }"
  ]}] }

private def checkComparison {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (function : BuiltinFunctionId) (a b : Value) (expected : Bool) : IO Unit := do
  let comparator ← SourceCompilerFeatureSupport.get "builtin leaf comparator"
    (SourceCoreCompatibleDataEquality.prepare 500 checked function.type)
  let store : Store := [.word (Word.ofNatModulo 41)]
  let expression := CompatibleEquality.comparison comparator (.var 0) (.var 1)
  SourceCompilerFeatureSupport.require (infer? [comparator.type, comparator.type] expression prepared.layouts.definitions == some .bool)
    "builtin comparator rejected actual full definitions"
  let whole := runStateful 100000 (.initial expression [a, b] store)
  SourceCompilerFeatureSupport.require (whole == .done (.bool expected) (CompatibleEquality.preparedStore comparator [a, b] store))
    "builtin identity comparison changed capture-independent source equality or store"
  for fuel in [0, 3, 10, 29] do
    match runStateful fuel (.initial expression [a, b] store) with
    | .outOfFuel state => SourceCompilerFeatureSupport.require (runStateful 100000 state == whole) "builtin leaf equality resume changed result"
    | .done value after => SourceCompilerFeatureSupport.require ((StatefulRunResult.done value after) == whole) "builtin equality prefix changed result"
    | _ => throw (IO.userError "builtin leaf comparator stuck")

def run : IO Unit := do
  let sourceProgram ← SourceCompilerFeatureSupport.get "builtin leaf source checker" (checkProgram workspace)
  let seeds := sourceProgram.signatures.functions.map fun signature => (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run sourceProgram seeds 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"builtin leaf worklist: {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "builtin leaf compatible artifact" (SourceCoreCompatibleFunctions.prepare sourceProgram plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "builtin leaf indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let snapshot := SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame .empty
  let frameExpression := SourceCoreCallableIndexedDispatch.literal prepared.ancestry.layout.frame .empty
  SourceCompilerFeatureSupport.require ((infer? [] frameExpression automatic.checked.catalog.definitions).isNone)
    "fresh indexed frame unexpectedly belongs to source catalog"
  let environment : Environment := [snapshot, .cellRef .word 0]
  let store : Store := [.word (Word.ofNatModulo 41)]
  let context : Core.Context := [prepared.ancestry.layout.frame.type, .cell .word]
  let mut observed : List (BuiltinFunctionId × Value × Value) := []
  for specialized in prepared.base.plan.specializations do
    let source := specialized.function.typedBody
    let compilation : SourceCoreFunctions.Context :=
      ⟨prepared.base.plan, specialized.key, prepared.base.globals, 0, [], Word.zero⟩
    for raw in source.nodes do
      match raw with
      | .expression node =>
        match node.form with
        | .reference name (.builtinFunction function) =>
          let lowered ← SourceCompilerFeatureSupport.get "actual builtin leaf reference"
            (SourceCoreFunctions.builtinReference
              (SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) [])
              compilation source node name function)
          SourceCompilerFeatureSupport.require (infer? context lowered.expression prepared.layouts.definitions == some (LanguageResult.resultType lowered.type))
            "actual builtin reference rejected fresh frame capture context"
          let value ← match runStateful 1000 (.initial lowered.expression environment store) with
            | .done (.inRight .word value) after =>
              SourceCompilerFeatureSupport.require (after == store) "builtin reference mutated store"
              pure value
            | other => throw (IO.userError s!"actual builtin reference result: {reprStr other}")
          let other ← match runStateful 1000 (.initial lowered.expression [] store) with
            | .done (.inRight .word value) after =>
              SourceCompilerFeatureSupport.require (after == store) "empty capture builtin reference mutated store"
              pure value
            | result => throw (IO.userError s!"empty capture reference: {reprStr result}")
          let descriptor ← SourceCompilerFeatureSupport.get "owned builtin descriptor"
            (SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.builtin function))
          let index ← match BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) with
            | some (_, index) => pure index | none => throw (IO.userError "missing builtin inventory")
          let identity ← match Word.ofNat? (prepared.base.globals.length + index + 1) with
            | some identity => pure identity | none => throw (IO.userError "builtin identity overflow")
          SourceCompilerFeatureSupport.require (value == BuiltinCalls.Protocol.contractedValue function identity descriptor.id environment)
            "actual reference lost identity, descriptor, code or actual captures"
          checkComparison prepared function value other true
          observed := (function, value, other) :: observed
        | _ => pure ()
      | _ => pure ()
  SourceCompilerFeatureSupport.require (observed.length == BuiltinFunctionId.all.length) "builtin fixture missed an accepted branch"
  for (left, a, _) in observed do
    for (right, b, _) in observed do
      if SourceCoreInteger.builtinParameter left == SourceCoreInteger.builtinParameter right &&
          SourceCoreInteger.builtinResult left == SourceCoreInteger.builtinResult right then
        checkComparison prepared left a b (left == right)
  IO.println "indexed builtin leaves: actual identities/descriptors, full-definition captures, source equality and resume GREEN"
end Tests.SourceCoreCallableIndexedBuiltinValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedCachedNativeTyping
/-! Cached native roots type their actual second-pass closures. Both global
slots and wrapper input types are retained; native typing grants no source
closure authority. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedCachedNativeTyping
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedCachedNativeTyping

theorem actual_cached_closure (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {closure : Expr} {signature : SourceCoreCalls.Signature}
    (selected : cached.indexed.secondPass.closures[index]? = some closure)
    (global : cached.indexed.base.globals[index]? = some signature) :
    HasType (cached.indexed.base.globals.map (·.referenceType) ++ .cell cached.indexed.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
      closure signature.functionType cached.indexed.layouts.definitions :=
  prepared_native_closure cached.indexedPrepared member selected global

theorem actual_cached_named_output (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named)
    (global : cached.indexed.base.globals[index]? = some named.signature) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.output (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  prepared_named_output cached.indexedPrepared member selected global

/-- A later installer Unit binder is removed syntactically, including from a
lambda's lifted body renaming. The original context can have hidden entries. -/
theorem second_slot {definitions : DataEnvironment} {context : Core.Context}
    {first second continuation : Expr} {type functionType : Ty}
    (typed : HasType context (SourceCoreRecursiveEntry.installFunctions [first, second] continuation) type definitions)
    (reference : context[1]? = some (OptionalCell.referenceType functionType)) :
    HasType context second functionType definitions :=
  installed_closure typed rfl reference

theorem invalid_installer_rejected (tail : Expr) :
    ¬ HasType [OptionalCell.referenceType (.function .unit .unit)]
      (SourceCoreRecursiveEntry.installFunctions [.word Word.zero] tail) .unit [] := by
  intro typed
  have invalid := installed_closure typed (index := 0) (closure := .word Word.zero) rfl rfl
  cases invalid

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function step(value: Word) returns (Word) { return value + 1; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return step(recursive(value - 1)); }",
    "function even(value: Word) returns (Bool) { if (value == 0) { return true; } return odd(value - 1); }",
    "function odd(value: Word) returns (Bool) { if (value == 0) { return false; } return even(value - 1); }",
    "function mixed(flag: Bool, seed: Word) returns (Word) { let value = seed; for (let i = 0; i < 3; i = step(i)) { value = step(value); } if (flag) { return recursive(value); } return value; }",
    "function captured(seed: Word) returns (Word) { let value = seed; let increase = lam(item: Word) -> Word { let i = 0; while (i < 2) { value = step(value); i = step(i); } return value + item; }; return increase(3); }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkCached (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  require (!prepared.entries.isEmpty) "actual native root missing"
  require (prepared.base.globals.length == prepared.secondPass.closures.length) "closure/global inventory mismatch"
  for root in prepared.entries do
    let context := prepared.base.globals.map (·.referenceType) ++ .cell prepared.ancestry.layout.frame.type ::
      SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
    for (closure, index) in prepared.secondPass.closures.zipIdx do
      let signature ← match prepared.base.globals[index]? with
        | some signature => pure signature | none => throw (IO.userError "cached global slot missing")
      require (Core.infer? context closure prepared.layouts.definitions == some signature.functionType)
        "cached checked root did not type its original closure"
      match closure with
      | .lambda parameter result body =>
        require (parameter == signature.parameterType && result == LanguageResult.resultType signature.resultType)
          "actual named closure signature changed"
        require (Core.infer? (parameter :: context) body prepared.layouts.definitions == some result)
          "actual named output lost body typing"
      | _ => throw (IO.userError "cached named compiler did not emit a lambda")

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "cached native source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("recursive", [scalar 3], scalar 4),
      ("even", [scalar 4], (.bool true : SourceCoreExecution.Value)),
      ("mixed", [(.bool true : SourceCoreExecution.Value), scalar 2], scalar 6),
      ("captured", [scalar 2], scalar 7)] do
    let entry ← compileNamed checked name
    checkCached entry
    require ((← entry.run arguments) == expected) "cached native source result changed"
    entry.checkResume arguments expected 1
  IO.println "cached native typing: actual prepared roots, all installed global slots, exact named outputs, recursive/mutual/loop/lambda bodies and resume GREEN"

end Tests.SourceCoreCallableIndexedCachedNativeTyping
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedFormation
/-! Actual compiler receipts and finite entry/formation laws. Dynamic metadata
is carried from saved cells, not inferred from native descriptors or indices. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedFormation
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch

/-- Even a completed language failure restores the caller's stable or pending
read token. The invoked lambda keeps its independent lexical ghost parent. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {current : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin reason : Word}
    (lexical : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (currentHistory : Current graph.inputs graph.table current currentGhost)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) current ≠ .invalid) :
    Evaluates [.unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout current]
      (withFrame (.var 2) (lambdaFrame graph.table layout origin (.var 1) (.loadCell (.var 2)))
        ((LanguageResult.failure .unit (.word reason)).weakenAt 1))
      (.inLeft .unit (.word reason)) [encode layout current] := by
  have caller : CellState graph.inputs graph.table layout 0 current currentGhost [encode layout current] := ⟨rfl, currentHistory⟩
  have bodyEvaluation : Evaluates
      [.unit, encode layout current, .unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0]
      ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
      ((((LanguageResult.failure .unit (.word reason)).weakenAt 1).weakenAt 0).weakenAt 0)
      (.inLeft .unit (.word reason))
      ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current))) := by
    simpa [LanguageResult.failure, Expr.weakenAt] using
      (show Evaluates [.unit, encode layout current, .unit, encode layout (.state (Int.ofNat position)), .cellRef layout.type 0]
        ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
        (.inLeft .unit (.word reason)) (.inLeft .unit (.word reason))
        ([encode layout current].set 0 (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) current)))
        from .inLeft .word)
  obtain ⟨_, _, _, evaluated, _⟩ := CallableIndexedEntry.lambda_body_evaluates graph
    (referenceIndex := 0) (environment := [.cellRef layout.type 0]) (argument := .unit)
    rfl caller lexical valid bodyEvaluation
  simpa using evaluated

/-- No arbitrary AST shape is substituted for actual compiler success. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {context : SourceCoreFunctions.Context} {source : SourceInference.TypedSource}
    {scope : SourceCoreFunctions.Scope} {node : SourceInference.ExpressionNode}
    {parameter result : Ty} {raw output : Expr}
    (accepted : SourceCoreCallableIndexedAncestry.expressionHook prepared owner active context source scope node parameter result raw = .ok output) :
    ∃ origin body, prepared.graph.inputs.callable.table.idAt? (.lambda owner node.id active) = some origin ∧
      raw = .lambda parameter (LanguageResult.resultType result) body ∧
      context.owner = owner ∧ context.globals = base.globals ∧ source.owner = owner.declaration ∧
      output = SourceCoreCallableIndexedAncestry.snapshotLambda prepared.graph.table prepared.layout.frame origin
        (SourceCoreCallableIndexedAncestry.creationReferenceIndex context scope) parameter result body :=
  CallableIndexedFormation.expressionHook_receipt prepared accepted

/-- Named entry history comes from the actual owned graph row accepted by the
compiler's named hook, without a prior supplied named metadata derivation. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {function : SourceCoreGeneralFunctions.Function} {body output : Expr}
    (accepted : SourceCoreCallableIndexedAncestry.namedBody prepared function body = .ok output) :
    ∃ origin index metadata,
      prepared.graph.inputs.callable.table.idAt? (.named function.signature.key) = some origin ∧
      Carries prepared.graph.inputs prepared.graph.table (.state index) (.named origin) (some metadata) ∧
      output = withFrame (.var (base.globals.length + 1)) (literal prepared.layout.frame (.state index)) body :=
  CallableIndexedFormation.namedBody_history prepared accepted

/-- The source allocator callback's successful result exposes the original
allocation and its exact source-request reference mapping. -/
example (layout : Layout) (globals : Nat) (allocate : SourceCoreSourceCells.Allocator) (request : SourceCoreSourceCells.Request)
    {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals allocate request = .ok code) :
    ∃ receipt : SourceCoreCallableIndexedAllocationFrames.Annotated layout globals allocate request,
      SourceCoreCallableIndexedAllocationFrames.annotateWithReceipt layout globals allocate request = .ok receipt ∧
      code = SourceCoreCallableIndexedAllocationFrames.snapshotBefore layout
        (.var (SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request)) receipt.original :=
  CallableIndexedAllocation.allocator_receipt layout globals allocate request accepted

/-- Actual wrapper creation preserves identity, descriptor and the original
payload, while saving the caller's occurrence-specific read receipt separately. -/
example {checked : SourceCoreCallableIndexedAncestry.Checked}
    {base : SourceCoreCallableIndexedAncestry.Base checked}
    (prepared : SourceCoreCallableIndexedAncestry.Prepared base)
    {parameter result : Ty} {id target descriptor : Word} {identity payload : Value}
    {caller : NativeFrame} {callerGhost : GhostFrame} {metadata : MetadataState}
    (history : Carries prepared.graph.inputs prepared.graph.table caller callerGhost (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read prepared.graph.inputs metadata id target)
    (readPrepared : SourceCoreCallableAncestryReadRecipes.prepareRead prepared.graph.inputs metadata id target = .ok read) :
    Evaluates [.pair (.pair identity payload) (.word descriptor), .cellRef prepared.layout.frame.type 0]
      [encode prepared.layout.frame caller]
      (SourceCoreCallableIndexedAncestry.viewLower prepared.layout.frame parameter result id target 1
        (LanguageResult.success (.var 0)))
      (.inRight .word (.pair (.pair identity
        (.closure parameter (LanguageResult.resultType result)
          (SourceCoreCallableIndexedAncestry.viewBody prepared.layout.frame id target 1)
          [encode prepared.layout.frame caller, .pair (.pair identity payload) (.word descriptor),
            .pair (.pair identity payload) (.word descriptor), .cellRef prepared.layout.frame.type 0])) (.word descriptor)))
      [encode prepared.layout.frame caller] :=
  (CallableIndexedFormation.viewLower_history prepared history read readPrepared
    (Evaluates.inRight (.var rfl)) rfl rfl).1

end Solcore.Test.SourceCoreCallableIndexedFormation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedHistory
/-! Indexed protocol receipts retain two independent parents and authenticate
only transitions derived from the actual owned graph. No raw table index is
promoted into a runtime-history claim. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedHistory
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory CallableIndexedProtocol
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch

/-- A negative native integer is not a state-table location, even though the
ordinary Core carrier remains well typed. -/
example (table : SourceCoreCallableIndexedDispatch.Table) (negative : Nat) :
    SourceCoreCallableIndexedDispatch.lookup? table (.state (.negSucc negative)) = none := rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {ghost : GhostFrame} {metadata : Option MetadataState} :
    ¬ Carries inputs table .invalid ghost metadata := by intro carried; exact carried.not_invalid rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {table : CallableAncestryPairedLookup.Table} {ghost : GhostFrame} {metadata : Option MetadataState}
    (negative : Nat) : ¬ Carries inputs table (.state (.negSucc negative)) ghost metadata := by
  intro carried; cases carried

/-- A saved stable caller survives a read as its own independent ghost parent. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {native : NativeFrame} {caller : GhostFrame} {metadata : MetadataState} {id target : Word}
    (carried : Carries graph.inputs graph.table native caller (some metadata))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs metadata id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs metadata id target = .ok read) :
    Current graph.inputs graph.table (readFrame id target native) (.view id target caller) :=
  read_history carried read prepared

/-- No successful native transition or lookup is an additional premise here:
real caller/lexical recipe acceptance supplies the cached destination. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerIndex lexicalIndex : Nat} {callerGhost lexicalGhost : GhostFrame}
    {caller lexical : MetadataState} {id target : Word}
    (callerCarried : Carries graph.inputs graph.table (.state (Int.ofNat callerIndex)) callerGhost (some caller))
    (lexicalCarried : Carries graph.inputs graph.table (.state (Int.ofNat lexicalIndex)) lexicalGhost (some lexical))
    (read : SourceCoreCallableAncestryReadRecipes.Read graph.inputs caller id target)
    (prepared : SourceCoreCallableAncestryReadRecipes.prepareRead graph.inputs caller id target = .ok read)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (appliedPrepared : SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied) :
    Carries graph.inputs graph.table
      (selectedFrame graph.table target (.state (Int.ofNat lexicalIndex)) (.view id target (Int.ofNat callerIndex)))
      (.appliedView id target callerGhost lexicalGhost) (some (read.after lexical)) :=
  applied_complete graph callerCarried lexicalCarried read prepared applied appliedPrepared

/-- Actual reference-slot loading leaves the native store unchanged while
selecting from both parents. A closure-producing expression is never weakened. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {currentNative : NativeFrame} {lexicalGhost currentGhost : GhostFrame}
    {metadata : MetadataState} {origin : Word}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (current : Current graph.inputs graph.table currentNative currentGhost)
    (valid : selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative ≠ .invalid) :
    ∃ resultState,
      Evaluates [encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout currentNative]
        (lambdaFrame graph.table layout origin (.var 0) (.loadCell (.var 1)))
        (encode layout (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)) [encode layout currentNative] ∧
      Carries graph.inputs graph.table (selectedFrame graph.table origin (.state (Int.ofNat position)) currentNative)
        (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) :=
  dispatch_load graph (.var rfl) rfl carried ⟨rfl, current⟩ valid

/-- Closure of the prepared cache also covers ordinary entry from an unrelated
stable caller without changing the lexical metadata state. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {native otherNative : NativeFrame} {lexical other : GhostFrame}
    {metadata otherMetadata : MetadataState} {origin : Word}
    (lexicalCarried : Carries graph.inputs graph.table native lexical (some metadata))
    (otherCarried : Carries graph.inputs graph.table otherNative other (some otherMetadata))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed graph.inputs metadata origin = true) :
    Carries graph.inputs graph.table (selectedFrame graph.table origin native otherNative)
      (.lambda origin lexical) (some metadata) := ordinary_complete graph lexicalCarried otherCarried allowed

/-- Reflection consumes an actual completed state carrier, without assuming
that the dispatch validity check passed in advance. -/
example {checked : Checked} {base : Base checked}
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {layout : Layout} {position : Nat} {resultIndex : Int} {currentNative : NativeFrame}
    {lexicalGhost currentGhost : GhostFrame} {metadata : MetadataState} {origin : Word} {after : Store}
    (carried : Carries graph.inputs graph.table (.state (Int.ofNat position)) lexicalGhost (some metadata))
    (current : Current graph.inputs graph.table currentNative currentGhost)
    (evaluated : Evaluates [encode layout (.state (Int.ofNat position)), .cellRef layout.type 0] [encode layout currentNative]
      (lambdaFrame graph.table layout origin (.var 0) (.loadCell (.var 1))) (encode layout (.state resultIndex)) after) :
    after = [encode layout currentNative] ∧ ∃ resultState, Carries graph.inputs graph.table (.state resultIndex)
      (SourceCoreCallablePairedFrames.selectedFrame origin lexicalGhost currentGhost) (some resultState) :=
  dispatch_load_reflects_state graph (.var rfl) rfl carried ⟨rfl, current⟩ evaluated

end Solcore.Test.SourceCoreCallableIndexedHistory
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedNamedValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedNamedValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedNamedValues CompatiblePayload GeneralHeap

/-- Actual validator and canonical resolver success imply equality of complete
source values, with domain order retained as an explicit occurrence receipt. -/
theorem metadata_from_checks {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
    {key : SourceCompilationPlan.Key} {metadata : DeclarationInstantiation} {specialized : Specialized}
    {actual canonical : Evidence}
    (target : SourceCompilationPlan.exactInstantiationKey plan metadata = .ok key)
    (record : SourceCompilationPlan.exactSpecialization plan key = .ok specialized)
    (domain : specialized.parameterSubstitution.map Prod.fst = metadata.parameterSubstitution.map Prod.fst)
    (authenticated : SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key specialized.assumptions actual = .ok ())
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key specialized.assumptions = .ok canonical) :
    (⟨metadata, CallableNamedMetadata.environment actual⟩ : Dynamic.GlobalFunction) = CallableNamedMetadata.global specialized canonical :=
  CallableNamedMetadata.global_eq target record domain authenticated resolved

theorem distinct_dictionary_trees_rejected {program : CheckedProgram} {key : SourceCompilationPlan.Key}
    {predicates : List ProgramPredicate} {actual canonical : Evidence}
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program key predicates = .ok canonical)
    (different : actual ≠ canonical) :
    SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures key predicates actual ≠ .ok () := by
  intro accepted
  exact different (CallableNamedMetadata.authenticated_evidence_eq accepted resolved)

/-- Both named and builtin leaves discharge the comparator's identity and
observation laws, with no invocation or child-evaluation hypothesis. -/
theorem comparison_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

theorem runtime_view_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {mapping : LocationMap} {world : StoreTyping}
    {parameter result : TypeSystem.Ty} {source : Dynamic.Value} {value : Value} {type : Ty}
    (related : (model prepared profile).Represents registry mapping world (.function parameter result) source value type) :
    Dynamic.ValueRuntimeTypeMatches source (.function parameter result) :=
  runtime_views prepared profile related

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Eq<T> {}", "impl Eq<Word> {}", "trait Mark<T> {}", "impl Mark<Word> {}",
    "function first() returns (Bool) { return true; }",
    "function second() returns (Bool) { return false; }",
    "function firstRef() returns (function() returns (Bool)) { return first; }",
    "function secondRef() returns (function() returns (Bool)) { return second; }",
    "function keep<T>(value: T) returns (T) where T: Eq, T: Mark { return value; }",
    "function keepRef() returns (function(Word) returns (Word)) { return keep; }",
    "function pair<A, B>(a: A, b: B) returns (A) { return a; }",
    "function pairRef() returns (function(Word, Bool) returns (Word)) { return pair; }",
    "function nativeAdd(a: integer, b: integer) returns (integer) { return integerAdd(a, b); }",
    "function namedAddRef() returns (function(integer, integer) returns (integer)) { return nativeAdd; }",
    "function builtinAddRef() returns (function(integer, integer) returns (integer)) { return integerAdd; }"
  ]}] }

private def compare {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (sourceType : TypeSystem.Ty) (a b : Value) (expected : Bool) : IO Unit := do
  let comparator ← SourceCompilerFeatureSupport.get "named comparator" (SourceCoreCompatibleDataEquality.prepare 500 checked sourceType)
  let code := CompatibleEquality.comparison comparator (.var 0) (.var 1)
  SourceCompilerFeatureSupport.require (infer? [comparator.type, comparator.type] code prepared.layouts.definitions == some .bool) "named comparator rejected ambient definitions"
  let before : Store := [.word (Word.ofNatModulo 94)]
  let done := runStateful 100000 (.initial code [a,b] before)
  SourceCompilerFeatureSupport.require (done == .done (.bool expected) (CompatibleEquality.preparedStore comparator [a,b] before))
    "named/builtin equality did not preserve full source identity"
  for fuel in [0, 1, 13] do
    match runStateful fuel (.initial code [a,b] before) with
    | .outOfFuel suspended => SourceCompilerFeatureSupport.require (runStateful 100000 suspended == done) "named comparison resume changed result"
    | other => SourceCompilerFeatureSupport.require (other == done) "named comparison prefix changed result"

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey := do
  let found ← match program.signatures.functions.find? (·.name == name) with
    | some found => pure found
    | none => throw (IO.userError s!"missing named fixture {name}")
  pure ⟨found.id, []⟩

private def returned {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (name : String) : IO Value := do
  let target ← key prepared.base.sourceProgram name
  let initial ← SourceCompilerFeatureSupport.get "actual indexed reference return" (prepared.runSource target [] 0)
  let done := initial.resume 300000
  match done.result.native.observation with
  | .succeeded value _ =>
    let direct ← SourceCompilerFeatureSupport.get "direct indexed reference return" (prepared.runSource target [] 300000)
    match direct.result.native.observation with
    | .succeeded expected _ => SourceCompilerFeatureSupport.require (value == expected) "native named output resume changed captures"; pure value
    | other => throw (IO.userError s!"direct reference result {reprStr other}")
  | other => throw (IO.userError s!"named reference result {reprStr other}")

def run : IO Unit := do
  let sourceProgram ← SourceCompilerFeatureSupport.get "named leaf checked source" (checkProgram workspace)
  let seeds := (sourceProgram.signatures.functions.filter (·.scheme.parameters.isEmpty)).map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run sourceProgram seeds 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"named leaf worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "named leaf compatible artifact" (SourceCoreCompatibleFunctions.prepare sourceProgram plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "named leaf indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut observed : List (String × Value) := []
  let mut evidenceCount := 0
  let mut permutedCount := 0
  for name in ["firstRef", "secondRef", "keepRef", "pairRef", "namedAddRef"] do
    let value ← returned prepared name
    observed := observed ++ [(name, value)]
    match value with
    | .pair (.pair (.inRight .unit (.word identity)) (.closure parameter result body captured)) (.word contract) =>
      SourceCompilerFeatureSupport.require (identity.val > 0) "zero named identity"
      let index := identity.val - 1
      let signature ← match prepared.base.globals[index]? with
        | some signature => pure signature | none => throw (IO.userError "named identity outside actual globals")
      let record ← SourceCompilerFeatureSupport.get "canonical named record" (SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key)
      let header := CallableNamedMetadata.instantiation record
      let selected ← SourceCompilerFeatureSupport.get "canonical named target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan header)
      SourceCompilerFeatureSupport.require (decide (selected = signature.key)) "canonical metadata selected different target"
      let evidence ← SourceCompilerFeatureSupport.get "canonical full dictionary" (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment sourceProgram signature.key record.assumptions)
      let _ ← SourceCompilerFeatureSupport.get "authenticate full dictionary" (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence sourceProgram.signatures signature.key record.assumptions evidence)
      if !evidence.isEmpty then
        evidenceCount := evidenceCount + 1
        let changed := evidence.map fun | .byImpl goal _ premises => TraitResolution.Evidence.byImpl goal (.builtin .intWord) premises
        SourceCompilerFeatureSupport.require (match SourceCompilationPlan.validateAuthenticatedRuntimeEvidence sourceProgram.signatures signature.key record.assumptions changed with | .error _ => true | .ok _ => false)
          "same goals with changed evidence trees were accepted"
      if header.parameterSubstitution.length > 1 then
        permutedCount := permutedCount + 1
        let changed := {header with parameterSubstitution := header.parameterSubstitution.reverse}
        SourceCompilerFeatureSupport.require (decide (header ≠ changed)) "two-parameter fixture did not change retained order"
        let keyAgain ← SourceCompilerFeatureSupport.get "order-insensitive actual target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan changed)
        SourceCompilerFeatureSupport.require (decide (keyAgain = selected)) "actual matcher unexpectedly demands canonical list order"
      let descriptor ← SourceCompilerFeatureSupport.get "named owned descriptor" (SourceCoreCallableContracts.descriptor prepared.ancestry.graph.inputs.callable.table (.named signature.key))
      SourceCompilerFeatureSupport.require (contract == descriptor.id) "named carrier descriptor changed"
      let template ← match prepared.secondPass.closures[index]? with
        | some template => pure template | none => throw (IO.userError "missing cached named body")
      SourceCompilerFeatureSupport.require (SourceCoreCompatibleOutputs.installedTemplate index template == .lambda parameter result body)
        "actual named body differs from installed cached code"
      SourceCompilerFeatureSupport.require (!captured.isEmpty) "indexed named closure lost actual administrative captures"
      compare prepared header.type value value true
    | other => throw (IO.userError s!"unexpected named carrier {reprStr other}")
  SourceCompilerFeatureSupport.require (evidenceCount == 1 && permutedCount == 1) "qualified/multi-parameter fixture coverage changed"
  let first := (observed.find? (·.1 == "firstRef")).getD ("", .unit) |>.2
  let second := (observed.find? (·.1 == "secondRef")).getD ("", .unit) |>.2
  compare prepared (.function .unit .bool) first second false
  let namedAdd := (observed.find? (·.1 == "namedAddRef")).getD ("", .unit) |>.2
  let builtinAdd ← returned prepared "builtinAddRef"
  compare prepared BuiltinFunctionId.integerAdd.type namedAdd builtinAdd false
  IO.println "indexed named leaves: full metadata/evidence, permutation boundary, installed captures, mixed identities and resume GREEN"
end Tests.SourceCoreCallableIndexedNamedValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedOrdinaryAllocation
/-! A real accepted marked callback allocates an ordinary source cell at the
native payload index, while the snapshot and marker remain administrative.
The source binder retains its raw type. Complete native definitions and source
payload interpretation are explicit rather than inferred from scalar typing. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedOrdinaryAllocation
open Core Frontend SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly
open CallableIndexedHistory CallableIndexedAllocationCompletion CallableIndexedOrdinaryAllocation

example {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects}
    {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError) request = .ok code)
    (definitions : layouts.definitions = catalog.definitions)
    (registered : layout.Registered catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
    {environment : Dynamic.Environment} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {location : Location} {native : NativeFrame}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope environment canonical)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type location))
    (read : store.read? location = some (SourceCoreCallableIndexedFrames.encode layout native))
    (absent : request.payload = none)
    (projected : projects request.binder.scheme.body request.payloadType) :
    ∃ marker markerType,
      Evaluates actual store code (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2))
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inLeft request.payloadType .unit]) ∧
      GenericHeap.HeapRepresents model (mapping ++ [store.length + 2])
        (world ++ [layout.type, markerType, OptionalCell.cellType request.payloadType])
        ⟨heap.cells ++ [⟨request.binder.scheme.body, none, none⟩]⟩
        (store ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inLeft request.payloadType .unit]) ∧
      DataHeap.EnvRepresents catalog (mapping ++ [store.length + 2])
        (world ++ [layout.type, markerType, OptionalCell.cellType request.payloadType]) administrative
        ((request.binder.id, request.payloadType) :: request.scope)
        ((request.binder.id, ⟨heap.cells.length⟩) :: environment)
        (.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2) :: canonical) := by
  obtain ⟨allocation, annotation, same, emitted⟩ := accepted_receipts onError accepted
  obtain ⟨captured, evaluated, related, allocatedReference, _⟩ :=
    CallableIndexedOrdinaryAllocation.preserves allocation annotation same definitions registered environments agrees heaps
      reference read (.absent absent) (.uninitialized projected) Dynamic.Heap.Allocates.append
  exact ⟨_, _, emitted.symm ▸ evaluated, related, bind_environment environments allocatedReference⟩

/-- Captured source cells can themselves hold functions. Capture typing reads
the finite world's cell-reference type and does not unfold a recursive heap. -/
example (catalog : SourceCoreDataCatalog.Catalog) (first second : Resolved.LocalId)
    (inserted : Value) :
    ∃ captured,
      Captures [inserted, .cellRef (OptionalCell.cellType (.function .unit .unit)) 0,
        .cellRef (OptionalCell.cellType (.function .unit .unit)) 0]
        (fun index => index + 1) [(first, .function .unit .unit), (second, .function .unit .unit)] captured ∧
      RuntimeValueHasType [OptionalCell.cellType (.function .unit .unit)] captured
        (.product (OptionalCell.referenceType (.function .unit .unit))
          (OptionalCell.referenceType (.function .unit .unit))) catalog.definitions := by
  have reference : ReferenceRepresents [0] [OptionalCell.cellType (.function .unit .unit)]
      ⟨0⟩ 0 (.function .unit .unit) := ⟨rfl, rfl⟩
  have environments : DataHeap.EnvRepresents catalog [0] [OptionalCell.cellType (.function .unit .unit)] []
      [(first, .function .unit .unit), (second, .function .unit .unit)] [(first, ⟨0⟩), (second, ⟨0⟩)]
      [.cellRef (OptionalCell.cellType (.function .unit .unit)) 0,
        .cellRef (OptionalCell.cellType (.function .unit .unit)) 0] :=
    .cons reference (.cons reference (.nil .nil))
  exact captures_typed environments (fun found => found)

end Solcore.Test.SourceCoreCallableIndexedOrdinaryAllocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedOutputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Located.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Leaf.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedOutputs.Success.mk

set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev SourceValue := SourceTypedRuntime.Value
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "enum Holder { Hold(Word, F) }",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function tuple(seed: Word) returns (F, F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return (f, f); }",
    "function nominal(seed: Word) returns (Holder) { let f = lam(item) { keep(item); seed += 1; return seed; }; return .Hold(7, f); }",
    "function mappingReturn(value: mapping(Word => F), seed: Word) returns (mapping(Word => F)) { let f = lam(item) { keep(item); seed += 1; return seed; }; value[4] = f; return value; }",
    "function plain(seed: Word) returns (Word, Bool) { return (seed, true); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"deep output fixture missing {name}")
private structure Projected (checked : SourceCoreCompatibleCatalog.Checked)
    (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.function .word .word, none⟩]
private def prefixMatches (heap : List SourceTypedRuntime.Cell) : Bool :=
  reprStr (heap.take initial.length) == reprStr initial

private def closure (plan : SourceSpecializationWorklist.Plan) (value : SourceValue) : IO SourceTypedRuntime.Environment := do
  match value with
  | .instantiated substitution witnesses (.closure parameters _ _ _ _ captured _) =>
    assertTrue (!substitution.isEmpty && witnesses.length == 1) "deep output lost its actual read witnesses"
    assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "deep output specialized its raw original header"
    assertTrue (value.type? plan == some (.function .word .word)) "deep closure restored runtime type changed"
    assertTrue (captured.all (fun binding => initial.length ≤ binding.2.index)) "deep closure referenced opaque source prefix"
    pure captured
  | _ => throw (IO.userError "deep output lost instantiated original closure")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"deep output source rejected: {reprStr error}")
  let roots ← ["tuple", "nominal", "mappingReturn", "plain", "inc"].mapM (key program)
  let requests := roots.map fun owner =>
    (⟨owner.declaration, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"deep output worklist failed: {reprStr other}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"deep output base failed: {reprStr error}")
  let native ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"deep output native preparation failed: {reprStr error}")
  let output ← match SourceCoreCallableIndexedOutputs.prepare native with
    | .ok output => pure output | .error error => throw (IO.userError s!"deep output caches failed: {reprStr error}")
  let cellHeaders ← match SourceCoreCallableIndexedCellHeaders.prepare (program := native) output.graph with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"raw source cell headers failed: {reprStr error}")
  let heapOutput ← match SourceCoreCallableIndexedHeapOutputs.prepare native with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"heap output preparation failed: {reprStr error}")
  let inc ← key program "inc"
  let mapping : SourceValue := .mapping .word (.comptime (.function .word .word))
    [(.word (w 4), .global inc []), (.word (w 4), .global inc [])]
  let fixtures : List (String × List SourceValue) :=
    [("tuple", [.word (w 3)]), ("nominal", [.word (w 3)]),
     ("mappingReturn", [mapping, .word (w 3)]), ("plain", [.word (w 3)])]
  for (name, arguments) in fixtures do
    for budget in [0, 29, 100000] do
      let checkpoint ← match native.runSource (← key program name) arguments budget 500 with
        | .ok completion => pure completion
        | .error error => throw (IO.userError s!"deep output native call failed: {reprStr error}")
      if budget == 0 then
        let early ← match SourceCoreCallableIndexedHeapOutputs.exportHeap heapOutput checkpoint initial with
          | .ok exported => pure exported | .error error => throw (IO.userError s!"early heap export failed: {reprStr error}")
        assertTrue (early.heap.length == initial.length && prefixMatches early.heap) "zero-fuel export changed opaque source prefix"
      let completion := checkpoint.resume 100000
      let projected ← match same : automatic.checked.catalog.project completion.entry.sourceResultType with
        | .error error => throw (IO.userError s!"deep output projection failed: {reprStr error}")
        | .ok type =>
          if equal : type = completion.entry.native.resultType then
            pure (show Projected automatic.checked completion.entry.sourceResultType completion.entry.native.resultType from
              ⟨by simpa only [equal] using same⟩)
          else throw (IO.userError "deep output native result type changed")
      let decoded ← match SourceCoreCallableIndexedOutputs.decodeSuccess output completion completion.entry.sourceResultType
          projected.eq initial 1024 with
        | .ok decoded => pure decoded | .error error => throw (IO.userError s!"deep source output failed: {reprStr error}")
      for row in decoded.ledger.ledger.rows do
        let selected ← match SourceCoreCallableIndexedCellHeaders.select cellHeaders row with
          | .ok selected => pure selected | .error error => throw (IO.userError s!"raw allocation header selection failed: {reprStr error}")
        assertTrue (selected.header.raw.binder.id == row.entry.key.binder.id) "raw source cell header changed binder identity"
      let exported ← match SourceCoreCallableIndexedHeapOutputs.exportHeap heapOutput completion initial with
        | .ok exported => pure exported | .error error => throw (IO.userError s!"paired source heap export failed: {reprStr error}")
      assertTrue (prefixMatches exported.heap) "heap export changed opaque source prefix"
      assertTrue (exported.cells.length == decoded.ledger.ledger.rows.length) "heap export lost source allocation order"
      let genericRows := decoded.ledger.ledger.rows.filter (fun row => !row.entry.key.binder.scheme.quantified.isEmpty)
      if name != "plain" then
        assertTrue (!genericRows.isEmpty) "generic closure fixture no longer records a principal"
      for row in genericRows do
        match exported.heap[row.sourceLocation.index]? with
        | some ⟨_, some (.closure parameters _ _ _ _ captured _)⟩ =>
          assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "heap export specialized original principal"
          assertTrue (captured == row.environment) "heap export changed principal capture order or aliases"
        | _ => throw (IO.userError "heap export lost raw generic principal closure")
      match name, decoded.decoded.source with
      | "tuple", .product left right =>
        let leftEnv ← closure plan left
        let rightEnv ← closure plan right
        assertTrue (leftEnv == rightEnv && leftEnv.length == 1) "deep tuple split the shared seed cell"
      | "nominal", .constructed _ [.word number, value] =>
        assertTrue (number == w 7) "nominal data changed alongside closure restoration"
        assertTrue ((← closure plan value).length == 1) "nominal closure lost source capture"
      | "mappingReturn", .mapping keyType valueType [(.word first, left), (.word second, .global owner _)] =>
        assertTrue (keyType == .word && valueType == .comptime (.function .word .word)) "deep mapping raw metadata changed"
        assertTrue (first == w 4 && second == w 4 && owner == inc) "deep mapping duplicate order changed"
        assertTrue ((← closure plan left).length == 2) "deep mapping closure lost value/seed captures"
      | "plain", .product (.word number) (.bool flag) => assertTrue (number == w 3 && flag) "data-only output changed"
      | _, value => throw (IO.userError s!"unexpected deep source output {name}: {reprStr value}")
      match SourceCoreCallableIndexedOutputs.locate completion decoded.ledger (.word (w 987654321)) with
      | .error .unavailableValue => pure () | _ => throw (IO.userError "foreign value gained native result/payload provenance")
  let hidden := Core.Value.cellRef .word 42
  let carrier := Core.Value.closure .unit .unit .unit [hidden]
  assertTrue (SourceCoreCallableNativeSubvalues.find hidden carrier |>.isNone) "public native path entered a closure environment"
  IO.println "deep indexed tuple/nominal/mapping closure outputs, raw metadata and native data origins GREEN"

end Tests.SourceCoreCallableIndexedOutputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedOwnedFunctionState
/-! Actual pool transitions retain ordered record lists in each original row.
The allocator's reached witness is passed to restoration and to the next
transition; administrative transport preserves its complete observation. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedFunctionState
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionValues CallableIndexedOwnedFunctionEntries CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {initial middle finalIndex : ProtectedStateTransition.Index}

/-- Every retained snapshot is an actual old store cell, so the allocator's
next fresh location cannot already be registered in any input row. -/
theorem fresh_location_unregistered (pool : State headers keys initial)
    (record : CallableIndexedSnapshots.Record)
    (fresh : record.location = initial.store.length) :
    ¬ CallableIndexedAuthorityPool.Pool.Registered pool record := by
  rintro ⟨row, member⟩
  exact fresh_record_absent pool row fresh member

/-- Ordered prefix inclusion retains every original position, including
multiple occurrences of the same snapshot; it permits only an appended suffix. -/
theorem relates_keeps_ordered_row_prefix
    {before : State headers keys initial} {after : State headers keys middle}
    (related : Relates before after) (row : Fin keys.length) :
    (records after row).take (records before row).length = records before row ∧
    ∀ position, position < (records before row).length →
      (records after row)[position]? = (records before row)[position]? := by
  obtain ⟨suffix, appended⟩ := related row
  constructor
  · rw [appended]; simp
  · intro position bound
    rw [appended, List.getElem?_append_left bound]

section AdministrativeEffects
variable {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- Legacy administrative lifting uses this exact transport. Its complete
record observation is unchanged, even if the reached store has new cells. -/
theorem administrative_extension_keeps_observation
    (pool : State headers keys initial)
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap)
    (record : CallableIndexedSnapshots.Record) (fresh : record.location = initial.store.length) :
    let extended := (administrativeTransport headers keys).extend pool maps worlds frame metadata
    records extended = records pool ∧ ¬ CallableIndexedAuthorityPool.Pool.Registered extended record := by
  dsimp only
  have observed := administrative_records pool maps worlds frame metadata
  refine ⟨observed, ?_⟩
  rintro ⟨row, member⟩
  have atRow := congrFun observed row
  change record ∈ records ((administrativeTransport headers keys).extend pool maps worlds frame metadata) row at member
  rw [atRow] at member
  exact fresh_record_absent pool row fresh member

/-- The allocator's appended occurrence cannot be recovered by lifting a
legacy contract through administrative transport. This also detects an
appended duplicate, because the complete list observation keeps multiplicity. -/
theorem actual_append_cannot_be_administrative_post
    (pool : State headers keys initial) (post : State headers keys middle)
    (selected : Fin keys.length) (record : CallableIndexedSnapshots.Record)
    (appended : records post selected = records pool selected ++ [record])
    (maps : LocationMap.Extends initial.mapping mapping) (worlds : WorldExtends initial.world world)
    (frame : AdministrativePreserved initial.mapping initial.store mapping store)
    (metadata : Dynamic.HeapMetadataExtend initial.heap heap) :
    records post ≠ records ((administrativeTransport headers keys).extend pool maps worlds frame metadata) := by
  intro equal
  have sameRow := congrFun (equal.trans (administrative_records pool maps worlds frame metadata)) selected
  have lengths := congrArg List.length sameRow
  rw [appended, List.length_append, List.length_singleton] at lengths
  omega
end AdministrativeEffects

section SnapshotAndRestoration
variable {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
  {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {globals : Nat}
  {allocate : SourceCoreSourceCells.Allocator}
  {environment : Environment} {location : Location} {native : NativeFrame} {ghost : GhostFrame}
  {metadata : Option MetadataState} {payload : Option Value} {futureWorld : StoreTyping} {after : Dynamic.Heap}
  {next : NativeFrame} {nextGhost : GhostFrame}

/-- Real three-cell allocation supplies the first post-witness. An
authenticated mutable-frame write and restoration consume that witness in
sequence. The selected row keeps its appended snapshot, a different row
sharing the frame keeps its own ordered records, and a distinct frame keeps
its reached history. No callable body law is needed for these protocol atoms. -/
theorem actual_snapshot_write_and_restore
    (pool : State headers keys initial) (selected duplicate other : Fin keys.length)
    (duplicateRow : duplicate ≠ selected)
    (sameFrame : keys[duplicate.val].frameLocation = keys[selected.val].frameLocation)
    (differentFrame : keys[other.val].frameLocation ≠ keys[selected.val].frameLocation)
    (allocation : SourceCoreAllocationLayouts.Allocation layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
      globals allocate request)
    (same : annotation.original = allocation.expression)
    (reference : environment[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type location))
    (read : initial.store.read? location = some (encode compiled.indexed.ancestry.layout.frame native))
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table native ghost metadata)
    (bounded : ∀ target ∈ initial.mapping, target < initial.store.length)
    (slots : ∀ position binding, request.scope[position]? = some binding → ∃ target,
      environment[request.references position]? = some (.cellRef (OptionalCell.cellType binding.2) target))
    (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request environment payload)
    (worlds : WorldExtends initial.world futureWorld) (sourceMetadata : Dynamic.HeapMetadataExtend initial.heap after)
    (bodyHistory : Current compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table next nextGhost) :
    ∃ captured,
      let allocatedIndex := initial.extend (initial.mapping ++ [initial.store.length + 2]) futureWorld after
        (initial.store ++ [encode compiled.indexed.ancestry.layout.frame native,
          SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
          CallableIndexedAllocationCompletion.optionalValue request.payloadType payload])
      let writtenIndex := allocatedIndex.extend allocatedIndex.mapping allocatedIndex.world allocatedIndex.heap
        (allocatedIndex.store.set keys[selected.val].frameLocation (encode compiled.indexed.ancestry.layout.frame next))
      let restoredIndex := writtenIndex.extend writtenIndex.mapping writtenIndex.world writtenIndex.heap
        (writtenIndex.store.set keys[selected.val].frameLocation
          (encode compiled.indexed.ancestry.layout.frame (pool.rows selected).authority.current))
      Evaluates environment initial.store annotation.expression
        (.cellRef (OptionalCell.cellType request.payloadType) (initial.store.length + 2)) allocatedIndex.store ∧
      ∃ reached : State headers keys allocatedIndex,
        Relates pool reached ∧
        let written := install reached selected bodyHistory
        let final := restored pool written selected
        Relates pool final ∧ records final = records reached ∧
        records final selected = records pool selected ++ [⟨initial.store.length, native, ghost, metadata⟩] ∧
        records final duplicate = records pool duplicate ∧ records final other = records pool other ∧
        (final.rows duplicate).authority.current = (pool.rows selected).authority.current ∧
        (final.rows duplicate).authority.ghost = (pool.rows selected).authority.ghost ∧
        (final.rows other).authority.current = (written.rows other).authority.current ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame restoredIndex.mapping restoredIndex.store
          ⟨initial.store.length, native, ghost, metadata⟩ ∧
        ProtectedStateTransition.Transition (protocol headers keys) pool restoredIndex := by
  obtain ⟨captured, evaluated, reached, related, appended, unchanged, _⟩ :=
    CallableIndexedOwnedFunctionState.completed_snapshot pool selected allocation annotation same
      reference read history bounded slots payloadAt worlds sourceMetadata
  refine ⟨captured, ?_⟩
  dsimp only
  refine ⟨evaluated, reached, related, ?_⟩
  let written := install reached selected bodyHistory
  let final := restored pool written selected
  have recordsEq : records final = records reached :=
    (CallableIndexedOwnedFunctionState.restored_records pool written selected).trans
      (install_records reached selected bodyHistory)
  have finalRelated : Relates pool final := Relates.trans related
    (Relates.trans (install_related reached selected bodyHistory)
      (restored_related pool written selected))
  have otherRow : other ≠ selected := by
    intro equal
    subst other
    exact differentFrame rfl
  have finalMember : (⟨initial.store.length, native, ghost, metadata⟩ : CallableIndexedSnapshots.Record) ∈ records final selected := by
    rw [recordsEq, appended]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨duplicateCurrent, duplicateGhost⟩ :=
    CallableIndexedOwnedFunctionState.restored_same_frame pool written selected duplicate sameFrame
  have otherCurrent := (CallableIndexedOwnedFunctionState.restored_other_frame pool written selected other differentFrame).1
  refine ⟨finalRelated, recordsEq, ?_, ?_, ?_, duplicateCurrent, duplicateGhost, otherCurrent,
    record_snapshot final selected finalMember, ?_⟩
  · rw [recordsEq]; exact appended
  · rw [recordsEq]; exact unchanged duplicate duplicateRow
  · rw [recordsEq]; exact unchanged other otherRow
  · have first := ProtectedStateTransition.Transition.of_related (protocol headers keys) related
    have second := ProtectedStateTransition.Transition.then (protocol headers keys) first
      (fun actualPost _ => install_transition actualPost selected bodyHistory)
    exact ProtectedStateTransition.Transition.then (protocol headers keys) second
      (fun actualPost _ => restored_transition pool actualPost selected)
end SnapshotAndRestoration

end Tests.SourceCoreCallableIndexedOwnedFunctionState
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedOwnedFunctions
/-! Consumers of actual owned-value producers and reached-pool restoration.
The value receipts retain source dictionaries and complete native captures;
restoration keeps records produced during the body in every original row. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedFunctions
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CompatibleEquality CallableIndexedHistory
open CallableIndexedLambdaValues CallableIndexedOwnedFunctionValues

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {bodyRegistry : SourceCoreRawMetadata.Registry} {faults : FunctionCalls.FaultRep}
  {mapping : LocationMap} {world : StoreTyping} {heap : Dynamic.Heap} {store : Store}

/-- A named value exposes the ordered source dictionary, exact source frame,
and both canonical and actual references to its immutable physical owner. -/
theorem named_source_and_capture {sourceType : TypeSystem.Ty} {source : Dynamic.GlobalFunction}
    {native : Value} {type : Ty}
    (related : CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults
      mapping world sourceType (.global source) native type) :
    ∃ owner : OwnedKey keys, ∃ header : CallableIndexedOwnedFunctionValues.Header compiled program, ∃ identity,
      ∃ capture : NamedCapture headers owner.key header mapping world,
      ∃ descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
          (.named header.named.signature.key),
        header ∈ headers ∧
        header.function.evidence = source.evidence ∧
        NamedCalls.SourceFrame program source.instantiation header.sourceBody header.function ∧
        LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
          header.named.signature.key [] header.function.source ∧
        NodeOccurrencesUnique header.function.source ∧
        capture.canonical[header.globals]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        capture.captured[capture.embedding compiled.indexed.base.globals.length]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        NamedInstalledCode capture ∧
        compiled.compatible.checked.catalog.project sourceType = .ok type ∧
        native = .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
          (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id) := by
  obtain ⟨owner, header, _, identity, capture, descriptor, member, sourceAt, installed,
    _, projected, _, sourceType, native, type⟩ :=
    CallableIndexedOwnedFunctionValues.Represents.named_payload_inv related
  refine ⟨owner, header, identity, capture, descriptor, member, sourceAt.dictionary, sourceAt.frame,
    sourceAt.sourceOrigin, sourceAt.unique, capture.reference, capture.capturedReference, installed, ?_, native⟩
  simpa only [sourceType, type] using projected

/-- Anonymous inversion keeps the body registry, source origin, physical
owner reference, and the complete environment in the emitted closure. -/
theorem lambda_source_and_capture {sourceType : TypeSystem.Ty} {function : Dynamic.Closure}
    {native : Value} {type : Ty}
    (related : CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults
      mapping world sourceType (.closure function) native type) :
    ∃ owner : OwnedKey keys, ∃ scope actual,
      ∃ (captured : Captures compiled.indexed mapping world scope function.captured actual)
        (code : Code compiled.indexed function scope captured.administrative)
        (history : History code) (body : StaticSupport headers bodyRegistry faults code),
        LambdaSourceAlignment.SourceReceipt compiled.sourceProgram compiled.indexed.base.plan
          code.compilation.owner code.active function.source ∧
        NodeOccurrencesUnique function.source ∧
        history.metadata = CallableIndexedNamedGeneration.state body.1.named ∧
        captured.canonical[code.referenceIndex]? = some
          (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
        sourceType = FunctionValues.sourceType function ∧
        native = .pair (.pair (.inLeft .word .unit)
          (.closure code.receipt.parameterCore (LanguageResult.resultType code.receipt.resultCore)
            (code.body.rename captured.embedding.lift.lift)
            (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame history.native :: actual)))
          (.word code.descriptor.id) ∧
        type = CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore := by
  obtain ⟨owner, scope, actual, _, captured, code, history, body, origin,
    globals, referenceIndex, sourceType, native, type⟩ :=
    CallableIndexedOwnedFunctionValues.Represents.closure_inv related
  refine ⟨owner, scope, actual, captured, code, history, body, origin.source,
    origin.unique, origin.historyMetadata, ?_, sourceType, native, type⟩
  rw [referenceIndex]
  exact globals.reference

/-- A valid weak representation or native type cannot create an owned named
value when no catalogue key has been registered. -/
theorem no_named_owner_without_registered_key {sourceType : TypeSystem.Ty}
    {source : Dynamic.GlobalFunction} {native : Value} {type : Ty} :
    ¬ CallableIndexedOwnedFunctionValues.Represents headers [] bodyRegistry faults
      mapping world sourceType (.global source) native type := by
  intro related
  obtain ⟨owner, _⟩ := CallableIndexedOwnedFunctionValues.Represents.named_inv related
  exact Nat.not_lt_zero _ owner.position.isLt

/-- An anonymous value has the same registration boundary even if a native
closure is independently well typed and has a decodable descriptor. -/
theorem no_lambda_owner_without_registered_key {sourceType : TypeSystem.Ty}
    {function : Dynamic.Closure} {native : Value} {type : Ty} :
    ¬ CallableIndexedOwnedFunctionValues.Represents headers [] bodyRegistry faults
      mapping world sourceType (.closure function) native type := by
  intro related
  obtain ⟨owner, _⟩ := CallableIndexedOwnedFunctionValues.Represents.closure_inv related
  exact Nat.not_lt_zero _ owner.position.isLt

/-- A reached owned row supplies the complete named capture and its live
closure read, tying the pure owner token to actual pool authority. -/
theorem reached_owner_supplies_full_capture
    (pool : CallableIndexedOwnedFunctionEntries.OwnedPool headers keys mapping world heap store)
    (owner : OwnedKey keys) {header : CallableIndexedOwnedFunctionValues.Header compiled program}
    (member : header ∈ headers) :
    ∃ capture : NamedCapture headers owner.key header mapping world,
      store.read? (owner.key.locations header) = some (.inRight .unit
        (.closure header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType)
          (header.code.rename capture.embedding.lift) capture.captured)) ∧
      capture.captured[capture.embedding compiled.indexed.base.globals.length]? = some
        (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
      Dynamic.EnvironmentAgrees heap header.function.context.locals [] := by
  obtain ⟨capture⟩ := CallableIndexedOwnedFunctionEntries.capture_from_pool pool owner member
  exact ⟨NamedCapture.of_capture capture, capture.read, capture.capturedReference, capture.locals⟩

section NamedRead
variable {header : CallableIndexedOwnedFunctionValues.Header compiled program}
  {rawD : SourceTypedRuntime.RuntimeEvidenceEnvironment}
  {identity internalReason : Word} {callerPrefix : Nat} {scope : SourceCoreLocalCell.Scope}
  {canonical actual : Environment} {xi : Renaming}

/-- A real catalogue read produces an owned function with equality support.
Static installed code is checked against the cached template, while the
source dictionary comes from the actual named row and its header. -/
theorem qualified_named_read_is_owned
    (owner : OwnedKey keys) (member : header ∈ headers)
    (entry : RecursiveNamedCatalog.Entry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix callerPrefix scope mapping world heap store canonical)
    (capture : RecursiveNamedCatalog.Capture (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix owner.key.frameLocation header mapping world heap store)
    (agrees : EnvironmentsAgree xi canonical actual)
    (row : CallableIndexedNamedValues.Row compiled.indexed header.slot
      header.named.signature header.named.specialized rawD)
    (canonicalHeader : header.instantiation = CallableNamedMetadata.instantiation header.named.specialized)
    (dictionary : header.function.evidence = (CallableNamedMetadata.global header.named.specialized rawD).evidence)
    (cached : compiled.indexed.secondPass.closures[header.slot]? = some
      (.lambda header.named.signature.parameterType (LanguageResult.resultType header.named.signature.resultType) header.code))
    (embedding : capture.embedding = RecursiveGlobalInitializationMeaning.shift header.slot)
    (number : Word.ofNat? (header.slot + 1) = some identity)
    (projection : compiled.compatible.checked.catalog.project header.named.specialized.function.type = .ok
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType))
    (descriptor : SourceCoreCallableContracts.Descriptor compiled.indexed.ancestry.graph.inputs.callable.table
      (.named header.named.signature.key))
    (typed : RuntimeValueHasType world (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType) (header.code.rename capture.embedding.lift) capture.captured)
      header.named.signature.functionType compiled.indexed.layouts.definitions)
    (profile : compiled.compatible.checked.catalog.callableContracts = true) :
    let source := CallableNamedReversal.global (CallableNamedMetadata.global header.named.specialized rawD)
    let carrier := .pair (.pair (.inRight .unit (.word identity)) (.closure header.named.signature.parameterType
      (LanguageResult.resultType header.named.signature.resultType)
      (header.code.rename capture.embedding.lift) capture.captured)) (.word descriptor.id)
    let expression := LanguageResult.bind
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (SourceCoreFunctions.namedReference header.named.signature
        (xi (scope.length + callerPrefix + header.slot)) identity internalReason)
      (LanguageResult.success (descriptor.wrap (.var 0)))
    Evaluates actual store expression (.inRight .word carrier) store ∧
    CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults mapping world
      header.named.specialized.function.type (.global source) carrier
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType) ∧
    Observation compiled.compatible.checked.catalog bodyRegistry
      (CallableIndexedLambdaValues.Identity compiled.indexed)
      (CallableContract.functionType header.named.signature.parameterType header.named.signature.resultType)
      (.global source) carrier ∧
    (∀ result finalStore, Evaluates actual store expression result finalStore →
      result = .inRight .word carrier ∧ finalStore = store) := by
  dsimp only
  have sourceAt := NamedSourceAt.of_canonical_header row canonicalHeader dictionary
  have installed := NamedInstalledCode.of_cached (NamedCapture.of_capture capture) cached embedding
  obtain ⟨evaluation, related, deterministic⟩ := CallableIndexedOwnedFunctionValues.named_of_read
    (bodyRegistry := bodyRegistry) (faults := faults) owner member entry capture agrees sourceAt
    installed number projection descriptor typed
  exact ⟨evaluation, related,
    CallableIndexedOwnedFunctionValues.observations keys bodyRegistry faults profile related, deterministic⟩
end NamedRead

section LambdaFormation
variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
  {actual : Environment} {callerPrefix : Nat}

/-- Formation consumes a reached owner row and generated static support, and
copies the captured cells. The formed value supports source runtime guards and
remains owned when the explicit key domain grows. -/
theorem literal_formation_retains_owner
    (pool : CallableIndexedAuthorityPool.Pool (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers keys mapping world heap store)
    (owner : OwnedKey keys) (captured : Captures compiled.indexed mapping world scope function.captured actual)
    (code : Code compiled.indexed function scope captured.administrative) (history : History code)
    (body : StaticSupport headers bodyRegistry faults code)
    (metadata : history.metadata = CallableIndexedNamedGeneration.state body.1.named)
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (referenceIndex : code.referenceIndex = scope.length + 1 + compiled.indexed.base.globals.length)
    (current : (pool.rows owner.position).authority.current = history.native)
    (ghost : (pool.rows owner.position).authority.ghost = history.ghost)
    (profile : compiled.compatible.checked.catalog.callableContracts = true)
    {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel (CompatibleEquality.storageCatalog compiled.compatible.checked.catalog) projects
      compiled.indexed.layouts.definitions}
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (copied : code.policy.snapshotLambda code.id = true)
    (ordinary : Dynamic.OrdinaryRequirementLayout code.sourceNode.requirements code.sourceNode.coercions [])
    (coercions : code.sourceNode.coercions = [])
    (extra : List (CallableIndexedOwnedFunctionValues.Key compiled program)) :
    ∃ formed : Formed model captured code history heap store owner.key.frameLocation,
      Dynamic.ExpressionEvaluates program function.context function.evidence function.source function.captured heap
        code.id (.closure formed.closure) formed.finalHeap ∧
      Evaluates actual store (code.lowered.expression.rename captured.embedding)
        (.inRight .word (value code formed.embedding history.native formed.closureActual)) formed.finalStore ∧
      CallableIndexedOwnedFunctionValues.Represents headers keys bodyRegistry faults formed.finalMap formed.finalWorld
        (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      CallableIndexedOwnedFunctionValues.Represents headers (keys ++ extra) bodyRegistry faults formed.finalMap
        formed.finalWorld (FunctionValues.sourceType function) (.closure formed.closure)
        (value code formed.embedding history.native formed.closureActual)
        (CallableContract.functionType code.receipt.parameterCore code.receipt.resultCore) ∧
      Dynamic.ValueRuntimeTypeMatches (.closure formed.closure) (FunctionValues.sourceType function) ∧
      (KeyEmbedding.append keys extra |>.map owner).key = owner.key := by
  have origin := ActualSourceOrigin.of_support history body metadata
  obtain ⟨formed, sourceTrace, nativeTrace, related, _⟩ := CallableIndexedOwnedFunctionValues.lambda_of_formation
    pool owner captured code history body origin globals referenceIndex current ghost profile heaps copied ordinary coercions
  exact ⟨formed, sourceTrace, nativeTrace, related,
    CallableIndexedOwnedFunctionValues.Represents.map_keys (KeyEmbedding.append keys extra) related,
    CallableIndexedOwnedFunctionValues.runtime_views keys bodyRegistry faults profile (registry := bodyRegistry) related,
    (KeyEmbedding.append keys extra).same owner⟩
end LambdaFormation

section OwnedPrefixes
open CallableIndexedOwnedFunctionEntries

/-- Actual named parameter allocation uses the represented capture's full
canonical environment and administrative context. The generated prefix
retains its owner's original snapshots without an extra catalogue read. -/
theorem named_parameters_keep_original_capture
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    {header : CallableIndexedOwnedFunctionValues.Header compiled program} (member : header ∈ headers)
    (capture : NamedCapture headers owner.key header mapping world)
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value} {payloads : List Value}
    {actual : Environment} {actualContext : Core.Context} {xi : Renaming}
    (represented : CallableIndexedParameterMeaning.Arguments
      (CompatibleAmbientHeap.payloadModel compiled.compatible.checked registry functions)
      mapping world header.bindings arguments payloads)
    (heaps : CompatibleAmbientHeap.HeapRepresents compiled.compatible.checked registry functions mapping world heap store)
    (agrees : EnvironmentsAgree xi (DataPatternValues.packValues payloads :: capture.canonical) actual)
    (actualTyped : RuntimeEnvironmentHasTypes world actual actualContext compiled.indexed.layouts.definitions)
    (record : CallableIndexedSnapshots.Record)
    (recordMember : record ∈ (pool.rows owner.position).authority.records) :
    ∃ entry : RecursiveNamedCatalog.ParameterEntry (prepared := compiled.indexed.ancestry)
      (values := .initial compiled.compatible.checked)
      (ambient := CallableIndexedAmbient.ambientDefinitions compiled.indexed)
      headers owner.key.locations owner.key.capturePrefix functions registry header arguments heap store mapping world
      capture.administrative actualContext actual xi owner.key.frameLocation
      (pool.rows owner.position).authority.current (pool.rows owner.position).authority.ghost,
      DataHeap.EnvRepresents (storageCatalog compiled.compatible.checked.catalog) entry.mapping entry.world
        (SourceCoreCompatibleCatalog.packTypes (header.bindings.map Prod.snd) :: capture.administrative)
        (header.bindings.reverse.map (fun binding => (binding.1.id, binding.2))) entry.environment entry.canonical
        compiled.indexed.layouts.definitions ∧
      (named_parameter_catalog pool owner capture entry).authority.frameLocation = owner.key.frameLocation ∧
      (named_parameter_catalog pool owner capture entry).authority.records = (pool.rows owner.position).authority.records ∧
      CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
        compiled.indexed.ancestry.layout.frame entry.mapping entry.store record := by
  obtain ⟨entry⟩ := named_parameters pool owner member capture represented heaps agrees actualTyped
  have retained : record ∈ ((named_parameter_pool pool owner capture entry).rows owner.position).authority.records := by
    rw [named_parameter_pool_records]; exact recordMember
  refine ⟨entry, entry.environments, named_parameter_catalog_owner_frame pool owner capture entry, ?_,
    ((named_parameter_pool pool owner capture entry).rows owner.position).authority.snapshots record retained⟩
  rw [named_parameter_catalog_records, named_parameter_pool_records]

/-- The actual sized lambda prefix keeps its generated source history and
full metadata, with the same selected records as its reached pool. -/
theorem sized_lambda_prefix_keeps_source_history
    {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
    {captured : Captures compiled.indexed mapping world scope function.captured actual}
    {code : Code compiled.indexed function scope captured.administrative} {history : History code}
    {inputs : CallableIndexedLambdaEntryPrefix.Context (values := .initial compiled.compatible.checked) code}
    {functions : FunctionModel compiled.compatible.checked.catalog (CallableIndexedAmbient.ambientDefinitions compiled.indexed)}
    {registry : SourceCoreRawMetadata.Registry} {arguments : List Dynamic.Value}
    (pool : OwnedPool headers keys mapping world heap store) (owner : OwnedKey keys)
    (reached : CallableIndexedLambdaEntryBounds.PrefixFor (values := .initial compiled.compatible.checked)
      captured code history inputs functions registry arguments heap store owner.key.frameLocation
      (pool.rows owner.position).authority.current)
    {callerPrefix : Nat}
    (globals : CallableIndexedLambdaCatalogEntries.CaptureGlobals (prepared := compiled.indexed)
      (values := .initial compiled.compatible.checked) (program := program)
      headers owner.key.locations callerPrefix scope captured.canonical owner.key.frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (recordMember : record ∈ (pool.rows owner.position).authority.records) :
    let sourceEntry := ordinary_source_entry_sized pool owner reached globals
    sourceEntry.catalog.authority.records = ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records ∧
    sourceEntry.catalog.authority.ghost = .lambda code.descriptor.id history.ghost ∧
    Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      sourceEntry.catalog.authority.current (.lambda code.descriptor.id history.ghost) (some history.metadata) ∧
    reached.canonical[(code.receipt.loweredParameters.reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope).length
        + 1 + compiled.indexed.base.globals.length]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type owner.key.frameLocation) ∧
    CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      compiled.indexed.ancestry.layout.frame reached.mapping reached.store record := by
  dsimp only
  let sourceEntry := ordinary_source_entry_sized pool owner reached globals
  have retained : record ∈ ((ordinary_pool_sized pool owner reached).rows owner.position).authority.records := by
    rw [ordinary_pool_sized_records]; exact recordMember
  refine ⟨ordinary_source_entry_sized_records pool owner reached globals, sourceEntry.ghost,
    sourceEntry.carried, ?_, ((ordinary_pool_sized pool owner reached).rows owner.position).authority.snapshots record retained⟩
  have reference := sourceEntry.reference
  rw [ordinary_source_entry_sized_frame_eq] at reference
  exact reference
end OwnedPrefixes

section ReachedRestoration
open SourceCoreCallableIndexedFrames CallableIndexedOwnedFunctionEntries

variable {checked : SourceCoreCompatibleCatalog.Checked} {base : SourceCoreCompatibleFunctions.Prepared checked}
  {prepared : SourceCoreCallableIndexedAncestry.Prepared base} {values : SourceCoreCompatibleValues.Context}
  {ambient : AmbientDefinitions values.checked.catalog.definitions}
  {poolHeaders : RecursiveNamedCatalog.Inventory prepared values ambient.definitions program}
  {poolKeys : List (CallableIndexedAuthorityPool.Key prepared values ambient.definitions program)}
  {futureMap : LocationMap} {futureWorld : StoreTyping} {after : Dynamic.Heap} {futureStore : Store}

/-- A record created during a body remains a protected snapshot after restore.
Every row sharing the selected physical frame receives the saved history;
a distinct physical row keeps its reached history and record list. -/
theorem restore_retains_body_records
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected duplicate other row : Fin poolKeys.length)
    (same : poolKeys[duplicate.val].frameLocation = poolKeys[selected.val].frameLocation)
    (different : poolKeys[other.val].frameLocation ≠ poolKeys[selected.val].frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (produced : record ∈ (reached.rows row).authority.records) :
    let restored := restored_pool saved reached selected
    record ∈ (restored.rows row).authority.records ∧
    CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame futureMap
      (futureStore.set poolKeys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) record ∧
    (restored.rows selected).authority.current = (saved.rows selected).authority.current ∧
    (restored.rows duplicate).authority.current = (saved.rows selected).authority.current ∧
    (restored.rows duplicate).authority.ghost = (saved.rows selected).authority.ghost ∧
    (restored.rows other).authority.current = (reached.rows other).authority.current ∧
    (restored.rows other).authority.ghost = (reached.rows other).authority.ghost ∧
    (restored.rows other).authority.records = (reached.rows other).authority.records := by
  dsimp only
  have retained : record ∈ ((restored_pool saved reached selected).rows row).authority.records := by
    rw [restored_records]
    exact produced
  refine ⟨retained, ((restored_pool saved reached selected).rows row).authority.snapshots record retained,
    ?_, ?_, ?_, ?_, ?_, restored_records saved reached selected other⟩
  · rw [restored_current]; simp
  · rw [restored_current]; simp only [same, ↓reduceIte]
  · rw [restored_ghost]; simp only [same, ↓reduceIte]
  · rw [restored_current]; simp only [different, ↓reduceIte]
  · rw [restored_ghost]; simp only [different, ↓reduceIte]

/-- The actual restore boundary also retains the final source heap and its
new snapshots, while reinstating shared history at the selected physical cell. -/
theorem actual_restore_retains_body_effects
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected duplicate other row : Fin poolKeys.length)
    (same : poolKeys[duplicate.val].frameLocation = poolKeys[selected.val].frameLocation)
    (different : poolKeys[other.val].frameLocation ≠ poolKeys[selected.val].frameLocation)
    (record : CallableIndexedSnapshots.Record)
    (produced : record ∈ (reached.rows row).authority.records)
    {next : NativeFrame} {functions : FunctionModel values.checked.catalog ambient}
    {registry : SourceCoreRawMetadata.Registry}
    (registered : prepared.layout.frame.Registered ambient.definitions)
    (heaps : CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after futureStore)
    (worlds : WorldExtends world futureWorld)
    (frame : AdministrativePreserved mapping
      (store.set poolKeys[selected.val].frameLocation (encode prepared.layout.frame next)) futureMap futureStore) :
    let restoredStore := futureStore.set poolKeys[selected.val].frameLocation
      (encode prepared.layout.frame (saved.rows selected).authority.current)
    ∃ finalPool : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after restoredStore,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions futureMap futureWorld after restoredStore ∧
      AdministrativePreserved mapping store futureMap restoredStore ∧
      record ∈ (finalPool.rows row).authority.records ∧
      CallableIndexedSnapshots.Holds prepared.graph.inputs prepared.graph.table prepared.layout.frame
        futureMap restoredStore record ∧
      (finalPool.rows duplicate).authority.current = (saved.rows selected).authority.current ∧
      (finalPool.rows other).authority.current = (reached.rows other).authority.current ∧
      (finalPool.rows other).authority.records = (reached.rows other).authority.records := by
  dsimp only
  obtain ⟨finalPool, _, finalHeaps, finalFrame, _, records, currents, _, _⟩ :=
    restore_reached_pool saved reached selected registered heaps worlds frame
  have retained : record ∈ (finalPool.rows row).authority.records := by
    rw [records row]; exact produced
  refine ⟨finalPool, finalHeaps, finalFrame, retained, (finalPool.rows row).authority.snapshots record retained,
    ?_, ?_, records other⟩
  · rw [currents duplicate]; simp only [same, ↓reduceIte]
  · rw [currents other]; simp only [different, ↓reduceIte]

/-- Original records and newly reached records coexist after restore, using
membership extension rather than an equality assumption on record lists. -/
theorem restore_retains_original_and_new
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected row : Fin poolKeys.length) (retained : RecordsExtend saved reached)
    (original fresh : CallableIndexedSnapshots.Record)
    (oldMember : original ∈ (saved.rows row).authority.records)
    (newMember : fresh ∈ (reached.rows row).authority.records) :
    original ∈ ((restored_pool saved reached selected).rows row).authority.records ∧
    fresh ∈ ((restored_pool saved reached selected).rows row).authority.records := by
  constructor
  · exact RecordsExtend.restored saved reached selected retained row original oldMember
  · rw [restored_records]; exact newMember

/-- The body restore write preserves the exact full closure, even for a
catalogue row with a different physical owner and an unused capture suffix. -/
theorem restore_retains_full_capture
    (saved : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys mapping world heap store)
    (reached : CallableIndexedAuthorityPool.Pool poolHeaders poolKeys futureMap futureWorld after futureStore)
    (selected row : Fin poolKeys.length)
    {header : RecursiveNamedCatalog.Header prepared values ambient.definitions program}
    (member : header ∈ poolHeaders)
    (capture : RecursiveNamedCatalog.Capture poolHeaders poolKeys[row.val].locations poolKeys[row.val].capturePrefix
      (reached.rows row).authority.frameLocation header futureMap futureWorld after futureStore) :
    Store.read? (futureStore.set poolKeys[selected.val].frameLocation
        (encode prepared.layout.frame (saved.rows selected).authority.current)) (poolKeys[row.val].locations header) =
      some (.inRight .unit (.closure header.named.signature.parameterType
        (LanguageResult.resultType header.named.signature.resultType)
        (header.code.rename capture.embedding.lift) capture.captured)) :=
  restored_capture_read saved reached selected row member capture
end ReachedRestoration

end Tests.SourceCoreCallableIndexedOwnedFunctions
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedOwnedOrdinaryAllocation
/-! The actual ordinary source allocation registers one snapshot and binds
only its payload reference. Removing that source binder consumes the reached
pool and retains its full ordered row histories in the same heap and store. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedOwnedOrdinaryAllocation
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload CallableIndexedHistory SourceCoreCallableIndexedFrames
open CallableIndexedOwnedFunctionState

variable {compiled : SourceCoreUnifiedCompilation.Compiled} {program : SourceSemantics.Program}
  {headers : List (CallableIndexedOwnedFunctionValues.Header compiled program)}
  {keys : List (CallableIndexedOwnedFunctionValues.Key compiled program)}
  {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
  {model : GenericHeap.PayloadModel catalog projects compiled.indexed.layouts.definitions}
  {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
  {request : SourceCoreSourceCells.Request} {globals : Nat} {allocate : SourceCoreSourceCells.Allocator}
  {mapping : LocationMap} {world : StoreTyping} {administrative : Core.Context}
  {sourceEnvironment : Dynamic.Environment} {canonical actual : Environment}
  {before after : Dynamic.Heap} {store : Store} {metadata : Option MetadataState}
  {payload : Option Value} {sourceValue : Option Dynamic.Value} {sourceLocation : Dynamic.Location}

/-- Real allocator and source-allocation receipts supply the execution and
post-state. The fresh record remains registered after lexical restoration;
another row sharing the physical frame retains its own distinct history list.
The arbitrary original heap model and all old ordered occurrences survive. -/
theorem actual_bind_then_remove_source_binder
    (allocation : SourceCoreAllocationLayouts.Allocation compiled.indexed.layouts owner active request)
    (annotation : SourceCoreCallableIndexedAllocationFrames.Annotated compiled.indexed.ancestry.layout.frame
      globals allocate request)
    (same : annotation.original = allocation.expression)
    (registered : compiled.indexed.ancestry.layout.frame.Registered compiled.indexed.layouts.definitions)
    (initial : State headers keys ⟨request.scope, mapping, world, before, store, canonical⟩)
    (selected duplicate : Fin keys.length) (differentRow : duplicate ≠ selected)
    (sharedFrame : keys[duplicate.val].frameLocation = keys[selected.val].frameLocation)
    (history : Carries compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
      (initial.rows selected).authority.current (initial.rows selected).authority.ghost metadata)
    (environments : DataHeap.EnvRepresents catalog mapping world administrative request.scope
      sourceEnvironment canonical compiled.indexed.layouts.definitions)
    (agrees : EnvironmentsAgree request.references canonical actual)
    (heaps : GenericHeap.HeapRepresents model mapping world before store)
    (reference : actual[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef compiled.indexed.ancestry.layout.frame.type keys[selected.val].frameLocation))
    (payloadAt : CallableIndexedAllocationCompletion.PayloadAt request actual payload)
    (cell : GenericHeap.CellRepresents model mapping world
      ⟨request.binder.scheme.body, sourceValue, none⟩
      (CallableIndexedAllocationCompletion.optionalValue request.payloadType payload) request.payloadType)
    (allocated : Dynamic.Heap.Allocates before request.binder.scheme.body sourceValue sourceLocation after) :
    ∃ captured,
      let reachedIndex : ProtectedStateTransition.Index :=
        ⟨request.scope, mapping ++ [store.length + 2],
          world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
            OptionalCell.cellType request.payloadType], after,
          store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
            SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
            CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩
      let payloadReference := Value.cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)
      let fresh : CallableIndexedSnapshots.Record :=
        ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
      CallableIndexedAllocationCompletion.Captures actual request.references request.scope captured ∧
      RuntimeValueHasType world captured (SourceCoreSourceCells.captureType request.scope)
        compiled.indexed.layouts.definitions ∧
      Evaluates actual store annotation.expression payloadReference reachedIndex.store ∧
      GenericHeap.HeapRepresents model reachedIndex.mapping reachedIndex.world reachedIndex.heap reachedIndex.store ∧
      ReferenceRepresents reachedIndex.mapping reachedIndex.world sourceLocation (store.length + 2) request.payloadType ∧
      AdministrativePreserved mapping store reachedIndex.mapping reachedIndex.store ∧
      ∃ bound : State headers keys (reachedIndex.prepend request.binder.id request.payloadType payloadReference),
        Relates initial bound ∧
        let final : State headers keys reachedIndex :=
          (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
            (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
        Relates initial final ∧ records final = records bound ∧
        DataHeap.EnvRepresents catalog reachedIndex.mapping reachedIndex.world administrative
          request.scope sourceEnvironment canonical compiled.indexed.layouts.definitions ∧
        records final selected = records initial selected ++ [fresh] ∧
        (records final selected).take (records initial selected).length = records initial selected ∧
        (∀ i, i ≠ selected → records final i = records initial i) ∧
        (final.rows duplicate).authority.frameLocation = (final.rows selected).authority.frameLocation ∧
        records final selected ≠ records final duplicate ∧
        ¬ CallableIndexedAuthorityPool.Pool.Registered initial fresh ∧
        fresh ∈ records final selected ∧
        CallableIndexedAuthorityPool.Pool.Registered final fresh ∧
        CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
          compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store fresh ∧
        fresh.location ∉ reachedIndex.mapping ∧
        (∀ i : Fin keys.length, fresh.location ≠ keys[i.val].frameLocation) ∧
        (∀ i record, record ∈ records initial i →
          CallableIndexedSnapshots.Holds compiled.indexed.ancestry.graph.inputs compiled.indexed.ancestry.graph.table
            compiled.indexed.ancestry.layout.frame reachedIndex.mapping reachedIndex.store record) ∧
        ProtectedStateTransition.Transition (protocol headers keys) initial reachedIndex := by
  obtain ⟨captured, captures, capturedTyped, evaluated, finalHeaps, mapped, _boundEnvironments, frame,
      bound, boundRelated, appended, unchanged⟩ :=
    CallableIndexedOwnedOrdinaryAllocation.completed_bind allocation annotation same registered initial selected
      history environments agrees heaps reference payloadAt cell allocated
  refine ⟨captured, ?_⟩
  dsimp only
  let reachedIndex : ProtectedStateTransition.Index :=
    ⟨request.scope, mapping ++ [store.length + 2],
      world ++ [compiled.indexed.ancestry.layout.frame.type, allocation.entry.layout.type,
        OptionalCell.cellType request.payloadType], after,
      store ++ [encode compiled.indexed.ancestry.layout.frame (initial.rows selected).authority.current,
        SourceCoreHeapMarkers.markerValue allocation.entry.layout captured,
        CallableIndexedAllocationCompletion.optionalValue request.payloadType payload], canonical⟩
  let fresh : CallableIndexedSnapshots.Record :=
    ⟨store.length, (initial.rows selected).authority.current, (initial.rows selected).authority.ghost, metadata⟩
  let final : State headers keys reachedIndex :=
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
            (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
  have finalRecords : records final = records bound :=
    (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_records (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound
  have finalRelated : Relates initial final := Relates.trans boundRelated
    ((CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_related (index := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) bound)
  have selectedAppend : records final selected = records initial selected ++ [fresh] := by
    rw [finalRecords]
    exact appended
  have freshMember : fresh ∈ records final selected := by
    rw [selectedAppend]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  have freshOriginallyAbsent : ¬ CallableIndexedAuthorityPool.Pool.Registered initial fresh := by
    rintro ⟨row, member⟩
    exact fresh_record_absent initial row rfl member
  have duplicateUnchanged : records final duplicate = records initial duplicate := by
    rw [finalRecords]
    exact unchanged duplicate differentRow
  have freshHolds := record_snapshot final selected freshMember
  refine ⟨captures, capturedTyped, evaluated, finalHeaps, mapped, frame, bound, boundRelated,
    finalRelated, finalRecords, environments.extend ⟨_, rfl⟩ ⟨_, rfl⟩, selectedAppend, ?_, ?_, ?_, ?_,
    freshOriginallyAbsent, freshMember, ⟨selected, freshMember⟩, freshHolds, freshHolds.administrative, ?_, ?_, ?_⟩
  · rw [selectedAppend]
    simp
  · intro row different
    rw [finalRecords]
    exact unchanged row different
  · exact (final.rows duplicate).frame_eq.trans (sharedFrame.trans (final.rows selected).frame_eq.symm)
  · intro equal
    have member : fresh ∈ records initial duplicate := by
      rw [← duplicateUnchanged, ← equal]
      exact freshMember
    exact freshOriginallyAbsent ⟨duplicate, member⟩
  · intro row
    exact final.separated selected row fresh freshMember
  · intro row record member
    exact record_snapshot final row (Relates.mem finalRelated row member)
  · exact (CallableIndexedOwnedOrdinaryAllocation.bindings headers keys).restore_reached (reached := reachedIndex) (id := request.binder.id) (type := request.payloadType)
      (value := .cellRef (OptionalCell.cellType request.payloadType) (store.length + 2)) initial
      (ProtectedStateTransition.Transition.of_related (protocol headers keys) boundRelated)

end Tests.SourceCoreCallableIndexedOwnedOrdinaryAllocation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedFrames
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedDispatch.Dispatch.mk

/-! Kernel-checked carrier/dispatch laws and actual checked graph regression.
The small synthetic table tests native operations only; it supplies no source
ownership. The IO regression obtains its Dispatch from the sealed actual
metadata preparation and compares its cached recipes before native execution.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableIndexedFrames
open Solcore Core Frontend SourceInference
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
abbrev IndexedFrame := SourceCoreCallableIndexedFrames.Frame
private def w (n : Nat) : Word := Word.ofNatModulo n
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def dummyOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"main", rfl⟩], by decide⟩⟩, 0⟩
private def dummyState : SourceCoreCallableIndexedDispatch.State :=
  ⟨⟨⟨dummyOwner, []⟩, [], ⟨dummyOwner, [], [], []⟩⟩, []⟩
private def table : Table := {
  states := List.replicate 4 dummyState
  named := [⟨w 7, 0⟩]
  lambdas := [⟨0, w 8⟩, ⟨3, w 8⟩]
  views := [⟨1, 0, w 3, w 8, 2⟩, ⟨2, 0, w 3, w 8, 3⟩] }

example : definitions.WellFormed := DataEnvironment.isWellFormed_sound rfl
example (frame : IndexedFrame) : decode layout (encode layout frame) = some frame := decode_encode layout frame
example (frame : IndexedFrame) : RuntimeValueHasType [] (encode layout frame) layout.type definitions :=
  encode_runtime_typed [] registered frame
example : decode layout (.constructed layout.state (.word (w 0))) = none := rfl
example : decode layout (.constructed ⟨⟨1⟩, 1⟩ (.integer 0)) = none := rfl
example : decode layout (.cellRef layout.type 0) = none := rfl
example : decode layout (encode layout (.state (-1))) = some (.state (-1)) := rfl
example : lookup? table (.state (-1)) = none := rfl
example : lookup? table (.state 4) = none := rfl
example : lookup? table (.view (w 3) (w 8) 1) = none := rfl
example : lookup? table .invalid = none := rfl
example : lookup? table .empty = some none := rfl
example : namedFrame table (w 7) = .state 0 := rfl
example : namedFrame table (w 99) = .invalid := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 8) 1) = .state 2 := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 8) 2) = .state 3 := rfl
example : selectedFrame table (w 8) (.state 1) (.view (w 3) (w 8) 0) = .invalid := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 9) 1) = .state 0 := rfl
example : selectedFrame table (w 8) (.state 0) .empty = .state 0 := rfl
example : selectedFrame table (w 9) (.state 0) .empty = .invalid := rfl
example : selectedFrame table (w 8) (.state (-1)) .empty = .invalid := rfl
example : selectedFrame table (w 8) (.state 4) .empty = .invalid := rfl
example : selectedFrame {table with views := [⟨1, 0, w 3, w 8, 99⟩]}
    (w 8) (.state 0) (.view (w 3) (w 8) 1) = .invalid := rfl
example : readFrame (w 3) (w 8) (.state 1) = .view (w 3) (w 8) 1 := rfl
example : readFrame (w 3) (w 8) .empty = .invalid := rfl

example : HasType [layout.type, layout.type] (lambdaFrame table layout (w 8) (.var 0) (.var 1))
    layout.type definitions := lambdaFrame_hasType registered table (w 8) (.var rfl) (.var rfl)
example : HasType [layout.type] (readView layout (w 3) (w 8) (.var 0)) layout.type definitions :=
  readView_hasType registered (w 3) (w 8) (.var rfl)

private theorem selectedEvaluation : Evaluates [encode layout (.state 0), encode layout (.view (w 3) (w 8) 1)]
    [.word (w 55)] (lambdaFrame table layout (w 8) (.var 0) (.var 1))
    (encode layout (.state 2)) [.word (w 55)] :=
  SourceSemantics.CoreLowering.CallableIndexedContextFrames.lambdaFrame_evaluates
      (layout := layout) (lexicalFrame := .state 0) (currentFrame := .view (w 3) (w 8) 1)
      table (w 8) (.var rfl) (.var rfl) [.word (w 55)]

example : ∃ required, ∀ fuel, required ≤ fuel →
    runStateful fuel (.initial (lambdaFrame table layout (w 8) (.var 0) (.var 1))
      [encode layout (.state 0), encode layout (.view (w 3) (w 8) 1)] [.word (w 55)]) =
      .done (encode layout (.state 2)) [.word (w 55)] :=
  evaluation_runStateful_complete_with_sufficient_fuel selectedEvaluation

private def nativeProgram : Program := {
  dataDefinitions := definitions
  resultType := layout.type
  body := .letE (literal layout (.state 0))
    (.letE (literal layout (.view (w 3) (w 8) 1)) (lambdaFrame table layout (w 8) (.var 1) (.var 0))) }
private theorem nativeProgram_checked : nativeProgram.check = true :=
  Program.check_complete ⟨DataEnvironment.isWellFormed_sound rfl, registered.typeWellFormed,
    .letE (literal_hasType [] registered _) (.letE (literal_hasType _ registered _)
      (lambdaFrame_hasType registered table (w 8) (.var rfl) (.var rfl)))⟩
example (fuel : Nat) : (nativeProgram.runStateful fuel).HasType layout.type definitions :=
  Program.checked_runStateful_has_type nativeProgram_checked fuel
private theorem nativeProgram_evaluates : Evaluates [] [] nativeProgram.body (encode layout (.state 2)) [] :=
  .letE (SourceSemantics.CoreLowering.CallableIndexedContextFrames.literal_evaluates layout _ [] [])
    (.letE (SourceSemantics.CoreLowering.CallableIndexedContextFrames.literal_evaluates layout _ _ [])
      (SourceSemantics.CoreLowering.CallableIndexedContextFrames.lambdaFrame_evaluates
        (layout := layout) (lexicalFrame := .state 0) (currentFrame := .view (w 3) (w 8) 1)
        table (w 8) (.var rfl) (.var rfl) []))
example : ∃ required, ∀ fuel, required ≤ fuel →
    nativeProgram.runStateful fuel = .done (encode layout (.state 2)) [] :=
  evaluation_runStateful_complete_with_sufficient_fuel nativeProgram_evaluates
example : ∃ checkpoint, nativeProgram.runStateful 3 = .outOfFuel checkpoint := ⟨_, rfl⟩
example {checkpoint : Core.State} (exhausted : nativeProgram.runStateful 3 = .outOfFuel checkpoint) (additional : Nat) :
    (runStateful additional checkpoint).HasType layout.type definitions ∧
      runStateful additional checkpoint = nativeProgram.runStateful (3 + additional) :=
  well_typed_runStateful_resume_has_type (initial_state_has_type (Program.check_sound nativeProgram_checked)) exhausted additional

private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let probe: Word = 0; return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }"
  ]}] }

def run : IO Unit := do
  let program ← get "indexed source checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "sharedHistory") with
    | some signature => pure signature | none => throw (IO.userError "missing indexed root")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"indexed plan: {reprStr other}")
  let automatic ← get "indexed compiler base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let graph ← get "indexed metadata preparation" (SourceCoreCallableAncestryPairedPreparation.prepare automatic.prepared)
  let dispatch := prepare graph
  assertTrue (decide (dispatch.table = graph.table)) "dispatch lost graph ownership"
  let named ← match graph.inputs.callable.table.idAt? (.named key) with
    | some named => pure named | none => throw (IO.userError "missing indexed named descriptor")
  let lexical := namedFrame dispatch.table named
  assertTrue (lookup? dispatch.table lexical |>.isSome) "indexed named state was rejected"
  let shared ← match graph.inputs.views.entries.filter (·.view.binding.binder.name == "shared") with
    | [shared] => pure shared | _ => throw (IO.userError "wrong indexed shared views")
  let sharedTarget ← match graph.inputs.callable.table.idAt?
      (.lambda shared.view.owner shared.view.principal.initializer shared.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "missing shared target")
  let rootIndex ← match lexical.index? with
    | some index => pure index | none => throw (IO.userError "named state did not carry an index")
  for outer in graph.inputs.views.entries.filter (·.view.binding.binder.name == "outer") do
    let target ← match graph.inputs.callable.table.idAt?
        (.lambda outer.view.owner outer.view.principal.initializer outer.view.cumulative) with
      | some target => pure target | none => throw (IO.userError "missing outer target")
    let caller := selectedFrame dispatch.table target lexical (readFrame outer.id target lexical)
    let current := readFrame shared.id sharedTarget caller
    let actual := selectedFrame dispatch.table sharedTarget lexical current
    let callerIndex ← match caller.index? with
      | some index => pure index | none => throw (IO.userError "outer transition rejected")
    let actualIndex ← match actual.index? with
      | some index => pure index | none => throw (IO.userError "shared paired transition rejected")
    let recipe ← match graph.recipeAt? callerIndex rootIndex shared.id sharedTarget with
      | some recipe => pure recipe | none => throw (IO.userError "indexed pair lost its cached recipe")
    assertTrue (graph.table.stateAt? actualIndex == some (recipe.read.after recipe.lexical))
      "indexed native state disagreed with the authenticated read/application recipe"
    let expr := lambdaFrame dispatch.table layout sharedTarget (.var 0) (.var 1)
    assertTrue (Core.infer? [layout.type, layout.type] expr definitions == some layout.type)
      "indexed graph dispatch failed Core checker"
    match runStateful 100000 (.initial expr [encode layout lexical, encode layout current] [.word (w 91)]) with
    | .done native store =>
      assertTrue (decode layout native == some actual && store == [.word (w 91)])
        "indexed paired dispatch changed state or store"
    | result => throw (IO.userError s!"indexed native dispatch: {reprStr result}")
    let stable := (List.range 2000).foldl (fun frame _ => selectedFrame dispatch.table sharedTarget frame .empty) actual
    assertTrue (stable == actual) "repeated ordinary calls changed the prepared metadata state"
  IO.println "indexed callable frames: constant-depth carrier, separate cached caller/lexical recipes, native dispatch, malformed indices, typed checkpoint/resume GREEN"

end Tests.SourceCoreCallableIndexedFrames
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedParameterNativeInversion
/-! The actual checked cached root supplies native typing for its original
named body. Packed argument and wrapper slots survive the prefix inversion,
including bodies that produce closures. No source body typing is assumed. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedParameterNativeInversion
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedParameterNativeInversion

theorem actual_cached_named_body (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named)
    (global : cached.indexed.base.globals[index]? = some named.signature) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.parameterCode (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions :=
  prepared_named_body cached.indexedPrepared member selected global

/-- A frame wrapper cannot conceal a wrongly typed original body. -/
theorem wrong_body_rejected {definitions : DataEnvironment} {context : Core.Context}
    (reference next : Expr) :
    ¬ HasType context (SourceCoreCallableContextFrames.withFrame reference next (.word Word.zero)) .unit definitions := by
  intro typed
  cases withFrame_body typed

/-- The empty parameter fold retains a used raw argument slot. -/
theorem nil_keeps_raw_argument {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {frame : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    {onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error} {source : TypedSource}
    (definitions : DataEnvironment) (context : Core.Context) :
    HasType (.word :: context) (.var 0) .word definitions :=
  tree_body (CallableIndexedParameterCertificates.Tree.nil
    (layouts := layouts) (owner := owner) (active := active) (layout := frame) (globals := globals)
    (onError := onError) (source := source) (total := 0) (output := .word) (body := .var 0)
    (scope := []) (index := 0)) (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function zero() returns (Word) { return 9; }",
    "function single(value: Word) returns (Word) { return value + 1; }",
    "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return first; } return last; }",
    "function recursive(value: Word) returns (Word) { if (value == 0) { return 1; } return single(recursive(value - 1)); }",
    "function make(seed: Word) returns (function(Word, Bool) returns (Word)) { let extra = single(seed); return lam(item: Word, choose: Bool) -> Word { return choose ? extra + item : item; }; }"
  ]}] }

open Tests.SourceCompilerFeatureSupport in
private def checkBodies (entry : Entry) : IO Unit := do
  let prepared := entry.cached.indexed
  let diagnostics ← match prepared.base.diagnostics with
    | none => throw (IO.userError "actual named diagnostics missing")
    | some diagnostics => pure diagnostics.program
  let diagnostics := match prepared.base.callableContext with
    | none => diagnostics
    | some native => {diagnostics with rootTable := native.diagnostics.rootTable}
  let parents ← get "actual named parent contexts"
    (SourceCoreStageCodebook.prepareContexts prepared.base.sourceProgram prepared.base.plan
      (prepared.base.locals.bindings.flatMap (·.instances)))
  require (!prepared.entries.isEmpty) "actual native root missing"
  for (named, index) in prepared.base.functions.zipIdx do
    let own ← match diagnostics.base.find? named.signature.key with
      | some own => pure own | none => throw (IO.userError "actual named diagnostic function missing")
    let statements ← get "actual named roots" ((CallableIndexedNamedGeneration.source named).roots.mapM
      (m := Except SourceCoreGeneralFunctions.Error) (fun
        | .statement id => pure id | .expression id => throw (.expectedStatementRoot id)))
    let body ← get "actual named source body"
      (CallableIndexedNamedGeneration.bodyAction prepared named diagnostics parents own statements)
    let parameters ← get "actual named parameter fold"
      (SourceCoreSourceCells.bindParameters (CallableIndexedNamedGeneration.allocator prepared named)
        (CallableIndexedNamedGeneration.source named) [] named.inputs named.signature.resultType
        SourceCoreFunctions.argumentProjection body)
    let output ← get "actual named frame hook"
      (SourceCoreCallableIndexedAncestry.namedBody prepared.ancestry named parameters)
    let cached ← match prepared.secondPass.closures[index]? with
      | some cached => pure cached | none => throw (IO.userError "actual cached closure missing")
    require (cached == .lambda named.signature.parameterType (LanguageResult.resultType named.signature.resultType) output)
      "actual body actions did not reproduce the cached closure"
    for root in prepared.entries do
      let context := named.signature.parameterType :: prepared.base.globals.map (·.referenceType) ++
        .cell prepared.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext root.native.inputTypes
      let result := LanguageResult.resultType named.signature.resultType
      require (Core.infer? context parameters prepared.layouts.definitions == some result)
        "actual parameter fold lost native typing"
      require (Core.infer? (CallableIndexedParameterNativeTyping.finalContext named.inputs context)
        body prepared.layouts.definitions == some result) "original named body lost native typing or a wrapper slot"

open Tests.SourceCompilerFeatureSupport in
def run : IO Unit := do
  let checked ← get "parameter inversion source checker" (checkProgram workspace)
  for (name, arguments, expected) in [
      ("zero", [], scalar 9),
      ("single", [scalar 7], scalar 8),
      ("order", [scalar 11, (.bool false : SourceCoreExecution.Value), scalar 17], scalar 17),
      ("recursive", [scalar 3], scalar 4)] do
    let entry ← compileNamed checked name
    checkBodies entry
    require ((← entry.run arguments) == expected) "actual named body result changed"
    entry.checkResume arguments expected 1
  let entry ← compileNamed checked "make"
  checkBodies entry
  let created ← entry.invoke [scalar 7]
  let done ← match created.outcome with
    | .succeeded done => pure done | _ => throw (IO.userError "actual closure-producing body failed")
  let handle ← match done.value with
    | .function handle => pure handle | _ => throw (IO.userError "actual produced closure missing")
  let packed : SourceCoreExecution.Value := .product (scalar 3) (.bool true)
  let complete ← get "actual produced closure invocation"
    (← done.session.invokePacked handle packed executionOptions)
  let final ← match complete with
    | .succeeded final => pure final | _ => throw (IO.userError "actual produced closure invocation failed")
  require (final.value == scalar 11) "actual captured value or heterogeneous argument order changed"
  let baseline ← get "actual produced closure snapshot" (← final.session.snapshot 2048)
  for fuel in [0, 7, 43] do
    let pending ← get "actual produced closure suspension"
      (← done.session.invokePacked handle packed {executionOptions with executionFuel := fuel})
    let resumed ← match pending with
      | .outOfFuel pending => pending.resume 300000 2048 | complete => pure complete
    match resumed with
    | .succeeded actual =>
      let observed ← get "actual produced closure resumed snapshot" (← actual.session.snapshot 2048)
      require (actual.value == scalar 11 && reprStr observed.cells == reprStr baseline.cells)
        "actual produced closure resume changed parameter allocation or captured state"
    | _ => throw (IO.userError "actual produced closure resume failed")
  IO.println "parameter native inversion: actual cached body actions, zero/single/heterogeneous parameters, recursion, closure capture, hidden slots and resume GREEN"

end Tests.SourceCoreCallableIndexedParameterNativeInversion
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedParameters
/-! The real accepted parameter compiler reaches a closure-producing body.
The returned closure captures the actual temporary environment, while the
independent source parameter cells and previous context/snapshots are retained.
This tests both directions without exact closure equality under weakening. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedParameters
open Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering GeneralHeap ReadOnly CoreProof
open CallableIndexedHistory CallableIndexedParameterCertificates CallableIndexedParameterMeaning

theorem accepted_closure_body {layouts : SourceCoreAllocationLayouts.Prepared}
    {owner : SourceSpecialization.SpecializationKey} {active : TypeSystem.Substitution}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error)
    {source : TypedSource} {bindings : List Binding} {code : Expr}
    (accepted : SourceCoreSourceCells.bindParameters
      (SourceCoreCallableIndexedAllocationFrames.allocator layout globals (layouts.allocatorAt owner active onError))
      source [] bindings (.function .unit .unit) SourceCoreFunctions.argumentProjection
        (LanguageResult.success (.lambda .unit .unit (.var 0))) = .ok code)
    (inputs : source.inputs = bindings.map Prod.fst)
    {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects}
    (definitions : layouts.definitions = catalog.definitions)
    (registered : layout.Registered catalog.definitions)
    {mapping : LocationMap} {world : StoreTyping} {sources : List Dynamic.Value} {values : List Value}
    (represented : Arguments model mapping world bindings sources values)
    {administrative : Core.Context} {canonical actual : Environment}
    {heap : Dynamic.Heap} {store : Store} {ξ : Renaming} {contextLocation : Location}
    {native : NativeFrame} {ghost : GhostFrame}
    {checked : CallableAncestryPairedLookup.Checked} {base : CallableAncestryPairedLookup.Base checked}
    {owned : CallableAncestryPairedLookup.Inputs base} {table : CallableAncestryPairedLookup.Table}
    {records : List CallableIndexedSnapshots.Record}
    (environments : DataHeap.EnvRepresents catalog mapping world administrative [] [] canonical)
    (heaps : GenericHeap.HeapRepresents model mapping world heap store)
    (actualLayout : EnvironmentsAgree ξ (DataPatternValues.packValues values :: canonical) actual)
    (reference : canonical[globals]? = some (.cellRef layout.type contextLocation))
    (caller : CellState owned table layout contextLocation native ghost store)
    (snapshots : CallableIndexedSnapshots.All owned table layout mapping store records)
    (unmapped : contextLocation ∉ mapping) :
    ∃ finalEnvironment finalHeap finalActual finalStore finalMap finalWorld,
      Dynamic.BindersAllocate [] heap (bindings.map Prod.fst) sources finalEnvironment finalHeap ∧
      GenericHeap.HeapRepresents model finalMap finalWorld finalHeap finalStore ∧
      Evaluates actual store (code.rename ξ)
        (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore ∧
      CellState owned table layout contextLocation native ghost finalStore ∧
      CallableIndexedSnapshots.All owned table layout finalMap finalStore records ∧
      (∀ result finished, Evaluates actual store (code.rename ξ) result finished →
        result = .inRight .word (.closure .unit .unit (.var 0) finalActual) ∧ finished = finalStore) := by
  obtain ⟨finalEnvironment, finalHeap, _, finalActual, finalStore, finalMap, finalWorld,
    finalEmbedding, allocated, _, finalHeaps, _, _, frame, _, agreement⟩ :=
    CallableIndexedParameters.named_prefix onError accepted inputs definitions registered represented
      environments heaps actualLayout reference caller.read unmapped
  have child : Evaluates finalActual finalStore
      ((LanguageResult.success (.lambda .unit .unit (.var 0))).rename finalEmbedding)
      (.inRight .word (.closure .unit .unit (.var 0) finalActual)) finalStore := .inRight .lambda
  have evaluated := agreement.wrap child
  refine ⟨finalEnvironment, finalHeap, finalActual, finalStore, finalMap, finalWorld, allocated,
    finalHeaps, evaluated, CallableIndexedBodyFrames.body_current unmapped caller frame,
    snapshots.transport frame, ?_⟩
  intro result finished evaluated'
  have child' := agreement.unwrap evaluated'
  exact evaluation_deterministic child' child

/-- Argument payloads need no first-order restriction. The two copies may be
closures sharing the same mutable capture, and packing preserves their value. -/
example {catalog : SourceCoreDataCatalog.Catalog} {projects : GenericHeap.Projection}
    {model : GenericHeap.PayloadModel catalog projects} {mapping : LocationMap} {world : StoreTyping}
    (left right : SourceInference.TypedBinder) (type : Ty) (source : Dynamic.Value) (value : Value)
    (first : model.Represents mapping world left.scheme.body source value type)
    (second : model.Represents mapping world right.scheme.body source value type) :
    RuntimeValueHasType world (.pair value value) (.product type type) catalog.definitions := by
  have arguments : Arguments model mapping world [(left, type), (right, type)] [source, source] [value, value] :=
    .cons first (.cons second .nil)
  exact CallableIndexedParameters.Arguments.pack_typed arguments

end Solcore.Test.SourceCoreCallableIndexedParameters
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedPreparedInventories
/-! Consumers use the real factory equations. In particular the original
cached named body is typed without an independently supplied global-signature
correspondence or body-typing premise. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedPreparedInventories
open Solcore Core Frontend SourceInference SourceSemantics.CoreLowering
open CallableIndexedPreparedInventories

theorem actual_base (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base = cached.compatible.prepared :=
  indexed_base cached.indexedPrepared

/-- The entire ordered list of full signatures survives preparation. -/
theorem full_ordered_inventory (cached : SourceCoreUnifiedCompilation.Compiled) :
    cached.indexed.base.globals = cached.indexed.base.functions.map (·.signature) :=
  cached_globals cached

theorem other_signature_rejected (cached : SourceCoreUnifiedCompilation.Compiled)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function} {signature : SourceCoreCalls.Signature}
    (selected : cached.indexed.base.functions[index]? = some named)
    (different : signature ≠ named.signature) :
    cached.indexed.base.globals[index]? ≠ some signature := by
  rw [cached_global_at cached selected]
  intro same
  exact different (Option.some.inj same).symm

/-- Only actual entry and function membership remain as static inputs. -/
theorem actual_body_without_global_premise (cached : SourceCoreUnifiedCompilation.Compiled)
    {entry : SourceCoreCallableIndexedPrograms.Entry cached.indexed.layouts}
    (member : entry ∈ cached.indexed.entries)
    {index : Nat} {named : SourceCoreGeneralFunctions.Function}
    (selected : cached.indexed.base.functions[index]? = some named) :
    ∃ diagnostics code,
      ∃ compiled : CallableIndexedNamedGeneration.Compilation cached.indexed named diagnostics code,
      cached.indexed.secondPass.closures[index]? = some code ∧
      HasType (SourceCoreLocalCell.coreContext (named.inputs.reverse.map (fun binding => (binding.1.id, binding.2))) ++
        named.signature.parameterType :: cached.indexed.base.globals.map (·.referenceType) ++
        .cell cached.indexed.ancestry.layout.frame.type :: SourceCoreGeneralEntry.nativeInputContext entry.native.inputTypes)
        compiled.body (LanguageResult.resultType named.signature.resultType) cached.indexed.layouts.definitions := by
  obtain ⟨diagnostics, code, compiled, cached, parameters, body⟩ := cached_named_body cached member selected
  exact ⟨diagnostics, code, compiled, cached, body⟩

end Tests.SourceCoreCallableIndexedPreparedInventories
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedReadViews
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedReadViews.Template.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedReadViews.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedReadViews.Produced.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedReadViews.Stored.mk

#check_failure Solcore.Frontend.SourceCoreCallableNativeSnapshotScanner.Template.mk
#check_failure Solcore.Frontend.SourceCoreCallableNativeCaptureJoin.Capture.mk
#check_failure Solcore.Frontend.SourceCoreCallableNativeCaptureJoin.Slot.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedTemplates.Cache.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedTemplates.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedCaptures.Captured.mk

/-! Actual compiler output supplies the transparent read wrapper and its saved
original callable. Result and stored-payload provenance are kept separately.
The tests check native code/descriptor authenticity and by-value captures: two
reads of one generalized local share its principal's snapshot cells, and each
call starts again from them. Dynamic requirement rewriting is deliberately left
to the prepared ancestry metadata layer, rather than inferred from canonical
read rows.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedReadViews
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableIndexedReadViews
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function views(seed: Word) returns (F, F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return (f, f); }",
    "function nested(seed: Word) returns (F, F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); seed += 1; return seed; }; return (inner, inner); }; return outer(1); }",
    "function shared(seed: Word) returns (F, F) { let shared = lam(item) { seed += 1; return seed; }; let outer = lam(value) { keep(value); return (shared, shared); }; return outer(1); }",
    "function mono(seed: Word) returns (F) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return f; }",
    "function failure(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; while (true) {} return 0; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"read views fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["views", "nested", "shared", "mono", "failure", "suspended"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"read views worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"read views base failed: {reprStr error}")
private def initial : SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} {prepared : Prepared checked} (template : Template prepared) :
    template.carrier = SourceCoreCallableIndexedAncestry.viewRepack prepared.ancestry.layout.frame
      template.parameter template.result template.entry.id template.target template.referenceIndex := template.carrierExact

example {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : Authenticated cache world store value) :
    Core.RuntimeValueHasType world authenticated.original
      (Core.CallableContract.functionType authenticated.wrapper.parameter authenticated.wrapper.result)
      prepared.layouts.definitions := authenticated.originalTyped

example {checked : Checked} {prepared : Prepared checked} (templates : Templates prepared) :
    SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := templates.compiled

example {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (captured : SourceCoreCallableIndexedCaptures.Captured authenticated ledger) :
    captured.environment.map Prod.fst = authenticated.template.source.scope.map Prod.fst := captured.binders

example {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    {authenticated : SourceCoreCallableIndexedTemplates.Authenticated templates world store value}
    {initial : SourceHeap} {ledger : TypedLedger prepared.layouts initial world store}
    (captured : SourceCoreCallableIndexedCaptures.Captured authenticated ledger)
    {index : Nat} {binder : Resolved.LocalId} {location : SourceTypedRuntime.Location}
    (found : captured.environment[index]? = some (binder, location)) :
    initial.length ≤ location.index := captured.outsidePrefix found

private def retag (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with | .pair tagged _ => .pair tagged (.word descriptor) | other => other
private theorem retag_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty} (descriptor : Core.Word)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter result) definitions) :
    Core.RuntimeValueHasType world (retag value descriptor) (Core.CallableContract.functionType parameter result) definitions := by
  cases typed with | pair tagged _ => exact .pair tagged .word

private def replaceBody (value : Core.Value) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result _ environment)) descriptor =>
      .pair (.pair identity (.closure parameter result (Core.LanguageResult.success (.word (w 999))) environment)) descriptor
  | other => other
private theorem replaceBody_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter : Core.Ty}
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter .word) definitions) :
    Core.RuntimeValueHasType world (replaceBody value) (Core.CallableContract.functionType parameter .word) definitions := by
  cases typed with
  | pair tagged descriptor =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment _ => exact .pair (.pair identity (.closure environment (.inRight .word .word))) descriptor

private def replaceSavedDescriptor (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result body (caller :: original :: outer))) own =>
      .pair (.pair identity (.closure parameter result body (caller :: retag original descriptor :: outer))) own
  | other => other

private theorem replaceSavedDescriptor_typed {checked : Checked} {prepared : Prepared checked}
    {templates : Templates prepared} {cache : Cache templates} {world : Core.StoreTyping}
    {store : Core.Store} {value : Core.Value} (authenticated : Authenticated cache world store value)
    (descriptor : Core.Word) : Core.RuntimeValueHasType world (replaceSavedDescriptor value descriptor)
      (Core.CallableContract.functionType authenticated.wrapper.parameter authenticated.wrapper.result)
      prepared.layouts.definitions := by
  have typed := authenticated.typed
  conv at typed => arg 2; rw [authenticated.exact]
  conv => arg 2; rw [authenticated.exact]; simp only [replaceSavedDescriptor]
  cases typed with
  | pair tagged own =>
    cases tagged with
    | pair identity function =>
      cases function with
      | closure environment body =>
        cases environment with
        | cons caller rest =>
          cases rest with
          | cons original outer =>
            have changed := retag_typed descriptor authenticated.originalTyped
            rw [← authenticated.originalTyped.type_eq, original.type_eq] at changed
            exact .pair (.pair identity (.closure (.cons caller (.cons changed outer)) body)) own

private def reuse {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (left right : Core.Value)
    (leftTyped : Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) definitions)
    (rightTyped : Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) definitions)
    (frame : SourceCoreCallableIndexedFrames.Layout) (snapshot allocated : Nat) : IO Unit := do
  let body := Core.LocalSequence.pair .word .word
    (.apply (.second (.first (.var 1))) (.word (w 10)))
    (.apply (.second (.first (.var 0))) (.word (w 20)))
  have typed : Core.HasType [Core.CallableContract.functionType .word .word, Core.CallableContract.functionType .word .word]
      body (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := .initial body [right, left] store
    typed := .eval stored (.cons rightTyped (.cons leftTyped .nil)) typed .nil }
  for spent in [0, 31, 100000] do
    let first := checkpoint.resume spent
    let completed := match first.checkpoint? with | none => first | some checkpoint => checkpoint.resume 100000
    match completed.observation with
    | .succeeded (.pair (.word first) (.word second)) final =>
      -- Each call starts again from the principal's snapshot `seed = 3`.
      assertTrue (first == w 4 && second == w 4) "read wrapper did not restart each call from the principal's snapshot"
      assertTrue (final[snapshot]? == some (.inRight .unit (.word (w 3)))) "read wrapper call wrote the principal's snapshot cell"
      assertTrue (final[0]? == some (SourceCoreCallableIndexedFrames.encode frame .empty)) "view/lambda frames were not restored"
      assertTrue (final.length == store.length + allocated) "view reentry changed actual capture copies or source parameter allocations"
    | observation => throw (IO.userError s!"read wrapper reentry failed: {reprStr observation}")

private def pair {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) (nested sharedPrincipal : Bool) : IO Unit := do
  for spent in [0, 39, 100000] do
    let first ← match prepared.runSource owner [.word (w 3)] spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"read views source run failed: {reprStr error}")
    let _ ← match SourceCoreCallableIndexedLedger.scan first initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"read views partial ledger failed: {reprStr error}")
    let completion := first.resume 100000
    if same : completion.entry.native.resultType = .product (Core.CallableContract.functionType .word .word) (Core.CallableContract.functionType .word .word) then
      match success : completion.result.native.observation with
      | .succeeded (.pair left right) store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) left (Core.CallableContract.functionType .word .word) prepared.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) right (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
          obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
          have equal := stored.world_eq
          subst world
          rw [same] at typed
          cases typed with | pair left right => exact ⟨stored, left, right⟩
        let leftAuth ← match authenticate cache typed.1 left .word .word typed.2.1 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"left read wrapper auth failed: {reprStr error}")
        let rightAuth ← match authenticate cache typed.1 right .word .word typed.2.2 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"right read wrapper auth failed: {reprStr error}")
        assertTrue (leftAuth.wrapper.entry.id != rightAuth.wrapper.entry.id) "different reads shared a view token"
        assertTrue (!leftAuth.canonicalOwnSubstitution.isEmpty && !rightAuth.canonicalOwnSubstitution.isEmpty)
          "generalized read lost its own substitution"
        assertTrue (leftAuth.canonicalOwnWitnesses.length == (if sharedPrincipal then 0 else 1) && rightAuth.canonicalOwnWitnesses.length == (if sharedPrincipal then 0 else 1))
          "qualified read lost its exact own witnesses"
        assertTrue (sharedPrincipal || leftAuth.canonicalOwnWitnesses.map (·.actualRequirement) != rightAuth.canonicalOwnWitnesses.map (·.actualRequirement))
          "same-type reads collapsed occurrence-specific requirements"
        assertTrue ((!leftAuth.parentActive.isEmpty) == nested) "parent context was confused with own substitution"
        assertTrue (leftAuth.underlying.template.source.lambda.active == leftAuth.cumulative)
          "underlying native code was not the cumulative selected instance"
        for owned in [(⟨left, leftAuth⟩ : Σ value : Core.Value, Authenticated cache (store.map Core.Value.type) store value), ⟨right, rightAuth⟩] do
          let authenticated := owned.2
          let callerPosition ← match authenticated.caller.frame.index? with
            | some index => pure index | _ => throw (IO.userError "read caller snapshot lacks prepared state")
          let lexicalPosition ← match authenticated.underlying.snapshot.frame.index? with
            | some index => pure index | _ => throw (IO.userError "lexical snapshot lacks prepared state")
          let recipe ← match graph.recipeAt? callerPosition lexicalPosition authenticated.wrapper.entry.id authenticated.wrapper.target with
            | some recipe => pure recipe | none => throw (IO.userError "exact read caller/principal pair lacks cached recipe")
          assertTrue (recipe.read.substitution == authenticated.canonicalOwnSubstitution) "paired read changed its own substitution"
          assertTrue ((!recipe.read.witnesses.isEmpty) == !sharedPrincipal) "paired read inherited unrelated caller witnesses"
          assertTrue ((authenticated.caller.frame != authenticated.underlying.snapshot.frame) == sharedPrincipal)
            "read caller and lexical principal were incorrectly rebased"
          if sharedPrincipal then
            assertTrue (recipe.lexical.nativeActive.isEmpty && !recipe.caller.nativeActive.isEmpty &&
              (recipe.read.after recipe.lexical).metadata.active != (recipe.read.after recipe.lexical).nativeActive)
              "shared principal was forced to use its compiled cumulative context"
        assertTrue (leftAuth.underlying.current.frame == .empty) "returned view retained active administrative context"
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts initial (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"read views ledger failed: {reprStr error}")
        let leftProduced := Produced.of_success (authenticated := leftAuth) success (.pairLeft .root)
        let rightProduced := Produced.of_success (authenticated := rightAuth) success (.pairRight .root)
        let leftJoined ← match joinProduced leftProduced ledger with
          | .ok joined => pure joined | .error error => throw (IO.userError s!"left read captures failed: {reprStr error}")
        let rightJoined ← match joinProduced rightProduced ledger with
          | .ok joined => pure joined | .error error => throw (IO.userError s!"right read captures failed: {reprStr error}")
        assertTrue (leftJoined.captures.environment == rightJoined.captures.environment) "read wrappers lost the principal's shared snapshot environment"
        assertTrue (leftJoined.captures.environment.map Prod.fst == leftAuth.underlying.template.source.scope.map Prod.fst)
          "read wrapper added saved carrier/context slots to source captures"
        assertTrue (leftJoined.captures.environment.all (fun binding => initial.length ≤ binding.2.index))
          "read capture referenced inert source prefix"
        match authenticate cache typed.1 (retag left (w 999999)) .word .word (retag_typed _ typed.2.1) with
        | .error .closureMismatch => pure () | _ => throw (IO.userError "typed foreign view descriptor authenticated")
        match authenticate cache typed.1 (replaceBody left) .word .word (replaceBody_typed typed.2.1) with
        | .error .closureMismatch => pure () | _ => throw (IO.userError "typed foreign view body authenticated")
        match authenticate cache typed.1 (replaceSavedDescriptor left (w 999999)) leftAuth.wrapper.parameter leftAuth.wrapper.result
            (replaceSavedDescriptor_typed leftAuth (w 999999)) with
        | .error (.underlying .closureMismatch) => pure ()
        | _ => throw (IO.userError "typed foreign saved original carrier authenticated")
        if spent == 100000 then
          let seed ← match leftAuth.underlying.sourceCaptures.find? (fun capture =>
              (leftAuth.underlying.template.source.lambda.context.bindingAt? capture.binder).map (·.binding.binder.name) == some "seed") with
            | some capture => pure capture | none => throw (IO.userError "read wrapper source seed capture missing")
          -- Each call makes marked allocations of three cells: the copies of the
          -- principal's captures (`seed`, and in `nested` also `value`), the
          -- lambda's parameter and, except for `shared`, `keep`'s parameter.
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame seed.location
            (if sharedPrincipal then 12 else if nested then 24 else 18)
      | observation => throw (IO.userError s!"read views pair did not succeed: {reprStr observation}")
    else throw (IO.userError "read views pair result projection changed")

private def stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 10000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored read source run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored read observation classification changed"
  let ledger ← match SourceCoreCallableIndexedLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored read ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored read allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored read payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallableIndexedLedger.world completion) value
          (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
        simpa only [type] using row.payload_typed ledger.typed payloadFound
      let authenticated ← match authenticate cache ledger.typed value .word .word typed with
        | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"stored read auth failed: {reprStr error}")
      let receipt := Stored.of_payload (authenticated := authenticated) rfl ordinal payloadFound .root
      let joined ← match joinStored receipt with
        | .ok joined => pure joined | .error error => throw (IO.userError s!"stored read captures failed: {reprStr error}")
      assertTrue (joined.captures.environment.length == 1) "stored read lost the principal seed capture"
      assertTrue (joined.captures.environment.all (fun binding => initial.length ≤ binding.2.index))
        "stored read capture referenced opaque prefix"
    else throw (IO.userError "stored read callable type changed")

private def monomorphic {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 100000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"mono read failed: {reprStr error}")
  if same : completion.entry.native.resultType = Core.CallableContract.functionType .word .word then
    match success : completion.result.native.observation with
    | .succeeded value store =>
      have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
          Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
        have equal := stored.world_eq
        subst world
        exact ⟨stored, by simpa only [same] using typed⟩
      match authenticate cache typed.1 value .word .word typed.2 with
      | .error .closureMismatch => pure () | _ => throw (IO.userError "monomorphic read was treated as instantiated view")
      match SourceCoreCallableIndexedTemplates.authenticate templates typed.1 value .word .word typed.2 with
      | .ok _ => pure () | .error error => throw (IO.userError s!"mono snapshot auth failed: {reprStr error}")
    | _ => throw (IO.userError "mono closure did not complete")
  else throw (IO.userError "mono result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"read views source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"read views marked compiler failed: {reprStr error}")
  let templates ← match SourceCoreCallableIndexedTemplates.prepare prepared with
    | .ok templates => pure templates | .error error => throw (IO.userError s!"read views snapshot cache failed: {reprStr error}")
  let cache ← match prepare templates with
    | .ok cache => pure cache | .error error => throw (IO.userError s!"read views emitted wrapper scan failed: {reprStr error}")
  for malformed in [SourceCoreCallableIndexedFrames.Frame.state (-1),
      .state (Int.ofNat prepared.ancestry.dispatch.table.states.length), .invalid,
      .view (w 999999) (w 999999) 0] do
    match SourceCoreCallableIndexedTemplates.decodeSnapshot prepared
        (SourceCoreCallableIndexedFrames.encode prepared.ancestry.layout.frame malformed) with
    | .error .foreignFrame => pure ()
    | _ => throw (IO.userError "negative/out-of-range/foreign frame index authenticated")
  assertTrue (!cache.wrappers.isEmpty) "actual two-pass compiler emitted no read wrappers"
  for wrapper in cache.wrappers do
    match decode prepared wrapper.carrier with
    | .ok decoded => assertTrue (decoded.entry.id == wrapper.entry.id && decoded.body == wrapper.body) "full carrier decoder changed the view"
    | .error error => throw (IO.userError s!"retained wrapper failed complete rescan: {reprStr error}")
    match decode prepared (.pair (.pair .unit (.lambda wrapper.parameter (Core.LanguageResult.resultType wrapper.result) wrapper.body)) (.word wrapper.target)) with
    | .error .malformedWrapper => pure () | _ => throw (IO.userError "carrier with forged copied identity was accepted")
  let graph := prepared.ancestry.graph
  pair cache graph (← key program "views") false false
  pair cache graph (← key program "nested") true false
  pair cache graph (← key program "shared") true true
  monomorphic cache (← key program "mono")
  stored cache (← key program "failure") false
  stored cache (← key program "suspended") true
  IO.println "indexed exact wrapper code, finite snapshots, ordered snapshot captures, stored failure/suspension and resume GREEN"


end Tests.SourceCoreCallableIndexedReadViews
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedRetainedNamedValues
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedRetainedNamedValues
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open CallableIndexedRetainedNamedValues CompatiblePayload GeneralHeap

theorem complete_source_equality {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {left right : Dynamic.Value} {a b : Word} (first : Identity prepared left a) (second : Identity prepared right b) :
    a = b ↔ left = right := (identity_faithful prepared).equal first second

theorem dictionary_unchanged (source : Dynamic.GlobalFunction) :
    (CallableNamedReversal.global source).evidence = source.evidence ∧
    (CallableNamedReversal.global source).instantiation.type = source.instantiation.type ∧
    CallableNamedReversal.global (CallableNamedReversal.global source) = source :=
  ⟨rfl, rfl, CallableNamedReversal.global_twice source⟩

/-- The actual inferred record, selector and specialization factory supply an
identity receipt without a canonical header/domain equality premise. -/
theorem selected_identity {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    {policy : SourceCoreFunctions.Policy} {compilation : SourceCoreFunctions.Context}
    {source : TypedSource} {node : ExpressionNode} {index : Nat} {signature : SourceCoreCalls.Signature}
    {sourceSignature : ProgramFunctionSignature} {function : CheckedFunction}
    {supplied : TypeSystem.ParameterSubstitution} {specialized : Specialized} {retained : Evidence}
    {identity : Word}
    (plan : compilation.plan = prepared.base.plan) (globals : compilation.globals = prepared.base.globals)
    (specialization : SourceSpecialization.specializeFunction sourceSignature function supplied = .ok specialized)
    (unique : sourceSignature.scheme.parameters.Nodup)
    (next : Nat) (final : TypeSystem.Substitution) (caller : TypeSystem.ParameterSubstitution)
    (selected : SourceCoreFunctions.selectedSignature policy compilation source node
      (CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller) true = .ok (index, signature))
    (record : SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key = .ok specialized)
    (resolved : SourceCompilationPlan.resolveRuntimeEvidenceEnvironment prepared.base.sourceProgram signature.key specialized.assumptions = .ok retained)
    (number : Word.ofNat? (index + 1) = some identity) :
    Identity prepared (.global ⟨CallableNamedCanonicalOrder.inferredInstantiation sourceSignature next final caller,
      CallableNamedMetadata.environment retained⟩) identity := by
  obtain ⟨row, same⟩ := row_of_inferred prepared plan globals selected record specialization unique next final caller rfl resolved
  rw [same]
  exact .retained (.named row number)

/-- Real full-definition payloads provide all equality laws for the retained
model. Distinct parameter list orders are not identified as source values. -/
theorem compare_from_receipts {checked : SourceCoreCompatibleCatalog.Checked} (prepared : Prepared checked)
    (profile : checked.catalog.callableContracts = true) (comparator : SourceCoreCompatibleDataEquality.Prepared checked)
    {registry : SourceCoreRawMetadata.Registry} {world : StoreTyping} {mapping : LocationMap}
    {leftType rightType : TypeSystem.Ty} {left right : Dynamic.Value} {a b : Value}
    (first : (model prepared profile).Represents registry mapping world leftType left a comparator.type)
    (second : (model prepared profile).Represents registry mapping world rightType right b comparator.type)
    (store : Store) :
    ∃ result, (result = true ↔ Dynamic.ValueEquivalent left right) ∧
      Evaluates [a, b] store (CompatibleEquality.comparison comparator (.var 0) (.var 1)) (.bool result)
        (CompatibleEquality.preparedStore comparator [a, b] store) :=
  CompatibleEquality.prepared_compare_preserves comparator (identity_faithful prepared)
    (observations prepared profile first) (observations prepared profile second) [a, b] store _ _ (.var rfl) (.var rfl)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "function first<A, B>(a: A, b: B) returns (A) { return a; }",
    "function second<A, B>(a: A, b: B) returns (A) { return a; }",
    "function firstRef() returns (function(Word, Bool) returns (Word)) { return first; }",
    "function secondRef() returns (function(Word, Bool) returns (Word)) { return second; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO SourceSpecialization.SpecializationKey := do
  let found ← match program.signatures.functions.find? (·.name == name) with
    | some found => pure found
    | none => throw (IO.userError s!"missing retained fixture {name}")
  pure ⟨found.id, []⟩

def run : IO Unit := do
  let program ← SourceCompilerFeatureSupport.get "retained named checker" (checkProgram workspace)
  let roots ← ["firstRef", "secondRef"].mapM (key program)
  let requests := roots.map fun root => (⟨root.declaration, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program requests 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"retained named worklist {reprStr other}")
  let automatic ← SourceCompilerFeatureSupport.get "retained named compatible artifact" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← SourceCompilerFeatureSupport.get "retained named indexed artifact" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let mut seen := 0
  let mut payloads : List Value := []
  for root in roots do
    let caller ← SourceCompilerFeatureSupport.get "retained caller" (SourceCompilationPlan.exactSpecialization prepared.base.plan root)
    let source := caller.function.typedBody
    let compilation : SourceCoreFunctions.Context := ⟨prepared.base.plan, root, prepared.base.globals, 0, [], Word.zero⟩
    let representation := SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts
    let policy := {representation.expressions with callables := SourceCoreGeneralFunctions.callablePolicy (some prepared.ancestry.graph.inputs.callable) []}
    for raw in source.nodes do
      match raw with
      | .expression node =>
        match node.form with
        | .reference _ (.declaration actual) =>
          let (index, signature) ← SourceCompilerFeatureSupport.get "actual retained selectedSignature"
            (SourceCoreFunctions.selectedSignature policy compilation source node actual true)
          let specialized ← SourceCompilerFeatureSupport.get "retained callee" (SourceCompilationPlan.exactSpecialization prepared.base.plan signature.key)
          let canonical := CallableNamedMetadata.instantiation specialized
          SourceCompilerFeatureSupport.require (actual.parameterSubstitution.length == 2) "fixture lost two distinct type parameters"
          SourceCompilerFeatureSupport.require (decide (actual = CallableNamedReversal.instantiation canonical))
            "actual checked metadata does not equal the reverse-ledger canonical header"
          SourceCompilerFeatureSupport.require (decide (actual ≠ canonical)) "actual and plan ledger order unexpectedly coincide"
          let actualTarget ← SourceCompilerFeatureSupport.get "actual retained exact target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan actual)
          let canonicalTarget ← SourceCompilerFeatureSupport.get "canonical exact target" (SourceCompilationPlan.exactInstantiationKey prepared.base.plan canonical)
          SourceCompilerFeatureSupport.require (decide (actualTarget = canonicalTarget)) "reverse matching changed target"
          SourceCompilerFeatureSupport.require (prepared.base.globals[index]? == some signature) "selected slot mismatch"
          seen := seen + 1
        | _ => pure ()
      | _ => pure ()
    let initial ← SourceCompilerFeatureSupport.get "retained named suspended" (prepared.runSource root [] 0)
    let resumed := initial.resume 300000
    let direct ← SourceCompilerFeatureSupport.get "retained named direct" (prepared.runSource root [] 300000)
    match resumed.result.native.observation, direct.result.native.observation with
    | .succeeded value store, .succeeded expected finalStore =>
      SourceCompilerFeatureSupport.require (value == expected && store == finalStore) "retained named resume changed captures or store"
      payloads := payloads ++ [value]
    | first, second => throw (IO.userError s!"retained named execution {reprStr first}, {reprStr second}")
  SourceCompilerFeatureSupport.require (seen == 2) "retained metadata fixture omitted an actual occurrence"
  let comparator ← SourceCompilerFeatureSupport.get "retained named equality" (SourceCoreCompatibleDataEquality.prepare 500 automatic.checked (.function (.product .word .bool) .word))
  for (left, i) in payloads.zipIdx do
    for (right, j) in payloads.zipIdx do
      let comparison := CompatibleEquality.comparison comparator (.var 0) (.var 1)
      let store : Store := [.word (Word.ofNatModulo 57)]
      SourceCompilerFeatureSupport.require (runStateful 100000 (.initial comparison [left, right] store) ==
        .done (.bool (i == j)) (CompatibleEquality.preparedStore comparator [left, right] store))
        "retained named identity equality changed"
  IO.println "retained named values: actual two-parameter reverse metadata, distinct source declarations and resumed captures GREEN"
end Tests.SourceCoreCallableIndexedRetainedNamedValues
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedSnapshots
/-! Protected allocation snapshots survive actual source writes and distinct
administrative writes. Capture proofs preserve ordered aliases, including
hidden match slots, and actual accepted callbacks supply allocation code. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableIndexedSnapshots
open Core Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableIndexedHistory GeneralHeap
open CallableIndexedSnapshots CallableIndexedAllocationCompletion

/-- The source payload, mutable context and a fresh helper can all change
without changing the allocation-time snapshot or its carried history. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {native : NativeFrame}
    {ghost : GhostFrame} {metadata : Option MetadataState}
    (history : Carries inputs table native ghost metadata) :
    Holds inputs table layout [3]
      [.bool true, SourceCoreCallableIndexedFrames.encode layout native, .unit,
        .inRight .unit (.bool true), .integer 7]
      ⟨1, native, ghost, metadata⟩ := by
  have initial := completed (layout := layout) (before := [.unit]) (mapping := []) history
    (by intro location impossible; cases impossible) .unit (.inRight .unit (.bool false))
  have sourceUpdated : Holds inputs table layout [3]
      [.unit, SourceCoreCallableIndexedFrames.encode layout native, .unit, .inRight .unit (.bool true)]
      ⟨1, native, ghost, metadata⟩ :=
    initial.source_write (location := 3) (by simp) rfl
  have contextUpdated : Holds inputs table layout [3]
      [.bool true, SourceCoreCallableIndexedFrames.encode layout native, .unit, .inRight .unit (.bool true)]
      ⟨1, native, ghost, metadata⟩ :=
    sourceUpdated.other_write (location := 0) (by change (1 : Nat) ≠ 0; decide) rfl
  exact contextUpdated.fresh_write (suffix := [.unit]) (offset := 0) rfl

/-- An administrative snapshot reference can physically occupy the temporary
slot zero while the generated capture expression still preserves both aliases. -/
example (first hidden : Resolved.LocalId) (inserted : Value) (store : Store) :
    Evaluates [inserted, .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0] store
      (SourceCoreSourceCells.captures (fun index => index + 1) [(first, .word), (hidden, .word)])
      (.pair (.cellRef (OptionalCell.cellType .word) 0) (.cellRef (OptionalCell.cellType .word) 0)) store := by
  exact (Captures.cons rfl (.singleton rfl)).evaluates store

/-- Scope alignment, including a hidden internal slot, supplies all native
capture lookups without requiring a capture execution as a premise. -/
example (catalog : SourceCoreDataCatalog.Catalog) (first hidden : Resolved.LocalId)
    (inserted : Value) :
    ∃ captured,
      Captures [.cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0]
        Renaming.id [(first, .word), (hidden, .word)] captured ∧
      Captures [inserted, .cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0]
        (fun index => index + 1) [(first, .word), (hidden, .word)] captured := by
  have reference : ReferenceRepresents [0] [OptionalCell.cellType .word] ⟨0⟩ 0 .word := ⟨rfl, rfl⟩
  have related : DataHeap.EnvRepresents catalog [0] [OptionalCell.cellType .word] []
      [(first, .word), (hidden, .word)] [(first, ⟨0⟩)]
      [.cellRef (OptionalCell.cellType .word) 0, .cellRef (OptionalCell.cellType .word) 0] :=
    .cons reference (.internal reference.typed (by intro location impossible; cases impossible) (.nil .nil))
  exact CallableIndexedCaptureEnvironment.captures_inserted related (fun found => found) inserted

/-- A real successful callback plus an already evaluated payload is enough
to derive completion; the payload may itself be an existing captured closure.
No child allocation evaluation or first-order-store restriction is supplied. -/
example {layouts : SourceCoreAllocationLayouts.Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    {layout : SourceCoreCallableIndexedFrames.Layout} {globals : Nat}
    (onError : SourceCoreAllocationLayouts.Error → SourceCoreBasic.Error) {code : Expr}
    (accepted : SourceCoreCallableIndexedAllocationFrames.allocator layout globals
      (layouts.allocatorAt owner active onError) request = .ok code)
    {payload : Value} {tail : Environment} {before : Store} {location : Location} {native : NativeFrame}
    (scope : request.scope = []) (initializer : request.payload = some (.var 0))
    (reference : (payload :: tail)[SourceCoreCallableIndexedAllocationFrames.referenceIndex globals request]? =
      some (.cellRef layout.type location))
    (read : before.read? location = some (SourceCoreCallableIndexedFrames.encode layout native)) :
    ∃ marker,
      Evaluates (payload :: tail) before code
        (.cellRef (OptionalCell.cellType request.payloadType) (before.length + 2))
        (before ++ [SourceCoreCallableIndexedFrames.encode layout native, marker, .inRight .unit payload]) := by
  obtain ⟨allocation, annotation, same, exactCode⟩ := accepted_receipts onError accepted
  subst code
  refine ⟨SourceCoreHeapMarkers.markerValue allocation.entry.layout .unit, ?_⟩
  have selected : Captures (payload :: tail) request.references request.scope .unit := by rw [scope]; exact .nil
  exact evaluates allocation annotation same reference read selected (.initialized initializer rfl)

/-- A whole-body semantic frame transports the allocation-time metadata even
when execution adds source cells and administrative closures of arbitrary type. -/
example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    {layout : SourceCoreCallableIndexedFrames.Layout} {mapping futureMapping : LocationMap}
    {before after : Store} {records : List Record}
    (snapshots : All inputs table layout mapping before records)
    (frame : AdministrativePreserved mapping before futureMapping after) :
    All inputs table layout futureMapping after records := snapshots.transport frame

end Solcore.Test.SourceCoreCallableIndexedSnapshots
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedStageOrigins
/-! Actual source receipts and compiler tables close function-leaf provenance
under one ambient model. These consumers retain the same formation completion;
contextual provenance requires the actual local-evidence factory receipt. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedStageOrigins
open Solcore Core Frontend SourceInference SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap CompatiblePayload CallableIndexedHistory CallableIndexedLambdaValues
open CallableIndexedLambdaRuntimeValues CallableIndexedStageOrigins

abbrev actual_callsite_coverage := @actual_compiled_coverage
abbrev actual_original_formation := @CallableIndexedStageOrigins.formation
abbrev actual_original_completion := @reflects_original
abbrev actual_formation_receipt := @formation_receipt
abbrev actual_capture_condition := @formation_condition

section Model
variable {values : SourceCoreCompatibleValues.Context}
  (indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked)
  {checkedProgram : CheckedProgram} {support : SupportFamily indexed}
  {prior : SupportCondition indexed support}
  {project : TypeSystem.Ty → Except SourceCoreLocalPolymorphism.Error Ty}
  {limits : SourceCoreStageCodebook.Limits} {firstId : Nat}
  (accepted : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
    .ok indexed.ancestry.graph.inputs.callable.table)
  {mapping : LocationMap} {world : StoreTyping} {sourceType : TypeSystem.Ty}
  {source : Dynamic.Value} {carrier : Value} {type : Ty}

include accepted in
theorem actual_function_leaf
    (related : RepresentsWith indexed support (provenanceCondition indexed checkedProgram support prior)
      mapping world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier :=
  origin_of_represents indexed accepted related

include accepted in
theorem retained_parameter_order
    (related : CallableIndexedRetainedNamedValues.Represents indexed world sourceType source carrier type) :
    CallableLedger.OriginRep indexed.base.plan indexed.ancestry.graph.inputs.callable.table source carrier :=
  retained_origin indexed accepted related

variable {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {actual : Environment}
  (captured : Captures indexed mapping world scope function.captured actual)
  (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)

theorem same_source_and_prior
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body) :
    prior captured code history body ∧
    LambdaSourceAlignment.SourceReceipt checkedProgram indexed.base.plan
      code.compilation.owner code.active function.source ∧ NodeOccurrencesUnique function.source := condition

variable
  (stable : ∀ {mapping futureMapping world futureWorld function scope actual}
    (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code),
    prior captured code history body →
    ∀ (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld),
    prior (captured.extend maps worlds) code history body)

include stable in
theorem same_capture_extension
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body)
    {futureMapping : LocationMap} {futureWorld : StoreTyping}
    (maps : LocationMap.Extends mapping futureMapping) (worlds : WorldExtends world futureWorld) :
    provenanceCondition indexed checkedProgram support prior (captured.extend maps worlds) code history body :=
  provenance_stable indexed checkedProgram support prior stable captured code history body condition maps worlds

include stable in
theorem same_model_payload_origin (profile : values.checked.catalog.callableContracts = true)
    {registry : SourceCoreRawMetadata.Registry} {sidecar : SourceCoreStageContracts.Sidecar}
    {site : SourceCoreCallableContracts.Callsite}
    (samePlan : sidecar.plan = indexed.base.plan)
    (sameTable : site.table = indexed.ancestry.graph.inputs.callable.table)
    (related : ValueRep values.checked registry
      (model indexed stable profile (checkedProgram := checkedProgram))
      mapping world sourceType source carrier type)
    (callable : Staging.CallBoundary.UserCallable source)
    (actualTable : SourceCoreStageCodebook.prepareWithProjection checkedProgram indexed.base.plan project limits firstId =
      .ok indexed.ancestry.graph.inputs.callable.table) :
    CallableLedger.OriginRep sidecar.plan site.table source carrier :=
  CompatibleAmbientStageOrigins.related_origin
    (function_origins indexed stable profile actualTable samePlan sameTable) related callable
end Model

section Contextual
variable {program : CheckedProgram} {plan : SourceCompilationPlan.Plan}
  {candidate : SourceCoreLocalPolymorphism.Instance} {parent : Option SourceCoreLocalEvidence.Prepared}
  {prepared : SourceCoreLocalEvidence.Prepared}

/-- A contextual receipt starts at the actual factory success. Native history
or a source type supplies none of these equalities. -/
theorem actual_contextual_source
    (accepted : SourceCoreLocalEvidence.prepare program plan candidate parent = .ok prepared)
    {sidecar : SourceCoreStageContracts.Sidecar}
    (selected : SourceCoreStageContracts.prepareSidecar plan candidate.origin.caller = .ok sidecar) :
    LambdaSourceAlignment.SourceReceipt program plan candidate.origin.caller prepared.substitution prepared.source ∧
    prepared.source = sidecar.source.applySubstitution prepared.substitution :=
  ⟨.contextual accepted, (LambdaSourceAlignment.SourceReceipt.contextual accepted).source selected⟩
end Contextual

section Boundaries
/-- Only function leaves are strengthened. Scalar representation still uses
its actual primitive representation without an origin hypothesis. -/
theorem scalar_keeps_no_origin
    {checked : SourceCoreCompatibleCatalog.Checked} {ambient : AmbientDefinitions checked.catalog.definitions}
    (functions : FunctionModel checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    (mapping : LocationMap) (world : StoreTyping) (value : Bool) :
    ValueRep checked registry functions mapping world .bool (.bool value) (.bool value) .bool :=
  .bool value

/-- The origin augmentation retains exactly the prior condition on this Code. -/
theorem forget_only_prior
    {values : SourceCoreCompatibleValues.Context} {indexed : SourceCoreCallableIndexedPrograms.Prepared values.checked}
    {checkedProgram : CheckedProgram} {support : SupportFamily indexed} {prior : SupportCondition indexed support}
    {mapping : LocationMap} {world : StoreTyping} {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope}
    {actual : Environment} (captured : Captures indexed mapping world scope function.captured actual)
    (code : Code indexed function scope captured.administrative) (history : History code) (body : support code)
    (condition : provenanceCondition indexed checkedProgram support prior captured code history body) :
    prior captured code history body := condition.1
end Boundaries

def run : IO Unit := Tests.SourceCoreCallableIndexedLambdaRuntimeBody.run
end Tests.SourceCoreCallableIndexedStageOrigins
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableIndexedPrograms
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedPrograms.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableIndexedAncestry.Prepared.mk

/-! Actual indexed compiler regressions. The graph is prepared once before
execution. Native snapshots contain one integer state index, while cached
recipes retain distinct read-caller and lexical source profiles. Closures
capture by value: a lambda keeps copies of its captured cells made when it is
created, and each call starts again from them. Compiler receipts, broad native
store typing, real allocation markers and checkpoints remain part of the
enclosing artifact; carrier shape alone is not authority. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableIndexedPrograms
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Frame := SourceCoreCallableIndexedFrames.Frame
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared (checked : Checked) := Solcore.Frontend.SourceCoreCallableIndexedPrograms.Prepared checked

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function sharedHistory(seed: Word) returns (Word) {",
    " let shared = lam(item) { let probe: Word = 0; return item; };",
    " let outer = lam(value) { keep(value); return shared(value); };",
    " return outer(seed) + outer(seed); }",
    "function getLocal(seed: Word) returns (F) { let f = lam(item) { seed += 1; return item; }; return f; }",
    "function useReturned(seed: Word) returns (Word) { let f = getLocal(seed); return f(8) + f(9); }",
    "function mono(seed: Word) returns (Word) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; f(3); return f(4); }",
    "function zero() returns (Word) { let f = lam() -> Word { let probe: Word = 9; return probe; }; return f(); }",
    "function recursive(n: Word) returns (Word) { let f: F; f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function deep() returns (Word) { let f0 = lam(item0) { let f1 = lam(item1) { let f2 = lam(item2) { let probeDeep: Word = 7; return probeDeep; }; return f2(true); }; return f1(true); }; return f0(true); }",
    "function repeatViews(limit: Word) returns (Word) { let total = 0; let f = lam(item) { total += 1; return item; }; let i = 0; while (i < limit) { f(true); i += 1; } return total; }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent(seed: Word) returns (Word) { let f = lam(item) { seed += 1; let absent: Word; return absent; }; return f(0); }",
    "function spin() returns (Word) { let f = lam() -> Word { while (true) {} return 0; }; return f(); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"indexed native fixture missing {name}")
private def initial : SourceCoreAllocationLedger.SourceHeap :=
  [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} (prepared : Prepared checked) :
    SourceCoreCompatibleMarkedFunctions.compileClosures prepared.base
      (SourceCoreCallableIndexedPrograms.markedRepresentation prepared.ancestry prepared.fuel prepared.layouts)
      prepared.fuel = .ok prepared.secondPass.closures := prepared.secondPass.compiled

example {checked : Checked} {prepared : Prepared checked}
    (completion : SourceCoreCallableIndexedPrograms.Completion prepared) :
    Core.RuntimeStoreHasTypes (SourceCoreCallableIndexedLedger.world completion)
      (SourceCoreCallableIndexedLedger.store completion) prepared.layouts.definitions :=
  SourceCoreCallableIndexedLedger.store_typed completion

/-- Run `owner` after `spent` fuel to its end and check its ledgers, raw
headers and restored frame, whatever its outcome. -/
private def completed {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (spent : Nat) :
    IO (SourceCoreCallableIndexedPrograms.Completion prepared) := do
  let cellHeaders ← get "indexed raw cell header cache"
    (SourceCoreCallableIndexedCellHeaders.prepare (program := prepared) prepared.ancestry.graph)
  let principalHeaders ← get "indexed raw principal header cache"
    (SourceCoreCallablePairedHeaders.prepare prepared.ancestry.graph)
  let first ← get "indexed native start" (prepared.runSource owner arguments spent 500)
  let early ← get "indexed partial typed ledger" (SourceCoreCallableIndexedLedger.scan first initial)
  assertTrue (early.ledger.initialHeap.map (·.type) == initial.map (·.type)) "suspension altered inert source prefix"
  let completion := first.resume 150000
  let ledger ← get "indexed complete typed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
  assertTrue ledger.ledger.pending.isNone "indexed completion retained an incomplete marker"
  assertTrue (ledger.ledger.rows.all (fun row => initial.length ≤ row.sourceLocation.index))
    "indexed administrative cell entered the source prefix"
  for row in ledger.ledger.rows do
    let selected ← get "indexed raw cell header" (SourceCoreCallableIndexedCellHeaders.select cellHeaders row)
    assertTrue (selected.header.raw.binder.id == row.entry.key.binder.id) "indexed cache changed stable source binder identity"
    if !selected.header.raw.binder.scheme.quantified.isEmpty then
      let restored ← get "indexed raw generic principal"
        (SourceCoreCallableIndexedPrincipalAllocations.restore principalHeaders row)
      assertTrue (restored.cell.type == selected.header.raw.binder.scheme.body) "indexed principal lost original raw type"
      match restored.cell.value with
      | some (.closure parameters _ _ _ _ captures _) =>
        assertTrue (captures == row.environment) "indexed principal changed capture order or aliases"
        assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "indexed principal was specialized during export"
      | _ => throw (IO.userError "indexed principal was not restored as its original closure")
  assertTrue (SourceCoreCallableIndexedLedger.frame? completion == some .empty)
    "indexed invocation failed to restore its empty current frame"
  pure completion

private def successful {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (expected : Nat) (spent : Nat) :
    IO (SourceCoreCallableIndexedPrograms.Completion prepared) := do
  let completion ← completed prepared owner arguments spent
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w expected) "indexed execution changed the result"
  | other => throw (IO.userError s!"indexed invocation did not succeed: {reprStr other}")
  pure completion

/-- The binder `name` declared in `owner`'s checked body. -/
private def binder {checked : Checked} (prepared : Prepared checked) (owner : Key) (name : String) :
    IO Resolved.LocalId := do
  let specialized ← get "indexed specialization" (SourceCompilationPlan.exactSpecialization prepared.base.plan owner)
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"indexed fixture binder missing {name}")

private def shared {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (owner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "indexed shared origin missing")
  let lexical := SourceCoreCallableIndexedDispatch.namedFrame graph.table named
  let rootPosition ← match lexical.index? with
    | some index => pure index | _ => throw (IO.userError "indexed lexical root unavailable")
  let view ← match graph.inputs.views.entries.filter (·.view.binding.binder.name == "shared") with
    | [view] => pure view | _ => throw (IO.userError "wrong indexed shared view count")
  let target ← match graph.inputs.callable.table.idAt?
      (.lambda view.view.owner view.view.principal.initializer view.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "indexed shared target missing")
  let mut expected : List Frame := []
  let mut callerSources : List TypedSource := []
  for outer in graph.inputs.views.entries.filter (·.view.binding.binder.name == "outer") do
    let outerTarget ← match graph.inputs.callable.table.idAt?
        (.lambda outer.view.owner outer.view.principal.initializer outer.view.cumulative) with
      | some target => pure target | none => throw (IO.userError "indexed outer target missing")
    let caller := SourceCoreCallableIndexedDispatch.selectedFrame graph.table outerTarget lexical
      (SourceCoreCallableIndexedDispatch.readFrame outer.id outerTarget lexical)
    let callerPosition ← match caller.index? with
      | some index => pure index | _ => throw (IO.userError "indexed outer transition missing")
    let recipe ← match graph.recipeAt? callerPosition rootPosition view.id target with
      | some recipe => pure recipe | none => throw (IO.userError "indexed cached paired recipe missing")
    let next := SourceCoreCallableIndexedDispatch.selectedFrame graph.table target lexical
      (SourceCoreCallableIndexedDispatch.readFrame view.id target caller)
    expected := expected ++ [next]
    callerSources := callerSources ++ [recipe.caller.metadata.source]
  assertTrue (expected.length == 2 && callerSources.eraseDups.length == 2)
    "indexed preparation collapsed occurrence-specific read caller metadata"
  for spent in [0, 31, 150000] do
    let completion ← successful prepared owner [.word (w 3)] 6 spent
    let ledger ← get "shared indexed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let principal ← match ledger.ledger.rows.find? (·.entry.key.binder.name == "shared") with
      | some row => pure row | none => throw (IO.userError "indexed shared bundle missing")
    -- The principal captures the copy of `seed` taken around its declaration,
    -- allocated after the input and right before the principal's own cell.
    let [input, seed] := (ledger.ledger.rows.takeWhile (·.entry.key.binder.name != "shared")).filter
        (·.entry.key.binder.name == "seed")
      | throw (IO.userError "indexed shared seed or its snapshot missing")
    assertTrue (principal.environment == [(seed.entry.key.binder.id, seed.sourceLocation)] && seed.payload == input.payload)
      "indexed read-parent compilation changed principal lexical captures"
    let mut observed : List Frame := []
    let mut sources : List TypedSource := []
    for row in ledger.ledger.rows do
      let snapshot ← get "indexed allocation snapshot"
        (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      let state ← match SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame with
        | some (some state) => pure state
        | _ => throw (IO.userError s!"actual indexed allocation {row.entry.key.binder.name} lacks cached metadata")
      assertTrue (match snapshot.frame with | .state _ => true | _ => false)
        "source allocation saved a recursive or transient frame"
      if row.entry.key.binder.name == "probe" then
        assertTrue (expected.contains snapshot.frame) "native shared application selected the wrong indexed pair"
        assertTrue (state.nativeActive != state.metadata.active && state.metadata.active == view.view.ownSubstitution)
          "native cumulative context leaked into original source principal metadata"
        observed := observed ++ [snapshot.frame]
        sources := sources ++ [state.metadata.source]
    assertTrue (observed.length == 2 && sources.eraseDups.length == 1)
      "indexed shared calls changed their single original source principal"

private def escaped {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (getOwner useOwner : Key) : IO Unit := do
  let named ← match graph.inputs.callable.table.idAt? (.named getOwner) with
    | some named => pure named | none => throw (IO.userError "indexed get origin missing")
  let lexical := SourceCoreCallableIndexedDispatch.namedFrame graph.table named
  for spent in [0, 41, 150000] do
    let completion ← successful prepared useOwner [.word (w 3)] 17 spent
    let ledger ← get "returned indexed ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let wrapper ← match ledger.ledger.rows.find? (fun row =>
        row.entry.key.binder.name == "f" && row.entry.key.owner == useOwner) with
      | some row => pure row | none => throw (IO.userError "escaped view payload missing")
    match wrapper.payload with
    | some (.pair (.pair _ (.closure _ _ _ (readSnapshot :: original :: _))) _) =>
      assertTrue (SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame readSnapshot == some lexical)
        "escaped view sampled the application caller instead of the read-time caller"
      match original with
      | .pair (.pair _ (.closure _ _ _ (creationSnapshot :: _))) _ =>
        assertTrue (SourceCoreCallableIndexedFrames.decode prepared.ancestry.layout.frame creationSnapshot == some lexical)
          "escaped view lost its original lambda's creation snapshot"
      | _ => throw (IO.userError "escaped view did not retain its original native callable")
    | _ => throw (IO.userError "escaped read wrapper did not save its two values at creation")
    -- Closures capture by value: `getLocal`'s input and the returned closure's
    -- snapshot keep 3, and each application increments its own copy once.
    let seeds := (ledger.ledger.rows.filter (fun row =>
        row.entry.key.binder.name == "seed" && row.entry.key.owner == getOwner)).map (·.payload)
    assertTrue (seeds == [3, 3, 4, 4].map (fun n => some (.word (w n))))
      "escaped applications did not each restart from the returned closure's snapshot"
    let items := ledger.ledger.rows.filter (·.entry.key.binder.name == "item")
    assertTrue (items.length == 2) "escaped applications lost their source parameter allocations"
    for row in items do
      let snapshot ← get "escaped application snapshot"
        (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue (match snapshot.frame with | .state _ => true | _ => false)
        "escaped application saved a transient or recursive carrier"
      assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame).isSome)
        "escaped indexed snapshot lacked a prepared source profile"

private def otherFlows {checked : Checked} (prepared : Prepared checked)
    (graph : SourceCoreCallableAncestryPairedPreparation.Prepared prepared.base)
    (program : CheckedProgram) : IO Unit := do
  -- Each call starts again from its lambda's creation-time captures: the second
  -- call of `mono`'s `f` returns 10 + 4, and the thirty calls in `repeatViews`
  -- each increment their own copy of `total`, which stays 0.
  for (name, arguments, expected) in [
      ("mono", [SourceTypedRuntime.Value.word (w 10)], 14),
      ("zero", [], 9), ("unused", [], 7), ("looping", [.word (w 4)], 6), ("deep", [], 7),
      ("repeatViews", [.word (w 30)], 0)] do
    let owner ← key program name
    for spent in [0, 37, 150000] do
      let completion ← successful prepared owner arguments expected spent
      let ledger ← get "indexed simple flow ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
      for row in ledger.ledger.rows do
        let snapshot ← get "indexed simple flow snapshot"
          (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
        assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame).isSome) s!"{name} lost an allocation metadata profile"
        assertTrue (match snapshot.frame with | .state _ => true | _ => false)
          s!"{name} allocation transported a recursive or transient frame"
        if name == "zero" && row.entry.key.binder.name == "probe" then
          assertTrue (match snapshot.frame with | .state .. => true | _ => false)
            "zero-parameter monomorphic lambda acquired a generalized view"
        if name == "unused" && row.entry.key.binder.name == "unused" then
          assertTrue (row.payload == some .unit) "unused principal unexpectedly required a native lambda"
  -- `f` is still uninitialized when its lambda is created, so the lambda's copy
  -- of `f` is too, and the first recursive read faults.
  let recursive ← key program "recursive"
  let missing ← binder prepared recursive "f"
  for spent in [0, 37, 150000] do
    let completion ← completed prepared recursive [.word (w 4)] spent
    match completion.result.native.observation with
    | .failed reason _ =>
      assertTrue ((completion.result.diagnostics.diagnostic? reason).map (·.error) == some (.uninitializedLocal missing))
        "read of the lambda's uninitialized copy of its own local did not fault"
    | other => throw (IO.userError s!"indexed recursive capture classification changed: {reprStr other}")
    let ledger ← get "indexed recursive ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    for row in ledger.ledger.rows do
      let snapshot ← get "indexed recursive snapshot"
        (SourceCoreCallableIndexedAllocationFrames.snapshot prepared.ancestry.layout.frame row)
      assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table snapshot.frame).isSome)
        "recursive lost an allocation metadata profile"
      assertTrue (match snapshot.frame with | .state _ => true | _ => false)
        "recursive allocation transported a recursive or transient frame"
  let failed ← get "indexed language failure" (prepared.runSource (← key program "absent") [.word (w 3)] 150000 500)
  match failed.result.native.observation with
  | .failed reason _ =>
    assertTrue ((failed.result.diagnostics.diagnostic? reason).isSome) "indexed failure lost its source diagnostic"
    assertTrue (SourceCoreCallableIndexedLedger.frame? failed == some .empty) "language failure did not restore context"
    let ledger ← get "indexed failure ledger" (SourceCoreCallableIndexedLedger.scan failed initial)
    -- The input and the snapshot of `f` keep 3; the call's own copy keeps the
    -- body's write made before the failure.
    let seeds := (ledger.ledger.rows.filter (·.entry.key.binder.name == "seed")).map (·.payload)
    assertTrue (seeds == [3, 3, 4].map (fun n => some (.word (w n))))
      "language failure erased the call's earlier write to its copy"
  | other => throw (IO.userError s!"indexed language failure classification changed: {reprStr other}")
  let pending ← get "indexed nonterminating run" (prepared.runSource (← key program "spin") [] 5000 500)
  let resumed := pending.resume 5000
  for completion in [pending, resumed] do
    assertTrue (match completion.result.native.observation with | .outOfFuel .. => true | _ => false)
      "infinite source loop was reported as completion"
    let _ ← get "indexed suspended ledger" (SourceCoreCallableIndexedLedger.scan completion initial)
    let current ← match SourceCoreCallableIndexedLedger.frame? completion with
      | some current => pure current | none => throw (IO.userError "suspended indexed frame missing")
    assertTrue ((SourceCoreCallableIndexedDispatch.lookup? graph.table current).isSome) "suspended callable lost its prepared metadata profile"

def run : IO Unit := do
  let program ← get "indexed source checker" (checkProgram workspace)
  let names := ["sharedHistory", "getLocal", "useReturned", "mono", "zero", "recursive", "unused", "deep", "repeatViews", "looping", "absent", "spin"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"indexed worklist failed: {reprStr other}")
  let automatic ← get "indexed compatible base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "indexed two-pass compiler" (SourceCoreCallableIndexedPrograms.prepare automatic.prepared 500)
  let graph := prepared.ancestry.graph
  assertTrue (prepared.entries.length == keys.length) "indexed root inventory changed"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "indexed administrative suffix changed the original catalog"
  assertTrue (!prepared.layouts.entries.isEmpty) "indexed compilation emitted no source markers"
  shared prepared graph (← key program "sharedHistory")
  escaped prepared graph (← key program "getLocal") (← key program "useReturned")
  otherFlows prepared graph program
  IO.println "actual indexed callable compiler: cached caller/lexical edges, constant-depth snapshots, by-value captures, failures and typed resume GREEN"

end Tests.SourceCoreCallableIndexedPrograms
end
