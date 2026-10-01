import Solcore.SourceSemantics.CoreLowering.CallableIndexedAmbient
import Solcore.SourceSemantics.CoreLowering.CompatibleAmbientHeap
import Solcore.SourceSemantics.CoreLowering.CompatibleEqualityMeaning
import Solcore.SourceSemantics.CoreLowering.CompatiblePayloadRuntimeTypes
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder
import Solcore.SourceSemantics.CoreLowering.DataMappingHeap
import Solcore.Frontend.SourceCoreCallableIndexedLedger
import Solcore.Frontend.ProgramChecking

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
  match completion.result.native.observation with
  | .succeeded (.word result) _ => assertTrue (result == Word.ofNatModulo 9) "ambient closure lost shared captured cell"
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
