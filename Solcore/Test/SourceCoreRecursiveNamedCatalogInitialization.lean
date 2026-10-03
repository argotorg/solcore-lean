import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogInitialization
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Formal consumers derive the initial whole catalog and empty represented
source heap from the actual accepted recipe. No body meaning or source execution
is an input. Native IO audits deep installed closure typing and complete captures;
it does not manufacture semantic source headers from a runtime cache. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedCatalogInitialization
open Solcore Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping
open RecursiveNamedCatalogInitialization

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (rows : List LambdaRow)
  (cached : compiled.indexed.secondPass.closures = rows.map LambdaRow.expression)
  (ordered : ∀ (i : Nat) (row : LambdaRow), rows[i]? = some row → ∃ (signature : Signature),
    compiled.indexed.base.globals[i]? = some signature ∧ signature.functionType = .function row.parameter row.result)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (globals : ∀ header, header ∈ headers → compiled.indexed.base.globals[header.slot]? = some header.named.signature)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_authority :
    ∃ world, Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
      (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) :=
  of_recipe compiled headers rows cached ordered ledger globals sizes locals accepted definitions

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_source_heap
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)) := by
  obtain ⟨world, heaps, ⟨entry⟩⟩ := initial_entry compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry
  exact ⟨world, heaps, ⟨entry.authority⟩⟩

include cached ordered ledger globals sizes locals accepted definitions in
theorem actual_initial_caller_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame) ∧
      Nonempty (Entry headers (fun header => location compiled.indexed.base.globals header.slot) 0 0 [] [] world ⟨[]⟩
        (initialStore compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame)
        (initialEnvironment compiled.indexed.base.globals compiled.indexed.ancestry.layout.frame)) :=
  initial_entry compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry

include cached ordered ledger globals sizes locals accepted definitions in
/-- Any finite completion of the original bootstrap has this same initialized
store and whole catalog. It does not use a source execution as a premise. -/
theorem any_completed_bootstrap
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Authority headers (fun header => location compiled.indexed.base.globals header.slot) 0 [] world ⟨[]⟩ finalStore) := by
  obtain ⟨_, emitted⟩ := recipe_emitted accepted
  have expected := framed_bootstrap compiled.indexed.base.globals rows compiled.indexed.ancestry.layout.frame ordered
  rw [← cached, ← emitted] at expected
  obtain ⟨rfl, rfl⟩ := evaluation_deterministic (runStateful_evaluation_sound completed) expected
  exact ⟨rfl, actual_initial_source_heap compiled headers rows cached ordered ledger globals sizes locals accepted definitions functions registry⟩
end Formal

private def content : String := String.intercalate "\n" [
  "function step(value: Word) returns (Word) { return value + 1; }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { if (n == 0) { return false; } return left(n - 1); }",
  "function order(first: Word, flag: Bool, last: Word) returns (Word) { if (flag) { return step(first); } return step(last); }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { extra += value; return extra; }; }",
  "function fail() returns (Word) { let written = 17; let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def finish (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"catalog initialization did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "initial whole catalog" content
    ["left", "right", "order", "make", "fail", "zero"]
  let indexed := compiled.indexed
  let recipe ← get "actual initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows ← indexed.secondPass.closures.mapM fun expression =>
    match expression with
    | .lambda parameter result body => pure (⟨parameter, result, body⟩ : LambdaRow)
    | _ => throw (IO.userError "actual cached row is not a lambda")
  let canonical := initialEnvironment indexed.base.globals indexed.ancestry.layout.frame
  let expected := initialStore indexed.base.globals rows indexed.ancestry.layout.frame
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected) "initial whole catalog store changed"
  require (reprStr value == reprStr (Value.inRight .word .unit)) "initial whole catalog success changed"
  let world := store.map Value.type
  require (world[0]? == some indexed.ancestry.layout.frame.type) "initial frame type changed"
  require (store.read? 0 == some (SourceCoreCallableIndexedFrames.encode indexed.ancestry.layout.frame .empty))
    "actual empty frame changed"
  for reference in canonical do
    match reference with
    | .cellRef element location =>
      require (world[location]? == some element) "canonical global/frame reference type changed"
    | _ => throw (IO.userError "initial canonical environment contains a non-reference")
  for (row, slot) in rows.zipIdx do
    let signature ← match indexed.base.globals[slot]? with
      | some signature => pure signature | none => throw (IO.userError "real ordered signature missing")
    require (signature.functionType == .function row.parameter row.result) "full static cache signature changed"
    require (canonical[slot]? == some (.cellRef (OptionalCell.cellType signature.functionType) (location indexed.base.globals slot)))
      "actual coherent catalog reference changed"
    match store.read? (location indexed.base.globals slot) with
    | some (.inRight .unit (.closure parameter result body captured)) =>
      require (captured.length == slot + canonical.length) "real installer capture prefix length changed"
      require (captured.take slot == List.replicate slot Value.unit) "real installer Unit capture prefix changed"
      require (reprStr (captured.drop slot) == reprStr canonical) "canonical captured catalog changed"
      require (reprStr body == reprStr (row.body.rename (shift slot).lift)) "full actual renamed closure code changed"
      require (infer? (parameter :: captured.map Value.type) body indexed.layouts.definitions == some result)
        "deep native typing of actual stored capture/code failed"
      require (captured[shift slot indexed.base.globals.length]? == canonical[indexed.base.globals.length]?)
        "actual captured frame reference changed"
    | _ => throw (IO.userError "actual installed full closure missing")
  for fuel in [0, 1, 43, 300000] do
    let result ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel checkpoint => finish checkpoint
      | other => throw (IO.userError s!"actual typed bootstrap fault {reprStr other}")
    require (reprStr result == reprStr (value, store)) s!"whole initialized catalog resume changed {fuel}"
  IO.println "initial whole catalog: actual native store/capture typing, full coherent global/frame references, empty frame and complete resume GREEN"

end Tests.SourceCoreRecursiveNamedCatalogInitialization
