import Solcore.SourceSemantics.CoreLowering.RecursiveNamedCatalogPreparedInitialization
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Formal consumers start from actual compiled preparation. They request no
lambda-row decoding equation, ordered cache-signature law, global-signature
law or syntactic support input. Independent source headers and their ledger
remain explicit. Native IO audits actual cached code and original bootstrap. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPreparedInitialization
open Solcore Core Frontend SourceSemantics SourceSemantics.CoreLowering
open GeneralHeap ReadOnly CompatiblePayload RecursiveNamedCatalog
open RecursiveGlobalInitializationMeaning RecursiveGlobalInitializationTyping

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)

include accepted in
theorem actual_typed_initial_store :
    ∃ world, RuntimeStoreHasTypes world (RecursiveNamedCatalogPreparedInitialization.store compiled)
      compiled.indexed.layouts.definitions :=
  RecursiveNamedCatalogPreparedInitialization.typed accepted

include accepted in
theorem actual_cached_support {slot : Nat} {code : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    NativeExpressionContextSupport.supported code (compiled.indexed.base.globals.length + 1) = true :=
  RecursiveNamedCatalogPreparedInitialization.supported_cached accepted cached

variable {values : ValuesContext} {ambient : AmbientDefinitions values.checked.catalog.definitions} {program : SourceSemantics.Program}
  (headers : Inventory compiled.indexed.ancestry values ambient.definitions program)
  (ledger : Ledger headers compiled.indexed.secondPass.closures)
  (sizes : ∀ header, header ∈ headers → header.globals = compiled.indexed.base.globals.length)
  (locals : ∀ header, header ∈ headers → header.function.context.locals = [])
  (definitions : compiled.indexed.layouts.definitions = ambient.definitions)

include accepted ledger sizes locals definitions in
theorem actual_source_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry) :
    ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩
        (RecursiveNamedCatalogPreparedInitialization.store compiled) ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ (RecursiveNamedCatalogPreparedInitialization.store compiled)
        (RecursiveNamedCatalogPreparedInitialization.environment compiled)) :=
  RecursiveNamedCatalogPreparedInitialization.entry compiled headers ledger sizes locals accepted definitions functions registry

include accepted ledger sizes locals definitions in
theorem actual_completed_source_entry
    (functions : FunctionModel values.checked.catalog ambient) (registry : SourceCoreRawMetadata.Registry)
    {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧ ∃ world,
      CompatibleAmbientHeap.HeapRepresents values.checked registry functions [] world ⟨[]⟩ finalStore ∧
      Nonempty (Entry headers
        (fun header => RecursiveNamedCatalogInitialization.location compiled.indexed.base.globals header.slot)
        0 0 [] [] world ⟨[]⟩ finalStore (RecursiveNamedCatalogPreparedInitialization.environment compiled)) :=
  RecursiveNamedCatalogPreparedInitialization.completed_entry compiled headers ledger sizes locals accepted definitions functions registry completed
end Formal

private def content : String := String.intercalate "\n" [
  "function step(value: Word) returns (Word) { return value + 1; }",
  "function left(n: Word) returns (Bool) { if (n == 0) { return true; } return right(n - 1); }",
  "function right(n: Word) returns (Bool) { if (n == 0) { return false; } return left(n - 1); }",
  "function make(seed: Word) returns (function(Word) returns (Word)) { let extra = step(seed); return lam(value: Word) -> Word { extra += value; return extra; }; }",
  "function terminal(flag: Bool) returns (Word) { if (flag) { return 7; } else { return 9; } }",
  "function failed() returns (Word) { let gap: Word; return gap; }",
  "function zero() {}"
]
private def require := SourceCoreUnifiedCorpusSupport.assertTrue
private def get {α ε : Type} [Repr ε] := @SourceCoreUnifiedCorpusSupport.get α ε _
private def finish (state : State) : IO (Value × Store) :=
  match runStateful 300000 state with
  | .done value store => pure (value, store)
  | other => throw (IO.userError s!"prepared initialization did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "prepared catalog initialization" content
    ["left", "right", "make", "terminal", "failed", "zero"]
  let recipe ← get "actual prepared initialization recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let rows := RecursiveNamedCachedRows.rows compiled
  let base := compiled.indexed.base
  require (rows.length == base.functions.length && rows.length == base.globals.length)
    "actual complete ordered cache length changed"
  require (reprStr (rows.map LambdaRow.expression) == reprStr compiled.indexed.secondPass.closures)
    "actual entire cached lambda code changed"
  for (row, slot) in rows.zipIdx do
    let named ← match base.functions[slot]? with
      | some named => pure named | none => throw (IO.userError "actual row lost ordered named function")
    let signature ← match base.globals[slot]? with
      | some signature => pure signature | none => throw (IO.userError "actual row lost full signature")
    require (signature == named.signature && row.parameter == signature.parameterType &&
      row.result == LanguageResult.resultType signature.resultType)
      "full prepared row signature/order changed"
    require (NativeExpressionContextSupport.supported row.expression (base.globals.length + 1))
      "actual cached support depends on an extra wrapper input"
  let expected := RecursiveNamedCatalogPreparedInitialization.store compiled
  let canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr store == reprStr expected && reprStr value == reprStr (Value.inRight .word .unit))
    "actual prepared bootstrap result/store changed"
  for (row, slot) in rows.zipIdx do
    let expectedClosure : Value := .inRight .unit (installedValue canonical slot row)
    require (reprStr (store.read? (RecursiveNamedCatalogInitialization.location base.globals slot)) ==
      reprStr (some expectedClosure)) "actual complete stored closure/capture changed"
    match expectedClosure with
    | .inRight _ (.closure parameter result body captured) =>
      require (infer? (parameter :: captured.map Value.type) body compiled.indexed.layouts.definitions == some result)
        "actual prepared stored body/capture typing changed"
    | _ => throw (IO.userError "prepared actual row did not produce a closure")
  for fuel in [0, 1, 43, 300000] do
    let resumed ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel state => finish state
      | other => throw (IO.userError s!"actual prepared bootstrap failed: {reprStr other}")
    require (reprStr resumed == reprStr (value, store)) s!"prepared bootstrap resume changed {fuel}"
  IO.println "prepared catalog initialization: actual whole cache rows/signatures/code/support, full stored captures and bootstrap resume GREEN"

end Tests.SourceCoreRecursiveNamedPreparedInitialization
