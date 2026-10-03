import Solcore.SourceSemantics.CoreLowering.RecursiveNamedPublicBootstrapGlobals
import Solcore.Test.SourceCoreUnifiedCorpusSupport

/-! Formal consumers connect the actual owned cache to the public native
checker after fresh initialization. IO audits the whole ordered cache, exact
closure bodies and captures, occupied slots, checker rejection and both native
and public bootstrap resumption. Source body meaning is outside this unit. -/
#check_failure Solcore.Frontend.SourceTypedRuntime.run
set_option autoImplicit false
namespace Tests.SourceCoreRecursiveNamedPublicBootstrapGlobals
open Solcore Core Frontend SourceSemantics.CoreLowering
open RecursiveGlobalInitializationMeaning

section Formal
variable (compiled : SourceCoreUnifiedCompilation.Compiled)
  (cache : SourceCoreCallableIndexedTemplates.Cache compiled.indexed)

theorem public_environment :
    RecursiveNamedCatalogPreparedInitialization.environment compiled =
      SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed :=
  RecursiveNamedPublicBootstrapGlobals.environment_eq compiled

theorem actual_complete_native_slots :
    cache.nativeGlobals.length = compiled.indexed.base.globals.length ∧
      ∀ slot, slot ∈ cache.nativeGlobals →
        (RecursiveNamedCatalogPreparedInitialization.store compiled)[slot.1]? = some slot.2 :=
  ⟨RecursiveNamedPublicBootstrapGlobals.native_globals_length compiled cache,
    fun _ member => RecursiveNamedPublicBootstrapGlobals.native_slot compiled cache member⟩

theorem actual_cached_code_capture {slot : Nat} {code : Expr}
    (cached : compiled.indexed.secondPass.closures[slot]? = some code) :
    ∃ row, (RecursiveNamedCachedRows.rows compiled)[slot]? = some row ∧ code = row.expression ∧
      (RecursiveNamedCatalogPreparedInitialization.store compiled)[RecursiveNamedCatalogInitialization.location
        compiled.indexed.base.globals slot]? = some (.inRight .unit
          (installedValue (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed) slot row)) :=
  RecursiveNamedPublicBootstrapGlobals.cached_slot compiled cached

theorem actual_public_check :
    ∃ globals : SourceCoreCallableIndexedTemplates.Globals compiled.indexed
        (RecursiveNamedCatalogPreparedInitialization.store compiled),
      SourceCoreCallableNativeSlots.checkPreparedGlobals cache.nativeGlobals cache.nativeGlobalsGenerated
        (RecursiveNamedCatalogPreparedInitialization.store compiled) = .ok globals :=
  RecursiveNamedPublicBootstrapGlobals.globals_checked compiled cache

variable {recipe : SourceCoreIndexedSession.Recipe}
  (accepted : SourceCoreIndexedSession.Recipe.prepare compiled = .ok recipe)
include accepted in
theorem actual_completed_public_check {fuel : Nat} {value : Value} {finalStore : Store}
    (completed : runStateful fuel (.initial recipe.bootstrap [] []) = .done value finalStore) :
    value = .inRight .word .unit ∧
      ∃ globals : SourceCoreCallableIndexedTemplates.Globals recipe.compiled.indexed finalStore,
        SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
          finalStore = .ok globals :=
  RecursiveNamedPublicBootstrapGlobals.completed_globals accepted completed
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
  | other => throw (IO.userError s!"public bootstrap globals did not finish: {reprStr other}")

def run : IO Unit := do
  let compiled ← SourceCoreUnifiedCorpusSupport.prepare "public bootstrap globals" content
    ["step", "left", "right", "make", "terminal", "failed", "zero"]
  let recipe ← get "public bootstrap recipe" (SourceCoreIndexedSession.Recipe.prepare compiled)
  let base := compiled.indexed.base
  let rows := RecursiveNamedCachedRows.rows compiled
  let canonical := RecursiveNamedCatalogPreparedInitialization.environment compiled
  let publicGlobals := SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed
  require (reprStr canonical == reprStr publicGlobals) "actual initial environment differs from public globals"
  require (rows.length == base.globals.length && recipe.templates.nativeGlobals.length == base.globals.length)
    "public bootstrap omits a cached/global slot"
  let expectedSlots := rows.zipIdx.map fun (row, slot) =>
    (RecursiveNamedCatalogInitialization.location base.globals slot, Value.inRight .unit (installedValue publicGlobals slot row))
  require (reprStr recipe.templates.nativeGlobals == reprStr expectedSlots)
    "actual generator changed ordered full code/capture slots"
  let (value, store) ← finish (.initial recipe.bootstrap [] [])
  require (reprStr value == reprStr (Value.inRight .word .unit) &&
    reprStr store == reprStr (RecursiveNamedCatalogPreparedInitialization.store compiled))
    "closed fresh initialization changed value or whole store"
  require (store.length == base.globals.length + 1 &&
    reprStr store[0]? == reprStr (some (SourceCoreCallableIndexedFrames.encode compiled.indexed.ancestry.layout.frame .empty)))
    "fresh initialization changed frame zero or physical slot count"
  for (row, slot) in rows.zipIdx do
    let location := RecursiveNamedCatalogInitialization.location base.globals slot
    require (reprStr publicGlobals[slot]? == reprStr (some (Value.cellRef (OptionalCell.cellType (.function row.parameter row.result)) location)))
      "public environment lost actual full signature/reference order"
    require (reprStr store[location]? == reprStr (some (Value.inRight .unit (installedValue publicGlobals slot row))))
      "cached code, Unit prefix or captured public globals changed"
  for (location, closure) in recipe.templates.nativeGlobals do
    require (reprStr store[location]? == reprStr (some closure)) "generated native slot missing in bootstrap store"
    require (!(SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
      (store.set location .unit)).isOk) "public checker accepted a corrupted installed closure"
  require (SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated store).isOk
    "public checker rejected closed initialization"
  require (SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated
    (store ++ [.word (Word.ofNatModulo 88)])).isOk "public global checker changed occupied slots under extra cell"
  let (_, shiftedStore) ← finish (.initial recipe.bootstrap [] [.word (Word.ofNatModulo 88)])
  require (!(SourceCoreCallableNativeSlots.checkPreparedGlobals recipe.templates.nativeGlobals recipe.templates.nativeGlobalsGenerated shiftedStore).isOk)
    "fresh-base-zero checker accepted a displaced native initialization"
  for fuel in [0, 1, 43, 300000] do
    let resumed ← match runStateful fuel (.initial recipe.bootstrap [] []) with
      | .done value store => pure (value, store)
      | .outOfFuel state => finish state
      | other => throw (IO.userError s!"public bootstrap native fault: {reprStr other}")
    require (reprStr resumed == reprStr (value, store)) s!"full fresh native bootstrap resume changed {fuel}"
    let artifact ← recipe.open
    let bootstrap ← artifact.bootstrapFresh
    let session ← match bootstrap.resume fuel with
      | .ready session => pure session
      | .outOfFuel next => match next.resume 300000 with
        | .ready session => pure session
        | .error error => throw (IO.userError s!"public bootstrap resume rejected globals: {reprStr error}")
        | .outOfFuel _ => throw (IO.userError "public bootstrap resume did not finish")
      | .error error => throw (IO.userError s!"public bootstrap rejected globals: {reprStr error}")
    require (session.installedGlobalsPresent && session.heapSize == store.length)
      "public bootstrap lacks complete installed globals"
    let step ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "step"
    let outcome ← get "public call after bootstrap" (← session.run step [.word (Word.ofNatModulo 40)] 300000)
    let afterStep ← match outcome with
      | .succeeded result =>
        require (result.value == .word (Word.ofNatModulo 41) && result.session.installedGlobalsPresent)
          "public success changed installed globals or result"
        pure result.session
      | _ => throw (IO.userError "public initialized step did not succeed")
    let failed ← SourceCoreUnifiedCorpusSupport.key compiled.sourceProgram "failed"
    let outcome ← get "public fault after bootstrap" (← afterStep.run failed [] 300000)
    match outcome with
    | .failed _ session => require session.installedGlobalsPresent "public language fault replaced installed globals"
    | _ => throw (IO.userError "public initialized fault changed category")
  IO.println "public bootstrap globals: complete ordered native slots/code/captures, exact public environment, checker rejection and full native/public resume GREEN"

end Tests.SourceCoreRecursiveNamedPublicBootstrapGlobals
