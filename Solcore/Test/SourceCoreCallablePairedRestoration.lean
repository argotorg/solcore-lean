import Solcore.Frontend.SourceCoreCallablePairedRestoration
import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.Ordinary.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.Read.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.ProducedRead.mk
#check_failure Solcore.Frontend.SourceCoreCallablePairedRestoration.StoredRead.mk

set_option autoImplicit false
namespace Tests.SourceCoreCallablePairedRestoration
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function qualified(seed: Word) returns (F) { let f = lam(item) { keep(item); seed += 1; return seed; }; return f; }",
    "function nested(seed: Word) returns (F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); seed += 1; return seed; }; return inner; }; return outer(1); }",
    "function shared(seed: Word) returns (F) { let f = lam(item) { seed += 1; return seed; }; let outer = lam(value) { keep(value); return f; }; return outer(1); }",
    "function mono(seed: Word) returns (F) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return f; }",
    "function failure(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; while (true) {} return 0; }",
    "function named(seed: Word) returns (F) { return plus; }",
    "function plus(value: Word) returns (Word) { return value + 1; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"restoration fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["qualified", "nested", "shared", "mono", "failure", "suspended", "named"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"restoration worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"restoration base failed: {reprStr error}")
private def initial : List SourceTypedRuntime.Cell := [⟨.word, none⟩, ⟨.function .word .word, none⟩]

private def returned {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallablePairedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    (headers : SourceCoreCallablePairedHeaders.Prepared graph)
    (templates : SourceCoreCallablePairedTemplates.Cache program)
    (views : SourceCoreCallablePairedReadViews.Cache templates) (owner : Key) (ordinary shared : Bool) : IO Unit := do
  for spent in [0, 31, 100000] do
    let first ← match program.runSource owner [.word (w 3)] spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"restoration run failed: {reprStr error}")
    let completion := first.resume 100000
    if same : completion.entry.native.resultType = Core.CallableContract.functionType .word .word then
      match success : completion.result.native.observation with
      | .succeeded value store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store program.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType .word .word) program.layouts.definitions := by
          obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
          have equal := stored.world_eq
          subst world
          exact ⟨stored, by simpa only [same] using typed⟩
        let ledger ← match SourceCoreAllocationLedger.scanTyped program.layouts initial (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"restoration ledger failed: {reprStr error}")
        if ordinary then
          let authenticated ← match SourceCoreCallablePairedTemplates.authenticate templates typed.1 value .word .word typed.2 with
            | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"ordinary auth failed: {reprStr error}")
          let produced := SourceCoreCallablePairedCaptures.Produced.of_success authenticated success .root
          let receipt ← match SourceCoreCallablePairedRestoration.restoreProducedOrdinary headers produced ledger with
            | .ok receipt => pure receipt | .error error => throw (IO.userError s!"ordinary restoration failed: {reprStr error}")
          let restored := receipt.restored
          assertTrue (restored.source.type? program.base.plan == some (.function .word .word)) "ordinary restored type changed"
          match restored.source with
          | .closure parameters result body source owner captures _ =>
            assertTrue (parameters == restored.header.parameters && result == restored.header.resultType && body == restored.header.body)
              "ordinary restoration changed its raw header"
            assertTrue (source == restored.header.state.metadata.source && owner == restored.header.state.metadata.owner)
              "ordinary restoration changed its lexical source"
            assertTrue (captures == restored.captures.environment && captures.length == 1) "ordinary restoration changed captures"
          | _ => throw (IO.userError "ordinary source closure shape changed")
        else
          let authenticated ← match SourceCoreCallablePairedReadViews.authenticate views typed.1 value .word .word typed.2 with
            | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"read auth failed: {reprStr error}")
          let produced := SourceCoreCallablePairedReadViews.Produced.of_success (authenticated := authenticated) success .root
          let receipt ← match SourceCoreCallablePairedRestoration.restoreProducedRead headers produced ledger with
            | .ok receipt => pure receipt | .error error => throw (IO.userError s!"read restoration failed: {reprStr error}")
          let restored := receipt.restored
          assertTrue (restored.source.type? program.base.plan == some (.function .word .word)) "read restored type changed"
          match restored.source with
          | .instantiated substitution witnesses (.closure parameters result body source owner captures _) =>
            assertTrue (substitution == restored.recipe.read.substitution && witnesses.length == (if shared then 0 else 1))
              "read restoration changed its actual own substitution or witnesses"
            assertTrue (parameters == restored.recipe.applied.parameters && result == restored.recipe.applied.resultType && body == restored.recipe.applied.body)
              "read restoration replaced the original raw header"
            assertTrue (parameters.any (fun binder => !binder.scheme.body.freeVariables.isEmpty)) "read restoration prematurely specialized raw parameters"
            assertTrue (source == restored.recipe.lexical.metadata.source && owner == restored.recipe.lexical.metadata.owner)
              "read restoration used caller source instead of lexical source"
            assertTrue (captures == restored.captures.environment && captures.all (fun binding => initial.length ≤ binding.2.index))
              "read restoration changed source captures or opaque prefix"
            if shared then assertTrue (restored.caller != restored.lexical) "shared read collapsed caller and lexical states"
          | _ => throw (IO.userError "read restoration lost instantiated original closure")
      | _ => throw (IO.userError "restoration invocation did not succeed")
    else throw (IO.userError "restoration result projection changed")

private def stored {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallablePairedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    (headers : SourceCoreCallablePairedHeaders.Prepared graph)
    {templates : SourceCoreCallablePairedTemplates.Cache program}
    (views : SourceCoreCallablePairedReadViews.Cache templates) (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match program.runSource owner [.word (w 3)] 10000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored restoration run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored restoration observation changed"
  let ledger ← match SourceCoreCallablePairedLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored restoration ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored restoration allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored restoration payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallablePairedLedger.world completion) value
          (Core.CallableContract.functionType .word .word) program.layouts.definitions := by
        simpa only [type] using row.payload_typed ledger.typed payloadFound
      let authenticated ← match SourceCoreCallablePairedReadViews.authenticate views ledger.typed value .word .word typed with
        | .ok authenticated => pure authenticated | .error error => throw (IO.userError s!"stored restoration auth failed: {reprStr error}")
      let stored := SourceCoreCallablePairedReadViews.Stored.of_payload (authenticated := authenticated) rfl ordinal payloadFound .root
      let receipt ← match SourceCoreCallablePairedRestoration.restoreStoredRead headers stored with
        | .ok receipt => pure receipt | .error error => throw (IO.userError s!"stored read restoration failed: {reprStr error}")
      assertTrue (receipt.restored.source.type? program.base.plan == some (.function .word .word)) "stored source type changed"
      assertTrue (receipt.restored.captures.environment.length == 1) "stored source seed capture missing"
    else throw (IO.userError "stored restoration payload type changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"restoration source rejected: {reprStr error}")
  let automatic ← artifact program
  let native ← match SourceCoreCallablePairedPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"restoration marked compiler failed: {reprStr error}")
  let templates ← match SourceCoreCallablePairedTemplates.prepare native with
    | .ok templates => pure templates | .error error => throw (IO.userError s!"restoration template cache failed: {reprStr error}")
  let views ← match SourceCoreCallablePairedReadViews.prepare templates with
    | .ok views => pure views | .error error => throw (IO.userError s!"restoration wrapper cache failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPairedPreparation.prepare native.base with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"restoration graph failed: {reprStr error}")
  let headers ← match SourceCoreCallablePairedHeaders.prepare graph with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"restoration header cache failed: {reprStr error}")
  returned headers templates views (← key program "qualified") false false
  returned headers templates views (← key program "nested") false false
  returned headers templates views (← key program "shared") false true
  returned headers templates views (← key program "mono") true false
  stored headers views (← key program "failure") false
  stored headers views (← key program "suspended") true
  let outputRecipe ← match SourceCoreCompatibleOutputs.preparePaired native with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"paired output recipe failed: {reprStr error}")
  let named ← match native.runSource (← key program "named") [.word (w 3)] 100000 500 with
    | .ok named => pure named | .error error => throw (IO.userError s!"paired named run failed: {reprStr error}")
  match projected : automatic.checked.catalog.project (.function .word .word) with
  | .error error => throw (IO.userError s!"paired named output projection failed: {reprStr error}")
  | .ok type =>
    if same : type = named.entry.native.resultType then
      have projection : automatic.checked.catalog.project (.function .word .word) = .ok named.entry.native.resultType := by
        simpa only [same] using projected
      match SourceCoreCompatibleOutputs.decodeSuccess outputRecipe named.result.context named.result.contextOwner
          (.function .word .word) projection named.result.native with
      | .ok decoded => match decoded.decoded.source with
        | .global owner _ => assertTrue (owner == (← key program "plus")) "paired global output owner changed"
        | _ => throw (IO.userError "paired named output source shape changed")
      | .error error => throw (IO.userError s!"paired named output decode failed: {reprStr error}")
    else throw (IO.userError "paired named output projection changed")
  IO.println "paired raw closure/read and failed/suspended heap restoration, named exact outputs GREEN"

end Tests.SourceCoreCallablePairedRestoration
