import Solcore.Frontend.SourceCoreCallableAncestryCaptures
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Produced.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Stored.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Captured.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Slot.mk

/-! Actual two-pass compilation and typed native observations establish
provenance. Captures join by native location, not repeated source binder IDs.
Ordered source environments preserve aliasing and opaque-prefix offsets.
Stored lambda payloads are also joined on language failure and suspension. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryCaptures
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableAncestryCaptures
abbrev Key := SourceSpecialization.SpecializationKey
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function escaped(seed: Word) returns (F, F) {",
    " let outer = lam(value) { keep(value); let inner: F = lam(delta: Word) -> Word { seed = seed + delta; return seed; }; return inner; };",
    " return (outer(1), outer(2)); }",
    "function recursive(n: Word, value: Word) returns (F) { if (n == 0) { return lam(delta: Word) -> Word { value += delta; return value; }; } return recursive(n - 1, value + 1); }",
    "function repeated() returns (F, F) { return (recursive(2, 1), recursive(2, 10)); }",
    "function failure(seed: Word) returns (Word) { let captured: F = lam(delta: Word) -> Word { seed += delta; return seed; }; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let captured: F = lam(delta: Word) -> Word { seed += delta; return seed; }; while (true) {} return 0; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"captures fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["escaped", "repeated", "failure", "suspended"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"capture worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"capture base failed: {reprStr error}")
private def initial : SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example : ContextExtends [((⟨1⟩ : TypeSystem.TypeVarId), .variable ⟨2⟩)]
    [((⟨1⟩ : TypeSystem.TypeVarId), .word), (⟨2⟩, .word)] := by decide
example : ¬ContextExtends [((⟨1⟩ : TypeSystem.TypeVarId), .bool)]
    [((⟨1⟩ : TypeSystem.TypeVarId), .word), (⟨2⟩, .word)] := by decide

private def captureNamed {checked : Checked} {prepared : Prepared checked} {cache : Cache prepared}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (auth : Authenticated cache world store value) (name : String) : Option Resolved.LocalId :=
  (auth.sourceCaptures.find? fun capture =>
    (auth.template.source.lambda.context.bindingAt? capture.binder).map (·.binding.binder.name) == some name).map (·.binder)

private def checkPair {checked : Checked} (prepared : Prepared checked) (cache : Cache prepared)
    (owner : Key) (arguments : List SourceTypedRuntime.Value) (shared : Bool) (name : String) : IO Unit := do
  for spent in [0, 39, 250000] do
    let first ← match prepared.runSource owner arguments spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"capture invocation failed: {reprStr error}")
    let early ← match SourceCoreCallableAncestryLedger.scan first initial with
      | .ok early => pure early | .error error => throw (IO.userError s!"capture partial ledger failed: {reprStr error}")
    assertTrue (early.ledger.initialHeap.map (·.type) == initial.map (·.type)) "partial ledger changed inert source prefix"
    let completion := first.resume 250000
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
          cases typed with
          | pair left right => exact ⟨stored, left, right⟩
        let leftAuth ← match SourceCoreCallableAncestryTemplates.authenticate cache typed.1 left .word .word typed.2.1 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"left capture auth failed: {reprStr error}")
        let rightAuth ← match SourceCoreCallableAncestryTemplates.authenticate cache typed.1 right .word .word typed.2.2 with
          | .ok auth => pure auth | .error error => throw (IO.userError s!"right capture auth failed: {reprStr error}")
        let leftProduced := Produced.of_success leftAuth success (.pairLeft .root)
        let rightProduced := Produced.of_success rightAuth success (.pairRight .root)
        let emptyLedger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts [] (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"capture zero-prefix ledger failed: {reprStr error}")
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts initial (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"capture prefix ledger failed: {reprStr error}")
        let leftJoined ← match join leftProduced ledger with
          | .ok receipt => pure receipt | .error error => throw (IO.userError s!"left source capture join failed: {reprStr error}")
        let rightJoined ← match join rightProduced ledger with
          | .ok receipt => pure receipt | .error error => throw (IO.userError s!"right source capture join failed: {reprStr error}")
        let leftEmpty ← match join leftProduced emptyLedger with
          | .ok receipt => pure receipt | .error error => throw (IO.userError s!"source prefix comparison failed: {reprStr error}")
        assertTrue (leftJoined.environment.map Prod.fst == leftAuth.template.source.scope.map Prod.fst)
          "join changed expected source binder order"
        assertTrue (leftJoined.environment.length == leftAuth.sourceCaptures.length)
          "join omitted source capture or added administrative slot"
        assertTrue (leftJoined.environment == leftEmpty.environment.map (fun (binder, location) => (binder, {location with index := location.index + initial.length})))
          "opaque prefix did not shift every source location by the same offset"
        let leftBinder ← match captureNamed leftAuth name with
          | some binder => pure binder | none => throw (IO.userError "left lexical binder not in manifest")
        let rightBinder ← match captureNamed rightAuth name with
          | some binder => pure binder | none => throw (IO.userError "right lexical binder not in manifest")
        assertTrue (leftBinder == rightBinder) "fixture stopped reusing the same source binder ID"
        let leftLocation := (leftJoined.environment.find? (fun binding => binding.1 == leftBinder)).map Prod.snd
        let rightLocation := (rightJoined.environment.find? (fun binding => binding.1 == rightBinder)).map Prod.snd
        assertTrue (leftLocation.isSome && rightLocation.isSome) "join dropped a captured source binder"
        assertTrue ((leftLocation == rightLocation) == shared)
          "join selected a repeated binder allocation by ID instead of exact native location"
        assertTrue (leftJoined.environment.all (fun binding => initial.length ≤ binding.2.index))
          "new closure capture escaped into the inert source prefix"
        if !shared then
          assertTrue ((ledger.ledger.rows.filter (fun row => row.entry.key.binder.id == leftBinder)).length == 6)
            "fixture failed to allocate the same recursive binder six times"
      | observation => throw (IO.userError s!"capture pair did not succeed: {reprStr observation}")
    else throw (IO.userError "capture pair result projection changed")

private def checkStored {checked : Checked} (prepared : Prepared checked) (cache : Cache prepared)
    (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 5000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored capture run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored provenance fixture classification changed"
  let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored capture ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored lambda source allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored lambda payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallableAncestryLedger.world completion) value (Core.CallableContract.functionType .word .word) prepared.layouts.definitions := by
        simpa only [type] using row.payload_typed ledger.typed payloadFound
      let auth ← match SourceCoreCallableAncestryTemplates.authenticate cache ledger.typed value .word .word typed with
        | .ok auth => pure auth | .error error => throw (IO.userError s!"stored source lambda auth failed: {reprStr error}")
      let stored := Stored.of_payload auth rfl ordinal payloadFound .root
      let joined ← match joinStored stored with
        | .ok joined => pure joined | .error error => throw (IO.userError s!"stored source capture join failed: {reprStr error}")
      assertTrue (joined.environment.length == 1) "stored lambda lost its source seed capture"
      assertTrue (joined.environment.all (fun binding => initial.length ≤ binding.2.index)) "stored capture pointed at inert source prefix"
    else throw (IO.userError "stored source lambda payload type changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"capture source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"capture marked compiler failed: {reprStr error}")
  let cache ← match SourceCoreCallableAncestryTemplates.prepare prepared with
    | .ok cache => pure cache | .error error => throw (IO.userError s!"capture template cache failed: {reprStr error}")
  checkPair prepared cache (← key program "escaped") [.word (w 3)] true "seed"
  checkPair prepared cache (← key program "repeated") [] false "value"
  checkStored prepared cache (← key program "failure") false
  checkStored prepared cache (← key program "suspended") true
  IO.println "actual native capture joins, ordered aliasing/prefix offsets/recursive rows/failure/suspension GREEN"
end Tests.SourceCoreCallableAncestryCaptures
