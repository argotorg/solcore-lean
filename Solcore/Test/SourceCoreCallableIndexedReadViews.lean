import Solcore.Frontend.SourceCoreCallableIndexedReadViews
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation

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
The tests check native code/descriptor authenticity and source capture sharing;
dynamic requirement rewriting is deliberately left to the prepared ancestry
metadata layer, rather than inferred from canonical read rows.
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
    (frame : SourceCoreCallableIndexedFrames.Layout) (shared allocated : Nat) : IO Unit := do
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
      assertTrue (first == w 4 && second == w 5) "read wrapper changed shared mutation order"
      assertTrue (final[shared]? == some (.inRight .unit (.word (w 5)))) "read wrapper split the underlying shared cell"
      assertTrue (final[0]? == some (SourceCoreCallableIndexedFrames.encode frame .empty)) "view/lambda frames were not restored"
      assertTrue (final.length == store.length + allocated) "view reentry changed actual source parameter allocations"
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
        assertTrue (leftJoined.captures.environment == rightJoined.captures.environment) "read wrappers lost shared source environments"
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
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame seed.location
            (if sharedPrincipal then 6 else 12)
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
  IO.println "indexed exact wrapper code, finite snapshots, ordered shared captures, stored failure/suspension and resume GREEN"


end Tests.SourceCoreCallableIndexedReadViews
