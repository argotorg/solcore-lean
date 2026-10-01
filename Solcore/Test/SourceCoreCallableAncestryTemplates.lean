import Solcore.Frontend.SourceCoreCallableAncestryTemplates
import Solcore.Frontend.SourceCoreCallableAncestryLedger
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryTemplates.Template.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryTemplates.Cache.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryTemplates.Authenticated.mk
#check_failure fun (template : Solcore.Frontend.SourceCoreCallableAncestryTemplates.Template) => { template with body := Solcore.Core.Expr.unit }

/-! The cache comes from the artifact's actual marked second pass. Successful
Core observations supply world/store typing; exact template authentication
retains lexical native slots and owned finite ancestry shapes. Source binder
locations are checked against the separate ledger in this fixture only: these
tests do not turn arbitrary well-typed frame words into source history. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryTemplates
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableAncestryTemplates
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
    "function maker(value: Word) returns (F) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }",
    "function zero() returns (function() returns (Word)) { return lam() -> Word { return 7; }; }",
    "function loop(value: Word) returns (F) { let f: F; while (true) { f = lam(delta: Word) -> Word { value = value + delta; return value; }; break; } return f; }",
    "function unused(value: Word) returns (Word) { let ignored = lam(item) { return item; }; return value; }",
    "function poly(flag: Bool) returns (Word, Bool) { let f = lam(item) { return item; }; return (f(1), f(flag)); }",
    "function nestedPoly(flag: Bool) returns (Word, Word) { let outer = lam(value) { let inner = lam(item) { return item; }; return inner(1); }; return (outer(1), outer(flag)); }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"ancestry template fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["escaped", "maker", "zero", "loop", "unused", "poly", "nestedPoly"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"ancestry templates plan failed: {reprStr result}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"ancestry templates base failed: {reprStr error}")
private def runSource {checked : Checked} (prepared : Prepared checked) (owner : Key)
    (arguments : List SourceTypedRuntime.Value) (fuel : Nat) :
    IO (SourceCoreCallableAncestryPrograms.Completion prepared) := do
  let completion ← match prepared.runSource owner arguments fuel 500 with
    | .ok completion => pure completion
    | .error error => throw (IO.userError s!"ancestry template invocation failed: {reprStr error}")
  let _ ← match SourceCoreCallableAncestryLedger.scan completion with
    | .ok early => pure early
    | .error error => throw (IO.userError s!"partial template ledger failed: {reprStr error}")
  pure (completion.resume 250000)

/-- A different descriptor remains Core-typed; source ownership must reject it. -/
private def retag (value : Core.Value) (descriptor : Core.Word) : Core.Value :=
  match value with
  | .pair tagged _ => .pair tagged (.word descriptor)
  | other => other

private theorem retag_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty} (descriptor : Core.Word)
    (typed : Core.RuntimeValueHasType world value (Core.CallableContract.functionType parameter result) definitions) :
    Core.RuntimeValueHasType world (retag value descriptor) (Core.CallableContract.functionType parameter result) definitions := by
  cases typed with
  | pair tagged _ => exact .pair tagged .word

/-- Replacing native lambda code with a constant keeps its type and captures. -/
private def replaceBody (value : Core.Value) : Core.Value :=
  match value with
  | .pair (.pair identity (.closure parameter result _ environment)) descriptor =>
      .pair (.pair identity (.closure parameter result
        (Core.LanguageResult.success (.word (w 999))) environment)) descriptor
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
      | closure environment _ =>
        exact .pair (.pair identity (.closure environment (.inRight .word .word))) descriptor

/-- Even a behaviorally transparent, typed edit invalidates cached global code. -/
private def replaceGlobal (value : Core.Value) : Core.Value :=
  match value with
  | .inRight .unit (.closure parameter result body environment) =>
      .inRight .unit (.closure parameter result (.letE .unit (body.weakenAt 0)) environment)
  | other => other

private theorem replaceGlobal_typed {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {value : Core.Value} {parameter result : Core.Ty}
    (typed : Core.RuntimeValueHasType world value
      (Core.OptionalCell.cellType (.function parameter result)) definitions) :
    Core.RuntimeValueHasType world (replaceGlobal value)
      (Core.OptionalCell.cellType (.function parameter result)) definitions := by
  cases typed with
  | inLeft payload => exact .inLeft payload
  | inRight function =>
    cases function with
    | closure environment body =>
      exact .inRight (.closure environment (.letE .unit
        (by simpa only [Core.Context.insertAt] using body.weakenAt (inserted := .unit) 0)))


private def checkCaptures {checked : Checked} {prepared : Prepared checked}
    {cache : Cache prepared}
    {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : Authenticated cache world store value)
    (ledger : SourceCoreAllocationLedger.TypedLedger prepared.layouts [] world store) : IO Unit := do
  assertTrue (authenticated.sourceCaptures.length == authenticated.template.source.scope.length)
    "capture certificate omitted a source lexical slot"
  assertTrue (authenticated.template.references == authenticated.template.manifestIndices.map (· - 3))
    "manifest depth did not exclude exactly the argument and frame binders"
  for capture in authenticated.sourceCaptures do
    let row ← match ledger.ledger.rows.find? (fun row => row.coreLocation == capture.location) with
      | some row => pure row | none => throw (IO.userError "source reference points at helper/global/context cell")
    assertTrue (row.entry.key.binder.id == capture.binder && row.entry.key.payloadType == capture.payloadType)
      "actual native capture failed binder/payload ledger alignment"

private def single {checked : Checked} (prepared : Prepared checked) (cache : Cache prepared)
    (owner : Key) (arguments : List SourceTypedRuntime.Value) (parameter : Core.Ty) : IO Unit := do
  for spent in [0, 17, 250000] do
    let completion ← runSource prepared owner arguments spent
    if same : completion.entry.native.resultType = Core.CallableContract.functionType parameter .word then
      match success : completion.result.native.observation with
      | .succeeded value store =>
        have typed : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layouts.definitions ∧
            Core.RuntimeValueHasType (store.map Core.Value.type) value (Core.CallableContract.functionType parameter .word) prepared.layouts.definitions := by
          obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed success
          have equal := stored.world_eq
          subst world
          exact ⟨stored, by simpa only [same] using typed⟩
        let authenticated ← match authenticate cache typed.1 value parameter .word typed.2 with
          | .ok authenticated => pure authenticated
          | .error error => throw (IO.userError s!"actual snapshot lambda failed authentication: {reprStr error}")
        assertTrue (authenticated.template.source.lambda.owner == owner) "template authenticated another source owner"
        assertTrue (authenticated.current.frame == .empty) "completion retained an active callable context"
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts [] (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"capture ledger failed: {reprStr error}")
        checkCaptures authenticated ledger
        match authenticate cache typed.1 (retag value (w 999999)) parameter .word (retag_typed _ typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "typed foreign descriptor authenticated")
        match authenticate cache typed.1 (replaceBody value) parameter .word (replaceBody_typed typed.2) with
        | .error .closureMismatch => pure ()
        | _ => throw (IO.userError "typed foreign lambda body authenticated")
        if spent == 250000 then
          let global ← match prepared.base.globals.head? with
            | some global => pure global | none => throw (IO.userError "template fixture has no globals")
          let location := prepared.base.globals.length
          let type := Core.OptionalCell.cellType global.functionType
          if found : (store.map Core.Value.type)[location]? = some type then
            match lookup : store.read? location with
            | none => throw (IO.userError "global slot unexpectedly absent")
            | some old =>
              have oldTyped : Core.RuntimeValueHasType (store.map Core.Value.type) old type prepared.layouts.definitions := by
                obtain ⟨other, otherLookup, otherTyped⟩ := typed.1.read found
                rw [lookup] at otherLookup
                cases otherLookup
                exact otherTyped
              match written : store.write? location (replaceGlobal old) with
              | none => throw (IO.userError "global write outside heap")
              | some changed =>
                let changedStored := typed.1.write found (replaceGlobal_typed oldTyped) written
                match authenticate cache changedStored value parameter .word typed.2 with
                | .error (.globalsMismatch _) => pure ()
                | _ => throw (IO.userError "typed edited installed global authenticated")
          else throw (IO.userError "actual globals base1 slot has wrong type")
      | observation => throw (IO.userError s!"snapshot lambda root did not succeed: {reprStr observation}")
    else throw (IO.userError "template fixture result projection changed")

private def reuse {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (left right : Core.Value)
    (leftTyped : Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) definitions)
    (rightTyped : Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) definitions)
    (frame : SourceCoreCallableContextFrames.Layout) (shared : Nat) : IO Unit := do
  let callLeft := Core.Expr.apply (.second (.first (.var 1))) (.word (w 1))
  let callRight := Core.Expr.apply (.second (.first (.var 0))) (.word (w 2))
  let body := Core.LocalSequence.pair .word .word callLeft callRight
  have typed : Core.HasType [Core.CallableContract.functionType .word .word, Core.CallableContract.functionType .word .word]
      body (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := .initial body [right, left] store
    typed := .eval stored (.cons rightTyped (.cons leftTyped .nil)) typed .nil
  }
  for spent in [0, 31, 250000] do
    let first := checkpoint.resume spent
    let completed := match first.checkpoint? with
      | none => first | some checkpoint => checkpoint.resume 250000
    match completed.observation with
    | .succeeded (.pair (.word first) (.word second)) final =>
      assertTrue (first == w 4 && second == w 6) "authenticated snapshots split the shared mutable source capture"
      assertTrue (final[shared]? == some (.inRight .unit (.word (w 6)))) "capture location changed on reentry"
      assertTrue (final[0]? == some (SourceCoreCallableContextFrames.encode frame .empty)) "reentry did not restore callable context"
      assertTrue (final.length == store.length + 6) "snapshot wrapper changed the parameter allocation and ancestry metadata suffix"
    | observation => throw (IO.userError s!"authenticated lambda reuse failed: {reprStr observation}")

private def escaped {checked : Checked} (prepared : Prepared checked) (cache : Cache prepared) (owner : Key) : IO Unit := do
  for spent in [0, 41, 250000] do
    let completion ← runSource prepared owner [.word (w 3)] spent
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
        let first ← match authenticate cache typed.1 left .word .word typed.2.1 with
          | .ok first => pure first | .error error => throw (IO.userError s!"first dynamic snapshot rejected: {reprStr error}")
        let second ← match authenticate cache typed.1 right .word .word typed.2.2 with
          | .ok second => pure second | .error error => throw (IO.userError s!"second dynamic snapshot rejected: {reprStr error}")
        assertTrue (first.snapshot.frame != second.snapshot.frame) "same native specialization lost per-read dynamic ancestry"
        assertTrue (first.template.body == second.template.body) "fixture failed to reuse an exact native template"
        let leftSeed := first.sourceCaptures.find? (fun capture =>
          (first.template.source.lambda.context.bindingAt? capture.binder).map (·.binding.binder.name) == some "seed")
        let rightSeed := second.sourceCaptures.find? (fun capture =>
          (second.template.source.lambda.context.bindingAt? capture.binder).map (·.binding.binder.name) == some "seed")
        assertTrue (leftSeed.map (·.location) == rightSeed.map (·.location) && leftSeed.isSome)
          "dynamic snapshot changed shared lexical source location"
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts [] (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"nested lambda ledger failed: {reprStr error}")
        checkCaptures first ledger
        checkCaptures second ledger
        if spent == 250000 then
          let capture ← match leftSeed with
            | some capture => pure capture | none => throw (IO.userError "shared seed disappeared")
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame capture.location
      | observation => throw (IO.userError s!"nested lambda did not succeed: {reprStr observation}")
    else throw (IO.userError "nested lambda product result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"ancestry templates source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"actual marked ancestry compiler failed: {reprStr error}")
  let cache ← match prepare prepared with
    | .ok cache => pure cache | .error error => throw (IO.userError s!"actual installed snapshot scanner failed: {reprStr error}")
  assertTrue (prepared.ancestry.templates.unusedPrincipals.any (·.binder.name == "ignored"))
    "unused principal falsely required emitted native lambda"
  assertTrue (cache.templates.any (·.source.scope.isEmpty)) "zero-parameter/scope-free template missing"
  assertTrue (cache.templates.all (fun template => template.references == template.source.references.map (· + 1)))
    "snapshot insertion lost a captured source reference"
  let nestedKey ← key program "nestedPoly"
  let nested := cache.templates.filter (fun template => template.source.lambda.owner == nestedKey)
  assertTrue (nested.length == 4) "nested polymorphic bundles lost actual snapshot templates"
  assertTrue ((nested.map (·.source.lambda.descriptor)).eraseDups.length == 4)
    "nested full contexts collided"
  single prepared cache (← key program "maker") [.word (w 3)] .word
  single prepared cache (← key program "zero") [] .unit
  single prepared cache (← key program "loop") [.word (w 3)] .word
  escaped prepared cache (← key program "escaped")
  for owner in ["poly", "nestedPoly"] do
    let completion ← runSource prepared (← key program owner) [.bool true] 23
    match completion.result.native.observation with
    | .succeeded (.pair _ _) _ => pure ()
    | observation => throw (IO.userError s!"snapshot bundle changed execution: {reprStr observation}")
  let sample ← match cache.templates.head? with
    | some sample => pure sample | none => throw (IO.userError "no cached snapshot templates")
  let .pair (.pair identity payload) _ := sample.carrier | throw (IO.userError "snapshot carrier changed")
  match decode prepared (.pair (.pair identity payload) (.word (w 999999))) with
  | .error _ => pure () | .ok _ => throw (IO.userError "descriptor/body inconsistency passed inverse scanner")
  match decodeSnapshot prepared (SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame (.named (w 999999))) with
  | .error .foreignFrame => pure () | _ => throw (IO.userError "unknown owned-frame word authenticated")
  IO.println "actual snapshot templates, inverse scanner, typed code/global/capture auth and resume GREEN"
end Tests.SourceCoreCallableAncestryTemplates
