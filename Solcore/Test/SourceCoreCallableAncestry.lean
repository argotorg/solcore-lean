import Solcore.Frontend.SourceCoreCallableAncestry
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Layout.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Compiled.mk

/-! The actual common compiler transports distinct read occurrences into
escaping nested closures. Their source cell remains shared. Named boundaries
reset lexical ancestry; failures restore it. Every run uses actual native
checking, typed checkpoints and the Core machine. No source evaluator is
imported or used. Source closure reconstruction remains a separate boundary.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestry
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableAncestry
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
    "function factory(seed: Word) returns (F) { return lam(delta: Word) -> Word { seed = seed + delta; return seed; }; }",
    "function namedBoundary(seed: Word) returns (F) { return factory(seed); }",
    "function failure(seed: Word) returns (Word) { let absent: Word; let f = lam(value) { keep(value); return absent; }; return f(seed); }",
    "function empty() returns (function() returns (Word)) { return lam() -> Word { return 7; }; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"ancestry fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["escaped", "namedBoundary", "failure", "empty"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"ancestry plan failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 256 with
  | .ok artifact => pure artifact
  | .error error => throw (IO.userError s!"ancestry base failed: {reprStr error}")

private def origin {checked : Checked} (base : Base checked) (origin : SourceCoreStageCodebook.Origin) : IO Core.Word := do
  let native ← match base.callableContext with
    | some native => pure native | none => throw (IO.userError "ancestry codebook missing")
  match native.table.idAt? origin with
  | some origin => pure origin | none => throw (IO.userError s!"ancestry origin missing: {reprStr origin}")

private def native {checked : Checked} {base : Base checked} {prepared : Prepared base}
    {original : SourceCoreGeneralFunctions.Representation} {fuel : Nat}
    (compiled : Compiled prepared original fuel) (owner : Key) (arguments : SourceCoreBasic.LoweredExpr) :
    IO (SourceCoreGeneralEntry.NativeEntry prepared.layout.definitions) := do
  let function ← match base.functions.find? (fun function => decide (function.signature.key = owner)) with
    | some function => pure function | none => throw (IO.userError "ancestry root missing")
  let body ← match assemble compiled owner arguments with
    | .ok body => pure body | .error error => throw (IO.userError s!"ancestry assembly failed: {reprStr error}")
  match SourceCoreGeneralEntry.NativeEntry.compile prepared.layout.definitions [] function.signature.resultType body with
  | .ok native => pure native
  | .error error => throw (IO.userError s!"ancestry ABI failed actual Core checking: {reprStr error}")
private def resumed {definitions : Core.DataEnvironment} (native : SourceCoreGeneralEntry.NativeEntry definitions)
    (fuel : Nat) : IO (SourceCoreGeneralEntry.Result definitions native.resultType) := do
  let first ← match native.run [] fuel with
    | .ok first => pure first | .error error => throw (IO.userError s!"ancestry runner failed: {reprStr error}")
  match first.checkpoint? with
  | none => pure first | some suspended => pure (suspended.resume 250000)

private def snapshot (value : Core.Value) : IO Core.Value :=
  match value with
  | .pair (.pair (.inLeft .word .unit) (.closure _ _ _ (snapshot :: _))) (.word _) => pure snapshot
  | _ => throw (IO.userError "native source lambda lost its snapshot slot")
private def wordReferences (value : Core.Value) : List Nat :=
  match value with
  | .pair (.pair _ (.closure _ _ _ environment)) _ => environment.filterMap fun
      | .cellRef (.sum .unit .word) location => some location
      | _ => none
  | _ => []

private def reuse {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (left right : Core.Value)
    (leftTyped : Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) definitions)
    (rightTyped : Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) definitions)
    (layout : SourceCoreCallableContextFrames.Layout) (shared : Nat) : IO Unit := do
  let applyLeft : Core.Expr := .apply (.second (.first (.var 1))) (.word (w 1))
  let applyRight : Core.Expr := .apply (.second (.first (.var 0))) (.word (w 2))
  let body := Core.LocalSequence.pair .word .word applyLeft applyRight
  have bodyTyped : Core.HasType [Core.CallableContract.functionType .word .word, Core.CallableContract.functionType .word .word]
      body (Core.LanguageResult.resultType (.product .word .word)) definitions :=
    Core.LocalSequence.pair_hasType .word .word
      (.apply (.second (.first (.var rfl))) .word)
      (.apply (.second (.first (.var rfl))) .word)
  let checkpoint : SourceCoreGeneralEntry.Checkpoint definitions (.product .word .word) := {
    state := .initial body [right, left] store
    typed := .eval stored (.cons rightTyped (.cons leftTyped .nil)) bodyTyped .nil
  }
  for spent in [0, 31, 250000] do
    let first := checkpoint.resume spent
    let final := match first.checkpoint? with
      | none => first | some suspended => suspended.resume 250000
    match final.observation with
    | .succeeded (.pair (.word leftResult) (.word rightResult)) finalStore =>
      assertTrue (leftResult == w 4 && rightResult == w 6) "read-view ancestry split a shared mutable capture"
      assertTrue (finalStore[shared]? == some (.inRight .unit (.word (w 6)))) "source capture location changed"
      assertTrue (finalStore[0]? == some (SourceCoreCallableContextFrames.encode layout .empty)) "lambda application retained its lexical frame"
      assertTrue (finalStore.length == store.length + 2) "snapshot/context wrapper allocated extra per-call heap cells"
    | other => throw (IO.userError s!"escaped ancestry reuse failed: {reprStr other}")

example {definitions : Core.DataEnvironment} {layout : SourceCoreCallableContextFrames.Layout} {context : Core.Context}
    {parameter result : Core.Ty} {body : Core.Expr} {index : Nat}
    (registered : layout.Registered definitions) (origin : Core.Word)
    (parameterWF : parameter.WellFormed definitions) (resultWF : result.WellFormed definitions)
    (reference : context[index]? = some (.cell layout.type))
    (bodyTyped : Core.HasType (parameter :: context) body (Core.LanguageResult.resultType result) definitions) :
    Core.HasType context (snapshotLambda layout origin index parameter result body)
      (.function parameter (Core.LanguageResult.resultType result)) definitions :=
  snapshotLambda_hasType registered origin parameterWF resultWF reference bodyTyped

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"ancestry source rejected: {reprStr error}")
  let artifact ← artifact program
  let base := artifact.prepared
  let prepared ← match prepare base with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"ancestry metadata failed: {reprStr error}")
  let original := SourceCoreCompatibleFunctions.representation (.initial artifact.checked) 256
  let compiled ← match compile prepared original 256 with
    | .ok compiled => pure compiled | .error error => throw (IO.userError s!"ancestry compiler failed: {reprStr error}")
  assertTrue prepared.layout.definitions.isWellFormed "context definition suffix is ill-formed"
  let escaped ← key program "escaped"
  let rootId ← origin base (.named escaped)
  let views := (prepared.views.entries.filter (fun entry => entry.view.binding.binder.name == "outer"))
    |>.mergeSort (fun left right => left.view.reference.original.span.startByte ≤ right.view.reference.original.span.startByte)
  let [firstView, secondView] := views | throw (IO.userError "repeated same-type read views not inventoried")
  let firstCandidate ← match firstView.view.selectedInstance with
    | some candidate => pure candidate | none => throw (IO.userError "ancestry selected instance missing")
  let outerId ← origin base (.lambda firstCandidate.origin.caller firstCandidate.origin.initializer firstCandidate.origin.substitution)
  assertTrue (firstView.id != secondView.id && firstView.view.cumulative == secondView.view.cumulative)
    "same native specialization erased per-occurrence read IDs"
  assertTrue (firstView.view.ownWitnesses.map (·.actualRequirement) != secondView.view.ownWitnesses.map (·.actualRequirement))
    "fixture does not exercise dynamically distinct requirement rewriting"
  let escapedNative ← native compiled escaped ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  if expectedType : escapedNative.resultType = .product (Core.CallableContract.functionType .word .word) (Core.CallableContract.functionType .word .word) then
    for spent in [0, 41, 250000] do
      let result ← resumed escapedNative spent
      match success : result.observation with
      | .succeeded (.pair left right) store =>
        have values : ∃ world, Core.RuntimeStoreHasTypes world store prepared.layout.definitions ∧
            Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) prepared.layout.definitions ∧
            Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) prepared.layout.definitions := by
          obtain ⟨world, stored, typed⟩ := result.success_typed success
          rw [expectedType] at typed
          cases typed with
          | pair leftTyped rightTyped => exact ⟨world, stored, leftTyped, rightTyped⟩
        let leftSnapshot ← snapshot left
        let rightSnapshot ← snapshot right
        assertTrue (leftSnapshot == SourceCoreCallableContextFrames.encode prepared.layout.frame (.lambda outerId (.view firstView.id outerId (.named rootId))))
          "escaping lambda lost first dynamic read-view ancestry"
        assertTrue (rightSnapshot == SourceCoreCallableContextFrames.encode prepared.layout.frame (.lambda outerId (.view secondView.id outerId (.named rootId))))
          "escaping lambda lost second dynamic read-view ancestry"
        assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.layout.frame .empty)) "named call did not restore its caller frame"
        let shared := (wordReferences left).filter (fun location => (wordReferences right).contains location)
        let [location] := shared.eraseDups | throw (IO.userError "escaping nested closures do not share exactly one source Word capture")
        have stored : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store prepared.layout.definitions := by
          obtain ⟨world, stored, _, _⟩ := values
          have equal := stored.world_eq
          subst world
          exact stored
        have leftTyped : Core.RuntimeValueHasType (store.map Core.Value.type) left (Core.CallableContract.functionType .word .word) prepared.layout.definitions := by
          obtain ⟨world, otherStored, leftTyped, _⟩ := values
          rw [otherStored.world_eq] at leftTyped
          exact leftTyped
        have rightTyped : Core.RuntimeValueHasType (store.map Core.Value.type) right (Core.CallableContract.functionType .word .word) prepared.layout.definitions := by
          obtain ⟨world, otherStored, _, rightTyped⟩ := values
          rw [otherStored.world_eq] at rightTyped
          exact rightTyped
        reuse stored left right leftTyped rightTyped prepared.layout.frame location
      | other => throw (IO.userError s!"dynamic ancestry root failed: {reprStr other}")
  else throw (IO.userError "ancestry tuple result projection changed")
  let boundary ← key program "namedBoundary"
  let factory ← key program "factory"
  let factoryId ← origin base (.named factory)
  let boundaryNative ← native compiled boundary ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  let boundaryResult ← resumed boundaryNative 29
  match boundaryResult.observation with
  | .succeeded value store =>
    assertTrue ((← snapshot value) == SourceCoreCallableContextFrames.encode prepared.layout.frame (.named factoryId))
      "named callee captured another named caller's dynamic frame"
    assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.layout.frame .empty)) "named boundary did not restore context"
  | other => throw (IO.userError s!"named ancestry boundary failed: {reprStr other}")
  let failure ← key program "failure"
  let failureNative ← native compiled failure ⟨.word, Core.LanguageResult.success (.word (w 3))⟩
  for spent in [0, 67, 250000] do
    let failureResult ← resumed failureNative spent
    match failureResult.observation with
    | .failed _ store =>
      assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.layout.frame .empty))
        "language failure retained a lambda/read-view/named context"
    | other => throw (IO.userError s!"context failure changed classification: {reprStr other}")
  let empty ← key program "empty"
  let emptyId ← origin base (.named empty)
  let emptyNative ← native compiled empty ⟨.unit, Core.LanguageResult.success .unit⟩
  let emptyResult ← resumed emptyNative 0
  match emptyResult.observation with
  | .succeeded value _ =>
    assertTrue ((← snapshot value) == SourceCoreCallableContextFrames.encode prepared.layout.frame (.named emptyId))
      "zero-argument/scopeless lambda lost lexical snapshot"
  | other => throw (IO.userError s!"empty lexical scope failed: {reprStr other}")
  IO.println "ordinary Core dynamic ancestry, exact read occurrences, shared captures/named reset/failure/resume GREEN"
end Tests.SourceCoreCallableAncestry
