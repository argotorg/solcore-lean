import Solcore.Frontend.SourceCoreCallableAncestryLedger
import Solcore.Frontend.ProgramChecking
import Solcore.Frontend.SourceCoreCallableAncestry
import Solcore.SourceSemantics.CoreLowering.CallableAncestryCache
import Solcore.Frontend.SourceCoreCallableAncestryCaptures
import Solcore.SourceSemantics.CoreLowering.CallableAncestryComposition
import Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
import Solcore.Frontend.SourceCoreCompatibleOutputs
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedValidation
import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProfiles
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedProgress
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedSeeds
import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedWorklist
import Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
import Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders
import Solcore.Frontend.SourceCoreCallableAncestryPreparation
import Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles
import Solcore.Frontend.SourceCoreAllocationLedger
import Solcore.SourceSemantics.CoreLowering.CallableAncestryReadRecipes
import Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
import Solcore.Frontend.SourceCoreCallableAncestryReadViews
import Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
import Solcore.Frontend.SourceCoreCallableAncestryTemplates
import Solcore.SourceSemantics.CoreLowering.CallableAncestryWorklist

/-!
# Callable ancestry tests

Callable ancestry: cache, captures, composition, metadata, read views, templates and worklists.
-/

section
-- leanmerge: from Solcore.Test.SourceCoreAncestryAllocationFrames
/-! Allocation snapshots preserve unused generalized principals' dynamic
ancestry, through the actual two-pass compiler and its typed native runner. -/
set_option autoImplicit false
namespace Tests.SourceCoreAncestryAllocationFrames
open Solcore Solcore.Frontend SourceInference
private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function unusedViews(seed: Word) returns (Word) {",
    " let outer = lam(value) { keep(value); let unused = lam(item) { return item; }; return seed; };",
    " return outer(1) + outer(2); }"
  ]}] }

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"allocation frame source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.find? (·.name == "unusedViews") with
    | some signature => pure signature | none => throw (IO.userError "allocation frame root absent")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"allocation frame plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"allocation frame base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"allocation frame compiler failed: {reprStr error}")
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer (-11))⟩]
  let mut pendingSeen := false
  let mut allocationSeen := false
  for budget in List.range 600 do
    let suspended ← match prepared.runSource key [.word (w 4)] budget with
      | .ok suspended => pure suspended
      | .error error => throw (IO.userError s!"allocation frame checkpoint failed: {reprStr error}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan suspended initial with
      | .ok ledger => pure ledger
      | .error error => throw (IO.userError s!"allocation frame checkpoint ledger failed: {reprStr error}")
    pendingSeen := pendingSeen || ledger.ledger.pending.isSome
    allocationSeen := allocationSeen || !ledger.ledger.rows.isEmpty
    for row in ledger.ledger.rows do
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok _ => pure ()
      | .error error => throw (IO.userError s!"checkpoint source allocation lost its preceding frame: {reprStr error}")
      assertTrue (initial.length ≤ row.sourceLocation.index &&
        row.environment.all (fun entry => initial.length ≤ entry.2.index))
        "administrative frame cells entered source locations or captures"
  assertTrue pendingSeen "allocation snapshot test missed a marker-only checkpoint"
  assertTrue allocationSeen "allocation snapshot test missed a completed source cell"
  for budget in [0, 7, 31, 67, 150000] do
    let completion ← match prepared.runSource key [.word (w 4)] budget with
      | .ok completion => pure completion | .error error => throw (IO.userError s!"allocation frame native run failed: {reprStr error}")
    let completion := completion.resume 150000
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"allocation frame ledger failed: {reprStr error}")
    let snapshots ← ledger.ledger.rows.mapM fun row =>
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot.frame | .error error => throw (IO.userError s!"allocation frame snapshot missing: {reprStr error}")
    assertTrue (snapshots.length == ledger.ledger.rows.length) "source rows lost their allocation-time frame"
    let unused := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (unused.length == 2) "unused generalized principal was not allocated on each call"
    assertTrue (unused.all fun row => !row.entry.key.binder.scheme.quantified.isEmpty && row.payload == some .unit)
      "unused generalized principal emitted a native executable closure"
    let histories ← unused.mapM fun row =>
      match SourceCoreAncestryAllocationFrames.snapshot prepared.ancestry.layout.frame row with
      | .ok snapshot => pure snapshot.frame | .error error => throw (IO.userError s!"unused principal ancestry absent: {reprStr error}")
    assertTrue (histories.eraseDups.length == 2) "same-type read occurrences lost their distinct principal ancestry"
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == w 8) "allocation frame transport changed source execution"
    | observation => throw (IO.userError s!"allocation frame outcome changed: {reprStr observation}")
  IO.println "allocation-time ancestry for unused generalized source principals GREEN"

end Tests.SourceCoreAncestryAllocationFrames
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestry
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Layout.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestry.Compiled.mk

/-! The actual common compiler transports distinct read occurrences into
escaping nested closures. Closures capture by value: each escaping closure
keeps its own snapshot of the source cells it captures, and each call starts
again from that snapshot. Named boundaries reset lexical ancestry; failures
restore it. Every run uses actual native checking, typed checkpoints and the
Core machine. No source evaluator is imported or used. Source closure
reconstruction remains a separate boundary.
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
    (layout : SourceCoreCallableContextFrames.Layout) (unchanged : List Nat) : IO Unit := do
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
      -- Each call starts again from its closure's creation-time `seed = 3`.
      assertTrue (leftResult == w 4 && rightResult == w 5) "read-view ancestry did not restart each call from its creation snapshot"
      assertTrue (unchanged.all (fun location => finalStore[location]? == some (.inRight .unit (.word (w 3)))))
        "a call wrote a snapshot or the outer principal's source capture"
      assertTrue (finalStore[0]? == some (SourceCoreCallableContextFrames.encode layout .empty)) "lambda application retained its lexical frame"
      -- Each call copies the two captured cells and binds its parameter: three plain cells.
      assertTrue (finalStore.length == store.length + 6) "snapshot/context wrapper allocated extra per-call heap cells"
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
        -- Each escaping closure's environment begins with its creation snapshot.
        -- The copies are made most recent binding first (`value`, then `seed`),
        -- each bound at the head of the environment, so the copy of `seed` comes first.
        let leftReferences := wordReferences left
        let rightReferences := wordReferences right
        let [leftSeed, leftValue] := leftReferences.take 2
          | throw (IO.userError "first escaping closure lost its creation snapshot")
        let [rightSeed, rightValue] := rightReferences.take 2
          | throw (IO.userError "second escaping closure lost its creation snapshot")
        let word := fun n => some (Core.Value.inRight .unit (.word (w n)))
        assertTrue (store[leftSeed]? == word 3 && store[leftValue]? == word 1 &&
            store[rightSeed]? == word 3 && store[rightValue]? == word 2)
          "escaping closures lost their creation-time seed and argument copies"
        -- They share only the outer principal's cells: the original `seed` and
        -- the copy the generalized `outer` took of it.
        let shared := (leftReferences.filter (fun location => rightReferences.contains location)).eraseDups
        assertTrue (shared.length == 2 && shared.all (fun location => store[location]? == word 3) &&
            ![leftSeed, leftValue, rightSeed, rightValue].any shared.contains)
          "escaping nested closures shared a snapshot cell or more than the outer principal's two Word cells"
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
        reuse stored left right leftTyped rightTyped prepared.layout.frame (leftSeed :: rightSeed :: shared)
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
  IO.println "ordinary Core dynamic ancestry, exact read occurrences, by-value captures/named reset/failure/resume GREEN"
end Tests.SourceCoreCallableAncestry
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryCache
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryCache.Prepared.mk

/-! The universal theorem consumes a completed finite closure certificate.
The concrete table test below tests only table lookup, not table ownership or
successful preparation of every compiler artifact. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryCache
open Solcore Solcore.Frontend SourceInference
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryCache

example {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {frame : ContextFrame}
    {state : Option Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state :=
  prepared.lookup_iff

example {checked : Checked} {base : Base checked} {owned : Owned base}
    (prepared : Prepared owned) {leftFrame rightFrame : ContextFrame}
    {left right : SourceCoreCallableAncestryCache.State}
    (leftFound : prepared.table.lookup? leftFrame = some (some left))
    (rightFound : prepared.table.lookup? rightFrame = some (some right))
    (same : left.key = right.key) : left = right :=
  prepared.lookup_key_injective leftFound rightFound same

private def ownerModule : Workspace.ModuleId :=
  ⟨.main, ⟨[⟨"ancestry_cache", by decide⟩], by decide⟩⟩
private def owner : Resolved.DeclarationId := ⟨ownerModule, 0⟩
private def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def state (requirement : Nat) : SourceCoreCallableAncestryCache.State := {
  owner := ⟨owner, []⟩, active := [], source := {
    owner, inputs := [], roots := [], nodes := [.expression {
      id := ⟨⟨owner, 0⟩⟩,
      span := { source := {origin := .main, path := "ancestry_cache.solc"}, startByte := 0, endByte := 1 },
      type := .word, requirements := [⟨requirement⟩], form := .literal (.decimal "1")
    }]
  }
}
private def table : SourceCoreCallableAncestryCache.Table := {
  states := [state 0, state 2, state 4]
  named := [⟨word 7, 0⟩]
  lambdas := [⟨0, word 9⟩, ⟨1, word 9⟩, ⟨2, word 9⟩]
  views := [⟨0, word 1, word 9, 1⟩, ⟨0, word 2, word 9, 2⟩]
}
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def run : IO Unit := do
  let left : ContextFrame := .view (word 1) (word 9) (.named (word 7))
  let right : ContextFrame := .view (word 2) (word 9) (.named (word 7))
  let repeated := (List.range 2000).foldl (fun (frame : ContextFrame) _ => .lambda (word 9) frame) right
  assertTrue (decide (table.lookup? .empty = some none)) "empty ancestry was rejected"
  assertTrue (decide (table.lookup? left = some (some (state 2)))) "left occurrence profile lost"
  assertTrue (decide (table.lookup? repeated = some (some (state 4)))) "repeated ancestry changed its cached state"
  assertTrue (decide ((state 2).key ≠ (state 4).key)) "key ignored occurrence-specific requirement IDs"
  let rejected : List ContextFrame := [.lambda (word 9) .empty,
      .named (word 999), .lambda (word 99) right, .view (word 1) (word 99) (.named (word 7)),
      .view (word 1) (word 9) right]
  for frame in rejected do
    assertTrue ((table.lookup? frame).isNone) "unprepared transition accepted"
  let malformed := {table with named := [⟨word 7, 999⟩]}
  assertTrue ((malformed.lookup? (.named (word 7))).isNone) "missing state row accepted"
  IO.println "finite ancestry table: 2000 repeated frames, exact occurrence profiles, invalid transitions rejected GREEN"
end Tests.SourceCoreCallableAncestryCache
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryCaptures
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Produced.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Stored.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Captured.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryCaptures.Slot.mk

/-! Actual two-pass compilation and typed native observations establish
provenance. Captures join by native location, not repeated source binder IDs.
Closures capture by value, so each closure joins to its own snapshot cells even
where one binder ID is allocated many times. Ordered source environments
preserve opaque-prefix offsets. Stored lambda payloads are also joined on
language failure and suspension. -/
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
    (owner : Key) (arguments : List SourceTypedRuntime.Value) (name : String) (allocations : Nat) : IO Unit := do
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
        assertTrue (leftLocation != rightLocation)
          "join selected a repeated binder allocation by ID instead of exact native location"
        assertTrue (leftJoined.environment.all (fun binding => initial.length ≤ binding.2.index))
          "new closure capture escaped into the inert source prefix"
        assertTrue ((ledger.ledger.rows.filter (fun row => row.entry.key.binder.id == leftBinder)).length == allocations)
          "fixture failed to allocate the same binder once per input, copy and snapshot"
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
  -- `seed`: the input, the generalized `outer`'s snapshot, and for each call of
  -- `outer` its copy and the snapshot of the inner lambda it returns.
  checkPair prepared cache (← key program "escaped") [.word (w 3)] "seed" 6
  -- `value`: in each of the two chains, three inputs and the returned lambda's snapshot.
  checkPair prepared cache (← key program "repeated") [] "value" 8
  checkStored prepared cache (← key program "failure") false
  checkStored prepared cache (← key program "suspended") true
  IO.println "actual native capture joins, ordered snapshots/prefix offsets/recursive rows/failure/suspension GREEN"
end Tests.SourceCoreCallableAncestryCaptures
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryComposition
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual closed-matcher ranges justify composition through quantified
binders. The final key keeps requirements, and equal authenticated keys
determine the entire metadata state, for arbitrary ancestry depth. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryComposition
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles.SourceComposition

example {scheme : Scheme} {actual : Ty} {substitution : Substitution}
    (matched : SourceSpecialization.matchClosedSchemeInstance? scheme actual = some substitution) :
    RangesClosed substitution := matchClosed_ranges matched

example (sourceValue : TypedSource) (newer older : Substitution) (closed : RangesClosed older) :
    sourceValue.applySubstitution (newer.compose older) = (sourceValue.applySubstitution older).applySubstitution newer :=
  source newer older closed sourceValue

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      RangesClosed state.active ∧
      eraseRequirements state.source = eraseRequirements (named.state.source.applySubstitution state.active) :=
  Authenticates.canonical authenticated

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {leftFrame rightFrame : ContextFrame}
    {left right : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (leftAuthenticated : Authenticates owned leftFrame (some left))
    (rightAuthenticated : Authenticates owned rightFrame (some right))
    (same : stateKey left = stateKey right) : left = right :=
  stateKey_injective leftAuthenticated rightAuthenticated same

private def first : TypeVarId := ⟨0⟩
private def bound : TypeVarId := ⟨1⟩
private def quantified : Scheme := ⟨[bound], .variable first⟩
private def olderOpen : Substitution := [(first, .variable bound)]
private def newerClosed : Substitution := [(bound, .word)]

/-- Removing the closed-range condition would make binder composition false:
the older open replacement can introduce the binder's protected variable. -/
example : quantified.apply (newerClosed.compose olderOpen) ≠ (quantified.apply olderOpen).apply newerClosed := by
  decide

example : ¬RangesClosed olderOpen := by
  intro closed
  have impossible := closed (first, .variable bound) (by simp [olderOpen])
  simp [Ty.freeVariables] at impossible

example : RangesClosed [(first, .word)] := by
  intro entry member
  cases List.mem_singleton.mp member
  rfl

end Tests.SourceCoreCallableAncestryComposition
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryMetadata
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.Owned.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.ViewStep.mk
#check_failure Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.Cache.mk

/-! Two reads with identical closed types, dictionaries and target descriptors
still retain different actual requirement IDs in a nested lambda's source.
The fixture uses actual checked/compiler-owned metadata. It proves no native
frame history or complete unbounded ancestry cache. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryMetadata
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
abbrev MetadataState := Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function pair() returns (WordFunction, WordFunction) {",
    " let outer = lam(value) { keep(value);",
    "   let inner: WordFunction = lam(item: Word) -> Word { return item; }; return inner; };",
    " return (outer(1), outer(2)); }"
  ]}] }

private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let signature ← match program.signatures.functions.filter (·.name == "pair") with
    | [signature] => pure signature
    | _ => throw (IO.userError "ancestry fixture missing pair")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"ancestry worklist failed: {reprStr result}")
  get "ancestry compatible artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)

private def requiredState {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} (result : {state : Option MetadataState // Authenticates owned frame state}) : IO MetadataState :=
  match result.val with | some state => pure state | none => throw (IO.userError "ancestry lost its source")

example (function : Solcore.SourceSemantics.Dynamic.GeneralizedClosure) (substitution : Substitution)
    (evidence : Solcore.SourceSemantics.Dynamic.EvidenceEnvironment) (witnesses : List Witness) :
    eraseRequirements (SourceTypedRuntime.rewriteLocalRequirements witnesses
      (function.source.applySubstitution substitution)) =
      eraseRequirements (function.instantiate substitution evidence).source :=
  dynamic_instantiate_erased function substitution evidence witnesses

example {checked : Checked} {base : Base checked} {owned : Owned base} {frame : ContextFrame}
    {state : MetadataState} (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), SourceRecipe named.state.source state.source := authenticated.recipe

example (canonical source : TypedSource) (alphabet : List RequirementId)
    (erased : eraseRequirements source = eraseRequirements canonical)
    (lengths : (requirementProfile source).map List.length = (requirementProfile canonical).map List.length)
    (bounded : ∀ spine ∈ requirementProfile source, ∀ id ∈ spine, id ∈ alphabet) :
    requirementProfile source ∈ FiniteProfiles.profiles alphabet ((requirementProfile canonical).map List.length) :=
  (FiniteProfiles.source_profile_bound canonical source alphabet erased lengths bounded).1

private def rejected {checked : Checked} {base : Base checked} (owned : Owned base) (frame : ContextFrame) : IO Unit :=
  match prepareFrame owned frame with
  | .error _ => pure ()
  | .ok _ => throw (IO.userError s!"forged ancestry metadata accepted: {reprStr frame}")

def run : IO Unit := do
  let program ← get "ancestry source checker" (checkProgram workspace)
  let artifact ← artifact program
  let base := artifact.prepared
  let owned ← get "ancestry owned tables" (prepare base)
  let reads := owned.views.entries.filter (·.view.principal.binder.name == "outer")
  let (left, right) ← match reads with
    | [left, right] => pure (left, right)
    | _ => throw (IO.userError "expected two exact outer reads")
  assertTrue (decide (left.view.ownSubstitution = right.view.ownSubstitution) &&
    decide (left.view.reference.original.rawType = right.view.reference.original.rawType))
    "fixture no longer uses two equal native/source types"
  let leftIds := left.view.ownWitnesses.map (·.actualRequirement)
  let rightIds := right.view.ownWitnesses.map (·.actualRequirement)
  assertTrue (!leftIds.isEmpty && decide (leftIds ≠ rightIds)) "fixture merged occurrence-specific requirement IDs"
  assertTrue (reprStr (left.view.ownWitnesses.map (·.evidence)) == reprStr (right.view.ownWitnesses.map (·.evidence)))
    "fixture should share dictionaries while retaining distinct requirement IDs"
  let owner := left.view.owner
  let named ← match owned.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "owned named origin missing")
  let target ← match owned.callable.table.idAt? (.lambda owner left.view.principal.initializer left.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "owned outer lambda target missing")
  let innerView ← match owned.views.entries.find? (·.view.principal.binder.name == "inner") with
    | some entry => pure entry | none => throw (IO.userError "owned inner lambda metadata missing")
  let inner ← match owned.callable.table.idAt? (.lambda owner innerView.view.principal.initializer left.view.cumulative) with
    | some inner => pure inner | none => throw (IO.userError "owned nested lambda target missing")
  let leftView : ContextFrame := .view left.id target (.named named)
  let rightView : ContextFrame := .view right.id target (.named named)
  let leftFrame : ContextFrame := .lambda inner (.lambda target leftView)
  let rightFrame : ContextFrame := .lambda inner (.lambda target rightView)
  let leftPrepared ← get "left nested ancestry" (prepareFrame owned leftFrame)
  let rightPrepared ← get "right nested ancestry" (prepareFrame owned rightFrame)
  let leftState ← requiredState leftPrepared
  let rightState ← requiredState rightPrepared
  assertTrue (decide (leftState.active = rightState.active) &&
    decide (eraseRequirements leftState.source = eraseRequirements rightState.source))
    "equal type contexts changed metadata beyond requirement IDs"
  assertTrue (decide (leftState.source ≠ rightState.source))
    "same-type read views collapsed the nested lambda's retained source"
  let leftPrincipal ← get "left dynamic principal" (preparePrincipal owned leftState innerView.view.binding.binder.id)
  let rightPrincipal ← get "right dynamic principal" (preparePrincipal owned rightState innerView.view.binding.binder.id)
  assertTrue (decide (leftPrincipal.entry.principal.declaration = rightPrincipal.entry.principal.declaration) &&
    decide (leftPrincipal.node.form = rightPrincipal.node.form)) "dynamic ancestry changed the cached principal declaration/header"
  let expectedLeft := SourceTypedRuntime.rewriteLocalRequirements left.view.ownWitnesses
    (left.view.principal.source.applySubstitution left.view.ownSubstitution)
  let expectedRight := SourceTypedRuntime.rewriteLocalRequirements right.view.ownWitnesses
    (right.view.principal.source.applySubstitution right.view.ownSubstitution)
  assertTrue (decide (leftState.source = expectedLeft) && decide (rightState.source = expectedRight))
    "transported ancestry did not retain the exact principal-source recipe"
  let differences := leftState.source.nodes.filterMap fun
    | .expression node => match rightState.source.lookupExpression? node.id with
      | some other => if node.requirements != other.requirements then some node.id else none
      | none => none
    | _ => none
  assertTrue (!differences.isEmpty) "fixture has no actual expression requirement difference"
  let alphabet := (requirementProfile left.view.principal.originalSource).flatten.eraseDups
  assertTrue ((requirementProfile leftState.source).map List.length ==
    (requirementProfile rightState.source).map List.length)
    "view transport changed requirement spine lengths"
  assertTrue ([leftState.source, rightState.source].all fun source =>
    (requirementProfile source).all fun spine => spine.all alphabet.contains)
    "view transport invented a requirement ID outside the original source alphabet"
  let cache ← get "finite ancestry cache" (prepareCache owned [.empty, leftFrame, rightFrame])
  for frame in [leftFrame, rightFrame] do
    assertTrue ((cache.lookup? frame).isSome) "cache lost a prepared source view"
  assertTrue ((cache.lookup? (.lambda target leftFrame)).isNone)
    "finite cache silently treated an unprepared history as prepared"
  rejected owned (.view left.id inner (.named named))
  rejected owned (.lambda target .empty)
  rejected owned (.named target)
  rejected owned (.view (w 999999) target (.named named))
  rejected owned (.lambda (w 999999) (.named named))
  IO.println "owned ancestry metadata: equal types/dictionaries, distinct read requirement IDs and cached nested sources GREEN"
end Tests.SourceCoreCallableAncestryMetadata
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryOutputs
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe.mk

/-! Cached compatible calls export global/builtin values at every data depth.
Core-only tampering keeps native typing while changing descriptors or closure
payloads; the reverse adapter must still reject it. Lambda export is an explicit
ledger boundary, independent of the typed native execution succeeding. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryOutputs
open Solcore Solcore.Frontend SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCallableAncestryPrograms.Prepared
abbrev Recipe := Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey

private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Holder { Hold(function(Word) returns (Word)) }",
    "trait Marker<T> {}", "impl Marker<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function inc(value: Word) returns (Word) { return value + 1; }",
    "function dec(value: Word) returns (Word) { return value - 1; }",
    "function getNamed() returns (function(Word) returns (Word)) { return inc; }",
    "function getBuiltin() returns (function(Word) returns (integer)) { return wordToInteger; }",
    "function getQualified() returns (function(Word) returns (Word)) { return keep; }",
    "function getNominal() returns (Holder) { return .Hold(inc); }",
    "function getTuple() returns (function(Word) returns (Word), function(Word) returns (integer)) { return (inc, wordToInteger); }",
    "function mappingReturn(value: mapping(function(Word) returns (Word) => function(Word) returns (Word))) returns (mapping(function(Word) returns (Word) => function(Word) returns (Word))) { return value; }",
    "function alias(value: mapping(@Word => function(Word) returns (Word))) returns (mapping(@Word => function(Word) returns (Word))) { return value; }",
    "function make(value: Word) returns (function(Word) returns (Word)) { return lam(delta: Word) -> Word { value = value + delta; return value; }; }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key := do
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"compatible output function missing: {name}")

private structure Projected (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : Type where
  eq : checked.catalog.project source = .ok native
private def project (checked : Checked) (source : TypeSystem.Ty) (native : Core.Ty) : IO (Projected checked source native) := do
  match projected : checked.catalog.project source with
  | .error error => throw (IO.userError s!"compatible output projection failed: {reprStr error}")
  | .ok actual =>
      if same : actual = native then pure ⟨by simpa only [same] using projected⟩
      else throw (IO.userError "compatible output actual native projection changed")

private def check {checked : Checked} (prepared : SourceCoreCallableAncestryPrograms.Prepared checked)
    (recipe : Solcore.Frontend.SourceCoreCompatibleOutputs.Recipe checked prepared.layouts.definitions)
    (owner : Key) (arguments : List SourceValue) (expected : SourceValue) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource owner arguments fuel with
      | .ok completion => pure (completion.resume 150000)
      | .error error => throw (IO.userError s!"marked output source run failed: {reprStr error}")
    let projection ← project checked completion.entry.sourceResultType completion.entry.native.resultType
    let exported ← match SourceCoreCompatibleOutputs.decodeSuccess recipe completion.result.context
        completion.result.contextOwner completion.entry.sourceResultType projection.eq completion.result.native with
      | .ok exported => pure exported
      | .error error => throw (IO.userError s!"marked output reverse failed: {reprStr error}")
    assertTrue (reprStr exported.decoded.source == reprStr expected)
      s!"marked output source metadata/order changed: {reprStr exported.decoded.source}"

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"ancestry output source rejected: {reprStr error}")
  let seeds := (program.signatures.functions.filter (·.name != "keep")).map fun signature =>
    (⟨signature.id, []⟩ : SourceSpecializationWorklist.Request)
  let plan ← match SourceSpecializationWorklist.run program seeds 300 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"ancestry output plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"ancestry output base failed: {reprStr error}")
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"ancestry output factory failed: {reprStr error}")
  let recipe ← match SourceCoreCompatibleOutputs.prepareAncestry prepared with
    | .ok recipe => pure recipe | .error error => throw (IO.userError s!"ancestry output recipe failed: {reprStr error}")
  let inc ← key program "inc"
  let dec ← key program "dec"
  let named : SourceValue := .global inc []
  let getNamed ← key program "getNamed"
  let getBuiltin ← key program "getBuiltin"
  check prepared recipe getNamed [] named
  check prepared recipe getBuiltin [] (.builtin .wordToInteger)
  let qualified ← match prepared.base.functions.filter (fun function => function.specialized.assumptions != []) with
    | [function] => pure function
    | _ => throw (IO.userError "compatible qualified output specialization absent")
  let evidence ← match SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program qualified.signature.key
      qualified.specialized.assumptions with
    | .ok evidence => pure evidence | .error error => throw (IO.userError s!"compatible expected qualified evidence failed: {reprStr error}")
  assertTrue (!evidence.isEmpty) "compatible qualified output test lacked evidence"
  check prepared recipe (← key program "getQualified") [] (.global qualified.signature.key evidence)
  let holder ← match program.signatures.dataTypes.find? (·.name == "Holder") with
    | some holder => pure holder | none => throw (IO.userError "compatible output Holder absent")
  let constructor ← match holder.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "compatible output Hold absent")
  let functionType := TypeSystem.Ty.function .word .word
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, [], [functionType], .nominal holder.id []⟩
  check prepared recipe (← key program "getNominal") [] (.constructed instantiation [named])
  check prepared recipe (← key program "getTuple") [] (.product named (.builtin .wordToInteger))
  let mapping : SourceValue := .mapping (.comptime functionType) functionType
    [(named, named), (named, .global dec [])]
  check prepared recipe (← key program "mappingReturn") [mapping] mapping
  let alias : SourceValue := .mapping (.proxy (.comptime .word)) (.comptime functionType)
    [(.proxy (.comptime .word), named), (.proxy .word, .global dec [])]
  check prepared recipe (← key program "alias") [alias] alias
  let made ← match prepared.runSource (← key program "make") [.word (w 3)] 150000 with
    | .ok made => pure made | .error error => throw (IO.userError s!"ancestry lambda run failed: {reprStr error}")
  let projection ← project automatic.checked made.entry.sourceResultType made.entry.native.resultType
  match SourceCoreCompatibleOutputs.decodeSuccess recipe made.result.context made.result.contextOwner
      made.entry.sourceResultType projection.eq made.result.native with
  | .error {code := .lambdaExportRequiresLedger (.lambda _ _ _), ..} => pure ()
  | .error error => throw (IO.userError s!"ancestry lambda ledger boundary changed: {reprStr error}")
  | .ok _ => throw (IO.userError "ancestry lambda exported without authentic capture ledger")
  IO.println "frame-aware source output ownership and deep raw callable metadata GREEN"

end Tests.SourceCoreCallableAncestryOutputs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedLookup
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Lookup consumers over actual successful preparation, including arbitrary
finite lambda repetition and paired caller/lexical derivations. This tests a
pure metadata domain; native execution history is not a premise hidden here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedLookup
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedValidation
abbrev State := SourceCoreCallableAncestryReadRecipes.State

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base) (frame : Frame) (state : Option State) :
    prepared.table.lookup? frame = some state ↔ Authenticates prepared.inputs frame state := prepared_lookup_iff prepared

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (table : Table)
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) :
    Sound inputs table ∧ Closed inputs table := ⟨valid_sound inputs validated, valid_closed inputs validated⟩

private def repeated (id : Core.Word) : Nat → Frame → Frame
  | 0, parent => parent
  | count + 1, parent => .lambda id (repeated id count parent)

private theorem repeated_authenticates {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {frame : Frame} {state : State} {id : Core.Word} (ancestry : Authenticates inputs frame (some state))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed inputs state id = true) (count : Nat) :
    Authenticates inputs (repeated id count frame) (some state) := by
  induction count with
  | zero => exact ancestry
  | succ count ih => exact .lambda ih allowed

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {frame : Frame} {state : State} {id : Core.Word} (ancestry : Authenticates prepared.inputs frame (some state))
    (allowed : SourceCoreCallableAncestryPairedPreparation.lambdaAllowed prepared.inputs state id = true) (count : Nat) :
    prepared.table.lookup? (repeated id count frame) = some (some state) :=
  (prepared_lookup_iff prepared).mpr (repeated_authenticates ancestry allowed count)

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {callerFrame lexicalFrame : Frame} {caller lexical result : State} {id target : Core.Word}
    (callerAuth : Authenticates prepared.inputs callerFrame (some caller))
    (lexicalAuth : Authenticates prepared.inputs lexicalFrame (some lexical))
    (selected : SourceCoreCallableAncestryPairedPreparation.view? prepared.inputs caller lexical id target = some result) :
    prepared.table.lookup? (.appliedView id target callerFrame lexicalFrame) = some (some result) :=
  (prepared_lookup_iff prepared).mpr (.appliedView callerAuth lexicalAuth selected)

example (table : Table) (id target : Core.Word) (caller : Frame) :
    table.lookup? (.view id target caller) = none := rfl

example {checked : Checked} {base : Base checked} {inputs : Inputs base}
    {caller lexical result : State} {id target : Core.Word}
    (accepted : SourceCoreCallableAncestryPairedPreparation.view? inputs caller lexical id target = some result) :
    ∃ (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
      (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical),
      SourceCoreCallableAncestryReadRecipes.prepareRead inputs caller id target = .ok read ∧
      SourceCoreCallableAncestryReadRecipes.applyRead read lexical = .ok applied ∧ result = read.after lexical :=
  view_receipts accepted

end Tests.SourceCoreCallableAncestryPairedLookup
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedPreparation
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation.Recipe.mk

/-! Actual checked shared principals require two different metadata parents.
The graph is prepared before execution. These manually assembled owned frames
test finite metadata lookup; actual native snapshot provenance is separate. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedPreparation
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableAncestryPairedPreparation
abbrev PairedFrame := SourceCoreCallablePairedFrames.Frame
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
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
  let program ← get "paired source checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "sharedHistory") with
    | some signature => pure signature | none => throw (IO.userError "missing paired root")
  let owner : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"paired plan failed: {reprStr other}")
  let automatic ← get "paired compiler base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let prepared ← get "paired metadata preparation" (prepare automatic.prepared)
  let named ← match prepared.inputs.callable.table.idAt? (.named owner) with
    | some named => pure named | none => throw (IO.userError "missing paired named origin")
  let root : PairedFrame := .named named
  let rootPosition ← match prepared.table.lookupIndex? root with
    | some (some index) => pure index | _ => throw (IO.userError "missing paired root state")
  let outerViews := prepared.inputs.views.entries.filter (·.view.binding.binder.name == "outer")
  let sharedViews := prepared.inputs.views.entries.filter (·.view.binding.binder.name == "shared")
  let shared ← match sharedViews with
    | [shared] => pure shared | _ => throw (IO.userError "wrong shared occurrence count")
  let sharedTarget ← match prepared.inputs.callable.table.idAt?
      (.lambda shared.view.owner shared.view.principal.initializer shared.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "missing shared descriptor")
  let mut observed : List SourceCoreCallableAncestryReadRecipes.State := []
  let mut callerSources : List TypedSource := []
  for outer in outerViews do
    let outerTarget ← match prepared.inputs.callable.table.idAt?
        (.lambda outer.view.owner outer.view.principal.initializer outer.view.cumulative) with
      | some target => pure target | none => throw (IO.userError "missing outer descriptor")
    let caller : PairedFrame := .appliedView outer.id outerTarget root root
    let callerPosition ← match prepared.table.lookupIndex? caller with
      | some (some index) => pure index | _ => throw (IO.userError "missing paired caller state")
    let frame : PairedFrame := .appliedView shared.id sharedTarget caller root
    let position ← match prepared.table.lookupIndex? frame with
      | some (some index) => pure index | _ => throw (IO.userError "shared lexical/read pair rejected")
    let state ← match prepared.table.stateAt? position with
      | some state => pure state | none => throw (IO.userError "missing paired destination")
    let recipe ← match prepared.recipeAt? callerPosition rootPosition shared.id sharedTarget with
      | some recipe => pure recipe | none => throw (IO.userError "missing cached paired recipe")
    assertTrue (state.nativeActive == shared.view.cumulative &&
      state.metadata.active == shared.view.ownSubstitution && state.metadata.active != state.nativeActive)
      "source context was collapsed into the compiled cumulative context"
    assertTrue (recipe.lexical.metadata.active.isEmpty && recipe.caller.nativeActive == shared.view.parentActive)
      "read caller replaced principal creation metadata"
    assertTrue (recipe.read.witnesses.isEmpty) "unqualified shared read inherited caller witnesses"
    match recipe.applied.sourceValue [] [] with
    | .instantiated _ _ (.closure _ _ _ source key _ _) =>
      assertTrue (source == recipe.lexical.metadata.source && key == owner) "cached export substituted its original principal"
    | _ => throw (IO.userError "cached export lost instantiated closure")
    let repeated := (List.range 2000).foldl (fun (frame : PairedFrame) _ => .lambda sharedTarget frame) frame
    assertTrue (decide (prepared.table.lookupIndex? repeated = some (some position)))
      "repeated metadata depth created an unavailable state"
    observed := observed ++ [state]
    callerSources := callerSources ++ [recipe.caller.metadata.source]
  assertTrue (observed.length == 2 && (observed.map (·.metadata.source)).eraseDups.length == 1 &&
    callerSources.eraseDups.length == 2)
    "shared principal source inherited the caller's unrelated requirements"
  assertTrue ((prepared.table.lookupIndex? (.appliedView shared.id sharedTarget root root)).isNone)
    "shared read accepted the lexical root as its caller"
  assertTrue ((prepared.table.lookupIndex? (.view shared.id sharedTarget root)).isNone)
    "transient tag acquired a principal source state"
  assertTrue (decide ((prepared.table.states.map SourceCoreCallableAncestryPairedCache.stateKey).Nodup))
    "duplicate paired state keys"
  assertTrue (decide (prepared.table.states.length ≤ capacity prepared.inputs prepared.initial))
    "paired state count exceeded its structural bound"
  IO.println s!"paired ancestry worklist: {prepared.table.states.length} reached states, shared lexical/read parents and occurrence-specific cached recipes GREEN"

end Tests.SourceCoreCallableAncestryPairedPreparation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedProfiles
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Theorems over actual named/read/application metadata receipts. There are
no runtime traces, supplied child evaluations, or bounds on frame depth. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedProfiles
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryMetadata CallableAncestryPairedProfiles

section
variable {checked : Checked} {base : Base checked} (inputs : Inputs base)
  (roots : List PairedState)
  (selected : ∀ root ∈ roots, ∃ id,
    SourceCoreCallableAncestryPreparation.named? inputs id = some root.metadata ∧ root.nativeActive = [])

example : RootsCoherent roots := seeded_coherent (roots_seeded inputs roots selected)

example {root : PairedState} (member : root ∈ roots) : Valid inputs roots root :=
  seeded_valid inputs (roots_seeded inputs roots selected) member

example {left right : PairedState} (leftValid : Valid inputs roots left) (rightValid : Valid inputs roots right)
    (same : key left = key right) : left = right :=
  key_injective (seeded_coherent (roots_seeded inputs roots selected)) leftValid rightValid same

example {caller lexical : PairedState} {id target : Core.Word}
    (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)
    (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)
    (callerValid : Valid inputs roots caller) (lexicalValid : Valid inputs roots lexical) :
    Valid inputs roots (read.after lexical) :=
  read_after_valid (seeded_coherent (roots_seeded inputs roots selected)) read applied callerValid lexicalValid

example (states : List PairedState) (unique : (states.map key).Nodup)
    (valid : ∀ state ∈ states, Valid inputs roots state) : states.length ≤ capacity inputs roots :=
  states_bounded inputs roots states unique valid

example : (keySpace inputs roots).length = capacity inputs roots := keySpace_length inputs roots

end

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (initial : SourceCoreCallableAncestryPairedCache.Table) (states : List PairedState)
    (unique : (states.map key).Nodup) (valid : ∀ state ∈ states, Valid inputs initial.states state) :
    states.length ≤ SourceCoreCallableAncestryPairedPreparation.capacity inputs initial :=
  prepared_capacity_bound inputs initial states unique valid

/-- Equal retained source metadata does not identify different native code
contexts. This dimension is essential for the paired protocol. -/
example (state : PairedState) (first second : Substitution) (different : first ≠ second) :
    key {state with nativeActive := first} ≠ key {state with nativeActive := second} := by
  intro same
  exact different (congrArg (fun value : CallableAncestryPairedProfiles.Key => value.nativeActive) same)

example (state : PairedState) (first second : Substitution) (different : first ≠ second) :
    key {state with metadata := {state.metadata with active := first}} ≠
      key {state with metadata := {state.metadata with active := second}} := by
  intro same
  exact different (congrArg (fun value : CallableAncestryPairedProfiles.Key => value.sourceActive) same)

example (contexts : List Substitution) (root : PairedState) :
    (keysFor [] contexts root).length = contexts.length *
      (CallableAncestryProfiles.alphabet root.metadata.source).length ^
        (CallableAncestryProfiles.alphabet root.metadata.source).length := by
  simpa [CallableAncestrySourceActive.capacity, CallableAncestrySourceActive.domainAlphabet,
    CallableAncestrySourceActive.alphabet] using keysFor_length [] contexts root

end Tests.SourceCoreCallableAncestryPairedProfiles
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedProgress
/-! The queue proof consumes actual factory equations. Final closure validation
and recipe success are conclusions, not assumptions supplied by the caller. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableAncestryPairedProgress
open Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    {initial final : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial)
    (completed : SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final) :
    SourceCoreCallableAncestryPairedPreparation.valid inputs final = true :=
  CallableAncestryPairedProgress.seeded_saturation_valid inputs seeded completed

example {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      SourceCoreCallableAncestryPairedPreparation.valid inputs final = true ∧
      ∃ recipes, final.views.attach.mapM (fun edge =>
        SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs final edge.val edge.property) = .ok recipes :=
  CallableAncestryPairedProgress.seeded_completion_total inputs seeded

/-- Successful compilation of the table preserves the independently defined
paired metadata authentication domain, including separately indexed parents. -/
example {checked : Checked} {base : Base checked} (inputs : Inputs base) {initial : Table}
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ table : Table, ∀ frame state, table.lookup? frame = some (some state) ↔ Authenticates inputs frame (some state) := by
  obtain ⟨table, _, validated, _⟩ := CallableAncestryPairedProgress.seeded_completion_total inputs seeded
  refine ⟨table, ?_⟩
  intro frame state
  exact lookup_iff (CallableAncestryPairedValidation.valid_sound inputs validated)
    (CallableAncestryPairedValidation.valid_closed inputs validated)

end Solcore.Test.SourceCoreCallableAncestryPairedProgress
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedRecipes
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The actual final edge checker suffices for all recipe factories. Cached
selection then needs no runtime substitution or evidence resolution. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedRecipes
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedRecipes

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) :
    ∃ recipes, table.views.attach.mapM (fun edge =>
      SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs table edge.val edge.property) = .ok recipes :=
  recipes_total validated

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {caller lexical destination : Nat} {id target : Core.Word}
    (selected : prepared.table.viewAt? caller lexical id target = some destination) :
    ∃ recipe, prepared.recipeAt? caller lexical id target = some recipe := recipeAt_complete prepared selected

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {edge : SourceCoreCallableAncestryPairedCache.ViewEdge} (member : edge ∈ prepared.table.views) :
    ∃ recipe ∈ prepared.recipes, recipe.edge = edge := prepared_recipe_member prepared member

end Tests.SourceCoreCallableAncestryPairedRecipes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedSeeds
/-! The actual compiler equation authenticates named seeds. Cache completion
requires no successful seed, validator, recipe, or runtime-execution premise. -/
set_option autoImplicit false
namespace Solcore.Test.SourceCoreCallableAncestryPairedSeeds
open Frontend SourceSemantics.CoreLowering
open CallableAncestryPairedLookup

example {checked : Checked} {base : Base checked} (inputs : Inputs base)
    (owned : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries) :
    ∃ initial, SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial :=
  CallableAncestryPairedSeeds.seed_total inputs owned

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    (inputs : Inputs base) : CallEntryCertificates.AllAuthenticated base.plan inputs.callable.table.entries :=
  CallableAncestryPairedSeeds.factory_authenticated compiled inputs

example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared, SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared :=
  CallableAncestryPairedSeeds.preparation_total compiled inputsPrepared

/-- The completed production cache exactly recognizes the independent paired
metadata domain. This does not assert that all native snapshots inhabit it. -/
example {program : CheckedProgram} {plan : SourceSpecializationWorklist.Plan}
    {checked : Checked} {ownership : checked.signatures = program.signatures} {fuel : Nat}
    {base : Base checked}
    (compiled : SourceCoreCompatibleFunctions.prepareWithCatalog program plan checked ownership fuel = .ok base)
    {inputs : Inputs base}
    (inputsPrepared : SourceCoreCallableAncestryPreparation.prepareInputs base = .ok inputs) :
    ∃ prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base,
      SourceCoreCallableAncestryPairedPreparation.prepare base = .ok prepared ∧
      ∀ frame state, prepared.table.lookup? frame = some state ↔ Authenticates prepared.inputs frame state := by
  obtain ⟨prepared, accepted⟩ := CallableAncestryPairedSeeds.preparation_total compiled inputsPrepared
  exact ⟨prepared, accepted, fun _ _ => CallableAncestryPairedValidation.prepared_lookup_iff prepared⟩

end Solcore.Test.SourceCoreCallableAncestryPairedSeeds
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPairedWorklist
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Actual worklist totality after successful named seeding. These consumers
do not assume a successful final saturation result, invent a traversal fuel,
or treat final validation/native-frame coverage as already established. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedWorklist
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedWorklist
abbrev State := SourceCoreCallableAncestryReadRecipes.State

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table)
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial = .ok final ∧
      StatesValid inputs final.states := seeded_saturation_total inputs seeded

example {checked : Checked} {base : Base checked} (inputs : Inputs base) (initial : Table)
    (seeded : SourceCoreCallableAncestryPairedPreparation.seed inputs = .ok initial) :
    SourceCoreCallableAncestryPairedPreparation.saturate inputs
      (SourceCoreCallableAncestryPairedPreparation.capacity inputs initial) 0 initial ≠
        .error .cardinalityExhausted := by
  obtain ⟨final, completed, _⟩ := seeded_saturation_total inputs seeded
  rw [completed]
  intro impossible
  cases impossible

example {checked : Checked} {base : Base checked} (inputs : Inputs base) :
    CallableAncestryPairedProfiles.RootsCoherent (namedRoots inputs) :=
  CallableAncestryPairedProfiles.seeded_coherent (named_roots_seeded inputs)

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {states : List State}
    (valid : StatesValid inputs states) {state : State} {frame : Frame}
    (authentic : Authenticates inputs frame (some state)) :
    ∃ position output, SourceCoreCallableAncestryPairedPreparation.intern states state = .ok (position, output) ∧
      StatesValid inputs output ∧ states ⊆ output ∧ state ∈ output := intern_total valid ⟨frame, authentic⟩

end Tests.SourceCoreCallableAncestryPairedWorklist
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPreparation
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPreparation.Prepared.mk

/-! Actual compiler-owned seeds and reachable transitions, prepared before any
native execution. The test distinguishes repeated frame depth from state count,
and occurrence-specific requirement profiles from identical closed types. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPreparation
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryCache

example {checked : Checked} {base : Base checked} (owned : Owned base)
    (prepared : SourceCoreCallableAncestryPreparation.Prepared base) {frame : ContextFrame}
    {state : Option Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State} :
    prepared.table.lookup? frame = some (state.map nativeState) ↔ Authenticates owned frame state :=
  Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions.prepared_lookup_iff owned prepared

private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type WordFunction = function(Word) returns (Word);",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function pair() returns (WordFunction, WordFunction) {",
    " let outer = lam(value) { keep(value);",
    "   let inner: WordFunction = lam(item: Word) -> Word { return item; }; return inner; };",
    " return (outer(1), outer(2)); }"
  ]}] }

def run : IO Unit := do
  let program ← get "cache source checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.filter (·.name == "pair") with
    | [signature] => pure signature | _ => throw (IO.userError "missing pair")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"specialization: {reprStr result}")
  let artifact ← get "compatible artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)
  let owned ← get "independent owned metadata" (prepare artifact.prepared)
  let prepared ← get "actual reachable preparation" (SourceCoreCallableAncestryPreparation.prepare artifact.prepared)
  let (left, right) ← match owned.views.entries.filter (·.view.principal.binder.name == "outer") with
    | [left, right] => pure (left, right) | _ => throw (IO.userError "expected two owned reads")
  let named ← match owned.callable.table.idAt? (.named left.view.owner) with
    | some id => pure id | none => throw (IO.userError "missing owner")
  let target ← match owned.callable.table.idAt?
      (.lambda left.view.owner left.view.principal.initializer left.view.cumulative) with
    | some id => pure id | none => throw (IO.userError "missing lambda target")
  let first : ContextFrame := .view left.id target (.named named)
  let second : ContextFrame := .view right.id target (.named named)
  let repeated := (List.range 2000).foldl (fun (frame : ContextFrame) _ => .lambda target frame) second
  let mut results : List SourceCoreCallableAncestryCache.State := []
  for frame in [first, second, repeated] do
    let expected ← get "independent metadata authentication" (prepareFrame owned frame)
    assertTrue (decide (prepared.table.lookup? frame = some (expected.val.map nativeState)))
      "actual reached cache disagrees with independent occurrence transport"
    match prepared.table.lookup? frame with
    | some (some state) => results := results ++ [state]
    | _ => throw (IO.userError "missing nonempty ancestry")
  match results with
  | [first, second, repeated] =>
    assertTrue (decide (first.active = second.active) && decide (first.source ≠ second.source))
      "equal type contexts collapsed occurrence-specific metadata"
    assertTrue (decide (second = repeated)) "repeated lambda depth allocated a different metadata state"
  | _ => throw (IO.userError "wrong result count")
  assertTrue (decide (prepared.table.states.length ≤ SourceCoreCallableAncestryPreparation.capacity prepared.inputs prepared.initial))
    "reached states exceeded the structural cardinality bound"
  assertTrue (decide ((prepared.table.states.map (·.key)).Nodup)) "duplicate reached state keys"
  assertTrue ((prepared.table.lookup? (.view left.id (Core.Word.ofNatModulo 999999) (.named named))).isNone)
    "foreign target accepted"
  IO.println s!"actual ancestry worklist: {prepared.table.states.length} reached states, 2000 repeated frames, distinct equal-type read profiles GREEN"
end Tests.SourceCoreCallableAncestryPreparation
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPrincipalHeaders
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Header.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Prepared.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.Restored.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryPrincipalHeaders.AllocationRestored.mk

/-! Actual finite graph preparation happens before native execution. Unused
generalized principals retain open lambda headers, occurrence-specific source
metadata and ordered source captures despite having a Unit native payload.
This test does not assert that every accepted artifact's preparation completes.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPrincipalHeaders
open Solcore Solcore.Frontend SourceInference
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def w (value : Nat) : Core.Word := Core.Word.ofNatModulo value
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function unusedViews(seed: Word) returns (Word) {",
    " let outer = lam(value) { keep(value); let unused = lam(item) { return item; }; return seed; };",
    " return outer(1) + outer(2); }"
  ]}] }

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"principal header source rejected: {reprStr error}")
  let signature ← match program.signatures.functions.find? (·.name == "unusedViews") with
    | some signature => pure signature | none => throw (IO.userError "principal header root missing")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 128 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"principal header plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"principal header base failed: {reprStr error}")
  let native ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok native => pure native | .error error => throw (IO.userError s!"principal header compiler failed: {reprStr error}")
  let graph ← match SourceCoreCallableAncestryPreparation.prepare automatic.prepared with
    | .ok graph => pure graph | .error error => throw (IO.userError s!"principal header graph preparation failed: {reprStr error}")
  let headers ← match SourceCoreCallableAncestryPrincipalHeaders.prepare native graph.table with
    | .ok headers => pure headers | .error error => throw (IO.userError s!"principal header preparation failed: {reprStr error}")
  let initial : SourceCoreAllocationLedger.SourceHeap := [⟨.integer, some (.integer 12)⟩, ⟨.bool, some (.bool true)⟩]
  for budget in [0, 31, 211, 100000] do
    let completion ← match native.runSource key [.word (w 4)] budget with
      | .ok completion => pure (completion.resume 100000)
      | .error error => throw (IO.userError s!"principal header native call failed: {reprStr error}")
    let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
      | .ok ledger => pure ledger | .error error => throw (IO.userError s!"principal header ledger failed: {reprStr error}")
    let rows := ledger.ledger.rows.filter (·.entry.key.binder.name == "unused")
    assertTrue (rows.length == 2) "unused principal allocation count changed"
    let sources ← rows.mapM fun row => do
      assertTrue (row.payload == some Core.Value.unit) "unused principal acquired native executable code"
      let allocation ← match SourceCoreCallableAncestryPrincipalHeaders.restoreAllocation headers row with
        | .ok restored => pure restored | .error error => throw (IO.userError s!"principal restoration failed: {reprStr error}")
      let restored := allocation.restored
      match restored.value with
      | .closure parameters result body source owner captured evidence =>
        assertTrue (!result.freeVariables.isEmpty && parameters.length == 1 && !body.isEmpty)
          "unused generic principal lost its open source header"
        assertTrue (owner == key && reprStr captured == reprStr row.environment)
          "principal owner or ordered capture locations changed"
        assertTrue (captured.all fun entry => initial.length ≤ entry.2.index)
          "principal captures included the opaque initial prefix"
        assertTrue (reprStr evidence == reprStr restored.header.principal.context.evidence)
          "principal cached evidence changed"
        pure (reprStr source)
      | _ => throw (IO.userError "principal restoration erased the source closure constructor")
    assertTrue (sources.eraseDups.length == 2) "same-type reads lost distinct principal requirement metadata"
    match completion.result.native.observation with
    | .succeeded (.word value) _ => assertTrue (value == w 8) "principal preparation changed native execution"
    | _ => throw (IO.userError "principal header source did not complete")
  IO.println "prepared principal headers: unused generic Unit bundles, raw sources, ordered captures and resume GREEN"

end Tests.SourceCoreCallableAncestryPrincipalHeaders
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryProfiles
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Universal factory/ancestry invariants and a checked qualified-local
fixture. Repeated lambda ancestry changes the finite frame, while retaining
the same occurrence profile. No cache-completeness assertion is made here. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryProfiles
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles

example {caller : SourceSpecialization.SpecializedFunction}
    {available : SourceCompilationPlan.EvidenceEnvironment} {binder : TypedBinder} {node : ExpressionNode}
    {substitution : Substitution} {witnesses : List Witness}
    (accepted : SourceCompilationPlan.localRequirementWitnesses caller available binder node = .ok (substitution, witnesses)) :
    ∀ witness ∈ witnesses, witness.actualRequirement ∈ node.requirements := witnesses_actual_subset accepted

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {frame : ContextFrame} {state : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (authenticated : Authenticates owned frame (some state)) :
    ∃ (id : Core.Word) (named : Named owned id), state.owner = named.state.owner ∧
      Bounded (alphabet named.state.source) state.source ∧
      (requirementProfile state.source).map List.length = (requirementProfile named.state.source).map List.length :=
  Authenticates.original_bound authenticated

example {checked : Checked} {base : Base checked} {owned : Owned base}
    {id target : Core.Word} {view : ViewAt owned id target}
    {before : Solcore.SourceSemantics.CoreLowering.CallableAncestryMetadata.State}
    (step : ViewStep view before) {canonical : TypedSource}
    (beforeCanonical : eraseRequirements before.source = eraseRequirements canonical) :
    step.after.owner = view.entry.view.owner ∧ step.after.active = view.entry.view.cumulative ∧
      eraseRequirements step.after.source = eraseRequirements (canonical.applySubstitution view.entry.view.ownSubstitution) :=
  ViewStep.canonical step beforeCanonical

private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "function keep<T>(item: T) returns (T) where T: Mark { return item; }",
    "function main() returns (Word) {",
    " let f = lam(value) { keep(value); return value; }; return f(1); }"
  ]}] }

def run : IO Unit := do
  let program ← get "profile fixture checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "main") with
    | some signature => pure signature | none => throw (IO.userError "profile fixture main missing")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"profile worklist: {reprStr result}")
  let artifact ← get "profile artifact" (SourceCoreCompatibleFunctions.prepare program plan 512)
  let owned ← get "profile metadata" (prepare artifact.prepared)
  let view ← match owned.views.entries.find? (·.view.principal.binder.name == "f") with
    | some view => pure view | none => throw (IO.userError "profile view missing")
  let named ← match owned.callable.table.idAt? (.named view.view.owner) with
    | some id => pure id | none => throw (IO.userError "profile named descriptor missing")
  let target ← match owned.callable.table.idAt? (.lambda view.view.owner view.view.principal.initializer view.view.cumulative) with
    | some id => pure id | none => throw (IO.userError "profile lambda descriptor missing")
  let root : ContextFrame := .view view.id target (.named named)
  let deep := (List.range 200).foldl (fun (frame : ContextFrame) _ => .lambda target frame) root
  let first ← get "profile first view" (prepareFrame owned root)
  let repeated ← get "profile repeated ancestry" (prepareFrame owned deep)
  let (first, repeated) ← match first.val, repeated.val with
    | some first, some repeated => pure (first, repeated)
    | _, _ => throw (IO.userError "profile ancestry lost source")
  assertTrue (decide (first = repeated)) "lambda ancestry altered metadata state"
  let original := view.view.principal.originalSource
  assertTrue ((requirementProfile repeated.source).map List.length == (requirementProfile original).map List.length)
    "actual view changed spine lengths"
  assertTrue ((requirementProfile repeated.source).all fun spine => spine.all (alphabet original).contains)
    "actual view introduced an ID outside the owned original source"
  IO.println "ancestry profiles: actual witness factory and 200 nested frames retain the finite original ID alphabet GREEN"
end Tests.SourceCoreCallableAncestryProfiles
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryPrograms
/-! Real checked multi-root compilation with one fixed allocation suffix.
Execution and resumption use the shared typed Core machine. Closures capture by
value: each call starts again from the values its captures had when the lambda
was created. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPrograms
open Solcore Solcore.Frontend SourceInference
abbrev Key := SourceSpecialization.SpecializationKey

private def assertTrue (test : Bool) (message : String) : IO Unit :=
  unless test do throw (IO.userError message)
private def w (n : Nat) : Core.Word := Core.Word.ofNatModulo n
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "enum Box<T> { Box(T) }",
    "trait Marker<T> {}", "impl Marker<mapping(Word => Word)> {}",
    "function keep<T>(value: T) returns (T) where T: Marker { return value; }",
    "function local(table: mapping(Word => Word)) returns (mapping(Word => Word)) { let f = lam(item) { return keep(item); }; return f(table); }",
    "function lazy() returns (mapping(Word => Word)) { let table: mapping(Word => Word); table[1] = 7; return table; }",
    "function choose(value: Box<Word>) returns (Word) { match (value) { case .Box(bound) { return bound; } default { return 99; } } }",
    "function capture(start: Word) returns (Word) { let value = start; let f = lam(step: Word) { value += step; return value; }; f(3); return f(4); }",
    "function recursive(n: Word) returns (Word) { let f: function(Word) returns (Word); f = lam(left: Word) { return left == 0 ? 0 : f(left - 1) + 1; }; return f(n); }",
    "function unused() returns (Word) { let unused = lam(item) { return item; }; return 7; }",
    "function tuple(value: (Word, Bool)) returns (Word) { match (value) { case ((left, flag)) { return flag ? left : 99; } default { return 77; } } }",
    "function looping(limit: Word) returns (Word) { let total = 0; for (let i = 0; i < limit; i += 1) { total += i; } return total; }",
    "function absent() returns (Word) { let absent: Word; return absent; }"
    , "function getLocal(start: Word) returns (function(Word) returns (Word)) { let value = start; let f = lam(item) { value += 1; return item; }; return f; }"
    , "function useReturned(start: Word) returns (Word) { let f = getLocal(start); return f(9); }"
  ]}] }

private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"marked fixture missing {name}")

private def runSuccess {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Solcore.Frontend.SourceCoreCallableAncestryPrograms.Prepared checked) (key : Key) (arguments : List SourceTypedRuntime.Value)
    (expected : SourceCoreCompatibleValues.Value) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource key arguments fuel 500 with
      | .ok completion => pure completion
      | .error error => throw (IO.userError s!"marked run failed: {reprStr error}")
    let opaqueInitial : List SourceTypedRuntime.Cell := [⟨.word, none⟩]
    let earlyReceipt ← match SourceCoreCallableAncestryLedger.scan completion opaqueInitial with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"frame-aware partial ledger failed: {reprStr error}")
    assertTrue (earlyReceipt.ledger.initialHeap.map (·.type) == opaqueInitial.map (·.type)) "partial ledger altered the opaque source prefix"
    let completion := completion.resume 150000
    let complete ← match SourceCoreCallableAncestryLedger.scan completion opaqueInitial with
      | .ok complete => pure complete
      | .error error => throw (IO.userError s!"frame-aware typed ledger failed: {reprStr error}")
    assertTrue complete.ledger.pending.isNone "completed invocation left a pending source marker"
    assertTrue (SourceCoreCallableAncestryLedger.frame? completion == some .empty)
      "completed invocation did not retain the exact restorable frame"
    match completion.result.native.observation with
    | .succeeded value store =>
      let decoded ← match SourceCoreCompatibleValues.decode 500 completion.result.context completion.entry.sourceResultType value with
        | .ok decoded => pure decoded
        | .error error => throw (IO.userError s!"marked output failed: {reprStr error}")
      assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame .empty))
        "completed invocation did not restore its administrative callable frame"
      let ledger ← match SourceCoreAllocationLedger.scan prepared.layouts [] store with
        | .ok ledger => pure ledger
        | .error error => throw (IO.userError s!"frame-aware ledger failed: {reprStr error}")
      assertTrue (ledger.rows.all fun row => row.coreLocation > prepared.base.globals.length)
        "administrative callable frame became a source cell"
      assertTrue (decoded == expected) s!"marked result changed: {reprStr decoded}"
      assertTrue (store.any fun value => match value with
        | .constructed constructor _ => constructor.owner.index ≥ checked.catalog.definitions.length
        | _ => false) "source invocation omitted allocation markers"
    | observation => throw (IO.userError s!"marked result did not succeed: {reprStr observation}")

/-- The binder `name` declared in `key`'s checked body. -/
private def binder (plan : SourceSpecializationWorklist.Plan) (key : Key) (name : String) : IO Resolved.LocalId := do
  let specialized ← match SourceCompilationPlan.exactSpecialization plan key with
    | .ok specialized => pure specialized
    | .error error => throw (IO.userError s!"marked specialization missing: {reprStr error}")
  match (SourceCoreDataPlaces.declaredBinders specialized.function.typedBody).filter (·.name == name) with
  | [binder] => pure binder.id
  | _ => throw (IO.userError s!"marked fixture binder missing {name}")

/-- A lambda created before a captured local is assigned copies that local
uninitialized, so its read in the body faults at every call. -/
private def runUninitialized {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Solcore.Frontend.SourceCoreCallableAncestryPrograms.Prepared checked) (key : Key)
    (arguments : List SourceTypedRuntime.Value) (missing : Resolved.LocalId) : IO Unit := do
  for fuel in [0, 7, 37, 150000] do
    let completion ← match prepared.runSource key arguments fuel 500 with
      | .ok completion => pure completion
      | .error error => throw (IO.userError s!"marked run failed: {reprStr error}")
    let completion := completion.resume 150000
    let opaqueInitial : List SourceTypedRuntime.Cell := [⟨.word, none⟩]
    let _ ← match SourceCoreCallableAncestryLedger.scan completion opaqueInitial with
      | .ok receipt => pure receipt
      | .error error => throw (IO.userError s!"frame-aware failure ledger failed: {reprStr error}")
    match completion.result.native.observation with
    | .failed reason store =>
      let diagnostic ← match completion.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic
        | none => throw (IO.userError "marked uninitialized capture diagnostic missing")
      assertTrue (diagnostic.error == .uninitializedLocal missing && diagnostic.span.isSome)
        "read of a lambda's uninitialized capture copy did not fault at its source site"
      assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame .empty))
        "language failure did not restore its administrative callable frame"
    | observation => throw (IO.userError s!"marked uninitialized capture changed: {reprStr observation}")

private def manyRoots : IO Unit := do
  let workspace : Workspace.RawWorkspace := {
    entry := "main.solc"
    externalLibraries := []
    mainSources := [{
      path := "main.solc"
      content := String.intercalate "\n" ((List.range 40).map fun index =>
        "function root" ++ toString index ++ "() returns (Word) { return 7; }")}] }
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"many roots rejected: {reprStr error}")
  let plan ← match SourceSpecializationWorklist.run program
      (program.signatures.functions.map (fun signature => ⟨signature.id, []⟩)) 500 with
    | .ok (.complete plan) => pure plan | result => throw (IO.userError s!"many roots plan failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 32 with
    | .ok automatic => pure automatic | .error error => throw (IO.userError s!"many roots base failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCallableAncestryPrograms.prepare automatic.prepared 32 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"many roots marked failed: {reprStr error}")
  assertTrue (prepared.entries.length == 40) "source fuel incorrectly bounded the complete Core inventory"
  let completion ← match prepared.runSource (← key program "root39") [] 50000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"many roots run failed: {reprStr error}")
  match completion.result.native.observation with
  | .succeeded (.word value) _ => assertTrue (value == w 7) "many roots result changed"
  | observation => throw (IO.userError s!"many roots observation changed: {reprStr observation}")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program
    | .error error => throw (IO.userError s!"marked fixture rejected: {reprStr error}")
  let names := ["local", "lazy", "choose", "capture", "recursive", "unused", "tuple", "looping", "absent", "getLocal", "useReturned"]
  let keys ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 128 with
    | .ok (.complete plan) => pure plan
    | result => throw (IO.userError s!"marked worklist failed: {reprStr result}")
  let automatic ← match SourceCoreCompatibleFunctions.prepare program plan 500 with
    | .ok automatic => pure automatic
    | .error error => throw (IO.userError s!"marked base factory failed: {reprStr error}")
  let prepared ← match Solcore.Frontend.SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared
    | .error error => throw (IO.userError s!"marked factory failed: {reprStr error}")
  assertTrue (prepared.entries.length == keys.length) "marked roots disappeared"
  assertTrue (!prepared.layouts.entries.isEmpty) "marked catalog is empty"
  assertTrue (prepared.layouts.definitions.take automatic.checked.catalog.definitions.length == automatic.checked.catalog.definitions)
    "marked suffix changed ambient definitions"
  runSuccess prepared (← key program "local") [.mapping .word .word [(.word (w 1), .word (w 9))]]
    (.mapping .word .word [(.word (w 1), .word (w 9))])
  runSuccess prepared (← key program "lazy") [] (.mapping .word .word [(.word (w 1), .word (w 7))])
  -- Both calls of `f` start again from `value = 10`; the second returns 10 + 4.
  runSuccess prepared (← key program "capture") [.word (w 10)] (.word (w 14))
  -- `f` is still uninitialized when its lambda is created, so the lambda's copy
  -- of `f` is too, and the first recursive read faults.
  let recursive ← key program "recursive"
  runUninitialized prepared recursive [.word (w 4)] (← binder plan recursive "f")
  runSuccess prepared (← key program "unused") [] (.word (w 7))
  runSuccess prepared (← key program "tuple") [.product (.word (w 13)) (.bool true)] (.word (w 13))
  runSuccess prepared (← key program "looping") [.word (w 4)] (.word (w 6))
  runSuccess prepared (← key program "useReturned") [.word (w 4)] (.word (w 9))
  let box ← match program.signatures.dataTypes.find? (·.name == "Box") with
    | some box => pure box | none => throw (IO.userError "marked Box missing")
  let constructor ← match box.constructors[0]? with
    | some constructor => pure constructor | none => throw (IO.userError "marked constructor missing")
  let instantiation : DataConstructorInstantiation := ⟨constructor.id, box.parameters.zip [.word], [.word], .nominal box.id [.word]⟩
  runSuccess prepared (← key program "choose") [.constructed instantiation [.word (w 7)]] (.word (w 7))
  let absent ← match prepared.runSource (← key program "absent") [] 150000 500 with
    | .ok completion => pure completion
    | .error error => throw (IO.userError s!"marked absent run failed: {reprStr error}")
  match absent.result.native.observation with
  | .failed reason store =>
      assertTrue (store[0]? == some (SourceCoreCallableContextFrames.encode prepared.ancestry.layout.frame .empty))
        "language failure did not restore its administrative callable frame"
      let diagnostic ← match absent.result.diagnostics.diagnostic? reason with
        | some diagnostic => pure diagnostic | none => throw (IO.userError "marked absent diagnostic missing")
      assertTrue diagnostic.span.isSome "marked absent span lost"
      assertTrue (!store.isEmpty) "marked failure lost allocations"
  | observation => throw (IO.userError s!"marked absent result changed: {reprStr observation}")
  manyRoots
  IO.println "actual compatible compiler with callable ancestry and shared source ledger GREEN"

end Tests.SourceCoreCallableAncestryPrograms
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryReadRecipeProofs
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Universal consumers of the paired metadata receipts. They need neither a
source execution nor equality of caller/lexical contexts. Independent dynamic
evidence is supplied explicitly, not inferred from native closure typing. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryReadRecipeProofs
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics Solcore.SourceSemantics.CoreLowering
open CallableAncestryReadRecipes CallableAncestryMetadata CallableAncestryProfiles

example {leftCaller rightCaller : SourceSpecialization.SpecializedFunction}
    {leftAvailable rightAvailable : SourceCompilationPlan.EvidenceEnvironment}
    {leftBinder rightBinder : TypedBinder} {leftNode rightNode : ExpressionNode}
    {leftSubstitution rightSubstitution : Substitution} {leftWitnesses rightWitnesses : List Witness}
    (left : SourceCompilationPlan.localRequirementWitnesses leftCaller leftAvailable leftBinder leftNode =
      .ok (leftSubstitution, leftWitnesses))
    (right : SourceCompilationPlan.localRequirementWitnesses rightCaller rightAvailable rightBinder rightNode =
      .ok (rightSubstitution, rightWitnesses))
    (scheme : leftBinder.scheme = rightBinder.scheme) (rawType : leftNode.rawType = rightNode.rawType) :
    leftSubstitution = rightSubstitution := factory_substitution_eq left right scheme rawType

section
variable {checked : SourceCoreCallableAncestryReadRecipes.Checked}
  {base : SourceCoreCallableAncestryReadRecipes.Base checked}
  {inputs : SourceCoreCallableAncestryReadRecipes.Inputs base}
  {caller lexical : SourceCoreCallableAncestryReadRecipes.State} {id target : Core.Word}
  (read : SourceCoreCallableAncestryReadRecipes.Read inputs caller id target)

example
    (scheme : read.binder.scheme =
      (read.entry.view.principal.binder.applySubstitution read.entry.view.parentActive).scheme)
    (rawType : read.node.rawType = read.entry.view.rawRead.rawType) :
    read.substitution ∈ CallableAncestrySourceActive.generators inputs.views :=
  read_generator_from_metadata read scheme rawType

example {callerIds lexicalIds : List RequirementId}
    (callerBounded : Bounded callerIds caller.metadata.source)
    (lexicalBounded : Bounded lexicalIds lexical.metadata.source) :
    Bounded (callerIds ++ lexicalIds) (read.after lexical).metadata.source :=
  after_bounded_union read lexical callerBounded lexicalBounded

example (reachable : CallableAncestrySourceActive.Reachable
    (CallableAncestrySourceActive.generators inputs.views) lexical.metadata.active) :
    (read.after lexical).metadata.active ∈
      CallableAncestrySourceActive.keySpace (CallableAncestrySourceActive.generators inputs.views) :=
  (after_finite read lexical reachable).2.2.2

example : (read.after lexical).metadata.active = read.substitution.compose lexical.metadata.active ∧
    (read.after lexical).nativeActive = read.entry.view.cumulative := (after_contexts read lexical).2

variable (applied : SourceCoreCallableAncestryReadRecipes.Applied read lexical)

example (context : SourceSemantics.Context) (binder : TypedBinder) (captured : Dynamic.Environment)
    (evidence : Dynamic.EvidenceEnvironment) :
    let result := (principal applied context binder captured).instantiate read.substitution evidence
    eraseRequirements (read.after lexical).metadata.source = eraseRequirements result.source ∧
      ExpressionForm.lambda result.parameters result.resultType result.body = read.template.node.form ∧
      result.captured = captured ∧ result.evidence = evidence :=
  instantiated_metadata applied context binder captured evidence

example (binding : Resolved.LocalId × SourceTypedRuntime.Location)
    (tail : SourceTypedRuntime.Environment) (evidence : SourceCompilationPlan.EvidenceEnvironment) :
    applied.sourceValue (binding :: binding :: tail) evidence =
      .instantiated read.substitution read.witnesses
        (.closure applied.parameters applied.resultType applied.body lexical.metadata.source lexical.metadata.owner
          (binding :: binding :: tail) evidence) := export_original applied _ _

example {left right : SourceTypedRuntime.Environment}
    {leftEvidence rightEvidence : SourceCompilationPlan.EvidenceEnvironment}
    (same : applied.sourceValue left leftEvidence = applied.sourceValue right rightEvidence) :
    left = right ∧ leftEvidence = rightEvidence := export_captures_injective applied same

end
end Tests.SourceCoreCallableAncestryReadRecipeProofs
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryReadRecipes
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadRecipes.Read.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadRecipes.Applied.mk

/-! Actual owned read factories distinguish read-caller metadata from the
principal source selected at creation. This test exercises preparation only;
native snapshot/capture provenance belongs to the paired runtime adapter. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryReadRecipes
open Solcore Solcore.Frontend SourceInference TypeSystem
open SourceCoreCallableAncestryReadRecipes
abbrev RecipeState := SourceCoreCallableAncestryReadRecipes.State
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def workspace : Workspace.RawWorkspace := {
  entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content := String.intercalate "\n" [
    "trait Mark<T> {}", "impl Mark<Word> {}",
    "type F = function(Word) returns (Word);",
    "function keep<T>(value: T) returns (T) where T: Mark { return value; }",
    "function nested(seed: Word) returns (F, F) { let outer = lam(value) { keep(value); let inner = lam(item) { keep(item); return seed; }; return (inner, inner); }; return outer(1); }"
  ]}] }

def run : IO Unit := do
  let program ← get "read recipes checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "nested") with
    | some signature => pure signature | none => throw (IO.userError "missing recipe root")
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"recipe plan failed: {reprStr other}")
  let automatic ← get "read recipes base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let inputs ← get "read recipes inventory" (SourceCoreCallableAncestryPreparation.prepareInputs automatic.prepared)
  let mut separated := 0
  for entry in inputs.views.entries do
    if entry.view.wrapsPrincipal then
      let target ← match inputs.callable.table.idAt?
          (.lambda entry.view.owner entry.view.principal.initializer entry.view.cumulative) with
        | some target => pure target | none => throw (IO.userError "missing recipe target")
      let caller : RecipeState := ⟨⟨entry.view.owner, entry.view.parentActive, entry.view.principal.source⟩, entry.view.parentActive⟩
      let read ← get "actual read recipe" (prepareRead inputs caller entry.id target)
      let _ ← get "same-context lexical application" (applyRead read caller)
      if !entry.view.parentActive.isEmpty then
        let specialized ← get "recipe principal root" (SourceCompilationPlan.exactSpecialization plan entry.view.owner)
        let lexical : RecipeState := ⟨⟨entry.view.owner, [], specialized.function.typedBody⟩, []⟩
        let applied ← get "different-context lexical application" (applyRead read lexical)
        let after := read.after lexical
        assertTrue (after.nativeActive == entry.view.cumulative && after.metadata.active == read.substitution)
          "native full context replaced the source substitution"
        assertTrue (after.metadata.active != after.nativeActive) "caller and principal contexts collapsed"
        assertTrue (after.metadata.source == SourceTypedRuntime.rewriteLocalRequirements read.witnesses
          (lexical.metadata.source.applySubstitution read.substitution)) "transport targeted the caller source"
        match applied.sourceValue [] [] with
        | .instantiated own witnesses (.closure _ _ _ source owner captured evidence) =>
          assertTrue (own == read.substitution && reprStr witnesses == reprStr read.witnesses &&
            source == lexical.metadata.source && owner == lexical.metadata.owner &&
            captured.isEmpty && evidence.isEmpty) "instantiated export lost the original principal"
        | _ => throw (IO.userError "recipe export collapsed the instantiated wrapper")
        assertTrue (match prepareRead inputs {caller with nativeActive := []} entry.id target with
          | .error _ => true | .ok _ => false)
          "read accepted the wrong native caller context"
        separated := separated + 1
  assertTrue (separated == 2) "missing nested occurrence-specific recipes"
  IO.println "paired read recipes: caller witnesses, lexical source, separate native/source contexts and original instantiated header GREEN"

end Tests.SourceCoreCallableAncestryReadRecipes
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryReadViews
#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadViews.Template.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadViews.Authenticated.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadViews.Produced.mk
#check_failure Solcore.Frontend.SourceCoreCallableAncestryReadViews.Stored.mk

/-! Actual compiler output supplies the transparent read wrapper and its saved
original callable. Result and stored-payload provenance are kept separately.
The tests check native code/descriptor authenticity and by-value captures: two
reads of one generalized local share its principal's snapshot cells, and each
call starts again from them. Dynamic requirement rewriting is deliberately left
to the prepared ancestry metadata layer, rather than inferred from canonical
read rows.
-/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryReadViews
open Solcore Solcore.Frontend SourceInference
open SourceCoreCallableAncestryReadViews
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
    "function mono(seed: Word) returns (F) { let f: F = lam(item: Word) -> Word { seed += item; return seed; }; return f; }",
    "function failure(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; let absent: Word; return absent; }",
    "function suspended(seed: Word) returns (Word) { let f = lam(item) { keep(item); seed += 1; return seed; }; let captured: F = f; while (true) {} return 0; }"
  ]}] }
private def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"read views fixture missing {name}")
private def artifact (program : CheckedProgram) : IO SourceCoreCompatibleFunctions.Automatic := do
  let keys ← ["views", "nested", "mono", "failure", "suspended"].mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (keys.map (fun key => ⟨key.declaration, []⟩)) 256 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"read views worklist failed: {reprStr other}")
  match SourceCoreCompatibleFunctions.prepare program plan 500 with
  | .ok automatic => pure automatic
  | .error error => throw (IO.userError s!"read views base failed: {reprStr error}")
private def initial : SourceHeap := [⟨.word, none⟩, ⟨.function .word .word, none⟩, ⟨.mapping .word .word, none⟩]

example {checked : Checked} {prepared : Prepared checked} (template : Template prepared) :
    template.carrier = SourceCoreCallableAncestry.viewRepack prepared.ancestry.layout.frame
      template.parameter template.result template.entry.id template.target template.referenceIndex := template.carrierExact

example {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    {cache : Cache templates} {world : Core.StoreTyping} {store : Core.Store} {value : Core.Value}
    (authenticated : Authenticated cache world store value) :
    Core.RuntimeValueHasType world authenticated.original
      (Core.CallableContract.functionType authenticated.wrapper.parameter authenticated.wrapper.result)
      prepared.layouts.definitions := authenticated.originalTyped

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
  | .pair (.pair identity (.closure parameter result body (original :: outer))) own =>
      .pair (.pair identity (.closure parameter result body (retag original descriptor :: outer))) own
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
        | cons original outer =>
          have changed := retag_typed descriptor authenticated.originalTyped
          rw [← authenticated.originalTyped.type_eq, original.type_eq] at changed
          exact .pair (.pair identity (.closure (.cons changed outer) body)) own

private def reuse {definitions : Core.DataEnvironment} {world : Core.StoreTyping} {store : Core.Store}
    (stored : Core.RuntimeStoreHasTypes world store definitions) (left right : Core.Value)
    (leftTyped : Core.RuntimeValueHasType world left (Core.CallableContract.functionType .word .word) definitions)
    (rightTyped : Core.RuntimeValueHasType world right (Core.CallableContract.functionType .word .word) definitions)
    (frame : SourceCoreCallableContextFrames.Layout) (snapshot allocated : Nat) : IO Unit := do
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
      assertTrue (final[0]? == some (SourceCoreCallableContextFrames.encode frame .empty)) "view/lambda frames were not restored"
      assertTrue (final.length == store.length + allocated)
        "view reentry changed its capture copies or parameter allocations (lambda and keep, with metadata cells)"
    | observation => throw (IO.userError s!"read wrapper reentry failed: {reprStr observation}")

private def pair {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) (nested : Bool) : IO Unit := do
  for spent in [0, 39, 100000] do
    let first ← match prepared.runSource owner [.word (w 3)] spent 500 with
      | .ok first => pure first | .error error => throw (IO.userError s!"read views source run failed: {reprStr error}")
    let _ ← match SourceCoreCallableAncestryLedger.scan first initial with
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
        assertTrue (leftAuth.canonicalOwnWitnesses.length == 1 && rightAuth.canonicalOwnWitnesses.length == 1)
          "qualified read lost its exact own witnesses"
        assertTrue (leftAuth.canonicalOwnWitnesses.map (·.actualRequirement) != rightAuth.canonicalOwnWitnesses.map (·.actualRequirement))
          "same-type reads collapsed occurrence-specific requirements"
        assertTrue ((!leftAuth.parentActive.isEmpty) == nested) "parent context was confused with own substitution"
        assertTrue (leftAuth.underlying.template.source.lambda.active == leftAuth.cumulative)
          "underlying native code was not the cumulative selected instance"
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
          -- lambda's parameter and `keep`'s parameter.
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame seed.location
            (if nested then 24 else 18)
      | observation => throw (IO.userError s!"read views pair did not succeed: {reprStr observation}")
    else throw (IO.userError "read views pair result projection changed")

private def stored {checked : Checked} {prepared : Prepared checked} {templates : Templates prepared}
    (cache : Cache templates) (owner : Key) (suspended : Bool) : IO Unit := do
  let completion ← match prepared.runSource owner [.word (w 3)] 10000 500 with
    | .ok completion => pure completion | .error error => throw (IO.userError s!"stored read source run failed: {reprStr error}")
  assertTrue (match completion.result.native.observation with
    | .failed _ _ => !suspended | .outOfFuel _ => suspended | _ => false) "stored read observation classification changed"
  let ledger ← match SourceCoreCallableAncestryLedger.scan completion initial with
    | .ok ledger => pure ledger | .error error => throw (IO.userError s!"stored read ledger failed: {reprStr error}")
  let ordinal ← match (List.finRange ledger.ledger.rows.length).find? (fun ordinal =>
      (ledger.ledger.rows[ordinal]).entry.key.binder.name == "captured") with
    | some ordinal => pure ordinal | none => throw (IO.userError "stored read allocation missing")
  let row := ledger.ledger.rows[ordinal]
  match payloadFound : row.payload with
  | none => throw (IO.userError "stored read payload missing")
  | some value =>
    if type : row.entry.key.payloadType = Core.CallableContract.functionType .word .word then
      have typed : Core.RuntimeValueHasType (SourceCoreCallableAncestryLedger.world completion) value
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
      match SourceCoreCallableAncestryTemplates.authenticate templates typed.1 value .word .word typed.2 with
      | .ok _ => pure () | .error error => throw (IO.userError s!"mono snapshot auth failed: {reprStr error}")
    | _ => throw (IO.userError "mono closure did not complete")
  else throw (IO.userError "mono result projection changed")

def run : IO Unit := do
  let program ← match checkProgram workspace with
    | .ok program => pure program | .error error => throw (IO.userError s!"read views source rejected: {reprStr error}")
  let automatic ← artifact program
  let prepared ← match SourceCoreCallableAncestryPrograms.prepare automatic.prepared 500 with
    | .ok prepared => pure prepared | .error error => throw (IO.userError s!"read views marked compiler failed: {reprStr error}")
  let templates ← match SourceCoreCallableAncestryTemplates.prepare prepared with
    | .ok templates => pure templates | .error error => throw (IO.userError s!"read views snapshot cache failed: {reprStr error}")
  let cache ← match prepare templates with
    | .ok cache => pure cache | .error error => throw (IO.userError s!"read views emitted wrapper scan failed: {reprStr error}")
  assertTrue (!cache.wrappers.isEmpty) "actual two-pass compiler emitted no read wrappers"
  for wrapper in cache.wrappers do
    match decode prepared wrapper.carrier with
    | .ok decoded => assertTrue (decoded.entry.id == wrapper.entry.id && decoded.body == wrapper.body) "full carrier decoder changed the view"
    | .error error => throw (IO.userError s!"retained wrapper failed complete rescan: {reprStr error}")
    match decode prepared (.pair (.pair .unit (.lambda wrapper.parameter (Core.LanguageResult.resultType wrapper.result) wrapper.body)) (.word wrapper.target)) with
    | .error .malformedWrapper => pure () | _ => throw (IO.userError "carrier with forged copied identity was accepted")
  pair cache (← key program "views") false
  pair cache (← key program "nested") true
  monomorphic cache (← key program "mono")
  stored cache (← key program "failure") false
  stored cache (← key program "suspended") true
  IO.println "exact emitted read wrappers, saved original auth, ordered snapshot captures, stored failure/suspension and resume GREEN"


end Tests.SourceCoreCallableAncestryReadViews
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestrySourceActive
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! These are source-metadata substitution bounds, not native code-context or
runtime ancestry ownership theorems. The actual owned witness factories supply
the closure/domain facts; no caller-provided matcher soundness is assumed. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestrySourceActive
open Solcore Solcore.Frontend SourceInference TypeSystem
open Solcore.SourceSemantics.CoreLowering.CallableAncestrySourceActive
open Solcore.SourceSemantics.CoreLowering.CallableAncestryProfiles.SourceComposition

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (active : Substitution)
    (reachable : Reachable (generators table) active) :
    RangesClosed active ∧ active.domain.Nodup ∧ active ⊆ alphabet (generators table) ∧
      active.length ≤ (domainAlphabet (generators table)).length ∧ active ∈ keySpace (generators table) :=
  ⟨reachable.closed (generators_valid table), reachable.domain_unique (generators_valid table),
    reachable.entries (generators_valid table), reachable.length_bound (generators_valid table),
    reachable.keySpace_member (generators_valid table)⟩

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (reached : List Substitution)
    (unique : reached.Nodup) (authentic : ∀ active ∈ reached, Reachable (generators table) active) :
    reached.length ≤ capacity (generators table) := owned_reached_count_bound table reached unique authentic

example {program : CheckedProgram} {plan : SourceCoreCallableViews.Plan}
    (table : SourceCoreCallableViews.Table program plan) (steps : List Substitution)
    (selected : ∀ own ∈ steps, own ∈ generators table) :
    (steps.foldl (fun active own => own.compose active) []).length ≤ (domainAlphabet (generators table)).length :=
  (Reachable.foldl .empty steps selected).length_bound (generators_valid table)

private def first : Substitution := [(⟨0⟩, .word)]
private def second : Substitution := [(⟨1⟩, .bool)]
private def conflicting : Substitution := [(⟨0⟩, .bool)]
private def choices : List Substitution := [first, second, conflicting]
private def combined : Substitution := second.compose first

example : combined = [(⟨0⟩, .word), (⟨1⟩, .bool)] := rfl
example : combined ≠ [] ∧ combined ∉ choices := by decide
example : combined ≠ first.compose second := by decide
example : conflicting.compose combined = combined := rfl
private theorem combined_reachable : Reachable choices combined := by
  have initial : Reachable choices first :=
    .step (own := first) .empty (by simp [choices])
  exact .step initial (show second ∈ choices by simp [choices])

example : Reachable choices combined := combined_reachable

example (count : Nat) : Reachable choices
    ((List.replicate count second).foldl (fun active own => own.compose active) combined) := by
  apply Reachable.foldl combined_reachable
  intro own member
  have same := List.eq_of_mem_replicate member
  simpa only [same] using (show second ∈ choices by simp [choices])

example : (domainAlphabet choices).length = 2 := by decide
example : capacity choices = 13 := by decide
example : (keySpace choices).length = 13 := keySpace_length choices

end Tests.SourceCoreCallableAncestrySourceActive
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryTemplates
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
    (frame : SourceCoreCallableContextFrames.Layout) (snapshots : List Nat) : IO Unit := do
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
      -- Each call starts again from its closure's creation-time `seed = 3`.
      assertTrue (first == w 4 && second == w 5) "authenticated snapshots did not restart each call from the creation-time capture"
      assertTrue (snapshots.all (fun location => final[location]? == some (.inRight .unit (.word (w 3)))))
        "reentry wrote a closure's snapshot cell"
      assertTrue (final[0]? == some (SourceCoreCallableContextFrames.encode frame .empty)) "reentry did not restore callable context"
      -- Each call makes three marked allocations of three cells: the copies of
      -- the two captured cells and the parameter.
      assertTrue (final.length == store.length + 18) "snapshot wrapper changed the capture copies, parameter allocation and ancestry metadata suffix"
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
        -- Closures capture by value: each closure's `seed` capture is its own
        -- snapshot cell, holding the creation-time value.
        let leftLocation := leftSeed.map (·.location)
        let rightLocation := rightSeed.map (·.location)
        let created := fun (location : Option Nat) =>
          (location.bind fun location => store[location]?) == some (.inRight .unit (.word (w 3)))
        assertTrue (leftLocation != rightLocation && created leftLocation && created rightLocation)
          "dynamic snapshots shared one lexical source location instead of each keeping its own copy"
        let ledger ← match SourceCoreAllocationLedger.scanTyped prepared.layouts [] (store.map Core.Value.type) store typed.1 with
          | .ok ledger => pure ledger | .error error => throw (IO.userError s!"nested lambda ledger failed: {reprStr error}")
        checkCaptures first ledger
        checkCaptures second ledger
        if spent == 250000 then
          let (some leftCapture, some rightCapture) := (leftLocation, rightLocation)
            | throw (IO.userError "snapshot seed disappeared")
          reuse typed.1 left right typed.2.1 typed.2.2 prepared.ancestry.layout.frame [leftCapture, rightCapture]
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
end

section
-- leanmerge: from Solcore.Test.SourceCoreCallableAncestryWorklist
#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Kernel-checked actual seed/traversal contracts. These cover the current
independent metadata transition graph; they do not assert that arbitrary native
call frames were emitted by that graph or that every artifact seeds/validates. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryWorklist
open Solcore Solcore.Frontend SourceInference
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryMetadata CallableAncestryCache CallableAncestryCardinality CallableAncestryWorklist

example {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {initial : SourceCoreCallableAncestryCache.Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    StatesValid owned initial.states ∧ CoversRoots owned initial.states :=
  seed_spec owned inputs seeded

example {checked : Checked} {base : Base checked} (owned : Owned base)
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base)
    {initial : SourceCoreCallableAncestryCache.Table}
    (seeded : SourceCoreCallableAncestryPreparation.seed inputs = .ok initial) :
    ∃ final, SourceCoreCallableAncestryPreparation.saturate inputs
      (SourceCoreCallableAncestryPreparation.capacity inputs initial) 0 initial = .ok final ∧
      StatesValid owned final.states := seeded_saturation_total owned inputs seeded

example {checked : Checked} {base : Base checked}
    (inputs : SourceCoreCallableAncestryPreparation.Inputs base) (initial : SourceCoreCallableAncestryCache.Table) :
    (keySpace inputs initial.states).length = SourceCoreCallableAncestryPreparation.capacity inputs initial :=
  universe_length inputs initial

example (alphabet : List RequirementId) (lengths : List Nat) :
    (FiniteProfiles.profiles alphabet lengths).length = alphabet.length ^ lengths.sum := profiles_length alphabet lengths

example : (FiniteProfiles.profiles [] [0, 0, 0]).length = 1 := by decide
example : (FiniteProfiles.profiles [⟨2⟩, ⟨4⟩] [1, 0, 2]).length = 8 := by decide

end Tests.SourceCoreCallableAncestryWorklist
end
