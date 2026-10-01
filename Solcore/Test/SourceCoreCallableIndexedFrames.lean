import Solcore.SourceSemantics.CoreLowering.CallableIndexedContextFrames
import Solcore.Frontend.ProgramChecking
import Solcore.Core.BoundedSafety

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreCallableIndexedDispatch.Dispatch.mk

/-! Kernel-checked carrier/dispatch laws and actual checked graph regression.
The small synthetic table tests native operations only; it supplies no source
ownership. The IO regression obtains its Dispatch from the sealed actual
metadata preparation and compares its cached recipes before native execution.
-/
set_option autoImplicit false
set_option maxRecDepth 8192
namespace Tests.SourceCoreCallableIndexedFrames
open Solcore Core Frontend SourceInference
open SourceCoreCallableIndexedFrames SourceCoreCallableIndexedDispatch
abbrev IndexedFrame := SourceCoreCallableIndexedFrames.Frame
private def w (n : Nat) : Word := Word.ofNatModulo n
private def layout : Layout := ⟨⟨0⟩⟩
private def definitions : DataEnvironment := [layout.definition]
private theorem registered : layout.Registered definitions := ⟨rfl⟩
private def dummyOwner : Resolved.DeclarationId :=
  ⟨⟨.main, ⟨[⟨"main", rfl⟩], by decide⟩⟩, 0⟩
private def dummyState : SourceCoreCallableIndexedDispatch.State :=
  ⟨⟨⟨dummyOwner, []⟩, [], ⟨dummyOwner, [], [], []⟩⟩, []⟩
private def table : Table := {
  states := List.replicate 4 dummyState
  named := [⟨w 7, 0⟩]
  lambdas := [⟨0, w 8⟩, ⟨3, w 8⟩]
  views := [⟨1, 0, w 3, w 8, 2⟩, ⟨2, 0, w 3, w 8, 3⟩] }

example : definitions.WellFormed := DataEnvironment.isWellFormed_sound rfl
example (frame : IndexedFrame) : decode layout (encode layout frame) = some frame := decode_encode layout frame
example (frame : IndexedFrame) : RuntimeValueHasType [] (encode layout frame) layout.type definitions :=
  encode_runtime_typed [] registered frame
example : decode layout (.constructed layout.state (.word (w 0))) = none := rfl
example : decode layout (.constructed ⟨⟨1⟩, 1⟩ (.integer 0)) = none := rfl
example : decode layout (.cellRef layout.type 0) = none := rfl
example : decode layout (encode layout (.state (-1))) = some (.state (-1)) := rfl
example : lookup? table (.state (-1)) = none := rfl
example : lookup? table (.state 4) = none := rfl
example : lookup? table (.view (w 3) (w 8) 1) = none := rfl
example : lookup? table .invalid = none := rfl
example : lookup? table .empty = some none := rfl
example : namedFrame table (w 7) = .state 0 := rfl
example : namedFrame table (w 99) = .invalid := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 8) 1) = .state 2 := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 8) 2) = .state 3 := rfl
example : selectedFrame table (w 8) (.state 1) (.view (w 3) (w 8) 0) = .invalid := rfl
example : selectedFrame table (w 8) (.state 0) (.view (w 3) (w 9) 1) = .state 0 := rfl
example : selectedFrame table (w 8) (.state 0) .empty = .state 0 := rfl
example : selectedFrame table (w 9) (.state 0) .empty = .invalid := rfl
example : selectedFrame table (w 8) (.state (-1)) .empty = .invalid := rfl
example : selectedFrame table (w 8) (.state 4) .empty = .invalid := rfl
example : selectedFrame {table with views := [⟨1, 0, w 3, w 8, 99⟩]}
    (w 8) (.state 0) (.view (w 3) (w 8) 1) = .invalid := rfl
example : readFrame (w 3) (w 8) (.state 1) = .view (w 3) (w 8) 1 := rfl
example : readFrame (w 3) (w 8) .empty = .invalid := rfl

example : HasType [layout.type, layout.type] (lambdaFrame table layout (w 8) (.var 0) (.var 1))
    layout.type definitions := lambdaFrame_hasType registered table (w 8) (.var rfl) (.var rfl)
example : HasType [layout.type] (readView layout (w 3) (w 8) (.var 0)) layout.type definitions :=
  readView_hasType registered (w 3) (w 8) (.var rfl)

private theorem selectedEvaluation : Evaluates [encode layout (.state 0), encode layout (.view (w 3) (w 8) 1)]
    [.word (w 55)] (lambdaFrame table layout (w 8) (.var 0) (.var 1))
    (encode layout (.state 2)) [.word (w 55)] :=
  SourceSemantics.CoreLowering.CallableIndexedContextFrames.lambdaFrame_evaluates
      (layout := layout) (lexicalFrame := .state 0) (currentFrame := .view (w 3) (w 8) 1)
      table (w 8) (.var rfl) (.var rfl) [.word (w 55)]

example : ∃ required, ∀ fuel, required ≤ fuel →
    runStateful fuel (.initial (lambdaFrame table layout (w 8) (.var 0) (.var 1))
      [encode layout (.state 0), encode layout (.view (w 3) (w 8) 1)] [.word (w 55)]) =
      .done (encode layout (.state 2)) [.word (w 55)] :=
  evaluation_runStateful_complete_with_sufficient_fuel selectedEvaluation

private def nativeProgram : Program := {
  dataDefinitions := definitions
  resultType := layout.type
  body := .letE (literal layout (.state 0))
    (.letE (literal layout (.view (w 3) (w 8) 1)) (lambdaFrame table layout (w 8) (.var 1) (.var 0))) }
private theorem nativeProgram_checked : nativeProgram.check = true :=
  Program.check_complete ⟨DataEnvironment.isWellFormed_sound rfl, registered.typeWellFormed,
    .letE (literal_hasType [] registered _) (.letE (literal_hasType _ registered _)
      (lambdaFrame_hasType registered table (w 8) (.var rfl) (.var rfl)))⟩
example (fuel : Nat) : (nativeProgram.runStateful fuel).HasType layout.type definitions :=
  Program.checked_runStateful_has_type nativeProgram_checked fuel
private theorem nativeProgram_evaluates : Evaluates [] [] nativeProgram.body (encode layout (.state 2)) [] :=
  .letE (SourceSemantics.CoreLowering.CallableIndexedContextFrames.literal_evaluates layout _ [] [])
    (.letE (SourceSemantics.CoreLowering.CallableIndexedContextFrames.literal_evaluates layout _ _ [])
      (SourceSemantics.CoreLowering.CallableIndexedContextFrames.lambdaFrame_evaluates
        (layout := layout) (lexicalFrame := .state 0) (currentFrame := .view (w 3) (w 8) 1)
        table (w 8) (.var rfl) (.var rfl) []))
example : ∃ required, ∀ fuel, required ≤ fuel →
    nativeProgram.runStateful fuel = .done (encode layout (.state 2)) [] :=
  evaluation_runStateful_complete_with_sufficient_fuel nativeProgram_evaluates
example : ∃ checkpoint, nativeProgram.runStateful 3 = .outOfFuel checkpoint := ⟨_, rfl⟩
example {checkpoint : Core.State} (exhausted : nativeProgram.runStateful 3 = .outOfFuel checkpoint) (additional : Nat) :
    (runStateful additional checkpoint).HasType layout.type definitions ∧
      runStateful additional checkpoint = nativeProgram.runStateful (3 + additional) :=
  well_typed_runStateful_resume_has_type (initial_state_has_type (Program.check_sound nativeProgram_checked)) exhausted additional

private def get {ε α : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
private def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
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
  let program ← get "indexed source checker" (checkProgram workspace)
  let signature ← match program.signatures.functions.find? (·.name == "sharedHistory") with
    | some signature => pure signature | none => throw (IO.userError "missing indexed root")
  let key : SourceSpecialization.SpecializationKey := ⟨signature.id, []⟩
  let plan ← match SourceSpecializationWorklist.run program [⟨signature.id, []⟩] 256 with
    | .ok (.complete plan) => pure plan | other => throw (IO.userError s!"indexed plan: {reprStr other}")
  let automatic ← get "indexed compiler base" (SourceCoreCompatibleFunctions.prepare program plan 500)
  let graph ← get "indexed metadata preparation" (SourceCoreCallableAncestryPairedPreparation.prepare automatic.prepared)
  let dispatch := prepare graph
  assertTrue (decide (dispatch.table = graph.table)) "dispatch lost graph ownership"
  let named ← match graph.inputs.callable.table.idAt? (.named key) with
    | some named => pure named | none => throw (IO.userError "missing indexed named descriptor")
  let lexical := namedFrame dispatch.table named
  assertTrue (lookup? dispatch.table lexical |>.isSome) "indexed named state was rejected"
  let shared ← match graph.inputs.views.entries.filter (·.view.binding.binder.name == "shared") with
    | [shared] => pure shared | _ => throw (IO.userError "wrong indexed shared views")
  let sharedTarget ← match graph.inputs.callable.table.idAt?
      (.lambda shared.view.owner shared.view.principal.initializer shared.view.cumulative) with
    | some target => pure target | none => throw (IO.userError "missing shared target")
  let rootIndex ← match lexical.index? with
    | some index => pure index | none => throw (IO.userError "named state did not carry an index")
  for outer in graph.inputs.views.entries.filter (·.view.binding.binder.name == "outer") do
    let target ← match graph.inputs.callable.table.idAt?
        (.lambda outer.view.owner outer.view.principal.initializer outer.view.cumulative) with
      | some target => pure target | none => throw (IO.userError "missing outer target")
    let caller := selectedFrame dispatch.table target lexical (readFrame outer.id target lexical)
    let current := readFrame shared.id sharedTarget caller
    let actual := selectedFrame dispatch.table sharedTarget lexical current
    let callerIndex ← match caller.index? with
      | some index => pure index | none => throw (IO.userError "outer transition rejected")
    let actualIndex ← match actual.index? with
      | some index => pure index | none => throw (IO.userError "shared paired transition rejected")
    let recipe ← match graph.recipeAt? callerIndex rootIndex shared.id sharedTarget with
      | some recipe => pure recipe | none => throw (IO.userError "indexed pair lost its cached recipe")
    assertTrue (graph.table.stateAt? actualIndex == some (recipe.read.after recipe.lexical))
      "indexed native state disagreed with the authenticated read/application recipe"
    let expr := lambdaFrame dispatch.table layout sharedTarget (.var 0) (.var 1)
    assertTrue (Core.infer? [layout.type, layout.type] expr definitions == some layout.type)
      "indexed graph dispatch failed Core checker"
    match runStateful 100000 (.initial expr [encode layout lexical, encode layout current] [.word (w 91)]) with
    | .done native store =>
      assertTrue (decode layout native == some actual && store == [.word (w 91)])
        "indexed paired dispatch changed state or store"
    | result => throw (IO.userError s!"indexed native dispatch: {reprStr result}")
    let stable := (List.range 2000).foldl (fun frame _ => selectedFrame dispatch.table sharedTarget frame .empty) actual
    assertTrue (stable == actual) "repeated ordinary calls changed the prepared metadata state"
  IO.println "indexed callable frames: constant-depth carrier, separate cached caller/lexical recipes, native dispatch, malformed indices, typed checkpoint/resume GREEN"

end Tests.SourceCoreCallableIndexedFrames
