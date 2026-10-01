import Solcore.SourceSemantics.CoreLowering.CallableAncestryTransitions
import Solcore.Frontend.ProgramChecking

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
