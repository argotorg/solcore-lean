import Solcore.Frontend.SourceCoreCallableAncestryPairedPreparation
import Solcore.Frontend.ProgramChecking

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
