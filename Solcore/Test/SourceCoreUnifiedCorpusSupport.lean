import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.Frontend.ProgramChecking

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! Shared test helpers prepare canonical checked Core artifacts once. Expected
values and source heap effects are supplied by the checked source fixtures. -/
set_option autoImplicit false
namespace Tests.SourceCoreUnifiedCorpusSupport
open Solcore Solcore.Frontend SourceInference
abbrev Compiled := SourceCoreUnifiedCompilation.Compiled
abbrev Value := SourceTypedRuntime.Value
abbrev State := SourceTypedRuntime.RuntimeState
abbrev Key := SourceSpecialization.SpecializationKey

def word (n : Nat) : Core.Word := Core.Word.ofNatModulo n

def assertTrue (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")

def key (program : CheckedProgram) (name : String) : IO Key :=
  match program.signatures.functions.filter (·.name == name) with
  | [signature] => pure ⟨signature.id, []⟩
  | _ => throw (IO.userError s!"corpus function missing {name}")

def prepare (label content : String) (names : List String) : IO Compiled := do
  let program ← get s!"{label} checked source" (checkProgram {
    entry := "main.solc", externalLibraries := [], mainSources := [{path := "main.solc", content}] })
  let roots ← names.mapM (key program)
  let plan ← match SourceSpecializationWorklist.run program (roots.map fun root => ⟨root.declaration, []⟩) 512 with
    | .ok (.complete plan) => pure plan
    | other => throw (IO.userError s!"{label} canonical worklist incomplete: {reprStr other}")
  let compiled ← get s!"{label} cached Core artifact" (SourceCoreUnifiedCompilation.prepare program plan 1000)
  assertTrue (compiled.keys == roots) s!"{label} root order changed"
  pure compiled

def execute (compiled : Compiled) (name : String) (arguments : List Value := [])
    (fuel : Nat := 300000) (initial : State := {}) : IO (SourceCoreUnifiedCompilation.Result compiled) := do
  let owner ← key compiled.sourceProgram name
  get s!"{name} Core execution/export" (compiled.run owner arguments 500 fuel initial)

def completed (compiled : Compiled) (name : String) (arguments : List Value := [])
    (spent : Nat := 300000) : IO (Value × State) := do
  let first ← execute compiled name arguments spent
  let result ← get s!"{name} native checkpoint resume" (SourceCoreUnifiedCompilation.Result.resume first 300000)
  match result.observation with
  | .done value state =>
    assertTrue (state.isDeeplySafe 500 compiled.indexed.base.sourceProgram.signatures compiled.indexed.base.plan)
      s!"{name} final source heap is not deeply safe"
    pure (value, state)
  | other => throw (IO.userError s!"{name} expected done, received {reprStr other}")

def expect (compiled : Compiled) (name : String) (arguments : List Value) (expected : Value)
    (spent : Nat := 300000) : IO State := do
  let (value, state) ← completed compiled name arguments spent
  assertTrue (reprStr value == reprStr expected) s!"{name} result changed: {reprStr value}"
  pure state

def hasWord (state : State) (n : Nat) : Bool := state.heap.any fun cell => match cell.value with
  | some (.word actual) => actual == word n
  | _ => false

end Tests.SourceCoreUnifiedCorpusSupport
