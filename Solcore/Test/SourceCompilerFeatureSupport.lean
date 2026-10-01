import Solcore.Frontend.SourceCoreExecution

#check_failure Solcore.Frontend.SourceTypedRuntime.run
#check_failure Solcore.Frontend.SourceCoreExecution.Options.backendPreference
#check_failure Solcore.Frontend.SourceCoreExecution.Invocation
#check_failure Solcore.Frontend.SourceCoreExecution.Value.cellRef
#check_failure Solcore.Frontend.SourceCoreExecution.Value.closure

/-! Test support for the single source execution boundary. Public invocations
and internal heap/layout audits start from exactly the same cached compiler
artifact. Raw audits inspect Core execution and its source observation adapter;
they neither execute source syntax nor expose raw stores in the public API. -/
set_option autoImplicit false
namespace Tests.SourceCompilerFeatureSupport
open Solcore Solcore.Frontend
abbrev Value := SourceCoreExecution.Value
abbrev RawValue := SourceTypedRuntime.Value
abbrev RawState := SourceTypedRuntime.RuntimeState

def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
def get {α ε : Type} [Repr ε] (label : String) : Except ε α → IO α
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{label}: {reprStr error}")
def word (value : Nat) : Core.Word := Core.Word.ofNatModulo value
def scalar (value : Nat) : Value := .word (word value)
def options : SourceCoreCompiler.Options := {specializationBudget := 256, compilationFuel := 1000}
def executionOptions : SourceCoreExecution.RunOptions :=
  {inputValidationFuel := 1024, executionFuel := 300000, outputValidationFuel := 1024}

structure Entry where
  compiled : SourceCoreCompiler.Compiled
  execution : SourceCoreExecution.Compiled
  prepared : SourceCoreExecution.prepare compiled = .ok execution
  root : SourceCoreCompiler.Root compiled.plan
  cached : SourceCoreUnifiedCompilation.Compiled
  cachedSelected : compiled.artifact? = some cached

def Entry.key (entry : Entry) := entry.root.key
def Entry.inputTypes (entry : Entry) := entry.root.inputTypes
def Entry.resultType (entry : Entry) := entry.root.resultType

def fromCompiled (compiled : SourceCoreCompiler.Compiled) (index : Nat := 0) : IO Entry := do
  let execution ← match prepared : SourceCoreExecution.prepare compiled with
    | .ok execution => pure (⟨execution, prepared⟩ : {execution // SourceCoreExecution.prepare compiled = .ok execution})
    | .error error => throw (IO.userError s!"public recipe: {reprStr error}")
  let root ← match compiled.root? index with
    | some root => pure root | none => throw (IO.userError s!"root {index} missing")
  let cached ← match selected : compiled.artifact? with
    | some cached => pure (⟨cached, selected⟩ : {cached // compiled.artifact? = some cached})
    | none => throw (IO.userError "fixture has no cached code")
  pure ⟨compiled, execution.val, execution.property, root, cached.val, cached.property⟩

def compileNamed (program : CheckedProgram) (name : String) (types : List TypeSystem.Ty := [])
    (configuration : SourceCoreCompiler.Options := options) : IO Entry := do
  let signature ← match program.signatures.functions.filter (·.name == name) with
    | [signature] => pure signature | _ => throw (IO.userError s!"fixture function missing: {name}")
  fromCompiled (← get s!"compile {name}" (SourceCoreCompiler.compileChecked program
    [SourceCoreCompiler.Seed.declaration signature.id types] configuration))

def boot (artifact : SourceCoreExecution.Artifact) : IO (SourceCoreExecution.Session artifact) := do
  let bootstrap ← artifact.bootstrap
  match bootstrap.resume 300000 with
  | .ready session => pure session
  | .error error => throw (IO.userError s!"bootstrap: {reprStr error}")
  | .outOfFuel _ => throw (IO.userError "bootstrap exhausted")

structure Invocation where
  artifact : SourceCoreExecution.Artifact
  key : SourceCoreExecution.Key
  initial : SourceCoreExecution.Session artifact
  outcome : SourceCoreExecution.Outcome artifact

def Entry.invoke (entry : Entry) (arguments : List Value)
    (configuration : SourceCoreExecution.RunOptions := executionOptions) : IO Invocation := do
  let artifact ← entry.execution.open
  let session ← boot artifact
  let outcome ← get "public invocation" (← session.run entry.key arguments configuration)
  pure ⟨artifact, entry.key, session, outcome⟩

def Invocation.diagnostic (invocation : Invocation) (reason : Core.Word) :
    IO (Option SourceCoreFaultSites.Diagnostic) :=
  let session := match invocation.outcome with
    | .succeeded completion => completion.session
    | .failed _ session | .exportError _ session => session
    | .outOfFuel _ => invocation.initial
  get "public diagnostic" (session.diagnostic invocation.key reason)

def Invocation.value (invocation : Invocation) : IO Value := do
  match invocation.outcome with
  | .succeeded completion => pure completion.value
  | .failed reason _ => throw (IO.userError s!"unexpected language failure: {reprStr (← invocation.diagnostic reason)}")
  | .outOfFuel _ => throw (IO.userError "public execution exhausted")
  | .exportError error _ => throw (IO.userError s!"public export: {reprStr error}")

def Entry.run (entry : Entry) (arguments : List Value) : IO Value :=
  (entry.invoke arguments) >>= Invocation.value

def Entry.checkResume (entry : Entry) (arguments : List Value) (expected : Value) (spent : Nat := 10) : IO Unit := do
  let artifact ← entry.execution.open
  let session ← boot artifact
  let complete ← get "complete invocation" (← session.run entry.key arguments executionOptions)
  let done ← match complete with
    | .succeeded done => pure done | _ => throw (IO.userError "complete invocation did not succeed")
  require (done.value == expected) "complete invocation changed result"
  let pending ← get "suspended invocation" (← session.run entry.key arguments {executionOptions with executionFuel := spent})
  let checkpoint ← match pending with
    | .outOfFuel checkpoint => pure checkpoint | _ => throw (IO.userError "small execution budget did not suspend")
  match ← checkpoint.resume 300000 1024 with
  | .succeeded resumed =>
      require (resumed.value == expected && resumed.session.heapSize == done.session.heapSize)
        "resume changed the returned value or allocated native world"
  | _ => throw (IO.userError "public checkpoint did not resume")

/-- Only test data is converted; function handles stay within their owning
session and cannot be treated as raw source closure records. -/
def rawData : Nat → Value → Except String RawValue
  | 0, _ => .error "test data depth exhausted"
  | fuel + 1, value => do
      match value with
      | .unit => pure .unit | .bool value => pure (.bool value)
      | .word value => pure (.word value) | .integer value => pure (.integer value)
      | .product left right => pure (.product (← rawData fuel left) (← rawData fuel right))
      | .proxy inner => pure (.proxy inner)
      | .constructed metadata values => pure (.constructed metadata (← values.mapM (rawData fuel)))
      | .mapping key value entries => pure (.mapping key value (← entries.mapM fun (left, right) => do
          pure (← rawData fuel left, ← rawData fuel right)))
      | .function _ => .error "owned function handles require public invocation"

def Entry.audit (entry : Entry) (arguments : List Value) (fuel : Nat := 300000) :
    IO (SourceCoreUnifiedCompilation.Result entry.cached) := do
  let arguments ← get "raw test data" (arguments.mapM (rawData 128))
  get "cached Core source observation" (entry.cached.run entry.key arguments 1024 fuel)

def sourceState {cached : SourceCoreUnifiedCompilation.Compiled} (result : SourceCoreUnifiedCompilation.Result cached) : RawState :=
  match result.observation with
  | .done _ state | .fault _ state | .outOfFuel state => state

def nativeObservation {cached : SourceCoreUnifiedCompilation.Compiled}
    (result : SourceCoreUnifiedCompilation.Result cached) : IO Core.LanguageResult.Observation :=
  match result.execution with
  | some execution => pure execution.completion.result.native.observation
  | none => throw (IO.userError "audit was rejected before native execution")

def Entry.checkCells (entry : Entry) (arguments : List Value) (expected : List (TypeSystem.Ty × Option Value)) : IO Unit := do
  let result ← entry.audit arguments
  let cells ← expected.mapM fun (type, value) => do
    let value ← match value with | none => pure none | some value => some <$> get "expected raw cell" (rawData 128 value)
    pure (SourceTypedRuntime.Cell.mk type value)
  require (reprStr (sourceState result).heap == reprStr cells) "source cell type/value/allocation order changed"

def Entry.native (entry : Entry) : IO (SourceCoreGeneralEntry.NativeEntry entry.cached.indexed.layouts.definitions) :=
  match entry.cached.indexed.entries.find? (fun candidate => candidate.key == entry.key) with
  | some selected => pure selected.native | none => throw (IO.userError "cached native root missing")

/-- Locate actual loop cells by their generated type, then validate their
self-reference against their current index in the complete indexed store. -/
def checkLoopCells (store : Core.Store) (resultType : Core.Ty) (expectedCount : Nat) : IO Unit := do
  let cycles := store.zipIdx.filterMap fun (value, index) => match value with
    | .inRight .unit (.closure .unit type _ captured) =>
        if type == Core.LocalLoop.resultType resultType then some (index, captured) else none
    | _ => none
  require (cycles.length == expectedCount) "generated loop cell allocation count changed"
  for (index, captured) in cycles do
    require (captured[0]? == some (.cellRef (Core.OptionalCell.cellType (Core.LocalLoop.functionType resultType)) index))
      "generated loop closure lost its actual cyclic self-reference"

example (entry : Entry) : SourceCoreExecution.prepare entry.compiled = .ok entry.execution := entry.prepared
example (entry : Entry) : entry.compiled.artifact? = some entry.cached := entry.cachedSelected
example {artifact : SourceCoreExecution.Artifact} (done : SourceCoreExecution.Completion artifact) :
    done.session.Authenticates done.boundaryFuel done.sourceType done.value := done.typed
end Tests.SourceCompilerFeatureSupport
