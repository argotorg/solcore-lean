import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.SourceCoreRootDiscovery

/-! A single source-facing compilation, value and session boundary. The
indexed recipe is prepared once from the cached compiler artifact. Opening
only mints ownership identities; execution uses the owned typed Core session.
An empty root set has an empty session and rejects every invocation.
The public types contain neither source closures nor native references. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreExecution

abbrev Seed := SourceCoreCompiler.Seed
abbrev Key := SourceCoreCompiler.Key
abbrev Options := SourceCoreCompiler.Options
abbrev Value := SourceCorePublicValues.Value
abbrev Handle := SourceCorePublicValues.Handle

structure RunOptions where
  inputValidationFuel : Nat := 1024
  executionFuel : Nat := 1024
  outputValidationFuel : Nat := 1024
  deriving Repr, DecidableEq

inductive CompileError where
  | compilation (error : SourceCoreCompiler.Error)
  | preparation (error : SourceCoreIndexedSession.Error)
  | discovery (error : SourceCoreRootDiscovery.StaticWordRootError)
  deriving Repr

structure Compiled where private mk ::
  private source : SourceCoreCompiler.Compiled
  private recipe : Option SourceCoreIndexedSession.Recipe
  private owned : match recipe with
    | none => source.artifact? = none
    | some recipe => source.artifact? = some recipe.compiled

def Compiled.program (compiled : Compiled) := compiled.source.program
def Compiled.plan (compiled : Compiled) := compiled.source.plan
def Compiled.roots (compiled : Compiled) := compiled.source.roots
def Compiled.keys (compiled : Compiled) := compiled.source.keys
def Compiled.rootCount (compiled : Compiled) := compiled.source.rootCount
def Compiled.root? (compiled : Compiled) (index : Nat) := compiled.source.root? index

def prepare (source : SourceCoreCompiler.Compiled) : Except CompileError Compiled := do
  match selected : source.artifact? with
  | none => pure ⟨source, none, selected⟩
  | some cached =>
      match prepared : SourceCoreIndexedSession.Recipe.prepare cached with
      | .error error => throw (.preparation error)
      | .ok recipe => pure ⟨source, some recipe, by
          simp only
          rw [SourceCoreIndexedSession.Recipe.prepare_compiled prepared]
          exact selected⟩

def compileChecked (program : CheckedProgram) (seeds : List Seed) (options : Options := {}) :
    Except CompileError Compiled := do
  let source ← (SourceCoreCompiler.compileChecked program seeds options).mapError CompileError.compilation
  prepare source

def compile (raw : Workspace.RawWorkspace) (seeds : List Seed) (options : Options := {}) :
    Except CompileError Compiled := do
  let source ← (SourceCoreCompiler.compile raw seeds options).mapError CompileError.compilation
  prepare source

theorem Compiled.plan_validated (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () :=
  compiled.source.plan_validated

private theorem prepare_program {source : SourceCoreCompiler.Compiled} {compiled : Compiled}
    (prepared : prepare source = .ok compiled) : compiled.program = source.program := by
  unfold prepare at prepared
  split at prepared
  · cases prepared; rfl
  · split at prepared
    · cases prepared
    · cases prepared; rfl

theorem compileChecked_program {program : CheckedProgram} {seeds : List Seed} {options : Options}
    {compiled : Compiled} (accepted : compileChecked program seeds options = .ok compiled) :
    compiled.program = program := by
  unfold compileChecked at accepted
  cases selected : SourceCoreCompiler.compileChecked program seeds options with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
      simp only [selected, Except.mapError, bind, Except.bind] at accepted
      exact (prepare_program accepted).trans (SourceCoreCompiler.compileChecked_program selected)

theorem compile_checked_source {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options}
    {compiled : Compiled} (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := by
  unfold compile at accepted
  cases selected : SourceCoreCompiler.compile raw seeds options with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok source =>
      simp only [selected, Except.mapError, bind, Except.bind] at accepted
      rw [prepare_program accepted]
      exact SourceCoreCompiler.compile_checked_source selected

def compileEntryChecked (program : CheckedProgram) (moduleId : Workspace.ModuleId) (options : Options := {}) :
    Except CompileError Compiled :=
  compileChecked program [SourceCoreCompiler.Seed.named moduleId "main"] options

def compileEntry (raw : Workspace.RawWorkspace) (options : Options := {}) : Except CompileError Compiled := do
  let entry ← (SourceCoreRootDiscovery.checkEntry raw options.checkingFuel).mapError
    (fun errors => CompileError.compilation (.checking errors))
  compileChecked entry.program [entry.seed] options

theorem compileEntry_checked_source {raw : Workspace.RawWorkspace} {options : Options}
    {compiled : Compiled} (accepted : compileEntry raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := by
  unfold compileEntry at accepted
  cases selected : SourceCoreRootDiscovery.checkEntry raw options.checkingFuel with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok entry =>
      simp only [selected, Except.mapError, bind, Except.bind] at accepted
      rw [compileChecked_program accepted]
      exact entry.source_checked

structure StaticWordRoot (compiled : Compiled) where private mk ::
  metadata : Abi.V1.MethodMetadata
  root : SourceCoreCompiler.Root compiled.plan

structure StaticWordProgram where private mk ::
  compiled : Compiled
  roots : List (StaticWordRoot compiled)

def StaticWordProgram.count (program : StaticWordProgram) : Nat := program.roots.length
def StaticWordProgram.rootForSelector? (program : StaticWordProgram) (selector : Abi.V1.Selector) :
    Option (StaticWordRoot program.compiled) := program.roots.find? (fun root => root.metadata.selector == selector)

def compileStaticWordChecked (program : CheckedProgram) (moduleId : Workspace.ModuleId)
    (options : Options := {}) : Except CompileError StaticWordProgram := do
  let requested ← (SourceCoreRootDiscovery.discoverStaticWordRoots program moduleId).mapError CompileError.discovery
  let compiled ← compileChecked program (requested.map (·.seed)) options
  if compiled.roots.map (·.seed) = requested.map (·.seed) then
    let roots := (requested.zip compiled.roots).map fun (request, root) =>
      (⟨request.metadata, root⟩ : StaticWordRoot compiled)
    pure ⟨compiled, roots⟩
  else throw (.compilation .rootOrderMismatch)

def compileStaticWord (raw : Workspace.RawWorkspace) (options : Options := {}) :
    Except CompileError StaticWordProgram := do
  let entry ← (SourceCoreRootDiscovery.checkEntry raw options.checkingFuel).mapError
    (fun errors => CompileError.compilation (.checking errors))
  compileStaticWordChecked entry.program entry.moduleId options

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

theorem compileStaticWordChecked_program {program : CheckedProgram} {moduleId : Workspace.ModuleId} {options : Options}
    {compiled : StaticWordProgram} (accepted : compileStaticWordChecked program moduleId options = .ok compiled) :
    compiled.compiled.program = program := by
  unfold compileStaticWordChecked at accepted
  obtain ⟨requested, _, accepted⟩ := bind_ok accepted
  obtain ⟨source, selected, accepted⟩ := bind_ok accepted
  split at accepted
  · cases accepted
    exact compileChecked_program selected
  · cases accepted

theorem compileStaticWord_checked_source {raw : Workspace.RawWorkspace} {options : Options}
    {compiled : StaticWordProgram} (accepted : compileStaticWord raw options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.compiled.program := by
  unfold compileStaticWord at accepted
  cases selected : SourceCoreRootDiscovery.checkEntry raw options.checkingFuel with
  | error error => simp [selected, Except.mapError, bind, Except.bind] at accepted
  | ok entry =>
      simp only [selected, Except.mapError, bind, Except.bind] at accepted
      rw [compileStaticWordChecked_program accepted]
      exact entry.source_checked

private inductive Opened (compiled : Compiled) where
  | empty (selected : compiled.recipe = none)
  | indexed (recipe : SourceCoreIndexedSession.Recipe) (selected : compiled.recipe = some recipe)
      (native : SourceCoreIndexedSession.Artifact)

structure Artifact where private mk ::
  private compilation : Compiled
  private opened : Opened compilation

def Compiled.open (compiled : Compiled) : IO Artifact := do
  match selected : compiled.recipe with
  | none => pure ⟨compiled, .empty selected⟩
  | some recipe => pure ⟨compiled, .indexed recipe selected (← recipe.open)⟩

def Artifact.keys (artifact : Artifact) := artifact.compilation.keys
def Artifact.rootCount (artifact : Artifact) := artifact.compilation.rootCount
def Artifact.root? (artifact : Artifact) (index : Nat) := artifact.compilation.root? index

private def SessionPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native => SourceCoreIndexedSession.Session native

structure Session (artifact : Artifact) where private mk ::
  private payload : SessionPayload artifact

private def BootstrapPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native => SourceCoreIndexedSession.Bootstrap native

structure Bootstrap (artifact : Artifact) where private mk ::
  private payload : BootstrapPayload artifact

def Artifact.bootstrap (artifact : Artifact) : IO (Bootstrap artifact) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure ⟨()⟩
  | indexed recipe selected native => exact do return ⟨← native.bootstrapFresh⟩

inductive BootResult (artifact : Artifact) where
  | ready (session : Session artifact)
  | outOfFuel (checkpoint : Bootstrap artifact)
  | error (error : SourceCoreIndexedSession.Error)

def Bootstrap.resume {artifact : Artifact} (bootstrap : Bootstrap artifact) (fuel : Nat) : BootResult artifact :=
  match artifact, bootstrap with
  | ⟨_, .empty _⟩, ⟨_⟩ => .ready ⟨()⟩
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ =>
      match native.resume fuel with
      | .ready session => .ready ⟨session⟩
      | .outOfFuel checkpoint => .outOfFuel ⟨checkpoint⟩
      | .error error => .error error

def Session.heapSize {artifact : Artifact} (session : Session artifact) : Nat :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => 0
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.heapSize
def Session.functionCount {artifact : Artifact} (session : Session artifact) : Nat :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => 0
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.functionCount

private def CheckpointPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Empty
  | .indexed _ _ native => SourceCoreIndexedSession.Checkpoint native

structure Checkpoint (artifact : Artifact) where private mk ::
  private payload : CheckpointPayload artifact

def Session.start {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (fuel : Nat := 1024) : Except SourceCoreIndexedSession.Error (Checkpoint artifact) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .missingEntry key⟩
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => do
      let checkpoint ← native.start key arguments fuel
      pure ⟨checkpoint⟩

/-- Start the owned callable with its source parameters packed into one value.
The native descriptor retains arity and the existing staging guards. -/
def Session.startHandlePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (fuel : Nat := 1024) : Except SourceCoreIndexedSession.Error (Checkpoint artifact) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .unknownHandle⟩
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => do
      let checkpoint ← native.startHandlePacked handle argument fuel
      pure ⟨checkpoint⟩

def Session.Authenticates {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) : Prop :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => False
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.Authenticates fuel expected value

structure Authentication {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) : Type where private mk ::
  typed : session.Authenticates fuel expected value

def Session.authenticate {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) :
    Except SourceCoreIndexedSession.Error (Authentication session fuel expected value) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact .error ⟨[], .unknownHandle⟩
  | indexed recipe selected native =>
      rcases session with ⟨session⟩
      exact do
        let checked ← session.authenticate fuel expected value
        pure ⟨checked.typed⟩

def Session.diagnostic {artifact : Artifact} (session : Session artifact) (key : Key)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .missingEntry key⟩
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.diagnostic key reason

def Checkpoint.diagnostic {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, checkpoint with
  | ⟨_, .empty _⟩, ⟨impossible⟩ => nomatch impossible
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.diagnostic reason

def Session.handleDiagnostic {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .unknownHandle⟩
  | ⟨_, .indexed _ _ _⟩, ⟨native⟩ => native.handleDiagnostic handle reason

structure Completion (artifact : Artifact) where private mk ::
  value : Value
  sourceType : TypeSystem.Ty
  session : Session artifact
  boundaryFuel : Nat
  authenticated : session.Authenticates boundaryFuel sourceType value

inductive Outcome (artifact : Artifact) where
  | succeeded (completion : Completion artifact)
  | failed (reason : Core.Word) (session : Session artifact)
  | outOfFuel (checkpoint : Checkpoint artifact)
  | exportError (error : SourceCoreIndexedSession.Error) (session : Session artifact)

def Session.named {artifact : Artifact} (session : Session artifact) (key : Key)
    (boundaryFuel : Nat := 1024) : IO (Except SourceCoreIndexedSession.Error (Completion artifact)) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure (.error ⟨[], .missingEntry key⟩)
  | indexed recipe selected native =>
      rcases session with ⟨session⟩
      exact do
        match ← session.named key boundaryFuel with
        | .error error => pure (.error error)
        | .ok completion => pure (.ok ⟨completion.value, completion.sourceType,
            ⟨completion.session⟩, completion.boundaryFuel, completion.authenticated⟩)

def Session.builtin {artifact : Artifact} (session : Session artifact) (function : BuiltinFunctionId)
    (boundaryFuel : Nat := 1024) : IO (Except SourceCoreIndexedSession.Error (Completion artifact)) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure (.error ⟨[], .missingBuiltin function⟩)
  | indexed recipe selected native =>
      rcases session with ⟨session⟩
      exact do
        match ← session.builtin function boundaryFuel with
        | .error error => pure (.error error)
        | .ok completion => pure (.ok ⟨completion.value, completion.sourceType,
            ⟨completion.session⟩, completion.boundaryFuel, completion.authenticated⟩)

def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected native =>
      rcases checkpoint with ⟨checkpoint⟩
      exact do
          match ← checkpoint.resume fuel boundaryFuel with
          | .succeeded completion => pure (.succeeded ⟨completion.value, completion.sourceType,
              ⟨completion.session⟩, completion.boundaryFuel, completion.authenticated⟩)
          | .failed reason session => pure (.failed reason ⟨session⟩)
          | .outOfFuel checkpoint => pure (.outOfFuel ⟨checkpoint⟩)
          | .exportError error session => pure (.exportError error ⟨session⟩)

def Session.run {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (options : RunOptions := {}) : IO (Except SourceCoreIndexedSession.Error (Outcome artifact)) := do
  match session.start key arguments options.inputValidationFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume options.executionFuel options.outputValidationFuel))

def Session.invokePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (options : RunOptions := {}) : IO (Except SourceCoreIndexedSession.Error (Outcome artifact)) := do
  match session.startHandlePacked handle argument options.inputValidationFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume options.executionFuel options.outputValidationFuel))

theorem Completion.typed {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  completion.authenticated

end Solcore.Frontend.SourceCoreExecution
