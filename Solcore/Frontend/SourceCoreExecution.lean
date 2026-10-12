import Solcore.Frontend.SourceCoreCompiler
import Solcore.Frontend.SourceCoreIndexedSession
import Solcore.Frontend.SourceCoreRootDiscovery
import Solcore.Frontend.SourceCoreHeapInput

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
      (atRecipe : native.RecipeAt recipe)

structure Artifact where private mk ::
  private compilation : Compiled
  private opened : Opened compilation

/-- The public artifact retains its original compiled facade in proofs only. -/
def Artifact.CompiledAt (artifact : Artifact) (compiled : Compiled) : Prop :=
  Artifact.casesOn (motive := fun _ => Prop) artifact (fun actual _ => actual = compiled)

/-- The exact opened indexed artifact, including its original selected recipe. -/
def Artifact.IndexedAt (artifact : Artifact) (compiled : Compiled)
    (recipe : SourceCoreIndexedSession.Recipe) (native : SourceCoreIndexedSession.Artifact) : Prop :=
  Artifact.casesOn (motive := fun _ => Prop) artifact fun actual opened =>
    actual = compiled ∧ match opened with
    | .empty _ => False
    | .indexed actualRecipe _ actualNative _ => actualRecipe = recipe ∧ actualNative = native

/-- An opened recipe is the recipe already retained by the compiled facade. -/
theorem Artifact.IndexedAt.compiled_recipe {artifact : Artifact} {compiled : Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {native : SourceCoreIndexedSession.Artifact}
    (opened : artifact.IndexedAt compiled recipe native) :
    Compiled.casesOn (motive := fun _ => Prop) compiled (fun _ actual _ => actual = some recipe) := by
  rcases artifact with ⟨actual, openedState⟩
  cases openedState with
  | empty selected => exact False.elim opened.2
  | indexed actualRecipe selected actualNative atRecipe =>
      rcases opened with ⟨rfl, rfl, rfl⟩
      exact selected

/-- Opening uses the same original recipe, rather than a second recipe choice. -/
theorem Artifact.IndexedAt.recipe_at {artifact : Artifact} {compiled : Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {native : SourceCoreIndexedSession.Artifact}
    (opened : artifact.IndexedAt compiled recipe native) : native.RecipeAt recipe := by
  rcases artifact with ⟨actual, openedState⟩
  cases openedState with
  | empty selected => exact False.elim opened.2
  | indexed actualRecipe selected actualNative atRecipe =>
      rcases opened with ⟨rfl, rfl, rfl⟩
      exact atRecipe

/-- Mint the original indexed authority once and retain its erased proof. -/
def Compiled.openWithReceipt (compiled : Compiled) : IO {artifact : Artifact // artifact.CompiledAt compiled} := do
  match selected : compiled.recipe with
  | none => pure ⟨⟨compiled, .empty selected⟩, rfl⟩
  | some recipe =>
      let native ← recipe.openWithReceipt
      pure ⟨⟨compiled, .indexed recipe selected native.val native.property⟩, rfl⟩

def Compiled.open (compiled : Compiled) : IO Artifact := do
  pure (← compiled.openWithReceipt).val

def Artifact.keys (artifact : Artifact) := artifact.compilation.keys
def Artifact.rootCount (artifact : Artifact) := artifact.compilation.rootCount
def Artifact.root? (artifact : Artifact) (index : Nat) := artifact.compilation.root? index

private def SessionPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native _ => SourceCoreIndexedSession.Session native

structure Session (artifact : Artifact) where private mk ::
  private payload : SessionPayload artifact

/-- Equality with the actual indexed session is proof-only. -/
def Session.IndexedAt {artifact : Artifact} (session : Session artifact)
    {native : SourceCoreIndexedSession.Artifact} (indexed : SourceCoreIndexedSession.Session native) : Prop :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => False
  | ⟨_, .indexed _ _ actual _⟩, ⟨payload⟩ => actual = native ∧ HEq payload indexed

/-- Two observations of the same public session identify its exact payload. -/
theorem Session.IndexedAt.unique {artifact : Artifact} {session : Session artifact}
    {native : SourceCoreIndexedSession.Artifact} {left right : SourceCoreIndexedSession.Session native}
    (first : session.IndexedAt left) (second : session.IndexedAt right) : left = right := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact False.elim first
  | indexed recipe selected actual atRecipe =>
      rcases session with ⟨payload⟩
      rcases first with ⟨rfl, same⟩
      exact (eq_of_heq same).symm.trans (eq_of_heq second.2)

private def BootstrapPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native _ => SourceCoreIndexedSession.Bootstrap native

structure Bootstrap (artifact : Artifact) where private mk ::
  private payload : BootstrapPayload artifact

/-- The public checkpoint retains the original indexed fresh construction. -/
def Bootstrap.FreshAt {artifact : Artifact} (bootstrap : Bootstrap artifact) : Prop :=
  match artifact, bootstrap with
  | ⟨_, .empty _⟩, ⟨_⟩ => True
  | ⟨_, .indexed recipe _ _ _⟩, ⟨indexed⟩ => indexed.InitialAt recipe {}

/-- Equality with the actual indexed bootstrap, without a machine getter. -/
def Bootstrap.IndexedAt {artifact : Artifact} (bootstrap : Bootstrap artifact)
    {native : SourceCoreIndexedSession.Artifact} (indexed : SourceCoreIndexedSession.Bootstrap native) : Prop :=
  match artifact, bootstrap with
  | ⟨_, .empty _⟩, ⟨_⟩ => False
  | ⟨_, .indexed _ _ actual _⟩, ⟨payload⟩ => actual = native ∧ HEq payload indexed

/-- Fresh bootstrap mints one original session authority and retains its proof. -/
def Artifact.bootstrapWithReceipt (artifact : Artifact) : IO {bootstrap : Bootstrap artifact // bootstrap.FreshAt} := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure ⟨⟨()⟩, True.intro⟩
  | indexed recipe selected native atRecipe => exact do
      let fresh ← native.bootstrapFreshWithReceipt recipe atRecipe
      pure ⟨⟨fresh.val⟩, fresh.property⟩

def Artifact.bootstrap (artifact : Artifact) : IO (Bootstrap artifact) := do
  pure (← artifact.bootstrapWithReceipt).val

inductive BootResult (artifact : Artifact) where
  | ready (session : Session artifact)
  | outOfFuel (checkpoint : Bootstrap artifact)
  | error (error : SourceCoreIndexedSession.Error)

def Bootstrap.resume {artifact : Artifact} (bootstrap : Bootstrap artifact) (fuel : Nat) : BootResult artifact :=
  match artifact, bootstrap with
  | ⟨_, .empty _⟩, ⟨_⟩ => .ready ⟨()⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ =>
      match native.resume fuel with
      | .ready session => .ready ⟨session⟩
      | .outOfFuel checkpoint => .outOfFuel ⟨checkpoint⟩
      | .error error => .error error

/-- The public ready equation retains the original fresh indexed checkpoint
and the same indexed session. No native bootstrap is evaluated in this proof. -/
theorem Bootstrap.ready_indexed {artifact : Artifact} {compiled : Compiled}
    {recipe : SourceCoreIndexedSession.Recipe} {native : SourceCoreIndexedSession.Artifact}
    {bootstrap : Bootstrap artifact} {session : Session artifact} {fuel : Nat}
    (opened : artifact.IndexedAt compiled recipe native) (fresh : bootstrap.FreshAt)
    (ready : bootstrap.resume fuel = .ready session) :
    ∃ (indexed : SourceCoreIndexedSession.Bootstrap native)
      (indexedSession : SourceCoreIndexedSession.Session native),
      bootstrap.IndexedAt indexed ∧ indexed.InitialAt recipe {} ∧
      session.IndexedAt indexedSession ∧ indexed.resume fuel = .ready indexedSession := by
  rcases artifact with ⟨actual, openedState⟩
  cases openedState with
  | empty selected => exact False.elim opened.2
  | indexed actualRecipe selected actualNative atRecipe =>
      rcases opened with ⟨rfl, rfl, rfl⟩
      rcases bootstrap with ⟨indexed⟩
      cases completed : indexed.resume fuel with
      | ready indexedSession =>
          simp only [Bootstrap.resume, completed] at ready
          cases ready
          exact ⟨indexed, indexedSession, ⟨rfl, HEq.rfl⟩, fresh, ⟨rfl, HEq.rfl⟩, completed⟩
      | outOfFuel checkpoint => simp only [Bootstrap.resume, completed] at ready; cases ready
      | error error => simp only [Bootstrap.resume, completed] at ready; cases ready

def Session.heapSize {artifact : Artifact} (session : Session artifact) : Nat :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => 0
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.heapSize
def Session.functionCount {artifact : Artifact} (session : Session artifact) : Nat :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => 0
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.functionCount

private def CheckpointPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Empty
  | .indexed _ _ native _ => SourceCoreIndexedSession.Checkpoint native

structure Checkpoint (artifact : Artifact) where private mk ::
  private payload : CheckpointPayload artifact

/-- Equality with the original indexed checkpoint, without a state getter. -/
def Checkpoint.IndexedAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    {native : SourceCoreIndexedSession.Artifact} (indexed : SourceCoreIndexedSession.Checkpoint native) : Prop :=
  match artifact, checkpoint with
  | ⟨_, .empty _⟩, ⟨impossible⟩ => nomatch impossible
  | ⟨_, .indexed _ _ actual _⟩, ⟨payload⟩ => actual = native ∧ HEq payload indexed

def Checkpoint.heapSize {artifact : Artifact} (checkpoint : Checkpoint artifact) : Nat :=
  match artifact, checkpoint with
  | ⟨_, .empty _⟩, ⟨impossible⟩ => nomatch impossible
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.heapSize

def Session.start {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (fuel : Nat := 1024) : Except SourceCoreIndexedSession.Error (Checkpoint artifact) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .missingEntry key⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => do
      let checkpoint ← native.start key arguments fuel
      pure ⟨checkpoint⟩

/-- Public startup uses the same indexed artifact, session and checkpoint.
The successful original action supplies the checkpoint equation internally. -/
theorem Session.start_indexed {compiled : Compiled} {artifact : Artifact}
    {session : Session artifact} {key : Key} {arguments : List Value} {fuel : Nat}
    {checkpoint : Checkpoint artifact} (opened : artifact.CompiledAt compiled)
    (accepted : session.start key arguments fuel = .ok checkpoint) :
    ∃ (recipe : SourceCoreIndexedSession.Recipe) (native : SourceCoreIndexedSession.Artifact)
      (indexedSession : SourceCoreIndexedSession.Session native)
      (indexedCheckpoint : SourceCoreIndexedSession.Checkpoint native),
      artifact.IndexedAt compiled recipe native ∧ session.IndexedAt indexedSession ∧
      checkpoint.IndexedAt indexedCheckpoint ∧ indexedSession.start key arguments fuel = .ok indexedCheckpoint := by
  rcases artifact with ⟨actual, openedState⟩
  cases openedState with
  | empty selected => cases accepted
  | indexed recipe selected native atRecipe =>
      rcases session with ⟨indexedSession⟩
      change actual = compiled at opened
      subst compiled
      change (indexedSession.start key arguments fuel >>= fun next => .ok ⟨next⟩) = .ok checkpoint at accepted
      obtain ⟨indexedCheckpoint, issued, accepted⟩ := bind_ok accepted
      cases accepted
      exact ⟨recipe, native, indexedSession, indexedCheckpoint,
        ⟨rfl, rfl, rfl⟩, ⟨rfl, HEq.rfl⟩, ⟨rfl, HEq.rfl⟩, issued⟩

/-- Start the owned callable with its source parameters packed into one value.
The native descriptor retains arity and the existing staging guards. -/
def Session.startHandlePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (fuel : Nat := 1024) : Except SourceCoreIndexedSession.Error (Checkpoint artifact) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .unknownHandle⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => do
      let checkpoint ← native.startHandlePacked handle argument fuel
      pure ⟨checkpoint⟩

def Session.Authenticates {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) : Prop :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => False
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.Authenticates fuel expected value

structure Authentication {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) : Type where private mk ::
  typed : session.Authenticates fuel expected value

def Session.authenticate {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (expected : TypeSystem.Ty) (value : Value) :
    Except SourceCoreIndexedSession.Error (Authentication session fuel expected value) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact .error ⟨[], .unknownHandle⟩
  | indexed recipe selected native _atRecipe =>
      rcases session with ⟨session⟩
      exact do
        let checked ← session.authenticate fuel expected value
        pure ⟨checked.typed⟩

def Session.diagnostic {artifact : Artifact} (session : Session artifact) (key : Key)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .missingEntry key⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.diagnostic key reason

def Checkpoint.diagnostic {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, checkpoint with
  | ⟨_, .empty _⟩, ⟨impossible⟩ => nomatch impossible
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.diagnostic reason

def Session.handleDiagnostic {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (reason : Core.Word) : Except SourceCoreIndexedSession.Error (Option SourceCoreFaultSites.Diagnostic) :=
  match artifact, session with
  | ⟨_, .empty _⟩, ⟨_⟩ => .error ⟨[], .unknownHandle⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.handleDiagnostic handle reason

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
  | indexed recipe selected native _atRecipe =>
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
  | indexed recipe selected native _atRecipe =>
      rcases session with ⟨session⟩
      exact do
        match ← session.builtin function boundaryFuel with
        | .error error => pure (.error error)
        | .ok completion => pure (.ok ⟨completion.value, completion.sourceType,
            ⟨completion.session⟩, completion.boundaryFuel, completion.authenticated⟩)

private def wrapCompletion {compiled : Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    {selected : compiled.recipe = some recipe} {native : SourceCoreIndexedSession.Artifact}
    {atRecipe : native.RecipeAt recipe} (completion : SourceCoreIndexedSession.Completion native) :
    Completion ⟨compiled, .indexed recipe selected native atRecipe⟩ :=
  ⟨completion.value, completion.sourceType, ⟨completion.session⟩,
    completion.boundaryFuel, completion.authenticated⟩

private def wrapOutcome {compiled : Compiled} {recipe : SourceCoreIndexedSession.Recipe}
    {selected : compiled.recipe = some recipe} {native : SourceCoreIndexedSession.Artifact}
    {atRecipe : native.RecipeAt recipe} (outcome : SourceCoreIndexedSession.Outcome native) :
    Outcome ⟨compiled, .indexed recipe selected native atRecipe⟩ :=
  match outcome with
  | .succeeded completion => .succeeded (wrapCompletion completion)
  | .failed reason session => .failed reason ⟨session⟩
  | .outOfFuel checkpoint => .outOfFuel ⟨checkpoint⟩
  | .exportError error session => .exportError error ⟨session⟩

/-- The public result comes from the original indexed resume action. -/
def Checkpoint.ResumeAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (fuel boundaryFuel : Nat) (outcome : Outcome artifact) : Prop :=
  match artifact, checkpoint with
  | ⟨_, .empty _⟩, ⟨impossible⟩ => nomatch impossible
  | ⟨_, .indexed _ _ _ _⟩, ⟨indexed⟩ =>
      ∃ actual, indexed.ResumeAt fuel boundaryFuel actual ∧ wrapOutcome actual = outcome

/-- Retain the actual native execution/export receipt and execute once. -/
def Checkpoint.resumeWithReceipt {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO {outcome : Outcome artifact // checkpoint.ResumeAt fuel boundaryFuel outcome} := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected native atRecipe =>
      rcases checkpoint with ⟨indexed⟩
      exact do
        let resumed ← indexed.resumeWithReceipt fuel boundaryFuel
        pure ⟨wrapOutcome resumed.val, resumed.val, resumed.property, rfl⟩

def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := do
  pure (← checkpoint.resumeWithReceipt fuel boundaryFuel).val

/-- A public success retains the exact native completion and full export
receipt. It does not infer Source execution from authentication alone. -/
theorem Checkpoint.ResumeAt.indexed_succeeded {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {completion : Completion artifact}
    {native : SourceCoreIndexedSession.Artifact} {indexed : SourceCoreIndexedSession.Checkpoint native}
    (atCheckpoint : checkpoint.IndexedAt indexed)
    (receipt : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ (actual : SourceCoreIndexedSession.Completion native)
      (generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (store : Core.Store),
      indexed.NativeDone fuel value store ∧
      indexed.SucceededResultAt fuel boundaryFuel generation value store actual ∧
      completion.value = actual.value ∧ completion.sourceType = actual.sourceType ∧
      completion.boundaryFuel = actual.boundaryFuel ∧ completion.session.IndexedAt actual.session := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected actualNative atRecipe =>
      rcases checkpoint with ⟨actualCheckpoint⟩
      rcases atCheckpoint with ⟨rfl, same⟩
      cases eq_of_heq same
      obtain ⟨outcome, resumed, returned⟩ := receipt
      cases outcome with
      | succeeded actual =>
          cases returned
          obtain ⟨generation, value, store, completed, exported⟩ := resumed.succeeded
          exact ⟨actual, generation, value, store, completed, exported, rfl, rfl, rfl, rfl, HEq.rfl⟩
      | failed reason session => cases returned
      | outOfFuel checkpoint => cases returned
      | exportError error session => cases returned

/-- A public failure retains the exact native failed-result receipt; its
independent Source fault meaning is established by the semantic layer. -/
theorem Checkpoint.ResumeAt.indexed_failed {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {reason : Core.Word}
    {session : Session artifact} {native : SourceCoreIndexedSession.Artifact}
    {indexed : SourceCoreIndexedSession.Checkpoint native}
    (atCheckpoint : checkpoint.IndexedAt indexed)
    (receipt : checkpoint.ResumeAt fuel boundaryFuel (.failed reason session)) :
    ∃ (actualSession : SourceCoreIndexedSession.Session native)
      (_generation : SourceCorePublicValues.ExportGeneration) (value : Core.Value) (store : Core.Store),
      indexed.NativeDone fuel value store ∧ indexed.FailedResultAt fuel value store reason actualSession ∧
      session.IndexedAt actualSession := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected actualNative atRecipe =>
      rcases checkpoint with ⟨actualCheckpoint⟩
      rcases atCheckpoint with ⟨rfl, same⟩
      cases eq_of_heq same
      obtain ⟨outcome, resumed, returned⟩ := receipt
      cases outcome with
      | succeeded actual => cases returned
      | failed actualReason actualSession =>
          cases returned
          obtain ⟨generation, value, store, completed, failed⟩ := resumed.failed
          exact ⟨actualSession, generation, value, store, completed, failed, rfl, HEq.rfl⟩
      | outOfFuel checkpoint => cases returned
      | exportError error session => cases returned

/-- Both public run branches retain their original startup result; a completed
run also retains the one original indexed resume receipt. -/
def Session.RunAt {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (options : RunOptions)
    (result : Except SourceCoreIndexedSession.Error (Outcome artifact)) : Prop :=
  match result with
  | .error error => session.start key arguments options.inputValidationFuel = .error error
  | .ok outcome => ∃ checkpoint,
      session.start key arguments options.inputValidationFuel = .ok checkpoint ∧
      checkpoint.ResumeAt options.executionFuel options.outputValidationFuel outcome

def Session.runWithReceipt {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (options : RunOptions := {}) :
    IO {result : Except SourceCoreIndexedSession.Error (Outcome artifact) // session.RunAt key arguments options result} := do
  match started : session.start key arguments options.inputValidationFuel with
  | .error error => pure ⟨.error error, started⟩
  | .ok checkpoint =>
      let resumed ← checkpoint.resumeWithReceipt options.executionFuel options.outputValidationFuel
      pure ⟨.ok resumed.val, checkpoint, started, resumed.property⟩

def Session.run {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (options : RunOptions := {}) : IO (Except SourceCoreIndexedSession.Error (Outcome artifact)) := do
  pure (← session.runWithReceipt key arguments options).val

def Session.invokePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (options : RunOptions := {}) : IO (Except SourceCoreIndexedSession.Error (Outcome artifact)) := do
  match session.startHandlePacked handle argument options.inputValidationFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume options.executionFuel options.outputValidationFuel))


private def PrefixPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native _ => SourceCoreIndexedSession.PrefixSnapshot native

structure PrefixSnapshot (artifact : Artifact) where private mk ::
  private payload : PrefixPayload artifact

def PrefixSnapshot.cells {artifact : Artifact} (inert : PrefixSnapshot artifact) : List SourceCoreHeapSnapshot.Cell :=
  match artifact, inert with
  | ⟨_, .empty _⟩, ⟨_⟩ => []
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.cells

def PrefixSnapshot.heapSize {artifact : Artifact} (inert : PrefixSnapshot artifact) : Nat := inert.cells.length

def Artifact.bootstrapFromPrefix (artifact : Artifact) (inert : PrefixSnapshot artifact) : IO (Bootstrap artifact) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure ⟨()⟩
  | indexed recipe selected native _atRecipe =>
      rcases inert with ⟨inert⟩
      exact do return ⟨← native.bootstrapFromPrefix inert⟩

namespace Internal
/-- A provider can only return an already authenticated, artifact-indexed
prefix. This bridge allows the separate historical import module to use the
common sealed prefix without adding raw state to the public compiler API. -/
def importPrefix (artifact : Artifact)
    (provider : (native : SourceCoreIndexedSession.Artifact) → Option (SourceCoreIndexedSession.PrefixSnapshot native)) :
    Option (PrefixSnapshot artifact) :=
  match artifact with
  | ⟨_, .empty _⟩ => none
  | ⟨_, .indexed _ _ native _⟩ => (provider native).map fun inert => ⟨inert⟩
end Internal

/-- Build an initial inert heap using the common data carrier. Existing
callables are transferred by `Snapshot.exportPrefix`, with cached provenance. -/
def Artifact.preparePrefix (artifact : Artifact) (cells : List SourceCoreHeapInput.Cell)
    (validationFuel : Nat := 1024) (conversionFuel : Nat := 1024) :
    Except SourceCoreHeapInput.Error (PrefixSnapshot artifact) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected =>
      exact if cells.isEmpty then .ok ⟨()⟩ else .error ⟨[], .emptyArtifactHeap cells.length⟩
  | indexed recipe selected native _atRecipe => exact do
      let state ← SourceCoreHeapInput.Internal.convert cells conversionFuel
      match SourceCoreIndexedSession.Legacy.preparePrefix native state validationFuel with
      | some inert => pure ⟨inert⟩
      | none => throw ⟨[], .validationRejected validationFuel⟩

private def SnapshotPayload (artifact : Artifact) : Type :=
  match artifact.opened with
  | .empty _ => Unit
  | .indexed _ _ native _ => SourceCoreIndexedSession.Snapshot native

structure Snapshot (artifact : Artifact) where private mk ::
  private payload : SnapshotPayload artifact

def Snapshot.cells {artifact : Artifact} (snapshot : Snapshot artifact) : List SourceCoreHeapSnapshot.Cell :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => []
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.cells

def Snapshot.heapSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat := snapshot.cells.length

def Snapshot.nativeHeapSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => 0
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.nativeHeapSize

def Snapshot.pendingAllocation {artifact : Artifact} (snapshot : Snapshot artifact) : Bool :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => false
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => native.pendingAllocation

def Snapshot.cellAt? {artifact : Artifact} (snapshot : Snapshot artifact) (location : Nat) : Option SourceCoreHeapSnapshot.Cell :=
  snapshot.cells[location]?

/-- This is the originally imported inert prefix. Restoring all active cells
uses `restore`, retaining their native world and session ownership. -/
def Snapshot.prefix {artifact : Artifact} (snapshot : Snapshot artifact) : PrefixSnapshot artifact :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => ⟨()⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => ⟨native.prefix⟩

def Snapshot.prefixSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat := snapshot.prefix.heapSize

/-- Authenticate the entire recorded source heap as a fresh inert prefix.
Export reconstructs callables from allocation receipts and validates the heap;
it does not transfer the saved native continuation or handle ownership. -/
def Snapshot.exportPrefix {artifact : Artifact} (snapshot : Snapshot artifact)
    (validationFuel : Nat := 1024) (boundaryFuel : Nat := 1024) :
    Except SourceCoreIndexedSession.Error (PrefixSnapshot artifact) :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => .ok ⟨()⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ => (native.exportPrefix validationFuel boundaryFuel).map fun inert => ⟨inert⟩

theorem Snapshot.exportPrefix_length {artifact : Artifact} {snapshot : Snapshot artifact}
    {validationFuel boundaryFuel : Nat} {exported : PrefixSnapshot artifact}
    (accepted : snapshot.exportPrefix validationFuel boundaryFuel = .ok exported) :
    exported.heapSize = snapshot.heapSize := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected =>
      rcases snapshot with ⟨snapshot⟩
      simp only [Snapshot.exportPrefix] at accepted
      cases accepted
      rfl
  | indexed recipe selected native _atRecipe =>
      rcases snapshot with ⟨snapshot⟩
      unfold Snapshot.exportPrefix at accepted
      cases result : snapshot.exportPrefix validationFuel boundaryFuel with
      | error error => simp [result, Except.map] at accepted
      | ok inert =>
          simp only [result, Except.map] at accepted
          cases accepted
          exact snapshot.exportPrefix_length result

inductive RestoredSnapshot (artifact : Artifact) where
  | ready (session : Session artifact)
  | suspended (checkpoint : Checkpoint artifact)

def Snapshot.restore {artifact : Artifact} (snapshot : Snapshot artifact) : RestoredSnapshot artifact :=
  match artifact, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩ => .ready ⟨()⟩
  | ⟨_, .indexed _ _ _ _⟩, ⟨native⟩ =>
      match native.restore with
      | .ready session => .ready ⟨session⟩
      | .suspended checkpoint => .suspended ⟨checkpoint⟩

def Session.restoreSnapshot {artifact : Artifact} (session : Session artifact) (snapshot : Snapshot artifact) :
    Except SourceCoreIndexedSession.Error (RestoredSnapshot artifact) :=
  match artifact, session, snapshot with
  | ⟨_, .empty _⟩, ⟨_⟩, ⟨_⟩ => .ok (.ready ⟨()⟩)
  | ⟨_, .indexed _ _ _ _⟩, ⟨session⟩, ⟨snapshot⟩ => do
      match ← session.restoreSnapshot snapshot with
      | .ready session => pure (.ready ⟨session⟩)
      | .suspended checkpoint => pure (.suspended ⟨checkpoint⟩)

def Session.snapshot {artifact : Artifact} (session : Session artifact) (boundaryFuel : Nat := 1024) :
    IO (Except SourceCoreIndexedSession.Error (Snapshot artifact)) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => exact pure (.ok ⟨()⟩)
  | indexed recipe selected native _atRecipe =>
      rcases session with ⟨session⟩
      exact do return (← session.snapshot boundaryFuel).map fun snapshot => ⟨snapshot⟩

def Checkpoint.snapshot {artifact : Artifact} (checkpoint : Checkpoint artifact) (boundaryFuel : Nat := 1024) :
    IO (Except SourceCoreIndexedSession.Error (Snapshot artifact)) := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rcases checkpoint with ⟨impossible⟩; exact nomatch impossible
  | indexed recipe selected native _atRecipe =>
      rcases checkpoint with ⟨checkpoint⟩
      exact do return (← checkpoint.snapshot boundaryFuel).map fun snapshot => ⟨snapshot⟩

theorem Snapshot.restore_native_size {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => session.heapSize = snapshot.nativeHeapSize
    | .suspended checkpoint => checkpoint.heapSize = snapshot.nativeHeapSize := by
  rcases artifact with ⟨compiled, opened⟩
  cases opened with
  | empty selected => rfl
  | indexed recipe selected native _atRecipe =>
      rcases snapshot with ⟨snapshot⟩
      have same := snapshot.restore_native_size
      cases restored : snapshot.restore with
      | ready session => exact (by simpa only [Snapshot.restore, Snapshot.nativeHeapSize, Session.heapSize, Checkpoint.heapSize, restored] using same)
      | suspended checkpoint => exact (by simpa only [Snapshot.restore, Snapshot.nativeHeapSize, Session.heapSize, Checkpoint.heapSize, restored] using same)

theorem Completion.typed {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  completion.authenticated

end Solcore.Frontend.SourceCoreExecution
