import Solcore.Frontend.SourceProgramExecution
import Solcore.Frontend.SourceTypedRuntime

/-!
The restricted public source compiler boundary.

Compilation checks a raw workspace, resolves one explicit ground root,
discovers its finite specialization plan, and selects the first executable
backend in this fixed order: direct Core, the structural runtime call graph,
then the source-typed runtime.  The resulting artifact can be run repeatedly
without repeating checking or specialization.

Core stores/values and source-typed heaps/values are intentionally separate
invocation carriers.  This boundary does not guess a conversion between them.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

open TypeSystem

abbrev SeedTarget := SourceProgramExecution.SeedTarget
abbrev Seed := SourceProgramExecution.Seed

/-- Bounds used after whole-program checking has already succeeded. -/
structure CompileOptions where
  specializationBudget : Nat := 1024
  stagingFuel : Nat := 1024
  deriving Repr, DecidableEq

/-- Raw-workspace compilation adds an independent checking bound. -/
structure CheckingOptions extends CompileOptions where
  checkingFuel : Nat := 1024
  deriving Repr, DecidableEq

/-- Execution and recursively nested input validation have independent bounds. -/
structure RunOptions where
  inputValidationFuel : Nat := 1024
  executionFuel : Nat := 1024
  deriving Repr, DecidableEq

/-- One-shot public limits. -/
structure Limits extends CheckingOptions, RunOptions where
  deriving Repr, DecidableEq

namespace Seed

/-- Select one root by stable declaration identity. -/
def declaration (id : Resolved.DeclarationId)
    (arguments : List Ty := []) : Seed :=
  SourceProgramExecution.Seed.declaration id arguments

/-- Select one exact module-local root name. -/
def named (moduleId : Workspace.ModuleId) (name : String)
    (arguments : List Ty := []) : Seed :=
  SourceProgramExecution.Seed.named moduleId name arguments

end Seed

/-- The exact runtime selected for a compiled root. -/
inductive Backend where
  | core
  | callGraph
  | typedSource
  deriving Repr, BEq, DecidableEq

/-- All three rejection reasons when no runtime can execute a canonical plan. -/
structure BackendFailures where
  direct : SourceCoreDirectLinking.Error
  callGraph : SourceRuntimeLinking.Error
  typedSource : SourceTypedRuntime.RuntimeError
  deriving Repr

/-- Stage-preserving compilation failures. -/
inductive CompileError where
  | checking (errors : List ProgramCheckError)
  | seed (error : SourceProgramExecution.SeedError)
  | worklist (error : SourceSpecializationWorklist.Error)
  | specializationBudgetExhausted
      (next : SourceSpecialization.SpecializationKey) (pendingCount : Nat)
  | invalidPlan (error : SourceCoreDirectLinking.Error)
  | rootKeyCountMismatch (actual : Nat)
  | rootSpecializationCountMismatch
      (key : SourceSpecialization.SpecializationKey) (actual : Nat)
  | backendEntryCountMismatch (backend : Backend) (actual : Nat)
  | noBackend (failures : BackendFailures)
  deriving Repr

/-- Backend-specific payload retained behind the compiled artifact's private
constructor. -/
private inductive Executable where
  | core (entry : SourceCoreDirectLinking.LinkedEntry)
  | callGraph (entry : SourceRuntimeLinking.LinkedEntry)
  | typedSource
  deriving Repr

/-- A checked, canonically specialized, reusable single-root artifact.  The
private constructor prevents callers from pairing an arbitrary plan and root. -/
structure CompiledEntry where private mk ::
  private program : CheckedProgram
  private plan : SourceSpecializationWorklist.Plan
  private root : SourceSpecialization.SpecializedFunction
  private executable : Executable

namespace CompiledEntry

/-- Canonical specialization identity of the public root. -/
def key (compiled : CompiledEntry) : SourceSpecialization.SpecializationKey :=
  compiled.root.key

/-- Source-level runtime inputs, after root generic substitution. -/
def inputTypes (compiled : CompiledEntry) : List Ty :=
  compiled.root.function.typedBody.inputs.map (·.scheme.body)

/-- Source-level result type, after root generic substitution. -/
def resultType (compiled : CompiledEntry) : Ty :=
  compiled.root.function.inferredBodyType

/-- The selected exact runtime. -/
def backend (compiled : CompiledEntry) : Backend :=
  match compiled.executable with
  | .core _ => .core
  | .callGraph _ => .callGraph
  | .typedSource => .typedSource

/-- Number of reachable canonical specializations retained by this artifact. -/
def specializationCount (compiled : CompiledEntry) : Nat :=
  compiled.plan.specializations.length

end CompiledEntry

/-- Runtime-domain tag supplied by a caller. -/
inductive InvocationKind where
  | coreValues
  | typedValues
  deriving Repr, BEq, DecidableEq

/-- Exact initial arguments and state.  No implicit Core/source conversion is
performed. -/
inductive Invocation where
  | coreValues (arguments : List Core.Value) (store : Core.Store)
  | typedValues
      (arguments : List SourceTypedRuntime.Value)
      (state : SourceTypedRuntime.RuntimeState)
  deriving Repr

namespace Invocation

/-- Invoke a Core-domain backend with an empty store. -/
def coreFresh (arguments : List Core.Value) : Invocation :=
  .coreValues arguments []

/-- Invoke the source-typed backend with an empty heap. -/
def typedFresh (arguments : List SourceTypedRuntime.Value) : Invocation :=
  .typedValues arguments {}

def kind : Invocation → InvocationKind
  | .coreValues _ _ => .coreValues
  | .typedValues _ _ => .typedValues

end Invocation

/-- Failures before a selected runtime starts.  Runtime faults and exhaustion
remain in `ExecutionResult`. -/
inductive RunError where
  | invocationKindMismatch (backend : Backend) (actual : InvocationKind)
  | coreInputTypesMismatch (expected actual : List Core.Ty)
  deriving Repr, DecidableEq

/-- Lossless result carrier for all selected backends. -/
inductive ExecutionResult where
  | core (result : Core.StatefulRunResult)
  | callGraph (result : SourceRuntime.RunResult)
  | typedSource (result : SourceTypedRuntime.RunResult)
  deriving Repr

namespace CompiledEntry

/-- Execute a reusable artifact in its selected runtime domain. -/
def run (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions := {}) :
    Except RunError ExecutionResult :=
  match compiled.executable, invocation with
  | .core entry, .coreValues arguments store =>
      match entry.runExact? arguments options.executionFuel store with
      | some (.core result) => .ok (.core result)
      | some (.runtime result) => .ok (.callGraph result)
      | none => .error (.coreInputTypesMismatch
          entry.elaborated.inputs.values (arguments.map Core.Value.type))
  | .callGraph entry, .coreValues arguments store =>
      .ok (.callGraph (entry.program.run options.executionFuel entry.key
        arguments store))
  | .typedSource, .typedValues arguments state =>
      .ok (.typedSource (SourceTypedRuntime.runWithValidationFuel
        compiled.program.signatures compiled.plan compiled.root.key arguments
        options.inputValidationFuel options.executionFuel state))
  | _, invocation =>
      .error (.invocationKindMismatch compiled.backend invocation.kind)

/-- Core-domain convenience wrapper. -/
def runCore (compiled : CompiledEntry) (arguments : List Core.Value)
    (options : RunOptions := {}) (store : Core.Store := []) :
    Except RunError ExecutionResult :=
  compiled.run (.coreValues arguments store) options

/-- Source-typed-domain convenience wrapper. -/
def runTyped (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions := {})
    (state : SourceTypedRuntime.RuntimeState := {}) :
    Except RunError ExecutionResult :=
  compiled.run (.typedValues arguments state) options

end CompiledEntry

private def exactRoot
    (plan : SourceSpecializationWorklist.Plan) :
    Except CompileError SourceSpecialization.SpecializedFunction := do
  let key ← match plan.seedKeys with
    | [key] => pure key
    | keys => throw (.rootKeyCountMismatch keys.length)
  match plan.specializations.filter fun specialized =>
      decide (specialized.key = key) with
  | [root] => pure root
  | roots => throw (.rootSpecializationCountMismatch key roots.length)

private def selectBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat) :
    Except CompileError Executable :=
  let complete : SourceSpecializationWorklist.Outcome := .complete plan
  match SourceCoreDirectLinking.linkWithStagingFuel program complete
      stagingFuel with
  | .ok linked =>
      match linked.entries with
      | [entry] => .ok (.core entry)
      | entries => .error (.backendEntryCountMismatch .core entries.length)
  | .error directError =>
      match SourceRuntimeLinking.link program complete with
      | .ok linked =>
          match linked.entries with
          | [entry] => .ok (.callGraph entry)
          | entries => .error
              (.backendEntryCountMismatch .callGraph entries.length)
      | .error callGraphError =>
          match SourceTypedRuntime.validateExecutablePlan plan with
          | .ok _ => .ok .typedSource
          | .error typedSourceError => .error (.noBackend {
              direct := directError
              callGraph := callGraphError
              typedSource := typedSourceError
            })

/-- Compile one explicit root from an already checked program.  This is the
compile-once path for clients which prepare several entries from one catalog. -/
def compileChecked (program : CheckedProgram) (seed : Seed)
    (options : CompileOptions := {}) : Except CompileError CompiledEntry := do
  let request ← (SourceProgramExecution.resolveSeed program seed).mapError
    CompileError.seed
  let outcome ← (SourceSpecializationWorklist.run program [request]
    options.specializationBudget).mapError CompileError.worklist
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending =>
        throw (.specializationBudgetExhausted next pending.length)
  SourceCoreDirectLinking.validatePlan program plan
    |>.mapError CompileError.invalidPlan
  let root ← exactRoot plan
  let executable ← selectBackend program plan options.stagingFuel
  pure ⟨program, plan, root, executable⟩

/-- Check a raw workspace and compile one explicit root. -/
def compile (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions := {}) : Except CompileError CompiledEntry := do
  let program ← (checkProgram raw options.checkingFuel).mapError
    CompileError.checking
  compileChecked program seed options.toCompileOptions

/-- Combined failure carrier for the one-shot convenience boundary. -/
inductive Error where
  | compilation (error : CompileError)
  | execution (error : RunError)
  deriving Repr

/-- Check, compile, and execute one explicit root once. -/
def run (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits := {}) :
    Except Error ExecutionResult := do
  let compiled ← (compile raw seed limits.toCheckingOptions).mapError
    Error.compilation
  (compiled.run invocation limits.toRunOptions).mapError Error.execution

end Solcore.Frontend.SourceCompiler
