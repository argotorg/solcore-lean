import Solcore.Frontend.SourceProgramExecution
import Solcore.Frontend.SourceCompilationPlan
import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
import Solcore.Core.Safety
import Solcore.Frontend.SourceCoreDirectLinking
import Solcore.Frontend.SourceCoreBasicEntry
import Solcore.Frontend.SourceCoreRecursiveEntry
import Solcore.Frontend.SourceCoreFunctionEntry
import Solcore.Frontend.SourceCoreSession
import Solcore.Frontend.ProgramInterfaces
import Solcore.Abi.StaticWord

/-!
The restricted public source compiler boundary.

Single-root compilation resolves a ground root and discovers its finite
specialization plan.  The whole-program facade can also discover conventional
`main` and exported Static Word ABI roots, or compile an ordered explicit root
set after checking the workspace once.  Automatic selection prefers direct
Core, then ordinary optional-cell Core, then catalog-indexed Core, and otherwise
uses cached source-compatible Core with the historical source-value interface.
Clients may request a specific invocation profile. Artifacts can be run
repeatedly without repeating checking or specialization. Every selected
execution path uses Core; `typedSource` remains a compatibility tag.

Core stores/values and source heaps/values still have distinct public carriers;
their final API unification is a later step. Core routes validate complete input
trees and allocate source parameter cells in order. Source-value observations
retain source metadata and diagnostics, with a sealed typed Core checkpoint
available for resumption.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

open TypeSystem

abbrev SeedTarget := SourceProgramExecution.SeedTarget
abbrev Seed := SourceProgramExecution.Seed

/-- Historical invocation-interface tags retained during the runtime migration. -/
inductive Backend where
  | core
  | typedSource
  deriving Repr, BEq, DecidableEq

/-- Backend policy for one compilation. Automatic selection deliberately keeps
the direct Core path first, tries ordinary Core lowering next, then chooses the
catalog Core before the source-compatible Core interface. -/
inductive BackendPreference where
  | automatic
  | core
  | typedSource
  deriving Repr, BEq, DecidableEq

namespace BackendPreference

/-- The exact invocation profile requested by a non-automatic preference. -/
def requested? : BackendPreference → Option Backend
  | .automatic => none
  | .core => some .core
  | .typedSource => some .typedSource

end BackendPreference

/-- Bounds used after whole-program checking has already succeeded. -/
structure CompileOptions where
  specializationBudget : Nat := 1024
  stagingFuel : Nat := 1024
  backendPreference : BackendPreference := .automatic
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

/-- One backend's exact rejection reason.  Both automatic exhaustion and an
explicit preference use this common carrier, so clients need only one
diagnostic traversal. -/
inductive BackendRejection where
  | core (error : SourceCoreDirectLinking.Error)
  | coreCatalog (error : SourceCorePlanCatalog.Error)
  | typedSource (error : SourceTypedRuntime.RuntimeError)
  | typedSourceCore (error : SourceCoreUnifiedCompilation.Error)
  deriving Repr

namespace BackendRejection

def backend : BackendRejection → Backend
  | .core _ | .coreCatalog _ => .core
  | .typedSource _ | .typedSourceCore _ => .typedSource

end BackendRejection

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
  | publicCoreResultProjection (error : SourceCoreElaboration.Error)
  | publicGeneralResultProjection (error : SourceCoreDataCatalog.Error)
  | publicCoreResultMismatch (expected actual : Core.Ty)
  | noBackend (rejections : List BackendRejection)
  | backendRejected (rejection : BackendRejection)
  deriving Repr

/-- Cached catalog code and its selected entry share their actual definitions. -/
private structure GeneralExecutable where
  recipe : SourceCoreSession.Recipe
  entry : SourceCoreGeneralEntry.Entry recipe.checked
  deriving Repr

private instance : Repr SourceCoreUnifiedCompilation.Compiled where
  reprPrec cached _ := "cached source-compatible Core artifact " ++ repr cached.keys

/-- Backend payload retained behind the compiled artifact's private constructor. -/
private inductive Executable where
  | core (entry : SourceCoreDirectLinking.LinkedEntry)
  | coreRuntime (entry : SourceCoreBasicEntry.Entry)
  | coreGeneral (general : GeneralExecutable)
  | typedSource (cached : SourceCoreUnifiedCompilation.Compiled)
  deriving Repr

private def Executable.backend : Executable → Backend
  | .core _ => .core
  | .coreRuntime _ | .coreGeneral _ => .core
  | .typedSource _ => .typedSource

private def Executable.OwnedBy (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) : Executable → Prop
  | .typedSource cached => cached.sourceProgram = program ∧ cached.validationPlan = plan
  | _ => True

private def Executable.HasPublicResultProjection
    (root : SourceSpecialization.SpecializedFunction) : Executable → Prop
  | .core entry =>
      SourceCoreElaboration.lowerType
        (.declaration root.declaration) root.function.inferredBodyType =
          .ok entry.elaborated.returnType
  | .coreRuntime entry =>
      SourceCoreScalar.lowerType
        (.declaration root.declaration) root.function.inferredBodyType =
          .ok entry.resultType
  | .coreGeneral general =>
      general.recipe.checked.catalog.project root.function.inferredBodyType = .ok general.entry.resultType
  | .typedSource _ => True

/-- A checked, canonically specialized, reusable single-root artifact.  The
private constructor prevents callers from pairing an arbitrary plan and root. -/
structure CompiledEntry where private mk ::
  private program : CheckedProgram
  private plan : SourceSpecializationWorklist.Plan
  private root : SourceSpecialization.SpecializedFunction
  private executable : Executable
  private owned : executable.OwnedBy program plan

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

/-- The selected historical invocation profile. Execution uses Core. -/
def backend (compiled : CompiledEntry) : Backend :=
  match compiled.executable with
  | .core _ => .core
  | .coreRuntime _ | .coreGeneral _ => .core
  | .typedSource _ => .typedSource

/-- Recover the classification, source occurrence and span assigned by the
ordinary Core compiler. The returned word remains separate from machine faults. -/
def coreFailureDiagnostic? (compiled : CompiledEntry) (reason : Core.Word) :
    Option SourceCoreFaultSites.Diagnostic :=
  match compiled.executable with
  | .coreRuntime entry => entry.failureDiagnostic? reason
  | .coreGeneral general => general.entry.failureDiagnostic? reason
  | .core _ | .typedSource _ => none

/-- Number of reachable canonical specializations retained by this artifact. -/
def specializationCount (compiled : CompiledEntry) : Nat :=
  compiled.plan.specializations.length

/-- The retained root is the unique specialization with the canonical seed
key.  Successful compilation establishes this provenance fact; it is kept
explicit because the sealed artifact's constructor retains source/plan ownership separately. -/
def HasCanonicalRoot (compiled : CompiledEntry) : Prop :=
  compiled.plan.specializations.filter (fun candidate =>
    decide (candidate.key = compiled.root.key)) = [compiled.root]

/-- The retained source program really came from a successful raw-workspace
check. This provenance is not automatic for `compileChecked`, whose caller can
provide an arbitrary `CheckedProgram` record. -/
def HasCheckedSourceWitness (compiled : CompiledEntry) : Prop :=
  ∃ raw fuel, checkProgram raw fuel = .ok compiled.program

/-- The sealed plan passed the source-compatible executable-plan preflight.
Successful compilation guarantees this for the `typedSource` invocation profile. -/
def HasValidatedTypedPlan (compiled : CompiledEntry) : Prop :=
  SourceCompilationPlan.validateExecutablePlanEvidence compiled.program
    compiled.plan = .ok ()

/-- A source value has this artifact's public source result type
in the complete executable plan deterministically prepared from the sealed
specialization plan.  This includes first-class globals discovered through
selected methods.  It does not validate a closure body or heap. -/
def TypedValueHasResultType (compiled : CompiledEntry)
    (value : SourceTypedRuntime.Value) : Prop :=
  value.HasPreparedType compiled.program compiled.plan compiled.resultType

/-- Deep typed-source result at the exact prepared plan used for execution.
This includes final-heap typing, closure/global code provenance, and
authenticated runtime evidence rather than only the returned value's outer
runtime tag. -/
def TypedDeepResult (compiled : CompiledEntry)
    (value : SourceTypedRuntime.Value)
    (finalState : SourceTypedRuntime.RuntimeState) : Prop :=
  match compiled.executable with
  | .typedSource _ =>
      SourceTypedRuntime.PreparedDeepResult compiled.program compiled.plan
        compiled.root.function.inferredBodyType value finalState
  | .core _ | .coreRuntime _ | .coreGeneral _ => False

/-- Full typed-source boundary certificate for one normal execution.  It keeps
the deeply safe initial heap and arguments, the deeply safe final heap and
result, and preservation of every pre-existing location's declared type. -/
def TypedDeepExecution (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState)
    (value : SourceTypedRuntime.Value)
    (finalState : SourceTypedRuntime.RuntimeState) : Prop :=
  match compiled.executable with
  | .typedSource _ =>
      SourceTypedRuntime.PreparedDeepExecution compiled.program compiled.plan
        (compiled.root.function.typedBody.inputs.map (·.scheme.body))
        compiled.root.function.inferredBodyType arguments initial value finalState
  | .core _ | .coreRuntime _ | .coreGeneral _ => False

/-- The selected backend's result projection agrees with the public source
result type.  Compilation checks this separately from runtime result typing:
the latter alone would only refer to a backend-native declaration. -/
def HasPublicResultProjection (compiled : CompiledEntry) : Prop :=
  compiled.executable.HasPublicResultProjection compiled.root

/-- Deep direct-Core result/store typing expressed against the compiler's
public source result type rather than only the linker's private return type. -/
def CoreResultHasPublicType (compiled : CompiledEntry)
    (value : Core.Value) (finalStore : Core.Store) : Prop :=
  match compiled.executable with
  | .core _ =>
      ∃ publicType,
        SourceCoreElaboration.lowerType
          (.declaration compiled.root.declaration) compiled.resultType =
            .ok publicType ∧
        ∃ finalWorld,
          Core.RuntimeStoreHasTypes finalWorld finalStore ∧
            Core.RuntimeValueHasType finalWorld value publicType
  | .coreRuntime _ =>
      ∃ publicType,
        SourceCoreScalar.lowerType
          (.declaration compiled.root.declaration) compiled.resultType =
            .ok publicType ∧
        ∃ finalWorld,
          Core.RuntimeStoreHasTypes finalWorld finalStore ∧
            Core.RuntimeValueHasType finalWorld value publicType
  | .coreGeneral general =>
      ∃ publicType, general.recipe.checked.catalog.project compiled.resultType = .ok publicType ∧
        ∃ finalWorld,
          Core.RuntimeStoreHasTypes finalWorld finalStore (SourceCoreGeneralEntry.definitions general.recipe.checked) ∧
          Core.RuntimeValueHasType finalWorld value publicType (SourceCoreGeneralEntry.definitions general.recipe.checked)
  | .typedSource _ => False

/-- The public projection covers successful values, failed stores and typed
exhaustion checkpoints from the ordinary Core result envelope. -/
def CoreLanguageResultHasPublicType (compiled : CompiledEntry)
    (observation : Core.LanguageResult.Observation) : Prop :=
  match compiled.executable with
  | .coreGeneral general =>
      ∃ publicType, general.recipe.checked.catalog.project compiled.resultType = .ok publicType ∧
        observation.HasType publicType (SourceCoreGeneralEntry.definitions general.recipe.checked)
  | _ =>
      ∃ publicType,
        SourceCoreScalar.lowerType (.declaration compiled.root.declaration)
          compiled.resultType = .ok publicType ∧ observation.HasType publicType

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

/-- Invoke the source-value compatibility profile with an empty heap. -/
def typedFresh (arguments : List SourceTypedRuntime.Value) : Invocation :=
  .typedValues arguments {}

def kind : Invocation → InvocationKind
  | .coreValues _ _ => .coreValues
  | .typedValues _ _ => .typedValues

end Invocation

/-- Invocation rejection and source-observation adapter failures. Language
faults and exhaustion remain in `ExecutionResult`. -/
inductive RunError where
  | invocationKindMismatch (backend : Backend) (actual : InvocationKind)
  | coreInputTypesMismatch (expected actual : List Core.Ty)
  | coreRuntimeInput (error : SourceCoreBasicEntry.Error)
  | coreGeneralInput (error : SourceCoreGeneralEntry.RunError)
  | typedSourceAdapter (error : SourceCoreUnifiedRuntime.Error)
  deriving Repr

/-- Lossless result carrier for all selected backends. -/
inductive ExecutionResult where
  | core (result : Core.StatefulRunResult)
  | coreLanguageResult (observation : Core.LanguageResult.Observation)
  | typedSource (result : SourceTypedRuntime.RunResult)
  deriving Repr

namespace CompiledEntry

/-- The extra semantic premise needed to lift executable runtime checks to a
preservation theorem. Direct Core needs genuinely typed values and store,
while the source-value interface needs the retained canonical-root certificate. -/
def PreservationPrecondition (compiled : CompiledEntry) : Invocation → Prop
  | .coreValues arguments store =>
      match compiled.executable with
      | .core entry =>
          ∃ world,
            Core.RuntimeEnvironmentHasTypes world arguments
                entry.elaborated.inputs.values ∧
              Core.StoreHasTypes world store
      | .coreRuntime _ | .coreGeneral _ => True
      | .typedSource _ => False
  | .typedValues _ _ =>
      match compiled.executable with
      | .typedSource _ => compiled.HasCanonicalRoot
      | .core _ | .coreRuntime _ | .coreGeneral _ => False

/-- Backend-native typing for every successful result carrier. Direct Core and
typed source include their final store/heap and deeply typed values;
typed-source certificates additionally retain closure code and authenticated
evidence. Fault and exhaustion cases are intentionally outside this predicate. -/
def SuccessfulResultHasNativeType (compiled : CompiledEntry) : ExecutionResult → Prop
  | .core (.done value finalStore) =>
      match compiled.executable with
      | .core entry =>
          ∃ finalWorld,
            Core.RuntimeStoreHasTypes finalWorld finalStore ∧
              Core.RuntimeValueHasType finalWorld value
                entry.elaborated.returnType
      | .coreRuntime _ | .coreGeneral _ => False
      | .typedSource _ => False
  | .core (.outOfFuel _) | .core (.fault _ _) => True
  | .typedSource (.done value finalState) =>
      match compiled.executable with
      | .typedSource _ =>
          SourceTypedRuntime.PreparedDeepResult compiled.program compiled.plan
            compiled.root.function.inferredBodyType value finalState
      | .core _ | .coreRuntime _ | .coreGeneral _ => False
  | .typedSource (.outOfFuel _) | .typedSource (.fault _ _) => True
  | .coreLanguageResult observation =>
      match compiled.executable with
      | .coreRuntime entry => observation.HasType entry.resultType
      | .coreGeneral general => observation.HasType general.entry.resultType
          (SourceCoreGeneralEntry.definitions general.recipe.checked)
      | .core _ | .typedSource _ => False

/-- A source observation and its sealed typed Core continuation retain the
exact original request across repeated resumptions. -/
structure TypedCheckpoint (compiled : CompiledEntry) where private mk ::
  private cached : SourceCoreUnifiedCompilation.Compiled
  private selected : compiled.executable = .typedSource cached
  private arguments : List SourceTypedRuntime.Value
  private initial : SourceTypedRuntime.RuntimeState
  private validationFuel : Nat
  private result : SourceCoreUnifiedCompilation.Result cached
  private requested : SourceCoreUnifiedRuntime.Result.Requests result compiled.key
    arguments validationFuel initial

namespace TypedCheckpoint

def observation {compiled : CompiledEntry} (checkpoint : TypedCheckpoint compiled) :
    SourceTypedRuntime.RunResult := checkpoint.result.observation

/-- Continue the saved Core machine; source checking and compilation are cached. -/
def resume {compiled : CompiledEntry} (checkpoint : TypedCheckpoint compiled) (fuel : Nat) :
    Except RunError (TypedCheckpoint compiled) :=
  match continued : checkpoint.result.resume fuel with
  | .error error => .error (.typedSourceAdapter error)
  | .ok result => .ok ⟨checkpoint.cached, checkpoint.selected, checkpoint.arguments,
      checkpoint.initial, checkpoint.validationFuel, result,
      SourceCoreUnifiedRuntime.Result.resume_requests checkpoint.requested continued⟩

/-- The original request is exposed independently of its machine checkpoint. -/
def inputArguments {compiled : CompiledEntry} (checkpoint : TypedCheckpoint compiled) :
    List SourceTypedRuntime.Value := checkpoint.arguments

def initialState {compiled : CompiledEntry} (checkpoint : TypedCheckpoint compiled) :
    SourceTypedRuntime.RuntimeState := checkpoint.initial

/-- Any successful observation after repeated native resumptions has the
original public request's deep input/heap/result certificate. -/
theorem done_has_public_deepExecution {compiled : CompiledEntry}
    (checkpoint : TypedCheckpoint compiled) (canonical : compiled.HasCanonicalRoot)
    {value : SourceTypedRuntime.Value} {finalState : SourceTypedRuntime.RuntimeState}
    (done : checkpoint.observation = .done value finalState) :
    compiled.TypedDeepExecution checkpoint.inputArguments checkpoint.initialState value finalState := by
  obtain ⟨specialized, selected, certificate⟩ :=
    SourceCoreUnifiedRuntime.Result.requested_done_specialization checkpoint.requested done
  obtain ⟨sourceExact, planExact⟩ := SourceCoreUnifiedPreparationCertificates.compiled_fields checkpoint.cached
  have owned := compiled.owned
  rw [checkpoint.selected] at owned
  simp only [Executable.OwnedBy] at owned
  rw [sourceExact, planExact, owned.1, owned.2] at certificate
  rw [planExact, owned.2] at selected
  have rootSelected : SourceCompilationPlan.exactSpecialization compiled.plan compiled.key = .ok compiled.root := by
    simp only [CompiledEntry.HasCanonicalRoot] at canonical
    change SourceCompilationPlan.exactSpecialization compiled.plan compiled.root.key = .ok compiled.root
    unfold SourceCompilationPlan.exactSpecialization
    rw [canonical]
  have same : specialized = compiled.root := Except.ok.inj (selected.symm.trans rootSelected)
  subst specialized
  simpa only [CompiledEntry.TypedDeepExecution, checkpoint.selected, inputArguments, initialState] using certificate

/-- Native resumption retains the original source arguments and initial heap. -/
theorem resume_request {compiled : CompiledEntry} {checkpoint resumed : TypedCheckpoint compiled} {fuel : Nat}
    (continued : checkpoint.resume fuel = .ok resumed) :
    resumed.inputArguments = checkpoint.inputArguments ∧ resumed.initialState = checkpoint.initialState := by
  unfold resume at continued
  split at continued
  · cases continued
  · cases continued
    exact ⟨rfl, rfl⟩

end TypedCheckpoint

/-- Invoke the source-value interface while retaining the native continuation. -/
def runTypedWithCheckpoint (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions := {})
    (state : SourceTypedRuntime.RuntimeState := {}) :
    Except RunError (TypedCheckpoint compiled) :=
  match selected : compiled.executable with
  | .typedSource cached =>
      match ran : cached.run compiled.key arguments options.inputValidationFuel options.executionFuel state with
      | .error error => .error (.typedSourceAdapter error)
      | .ok result => .ok ⟨cached, selected, arguments, state, options.inputValidationFuel,
          result, SourceCoreUnifiedRuntime.run_requests ran⟩
  | _ => .error (.invocationKindMismatch compiled.backend .typedValues)

/-- The public checkpoint is tied to the actual invocation's source inputs. -/
theorem runTypedWithCheckpoint_request (compiled : CompiledEntry)
    {arguments : List SourceTypedRuntime.Value} {options : RunOptions}
    {state : SourceTypedRuntime.RuntimeState} {checkpoint : TypedCheckpoint compiled}
    (ran : compiled.runTypedWithCheckpoint arguments options state = .ok checkpoint) :
    checkpoint.inputArguments = arguments ∧ checkpoint.initialState = state := by
  unfold runTypedWithCheckpoint at ran
  split at ran
  · split at ran
    · cases ran
    · cases ran
      exact ⟨rfl, rfl⟩
  · cases ran

/-- Execute a reusable artifact through its selected value interface. Both
interfaces execute Core; the source-value route restores source observations. -/
def run (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions := {}) :
    Except RunError ExecutionResult :=
  match compiled.executable, invocation with
  | .core entry, .coreValues arguments store =>
      match entry.run? arguments options.executionFuel store with
      | some result => .ok (.core result)
      | none => .error (.coreInputTypesMismatch
          entry.elaborated.inputs.values (arguments.map Core.Value.type))
  | .coreRuntime entry, .coreValues arguments store =>
      (entry.run arguments options.executionFuel store).map
        (fun result => .coreLanguageResult result.observation)
        |>.mapError RunError.coreRuntimeInput
  | .coreGeneral general, .coreValues arguments store =>
      (general.entry.run arguments options.executionFuel store).map
        (fun result => .coreLanguageResult result.observation)
        |>.mapError RunError.coreGeneralInput
  | .typedSource cached, .typedValues arguments state =>
      (cached.run compiled.key arguments options.inputValidationFuel options.executionFuel state).map
        (fun result => .typedSource result.observation)
        |>.mapError RunError.typedSourceAdapter
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

/-- Open a new owned artifact from cached Core code. Subsequent invocations use
its typed heap and opaque function handles. Opening does not repeat compilation. -/
def openCoreArtifact? (compiled : CompiledEntry) : IO (Option SourceCoreSession.Artifact) :=
  match compiled.executable with
  | .coreGeneral general => return some (← general.recipe.open)
  | _ => pure none

/-- The real catalog used by the general Core entry's deep source adapters. -/
def coreDataContext? (compiled : CompiledEntry) : Option SourceCoreDataValues.Context :=
  match compiled.executable with
  | .coreGeneral general => some ⟨general.recipe.checked, compiled.program.signatures⟩
  | _ => none

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

/-- Internal root recovery cannot change the canonical seed identity. -/
private theorem exactRoot_seedKeys (plan : SourceSpecializationWorklist.Plan)
    (root : SourceSpecialization.SpecializedFunction)
    (accepted : exactRoot plan = .ok root) :
    plan.seedKeys = [root.key] := by
  unfold exactRoot at accepted
  split at accepted
  next key seedKeysEqual =>
    simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    next rootsEqual =>
      cases accepted
      have member : root ∈ plan.specializations.filter (fun specialized =>
          decide (specialized.key = key)) := by
        rw [rootsEqual]
        simp
      have selectedKey : root.key = key := by
        exact of_decide_eq_true (List.mem_filter.mp member).2
      simpa [selectedKey] using seedKeysEqual
    next roots rootsEqual => cases accepted
  next keys seedKeysEqual => cases accepted

/-- Exact root recovery also retains the unique specialization witness needed
by the source-value successful-result preservation theorem. -/
private theorem exactRoot_specializations
    (plan : SourceSpecializationWorklist.Plan)
    (root : SourceSpecialization.SpecializedFunction)
    (accepted : exactRoot plan = .ok root) :
    plan.specializations.filter (fun candidate =>
      decide (candidate.key = root.key)) = [root] := by
  unfold exactRoot at accepted
  split at accepted
  next key seedKeysEqual =>
    simp only [pure, Pure.pure, Except.pure, bind, Except.bind] at accepted
    split at accepted
    next rootsEqual =>
      cases accepted
      have member : root ∈ plan.specializations.filter (fun candidate =>
          decide (candidate.key = key)) := by
        rw [rootsEqual]
        simp
      have selectedKey : root.key = key := by
        exact of_decide_eq_true (List.mem_filter.mp member).2
      simpa [selectedKey] using rootsEqual
    next roots rootsEqual => cases accepted
  next keys seedKeysEqual => cases accepted

private def prepareCoreRuntime (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (compilationFuel : Nat) (reason : Core.Word) :
    Except SourceCoreRecursiveEntry.Error SourceCoreBasicEntry.PreparedProgram :=
  match SourceCoreBasicEntry.prepare program plan compilationFuel reason with
  | .ok prepared => .ok prepared
  | .error _ =>
      match SourceCoreRecursiveEntry.prepare program plan compilationFuel reason with
      | .ok prepared => .ok prepared
      | .error _ => SourceCoreFunctionEntry.prepare program plan compilationFuel reason

private def selectCoreBackendFallback (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat) :
    Except CompileError Executable :=
  let complete : SourceSpecializationWorklist.Outcome := .complete plan
  match SourceCoreDirectLinking.linkWithStagingFuel program complete
      stagingFuel with
  | .ok linked =>
      match linked.entries with
      | [entry] => .ok (.core entry)
      | entries => .error (.backendEntryCountMismatch .core entries.length)
  | .error error =>
      match prepareCoreRuntime program plan stagingFuel Core.Word.zero with
      | .ok prepared =>
          match prepared.entries with
          | [entry] => .ok (.coreRuntime entry)
          | entries => .error (.backendEntryCountMismatch .core entries.length)
      | .error _ =>
          match SourceCoreSession.Recipe.prepareAutomatic program plan stagingFuel with
          | .ok recipe => match recipe.program.entries with
              | [entry] => .ok (.coreGeneral ⟨recipe, entry⟩)
              | entries => .error (.backendEntryCountMismatch .core entries.length)
          | .error _ => .error (.backendRejected (.core error))

/-- Callable-bearing plans require the retained contract profile before any
older lowering can erase parameter count or staging flags. -/
private def needsCallableContracts (plan : SourceSpecializationWorklist.Plan) : Bool :=
  plan.specializations.any fun specialized =>
    specialized.function.typedBody.nodes.any (fun
      | .expression {form := .lambda .., ..} => true
      | .expression {form := .call _ _ (.indirect _), ..} => true
      | _ => false)

private def selectCoreBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat) :
    Except CompileError Executable :=
  if needsCallableContracts plan then
    match SourceCoreSession.Recipe.prepareAutomatic program plan stagingFuel true with
    | .error error => .error (.backendRejected (.coreCatalog error))
    | .ok recipe => match recipe.program.entries with
        | [entry] => .ok (.coreGeneral ⟨recipe, entry⟩)
        | entries => .error (.backendEntryCountMismatch .core entries.length)
  else selectCoreBackendFallback program plan stagingFuel

private def selectTypedSourceBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (compilationFuel : Nat) :
    Except CompileError Executable :=
  match SourceCompilationPlan.validateExecutablePlanEvidence program plan with
  | .error error => .error (.backendRejected (.typedSource error))
  | .ok _ =>
      (SourceCoreUnifiedCompilation.prepare program plan compilationFuel).map Executable.typedSource
        |>.mapError (fun error => .backendRejected (.typedSourceCore error))

private def selectBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat)
    (preference : BackendPreference) : Except CompileError Executable :=
  match preference with
  | .core => selectCoreBackend program plan stagingFuel
  | .typedSource => selectTypedSourceBackend program plan stagingFuel
  | .automatic =>
      match selectCoreBackend program plan stagingFuel with
      | .ok executable => .ok executable
      | .error (.backendRejected coreError) =>
          match selectTypedSourceBackend program plan stagingFuel with
          | .ok executable => .ok executable
          | .error (.backendRejected typedSourceError) =>
              .error (.noBackend [coreError, typedSourceError])
          | .error error => .error error
      | .error error => .error error

private theorem selectCoreBackendFallback_success_backend
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (executable : Executable)
    (selected : selectCoreBackendFallback program plan stagingFuel = .ok executable) :
    executable.backend = .core := by
  unfold selectCoreBackendFallback at selected
  cases linkedResult : SourceCoreDirectLinking.linkWithStagingFuel program
      (.complete plan) stagingFuel with
  | error error =>
      cases prepared : prepareCoreRuntime program plan stagingFuel Core.Word.zero with
      | error preparationError =>
          cases cached : SourceCoreSession.Recipe.prepareAutomatic program plan stagingFuel with
          | error error => simp [linkedResult, prepared, cached] at selected
          | ok recipe =>
              cases entries : recipe.program.entries with
              | nil => simp [linkedResult, prepared, cached, entries] at selected
              | cons entry rest =>
                  cases rest with
                  | nil =>
                      simp [linkedResult, prepared, cached, entries] at selected
                      cases selected
                      rfl
                  | cons another tail => simp [linkedResult, prepared, cached, entries] at selected

      | ok preparedProgram =>
          cases entries : preparedProgram.entries with
          | nil => simp [linkedResult, prepared, entries] at selected
          | cons entry rest =>
              cases rest with
              | nil =>
                  simp [linkedResult, prepared, entries] at selected
                  cases selected
                  rfl
              | cons another tail => simp [linkedResult, prepared, entries] at selected
  | ok linked =>
      cases entries : linked.entries with
      | nil => simp [linkedResult, entries] at selected
      | cons entry rest =>
          cases rest with
          | nil =>
              simp [linkedResult, entries] at selected
              cases selected
              rfl
          | cons another tail =>
              simp [linkedResult, entries] at selected

private theorem selectCoreBackend_success_backend
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (executable : Executable)
    (selected : selectCoreBackend program plan stagingFuel = .ok executable) :
    executable.backend = .core := by
  unfold selectCoreBackend at selected
  split at selected
  · cases prepared : SourceCoreSession.Recipe.prepareAutomatic program plan stagingFuel true with
    | error error => simp [prepared] at selected
    | ok recipe =>
        cases entries : recipe.program.entries with
        | nil => simp [prepared, entries] at selected
        | cons entry rest =>
            cases rest with
            | nil =>
                simp [prepared, entries] at selected
                cases selected
                rfl
            | cons another tail => simp [prepared, entries] at selected
  · exact selectCoreBackendFallback_success_backend program plan stagingFuel executable selected

private theorem selectTypedSourceBackend_success
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (fuel : Nat) (executable : Executable)
    (selected : selectTypedSourceBackend program plan fuel = .ok executable) :
    executable.backend = .typedSource ∧ executable.OwnedBy program plan ∧
      SourceCompilationPlan.validateExecutablePlanEvidence program plan = .ok () := by
  cases validated : SourceCompilationPlan.validateExecutablePlanEvidence program plan with
  | error error => simp [selectTypedSourceBackend, validated] at selected
  | ok value =>
      cases value
      cases prepared : SourceCoreUnifiedCompilation.prepare program plan fuel with
      | error error => simp [selectTypedSourceBackend, validated, prepared, Except.mapError, Except.map] at selected
      | ok cached =>
          simp [selectTypedSourceBackend, validated, prepared, Except.mapError, Except.map] at selected
          cases selected
          obtain ⟨sourceExact, planExact, _⟩ := SourceCoreUnifiedPreparationCertificates.prepare_fields prepared
          exact ⟨rfl, ⟨sourceExact, planExact⟩, rfl⟩

private theorem selectBackend_success_ownership
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (fuel : Nat) (preference : BackendPreference) (executable : Executable)
    (selected : selectBackend program plan fuel preference = .ok executable) :
    executable.OwnedBy program plan := by
  have coreOwned (accepted : selectCoreBackend program plan fuel = .ok executable) :
      executable.OwnedBy program plan := by
    have backend := selectCoreBackend_success_backend program plan fuel executable accepted
    cases executable <;> simp_all [Executable.backend, Executable.OwnedBy]
  cases preference with
  | core => exact coreOwned (by simpa [selectBackend] using selected)
  | typedSource => exact (selectTypedSourceBackend_success program plan fuel executable
      (by simpa [selectBackend] using selected)).2.1
  | automatic =>
      cases selectedCore : selectCoreBackend program plan fuel with
      | ok core =>
          have same : core = executable := by simpa [selectBackend, selectedCore] using selected
          subst core
          exact coreOwned selectedCore
      | error error =>
          cases error <;> simp [selectBackend, selectedCore] at selected
          rename_i rejection
          cases selectedTyped : selectTypedSourceBackend program plan fuel with
          | ok typed =>
              have same : typed = executable := by simpa [selectedTyped] using selected
              subst typed
              exact (selectTypedSourceBackend_success program plan fuel executable selectedTyped).2.1
          | error error =>
              rw [selectedTyped] at selected
              cases error <;> cases selected

/-- An explicit preference retains its invocation tag even when both value
interfaces are implemented by Core. -/
private theorem selectBackend_backend_of_preference
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (preference : BackendPreference)
    (backend : Backend) (executable : Executable)
    (requested : preference.requested? = some backend)
    (selected : selectBackend program plan stagingFuel preference = .ok executable) :
    executable.backend = backend := by
  cases preference with
  | automatic => simp [BackendPreference.requested?] at requested
  | core =>
      have same : backend = .core := by simpa [BackendPreference.requested?] using requested.symm
      subst backend
      exact selectCoreBackend_success_backend program plan stagingFuel executable
        (by simpa [selectBackend] using selected)
  | typedSource =>
      have same : backend = .typedSource := by simpa [BackendPreference.requested?] using requested.symm
      subst backend
      exact (selectTypedSourceBackend_success program plan stagingFuel executable
        (by simpa [selectBackend] using selected)).1

private theorem selectBackend_typed_plan
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (preference : BackendPreference)
    (cached : SourceCoreUnifiedCompilation.Compiled)
    (selected : selectBackend program plan stagingFuel preference = .ok (.typedSource cached)) :
    SourceCompilationPlan.validateExecutablePlanEvidence program plan = .ok () := by
  have owned := selectBackend_success_ownership program plan stagingFuel preference (.typedSource cached) selected
  have valid := SourceCoreUnifiedPreparationCertificates.compiled_validation cached
  simp only [Executable.OwnedBy] at owned
  simpa only [owned.1, owned.2] using valid

/-- Guard the public result signature against an inconsistent linker payload. -/
private def validatePublicResultType
    (root : SourceSpecialization.SpecializedFunction)
    (executable : Executable) : Except CompileError Unit := do
  match executable with
  | .core entry =>
      let projected ← (SourceCoreElaboration.lowerType
          (.declaration root.declaration) root.function.inferredBodyType)
        |>.mapError CompileError.publicCoreResultProjection
      if projected = entry.elaborated.returnType then
        pure ()
      else
        throw (.publicCoreResultMismatch projected
          entry.elaborated.returnType)
  | .coreRuntime entry =>
      let projected ← (SourceCoreScalar.lowerType
          (.declaration root.declaration) root.function.inferredBodyType)
        |>.mapError CompileError.publicCoreResultProjection
      if projected = entry.resultType then
        pure ()
      else
        throw (.publicCoreResultMismatch projected entry.resultType)
  | .coreGeneral general =>
      let projected ← (general.recipe.checked.catalog.project root.function.inferredBodyType)
        |>.mapError CompileError.publicGeneralResultProjection
      if projected = general.entry.resultType then pure ()
      else throw (.publicCoreResultMismatch projected general.entry.resultType)
  | .typedSource _ => pure ()

private theorem validatePublicResultType_correct
    (root : SourceSpecialization.SpecializedFunction)
    (executable : Executable)
    (accepted : validatePublicResultType root executable = .ok ()) :
    executable.HasPublicResultProjection root := by
  cases executable with
  | core entry =>
      simp only [Executable.HasPublicResultProjection]
      cases projection : SourceCoreElaboration.lowerType
          (.declaration root.declaration) root.function.inferredBodyType with
      | error error =>
          simp [validatePublicResultType, projection, Except.mapError,
            bind, Except.bind] at accepted
      | ok projected =>
          by_cases same : projected = entry.elaborated.returnType
          · exact congrArg Except.ok same
          · simp [validatePublicResultType, projection, same,
              Except.mapError, bind, Except.bind] at accepted
  | coreRuntime entry =>
      simp only [Executable.HasPublicResultProjection]
      cases projection : SourceCoreScalar.lowerType
          (.declaration root.declaration) root.function.inferredBodyType with
      | error error =>
          simp [validatePublicResultType, projection, Except.mapError,
            bind, Except.bind] at accepted
      | ok projected =>
          by_cases same : projected = entry.resultType
          · exact congrArg Except.ok same
          · simp [validatePublicResultType, projection, same,
              Except.mapError, bind, Except.bind] at accepted
  | coreGeneral general =>
      simp only [Executable.HasPublicResultProjection]
      cases projection : general.recipe.checked.catalog.project root.function.inferredBodyType with
      | error error =>
          simp [validatePublicResultType, projection, Except.mapError, bind, Except.bind] at accepted
      | ok projected =>
          by_cases same : projected = general.entry.resultType
          · exact congrArg Except.ok same
          · simp [validatePublicResultType, projection, same, Except.mapError, bind, Except.bind] at accepted
  | typedSource cached =>
      trivial

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
  let executable ← match selected : selectBackend program plan options.stagingFuel options.backendPreference with
    | .error error => throw error
    | .ok executable => pure (⟨executable,
        selectBackend_success_ownership program plan options.stagingFuel options.backendPreference executable selected⟩ :
        {executable // executable.OwnedBy program plan})
  validatePublicResultType root executable.val
  pure ⟨program, plan, root, executable.val, executable.property⟩

/-- Checked compilation retains the exact caller-supplied checked program.
This is an identity fact, not a claim that the supplied record came from the
source checker. -/
theorem compileChecked_program
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled) :
    compiled.program = program := by
  unfold compileChecked at compiledOk
  cases seedResult : SourceProgramExecution.resolveSeed program seed with
  | error error =>
      rw [seedResult] at compiledOk
      cases compiledOk
  | ok request =>
      rw [seedResult] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      cases worklist : SourceSpecializationWorklist.run program [request]
          options.specializationBudget with
      | error error =>
          rw [worklist] at compiledOk
          cases compiledOk
      | ok outcome =>
          rw [worklist] at compiledOk
          cases outcome with
          | budgetExhausted plan next pending =>
              cases compiledOk
          | complete plan =>
              simp only [pure, Pure.pure, Except.pure] at compiledOk
              cases valid : SourceCoreDirectLinking.validatePlan program plan with
              | error error =>
                  rw [valid] at compiledOk
                  cases compiledOk
              | ok checked =>
                  rw [valid] at compiledOk
                  cases selected : exactRoot plan with
                  | error error =>
                      rw [selected] at compiledOk
                      cases compiledOk
                  | ok root =>
                      rw [selected] at compiledOk
                      dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                      split at compiledOk
                      next error backend =>
                          cases compiledOk
                      next executable backend =>
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              rfl

/-- An exact backend preference is authoritative: successful compilation never
falls through to a different runtime.  Automatic selection has no requested
backend and therefore cannot satisfy the premise. -/
theorem compileChecked_backend_of_preference
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry) (backend : Backend)
    (requested : options.backendPreference.requested? = some backend)
    (compiledOk : compileChecked program seed options = .ok compiled) :
    compiled.backend = backend := by
  unfold compileChecked at compiledOk
  cases seedResult : SourceProgramExecution.resolveSeed program seed with
  | error error =>
      rw [seedResult] at compiledOk
      cases compiledOk
  | ok request =>
      rw [seedResult] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      cases worklist : SourceSpecializationWorklist.run program [request]
          options.specializationBudget with
      | error error =>
          rw [worklist] at compiledOk
          cases compiledOk
      | ok outcome =>
          rw [worklist] at compiledOk
          cases outcome with
          | budgetExhausted plan next pending =>
              cases compiledOk
          | complete plan =>
              simp only [pure, Pure.pure, Except.pure] at compiledOk
              cases valid : SourceCoreDirectLinking.validatePlan program plan with
              | error error =>
                  rw [valid] at compiledOk
                  cases compiledOk
              | ok checked =>
                  rw [valid] at compiledOk
                  cases selected : exactRoot plan with
                  | error error =>
                      rw [selected] at compiledOk
                      cases compiledOk
                  | ok root =>
                      rw [selected] at compiledOk
                      dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                      split at compiledOk
                      next error backendSelection =>
                          cases compiledOk
                      next executable backendSelection =>
                          have exactBackend :=
                            selectBackend_backend_of_preference program plan
                              options.stagingFuel options.backendPreference
                              backend executable requested backendSelection
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              simpa [CompiledEntry.backend,
                                Executable.backend] using exactBackend

/-- Every artifact returned by the public checked compilation path retains its
root as the unique specialization selected by the canonical seed key. -/
theorem compileChecked_hasCanonicalRoot
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled) :
    compiled.HasCanonicalRoot := by
  unfold compileChecked at compiledOk
  cases seedResult : SourceProgramExecution.resolveSeed program seed with
  | error error =>
      rw [seedResult] at compiledOk
      cases compiledOk
  | ok request =>
      rw [seedResult] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      cases worklist : SourceSpecializationWorklist.run program [request]
          options.specializationBudget with
      | error error =>
          rw [worklist] at compiledOk
          cases compiledOk
      | ok outcome =>
          rw [worklist] at compiledOk
          cases outcome with
          | budgetExhausted plan next pending =>
              cases compiledOk
          | complete plan =>
              simp only [pure, Pure.pure, Except.pure] at compiledOk
              cases valid : SourceCoreDirectLinking.validatePlan program plan with
              | error error =>
                  rw [valid] at compiledOk
                  cases compiledOk
              | ok checked =>
                  rw [valid] at compiledOk
                  cases selected : exactRoot plan with
                  | error error =>
                      rw [selected] at compiledOk
                      cases compiledOk
                  | ok root =>
                      rw [selected] at compiledOk
                      dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                      split at compiledOk
                      next error backend =>
                          cases compiledOk
                      next executable backend =>
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              exact exactRoot_specializations plan root selected

/-- Selecting the typed-source backend certifies that its retained finite plan
passed the runtime's executable-profile preflight. -/
theorem compileChecked_hasValidatedTypedPlan
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource) :
    compiled.HasValidatedTypedPlan := by
  unfold compileChecked at compiledOk
  cases seedResult : SourceProgramExecution.resolveSeed program seed with
  | error error =>
      rw [seedResult] at compiledOk
      cases compiledOk
  | ok request =>
      rw [seedResult] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      cases worklist : SourceSpecializationWorklist.run program [request]
          options.specializationBudget with
      | error error =>
          rw [worklist] at compiledOk
          cases compiledOk
      | ok outcome =>
          rw [worklist] at compiledOk
          cases outcome with
          | budgetExhausted plan next pending =>
              cases compiledOk
          | complete plan =>
              simp only [pure, Pure.pure, Except.pure] at compiledOk
              cases valid : SourceCoreDirectLinking.validatePlan program plan with
              | error error =>
                  rw [valid] at compiledOk
                  cases compiledOk
              | ok checked =>
                  rw [valid] at compiledOk
                  cases selected : exactRoot plan with
                  | error error =>
                      rw [selected] at compiledOk
                      cases compiledOk
                  | ok root =>
                      rw [selected] at compiledOk
                      dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                      split at compiledOk
                      next error backendSelected =>
                          cases compiledOk
                      next executable backendSelected =>
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              cases executable with
                              | core entry | coreRuntime entry | coreGeneral entry =>
                                  simp [CompiledEntry.backend] at typedBackend
                              | typedSource cached =>
                                  exact selectBackend_typed_plan program plan
                                    options.stagingFuel options.backendPreference
                                    cached backendSelected

/-- The public result type is certified against the backend selected by every
successful checked compilation, including every explicit backend preference. -/
theorem compileChecked_hasPublicResultProjection
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled) :
    compiled.HasPublicResultProjection := by
  unfold compileChecked at compiledOk
  cases seedResult : SourceProgramExecution.resolveSeed program seed with
  | error error =>
      rw [seedResult] at compiledOk
      cases compiledOk
  | ok request =>
      rw [seedResult] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      cases worklist : SourceSpecializationWorklist.run program [request]
          options.specializationBudget with
      | error error =>
          rw [worklist] at compiledOk
          cases compiledOk
      | ok outcome =>
          rw [worklist] at compiledOk
          cases outcome with
          | budgetExhausted plan next pending =>
              cases compiledOk
          | complete plan =>
              simp only [pure, Pure.pure, Except.pure] at compiledOk
              cases valid : SourceCoreDirectLinking.validatePlan program plan with
              | error error =>
                  rw [valid] at compiledOk
                  cases compiledOk
              | ok checked =>
                  rw [valid] at compiledOk
                  cases selected : exactRoot plan with
                  | error error =>
                      rw [selected] at compiledOk
                      cases compiledOk
                  | ok root =>
                      rw [selected] at compiledOk
                      dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                      split at compiledOk
                      next error backend =>
                          cases compiledOk
                      next executable backend =>
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              simpa [CompiledEntry.HasPublicResultProjection]
                                using validatePublicResultType_correct root
                                  executable publicResult

/-- Successful compilation preserves the exact canonical identity obtained by
resolving the caller's seed.  In particular, backend fallback cannot swap the
public root after specialization. -/
theorem compileChecked_key_of_resolved (program : CheckedProgram) (seed : Seed)
    (options : CompileOptions) (request : SourceSpecializationWorklist.Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (compiled : CompiledEntry)
    (seedOk : SourceProgramExecution.resolveSeed program seed = .ok request)
    (resolved : SourceSpecializationWorklist.resolveRequest program request =
      .ok specialized)
    (compiledOk : compileChecked program seed options = .ok compiled) :
    compiled.key = specialized.key := by
  have canonical : SourceSpecializationWorklist.canonicalSeedKeys program
      [request] = .ok [specialized.key] := by
    simp only [SourceSpecializationWorklist.canonicalSeedKeys, resolved,
      bind, Except.bind, pure, Pure.pure, Except.pure]
  unfold compileChecked at compiledOk
  rw [seedOk] at compiledOk
  simp only [Except.mapError, bind, Except.bind] at compiledOk
  cases worklist : SourceSpecializationWorklist.run program [request]
      options.specializationBudget with
  | error error =>
      rw [worklist] at compiledOk
      cases compiledOk
  | ok outcome =>
      have seeds := SourceSpecializationWorklist.run_preserves_seedKeys program
        [request] options.specializationBudget outcome [specialized.key]
        canonical worklist
      cases outcome with
      | budgetExhausted plan next pending =>
          rw [worklist] at compiledOk
          cases compiledOk
      | complete plan =>
          simp only [SourceSpecializationWorklist.Outcome.plan_complete] at seeds
          rw [worklist] at compiledOk
          simp only [pure, Pure.pure, Except.pure] at compiledOk
          cases valid : SourceCoreDirectLinking.validatePlan program plan with
          | error error =>
              rw [valid] at compiledOk
              cases compiledOk
          | ok checked =>
              rw [valid] at compiledOk
              cases selected : exactRoot plan with
              | error error =>
                  rw [selected] at compiledOk
                  cases compiledOk
              | ok root =>
                  have rootSeeds := exactRoot_seedKeys plan root selected
                  have rootKey : root.key = specialized.key := by
                    simpa [rootSeeds] using seeds
                  rw [selected] at compiledOk
                  dsimp only [Except.mapError, bind, Except.bind] at compiledOk
                  split at compiledOk
                  next error executable =>
                      cases compiledOk
                  next backend executable =>
                      cases publicResult : validatePublicResultType root
                          backend with
                      | error error =>
                          rw [publicResult] at compiledOk
                          cases compiledOk
                      | ok checkedResult =>
                          rw [publicResult] at compiledOk
                          cases compiledOk
                          exact rootKey

/-- Check a raw workspace and compile one explicit root. -/
def compile (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions := {}) : Except CompileError CompiledEntry := do
  let program ← (checkProgram raw options.checkingFuel).mapError
    CompileError.checking
  compileChecked program seed options.toCompileOptions

/-- Raw-workspace compilation preserves the same exact-backend preference as
the checked-program entry point. -/
theorem compile_backend_of_preference
    (raw : Workspace.RawWorkspace) (seed : Seed) (options : CheckingOptions)
    (compiled : CompiledEntry) (backend : Backend)
    (requested : options.backendPreference.requested? = some backend)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.backend = backend := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      apply compileChecked_backend_of_preference program seed
        options.toCompileOptions compiled backend
      · simpa using requested
      · exact compiledOk

/-- Raw compilation records an actual successful source-checker run.  The
checked-program entry point deliberately has no corresponding unconditional
theorem because its input carrier is constructible by callers. -/
theorem compile_hasCheckedSourceWitness
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.HasCheckedSourceWitness := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      refine ⟨raw, options.checkingFuel, ?_⟩
      simpa [compileChecked_program program seed options.toCompileOptions
        compiled compiledOk] using checked

/-- The same typed-plan certificate is available after raw-workspace
compilation, provided the selected backend is typed source. -/
theorem compile_hasValidatedTypedPlan
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource) :
    compiled.HasValidatedTypedPlan := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      exact compileChecked_hasValidatedTypedPlan program seed
        options.toCompileOptions compiled compiledOk typedBackend

/-!
## Whole-program orchestration

The single-root compiler above remains the primitive operation.  The public
program boundary below checks a workspace once and then compiles each requested
root independently.  Independent root plans are intentional: they preserve
per-root backend selection, so one artifact may contain both direct-Core and
typed-source entries without forcing all roots onto the least common backend.
-/

/-- The exact root whose compilation failed in an ordered multi-root request. -/
structure RootCompileError where
  index : Nat
  seed : Seed
  error : CompileError
  deriving Repr

/-- A sealed ordered collection of independently compiled public roots. -/
structure CompiledProgram where private mk ::
  private compiledEntries : List CompiledEntry

namespace CompiledProgram

/-- Compiled entries in caller-supplied order, including repeated roots. -/
def entries (compiled : CompiledProgram) : List CompiledEntry :=
  compiled.compiledEntries

/-- Number of requested roots retained by the artifact. -/
def count (compiled : CompiledProgram) : Nat :=
  compiled.compiledEntries.length

/-- Selected backend of every root, in the same stable order. -/
def backends (compiled : CompiledProgram) : List Backend :=
  compiled.compiledEntries.map CompiledEntry.backend

/-- Whether successful automatic selection used more than one backend. -/
def usesMixedBackends (compiled : CompiledProgram) : Bool :=
  decide (compiled.backends.eraseDups.length > 1)

/-- Lookup by the zero-based request position. -/
def entry? (compiled : CompiledProgram) (index : Nat) : Option CompiledEntry :=
  compiled.compiledEntries[index]?

end CompiledProgram

private def compileRootsFrom (program : CheckedProgram)
    (options : CompileOptions) :
    Nat → List Seed → Except RootCompileError (List CompiledEntry)
  | _, [] => .ok []
  | index, seed :: rest => do
      let compiled ← (compileChecked program seed options).mapError fun error =>
        { index, seed, error }
      let compiledRest ← compileRootsFrom program options (index + 1) rest
      pure (compiled :: compiledRest)

/-- Compile any ordered root set from one already checked catalog.  Budgets
apply independently to each root; order and duplicates are preserved. -/
def compileManyChecked (program : CheckedProgram) (seeds : List Seed)
    (options : CompileOptions := {}) :
    Except RootCompileError CompiledProgram := do
  let entries ← compileRootsFrom program options 0 seeds
  pure ⟨entries⟩

/-- Pointwise certificate retained by an ordered multi-root artifact.  It
records the exact successful single-root compilation for every request, so
all single-root provenance and preservation theorems can be reused without
re-running checking or specialization. -/
def CompiledProgram.Certifies (compiled : CompiledProgram)
    (program : CheckedProgram) (seeds : List Seed)
    (options : CompileOptions) : Prop :=
  Workspace.ListCorresponds
    (fun seed entry => compileChecked program seed options = .ok entry)
    seeds compiled.entries

private theorem compileRootsFrom_certifies
    (program : CheckedProgram) (options : CompileOptions)
    (start : Nat) (seeds : List Seed) (entries : List CompiledEntry)
    (success : compileRootsFrom program options start seeds = .ok entries) :
    Workspace.ListCorresponds
      (fun seed entry => compileChecked program seed options = .ok entry)
      seeds entries := by
  induction seeds generalizing start entries with
  | nil =>
      simp [compileRootsFrom] at success
      cases success
      exact .nil
  | cons seed seeds induction =>
      simp only [compileRootsFrom] at success
      cases compiledResult : compileChecked program seed options with
      | error error =>
          rw [compiledResult] at success
          cases success
      | ok entry =>
          simp only [compiledResult, Except.mapError, bind, Except.bind] at success
          cases restResult : compileRootsFrom program options (start + 1) seeds with
          | error error =>
              rw [restResult] at success
              cases success
          | ok rest =>
              simp [restResult] at success
              cases success
              exact .cons compiledResult
                (induction (start := start + 1) (entries := rest) restResult)

/-- Successful ordered compilation retains the exact single-root derivation
for every entry, in caller-supplied order and including duplicates. -/
theorem compileManyChecked_certifies
    (program : CheckedProgram) (seeds : List Seed)
    (options : CompileOptions) (compiled : CompiledProgram)
    (success : compileManyChecked program seeds options = .ok compiled) :
    compiled.Certifies program seeds options := by
  unfold compileManyChecked at success
  cases rootsResult : compileRootsFrom program options 0 seeds with
  | error error =>
      rw [rootsResult] at success
      cases success
  | ok entries =>
      simp [rootsResult] at success
      cases success
      exact compileRootsFrom_certifies program options 0 seeds entries rootsResult

private theorem certified_entry_member
    {program : CheckedProgram} {options : CompileOptions}
    {seeds : List Seed} {entries : List CompiledEntry}
    (certified : Workspace.ListCorresponds
      (fun seed entry => compileChecked program seed options = .ok entry)
      seeds entries) {entry : CompiledEntry} (member : entry ∈ entries) :
    ∃ seed, seed ∈ seeds ∧
      compileChecked program seed options = .ok entry := by
  induction certified with
  | nil => simp at member
  | @cons seed head seeds tail headCompiled tailCertified induction =>
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst head
          exact ⟨seed, by simp, headCompiled⟩
      | inr tailMember =>
          obtain ⟨selected, selectedMember, selectedCompiled⟩ :=
            induction tailMember
          exact ⟨selected, by simp [selectedMember], selectedCompiled⟩

/-- Every member of a checked multi-root artifact has the same canonical-root
and public-result certificates as a directly compiled entry. -/
theorem compileManyChecked_entry_certificates
    (program : CheckedProgram) (seeds : List Seed)
    (options : CompileOptions) (compiled : CompiledProgram)
    (success : compileManyChecked program seeds options = .ok compiled)
    (entry : CompiledEntry) (member : entry ∈ compiled.entries) :
    entry.HasCanonicalRoot ∧ entry.HasPublicResultProjection := by
  have certified := compileManyChecked_certifies program seeds options compiled
    success
  obtain ⟨seed, _seedMember, compiledEntry⟩ :=
    certified_entry_member certified member
  exact ⟨compileChecked_hasCanonicalRoot program seed options entry
      compiledEntry,
    compileChecked_hasPublicResultProjection program seed options entry
      compiledEntry⟩

/-- Raw-workspace multi-root failures keep checking separate from the exact
root position that failed after checking. -/
inductive ProgramCompileError where
  | checking (errors : List ProgramCheckError)
  | root (error : RootCompileError)
  deriving Repr

/-- Check one raw workspace once and compile an ordered root set. -/
def compileMany (raw : Workspace.RawWorkspace) (seeds : List Seed)
    (options : CheckingOptions := {}) :
    Except ProgramCompileError CompiledProgram := do
  let program ← (checkProgram raw options.checkingFuel).mapError
    ProgramCompileError.checking
  (compileManyChecked program seeds options.toCompileOptions).mapError
    ProgramCompileError.root

/-- Raw multi-root compilation exposes the one checker result shared by all
root artifacts together with their exact ordered compilation certificates. -/
theorem compileMany_certifies
    (raw : Workspace.RawWorkspace) (seeds : List Seed)
    (options : CheckingOptions) (compiled : CompiledProgram)
    (success : compileMany raw seeds options = .ok compiled) :
    ∃ program,
      checkProgram raw options.checkingFuel = .ok program ∧
        compiled.Certifies program seeds options.toCompileOptions := by
  unfold compileMany at success
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at success
      cases success
  | ok program =>
      rw [checked] at success
      simp only [Except.mapError, bind, Except.bind] at success
      cases compiledResult : compileManyChecked program seeds
          options.toCompileOptions with
      | error error =>
          rw [compiledResult] at success
          cases success
      | ok actual =>
          rw [compiledResult] at success
          cases success
          exact ⟨program, rfl,
            compileManyChecked_certifies program seeds options.toCompileOptions
              compiled compiledResult⟩

/-- Every member produced from a raw workspace retains checker provenance,
canonical-root identity, and the public result projection. -/
theorem compileMany_entry_certificates
    (raw : Workspace.RawWorkspace) (seeds : List Seed)
    (options : CheckingOptions) (compiled : CompiledProgram)
    (success : compileMany raw seeds options = .ok compiled)
    (entry : CompiledEntry) (member : entry ∈ compiled.entries) :
    entry.HasCheckedSourceWitness ∧ entry.HasCanonicalRoot ∧
      entry.HasPublicResultProjection := by
  obtain ⟨program, checked, certified⟩ :=
    compileMany_certifies raw seeds options compiled success
  obtain ⟨seed, _seedMember, compiledEntry⟩ :=
    certified_entry_member certified member
  have sourceWitness : entry.HasCheckedSourceWitness := by
    refine ⟨raw, options.checkingFuel, ?_⟩
    simpa [compileChecked_program program seed options.toCompileOptions entry
      compiledEntry] using checked
  exact ⟨sourceWitness,
    compileChecked_hasCanonicalRoot program seed options.toCompileOptions entry
      compiledEntry,
    compileChecked_hasPublicResultProjection program seed
      options.toCompileOptions entry compiledEntry⟩

/-- Typed entries inside a checked multi-root artifact retain the same
executable-plan validation certificate as a single-root compilation. -/
theorem compileManyChecked_entry_hasValidatedTypedPlan
    (program : CheckedProgram) (seeds : List Seed)
    (options : CompileOptions) (compiled : CompiledProgram)
    (success : compileManyChecked program seeds options = .ok compiled)
    (entry : CompiledEntry) (member : entry ∈ compiled.entries)
    (typedBackend : entry.backend = .typedSource) :
    entry.HasValidatedTypedPlan := by
  have certified := compileManyChecked_certifies program seeds options compiled
    success
  obtain ⟨seed, _seedMember, compiledEntry⟩ :=
    certified_entry_member certified member
  exact compileChecked_hasValidatedTypedPlan program seed options entry
    compiledEntry typedBackend

private def checkWorkspaceAtEntry (raw : Workspace.RawWorkspace) (fuel : Nat) :
    Except (List ProgramCheckError) (CheckedProgram × Workspace.ModuleId) := do
  let loaded ← (loadProgram raw).mapError fun errors =>
    errors.map ProgramCheckError.loading
  let program ← checkLoadedProgram loaded fuel
  pure (program, loaded.workspace.entry.toModuleId)

/-- Compile the conventional ground `main` in a known entry module. -/
def compileEntryChecked (program : CheckedProgram)
    (entryModule : Workspace.ModuleId) (options : CompileOptions := {}) :
    Except CompileError CompiledEntry :=
  compileChecked program (Seed.named entryModule "main") options

/-- Validate and check a raw workspace once, derive its canonical entry module,
and compile that module's conventional ground `main`. -/
def compileEntry (raw : Workspace.RawWorkspace)
    (options : CheckingOptions := {}) : Except CompileError CompiledEntry := do
  let (program, entryModule) ←
    (checkWorkspaceAtEntry raw options.checkingFuel).mapError
      CompileError.checking
  compileEntryChecked program entryModule options.toCompileOptions

/-- The conventional checked entry is exactly a single-root compilation, so
its canonical root and public result projection are available directly. -/
theorem compileEntryChecked_certificates
    (program : CheckedProgram) (entryModule : Workspace.ModuleId)
    (options : CompileOptions) (compiled : CompiledEntry)
    (success : compileEntryChecked program entryModule options = .ok compiled) :
    compiled.HasCanonicalRoot ∧ compiled.HasPublicResultProjection := by
  exact ⟨compileChecked_hasCanonicalRoot program
      (Seed.named entryModule "main") options compiled success,
    compileChecked_hasPublicResultProjection program
      (Seed.named entryModule "main") options compiled success⟩

private theorem checkWorkspaceAtEntry_checked
    (raw : Workspace.RawWorkspace) (fuel : Nat)
    (program : CheckedProgram) (entryModule : Workspace.ModuleId)
    (success : checkWorkspaceAtEntry raw fuel = .ok (program, entryModule)) :
    checkProgram raw fuel = .ok program := by
  unfold checkWorkspaceAtEntry at success
  cases loadedResult : loadProgram raw with
  | error errors =>
      rw [loadedResult] at success
      cases success
  | ok loaded =>
      rw [loadedResult] at success
      simp only [Except.mapError, bind, Except.bind] at success
      cases checked : checkLoadedProgram loaded fuel with
      | error errors =>
          rw [checked] at success
          cases success
      | ok actual =>
          rw [checked] at success
          cases success
          simpa [checkProgram, loadedResult] using checked

/-- Automatic entry discovery preserves raw checker provenance in addition to
the single-root compiler certificates. -/
theorem compileEntry_certificates
    (raw : Workspace.RawWorkspace) (options : CheckingOptions)
    (compiled : CompiledEntry)
    (success : compileEntry raw options = .ok compiled) :
    compiled.HasCheckedSourceWitness ∧ compiled.HasCanonicalRoot ∧
      compiled.HasPublicResultProjection := by
  unfold compileEntry at success
  cases checkedEntry : checkWorkspaceAtEntry raw options.checkingFuel with
  | error errors =>
      rw [checkedEntry] at success
      cases success
  | ok pair =>
      obtain ⟨program, entryModule⟩ := pair
      rw [checkedEntry] at success
      simp only [Except.mapError, bind, Except.bind] at success
      have checked := checkWorkspaceAtEntry_checked raw options.checkingFuel
        program entryModule checkedEntry
      have certificates := compileEntryChecked_certificates program entryModule
        options.toCompileOptions compiled success
      have sourceWitness : compiled.HasCheckedSourceWitness := by
        refine ⟨raw, options.checkingFuel, ?_⟩
        simpa [compileChecked_program program (Seed.named entryModule "main")
          options.toCompileOptions compiled success] using checked
      exact ⟨sourceWitness, certificates⟩

/-!
## Exported Static Word ABI profile

This initial source-compiler ABI profile discovers explicitly exported
top-level functions from the workspace entry module.  It is deliberately not a
claim that contract `public` members are executable: nested contract members do
not yet participate in the checked-function and specialization catalogs.
-/

/-- One exported top-level root admitted by the `uint256 -> uint256` profile. -/
structure StaticWordRoot where
  metadata : Abi.V1.MethodMetadata
  seed : Seed

/-- Exact discovery failures for the exported Static Word source profile. -/
inductive StaticWordRootError where
  | interfaces (errors : List ProgramInterfaceError)
  | unknownEntryModule (moduleId : Workspace.ModuleId)
  | invalidMethodName (name : String)
  | missingSignature (declaration : Resolved.DeclarationId)
  | duplicateSignatures
      (declaration : Resolved.DeclarationId) (count : Nat)
  | genericFunction
      (declaration : Resolved.DeclarationId) (name : String) (arity : Nat)
  | unsupportedParameters
      (declaration : Resolved.DeclarationId) (name : String)
      (types : List Ty) (comptime : List Bool)
  | unsupportedResults
      (declaration : Resolved.DeclarationId) (name : String)
      (types : List Ty) (comptime : Bool)
  | duplicateSignature
      (firstName secondName : String) (signature : String)
  | selectorCollision
      (firstName secondName : String)
      (firstSignature secondSignature : String)
      (selector : Abi.V1.Selector)
  | noRoots (moduleId : Workspace.ModuleId)
  deriving Repr

private def staticWordRootOfEntity (program : CheckedProgram)
    (entity : ProgramPublicEntity) : Except StaticWordRootError StaticWordRoot := do
  let methodName ← match Abi.V1.validateMethodName? entity.publicName with
    | some name => pure name
    | none => throw (.invalidMethodName entity.publicName)
  let candidates := program.signatures.functions.filter fun signature =>
    decide (signature.id = entity.declaration.id)
  let signature ← match candidates with
    | [signature] => pure signature
    | [] => throw (.missingSignature entity.declaration.id)
    | signatures =>
        throw (.duplicateSignatures entity.declaration.id signatures.length)
  unless signature.scheme.parameters.isEmpty do
    throw (.genericFunction signature.id entity.publicName
      signature.scheme.parameters.length)
  match signature.parameters with
  | [parameter] =>
      unless parameter.type == .word && !parameter.comptime do
        throw (.unsupportedParameters signature.id entity.publicName
          signature.parameterTypes signature.parameterComptime)
  | _ =>
      throw (.unsupportedParameters signature.id entity.publicName
        signature.parameterTypes signature.parameterComptime)
  unless signature.returnTypes == [.word] && !signature.returnComptime do
    throw (.unsupportedResults signature.id entity.publicName
      signature.returnTypes signature.returnComptime)
  pure {
    metadata := Abi.V1.MethodMetadata.staticWord methodName
    seed := Seed.declaration signature.id
  }

private def staticWordRootsOfEntities (program : CheckedProgram) :
    List ProgramPublicEntity → Except StaticWordRootError (List StaticWordRoot)
  | [] => .ok []
  | entity :: rest =>
      if entity.declaration.kind == .function then do
        let root ← staticWordRootOfEntity program entity
        let roots ← staticWordRootsOfEntities program rest
        pure (root :: roots)
      else
        staticWordRootsOfEntities program rest

private structure IndexedStaticWordRoot where
  root : StaticWordRoot
  signature : String
  selector : Abi.V1.Selector

private def indexStaticWordRoot (root : StaticWordRoot) :
    IndexedStaticWordRoot := {
  root
  signature := root.metadata.canonicalSignatureText
  selector := root.metadata.selector
}

private def IndexedStaticWordRoot.signatureLE
    (left right : IndexedStaticWordRoot) : Bool :=
  (compare left.signature right.signature).isLE

private def canonicalStaticWordRoots
    (roots : List StaticWordRoot) : List IndexedStaticWordRoot :=
  (roots.map indexStaticWordRoot).mergeSort IndexedStaticWordRoot.signatureLE

private def firstDuplicateStaticWordSignature? :
    List IndexedStaticWordRoot →
      Option (IndexedStaticWordRoot × IndexedStaticWordRoot)
  | [] => none
  | first :: rest =>
      match rest.find? fun later => later.signature == first.signature with
      | some later => some (first, later)
      | none => firstDuplicateStaticWordSignature? rest

private def firstStaticWordSelectorCollision? :
    List IndexedStaticWordRoot →
      Option (IndexedStaticWordRoot × IndexedStaticWordRoot)
  | [] => none
  | first :: rest =>
      match rest.find? fun later => later.selector == first.selector with
      | some later => some (first, later)
      | none => firstStaticWordSelectorCollision? rest

private def validateStaticWordConflicts (roots : List StaticWordRoot) :
    Except StaticWordRootError Unit :=
  let indexed := canonicalStaticWordRoots roots
  match firstDuplicateStaticWordSignature? indexed with
  | some conflict =>
      .error (.duplicateSignature
        conflict.1.root.metadata.name.text
        conflict.2.root.metadata.name.text conflict.1.signature)
  | none =>
      match firstStaticWordSelectorCollision? indexed with
      | some conflict =>
          .error (.selectorCollision
            conflict.1.root.metadata.name.text
            conflict.2.root.metadata.name.text
            conflict.1.signature conflict.2.signature conflict.1.selector)
      | none => .ok ()

/-- Discover the complete exported Static Word root set of one checked entry
module.  Unsupported exported functions are diagnosed rather than skipped. -/
def discoverStaticWordRoots (program : CheckedProgram)
    (entryModule : Workspace.ModuleId) :
    Except StaticWordRootError (List StaticWordRoot) := do
  let interfaces ← (buildProgramInterfaces program.environment).mapError
    StaticWordRootError.interfaces
  let interface ← match interfaces.interface? entryModule with
    | some interface => pure interface
    | none => throw (.unknownEntryModule entryModule)
  let roots ← staticWordRootsOfEntities program interface.entities
  if roots.isEmpty then
    throw (.noRoots entryModule)
  validateStaticWordConflicts roots
  pure roots

/-- One ABI name/selector paired with its reusable compiled source root. -/
structure CompiledStaticWordRoot where
  metadata : Abi.V1.MethodMetadata
  entry : CompiledEntry

/-- Sealed ordered ABI artifact for the exported Static Word source profile. -/
structure CompiledStaticWordProgram where private mk ::
  private compiledRoots : List CompiledStaticWordRoot

namespace CompiledStaticWordProgram

/-- ABI roots in deterministic public-interface order. -/
def roots (compiled : CompiledStaticWordProgram) :
    List CompiledStaticWordRoot :=
  compiled.compiledRoots

/-- Number of ABI methods retained by the artifact. -/
def count (compiled : CompiledStaticWordProgram) : Nat :=
  compiled.compiledRoots.length

/-- Find the unique root for a four-byte selector.  Discovery rejects selector
collisions, so a successful result is unambiguous. -/
def rootForSelector? (compiled : CompiledStaticWordProgram)
    (selector : Abi.V1.Selector) : Option CompiledStaticWordRoot :=
  compiled.compiledRoots.find? fun root =>
    root.metadata.selector == selector

/-- Selected backends in deterministic ABI order. -/
def backends (compiled : CompiledStaticWordProgram) : List Backend :=
  compiled.compiledRoots.map fun root => root.entry.backend

/-- Whether ABI root compilation selected more than one runtime. -/
def usesMixedBackends (compiled : CompiledStaticWordProgram) : Bool :=
  decide (compiled.backends.eraseDups.length > 1)

end CompiledStaticWordProgram

/-- An ABI-root compilation failure retains both source identity and the exact
public export spelling used to derive its signature and selector. -/
structure StaticWordRootCompileError where
  index : Nat
  publicName : String
  seed : Seed
  error : CompileError
  deriving Repr

/-- Static Word compilation failures preserve discovery separately from the
exact exported root whose specialization or backend selection failed. -/
inductive StaticWordCompileError where
  | checking (errors : List ProgramCheckError)
  | discovery (error : StaticWordRootError)
  | root (error : StaticWordRootCompileError)
  deriving Repr

private def compileStaticWordRootsFrom (program : CheckedProgram)
    (options : CompileOptions) : Nat → List StaticWordRoot →
      Except StaticWordRootCompileError (List CompiledStaticWordRoot)
  | _, [] => .ok []
  | index, root :: rest => do
      let entry ← (compileChecked program root.seed options).mapError fun error =>
        { index, publicName := root.metadata.name.text,
          seed := root.seed, error }
      let compiledRest ←
        compileStaticWordRootsFrom program options (index + 1) rest
      pure ({ metadata := root.metadata, entry } :: compiledRest)

/-- Discover and compile all exported Static Word roots from an already checked
program and explicit entry module. -/
def compileStaticWordChecked (program : CheckedProgram)
    (entryModule : Workspace.ModuleId) (options : CompileOptions := {}) :
    Except StaticWordCompileError CompiledStaticWordProgram := do
  let roots ← (discoverStaticWordRoots program entryModule).mapError
    StaticWordCompileError.discovery
  let compiled ← (compileStaticWordRootsFrom program options 0 roots).mapError
    StaticWordCompileError.root
  pure ⟨compiled⟩

/-- Pointwise certificate for an exported Static Word artifact.  Besides the
exact single-root compilation, it retains the public ABI metadata paired with
that root. -/
def CompiledStaticWordProgram.Certifies
    (compiled : CompiledStaticWordProgram) (program : CheckedProgram)
    (roots : List StaticWordRoot) (options : CompileOptions) : Prop :=
  Workspace.ListCorresponds
    (fun root compiledRoot =>
      compiledRoot.metadata = root.metadata ∧
        compileChecked program root.seed options = .ok compiledRoot.entry)
    roots compiled.roots

private theorem compileStaticWordRootsFrom_certifies
    (program : CheckedProgram) (options : CompileOptions)
    (start : Nat) (roots : List StaticWordRoot)
    (compiled : List CompiledStaticWordRoot)
    (success : compileStaticWordRootsFrom program options start roots =
      .ok compiled) :
    Workspace.ListCorresponds
      (fun root compiledRoot =>
        compiledRoot.metadata = root.metadata ∧
          compileChecked program root.seed options = .ok compiledRoot.entry)
      roots compiled := by
  induction roots generalizing start compiled with
  | nil =>
      simp [compileStaticWordRootsFrom] at success
      cases success
      exact .nil
  | cons root roots induction =>
      simp only [compileStaticWordRootsFrom] at success
      cases entryResult : compileChecked program root.seed options with
      | error error =>
          rw [entryResult] at success
          cases success
      | ok entry =>
          simp only [entryResult, Except.mapError, bind, Except.bind] at success
          cases restResult : compileStaticWordRootsFrom program options
              (start + 1) roots with
          | error error =>
              rw [restResult] at success
              cases success
          | ok rest =>
              simp [restResult] at success
              cases success
              exact .cons ⟨rfl, entryResult⟩
                (induction (start := start + 1) (compiled := rest) restResult)

/-- Successful checked ABI compilation exposes discovery and exact
single-root compilation certificates in one deterministic order. -/
theorem compileStaticWordChecked_certifies
    (program : CheckedProgram) (entryModule : Workspace.ModuleId)
    (options : CompileOptions) (compiled : CompiledStaticWordProgram)
    (success : compileStaticWordChecked program entryModule options =
      .ok compiled) :
    ∃ roots,
      discoverStaticWordRoots program entryModule = .ok roots ∧
        compiled.Certifies program roots options := by
  unfold compileStaticWordChecked at success
  cases discovered : discoverStaticWordRoots program entryModule with
  | error error =>
      rw [discovered] at success
      cases success
  | ok roots =>
      rw [discovered] at success
      simp only [Except.mapError, bind, Except.bind] at success
      cases compiledResult : compileStaticWordRootsFrom program options 0 roots with
      | error error =>
          rw [compiledResult] at success
          cases success
      | ok compiledRoots =>
          rw [compiledResult] at success
          cases success
          exact ⟨roots, rfl,
            compileStaticWordRootsFrom_certifies program options 0 roots
              compiledRoots compiledResult⟩

private theorem certified_static_word_member
    {program : CheckedProgram} {options : CompileOptions}
    {roots : List StaticWordRoot} {compiled : List CompiledStaticWordRoot}
    (certified : Workspace.ListCorresponds
      (fun root compiledRoot =>
        compiledRoot.metadata = root.metadata ∧
          compileChecked program root.seed options = .ok compiledRoot.entry)
      roots compiled) {compiledRoot : CompiledStaticWordRoot}
    (member : compiledRoot ∈ compiled) :
    ∃ root, root ∈ roots ∧ compiledRoot.metadata = root.metadata ∧
      compileChecked program root.seed options = .ok compiledRoot.entry := by
  induction certified with
  | nil => simp at member
  | @cons root head roots tail headCertified tailCertified induction =>
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          subst head
          exact ⟨root, by simp, headCertified⟩
      | inr tailMember =>
          obtain ⟨selected, selectedMember, metadata, compiledEntry⟩ :=
            induction tailMember
          exact ⟨selected, by simp [selectedMember], metadata, compiledEntry⟩

/-- Every exported ABI root has the same canonical and public-result
certificates as its underlying single-root compiler artifact. -/
theorem compileStaticWordChecked_root_certificates
    (program : CheckedProgram) (entryModule : Workspace.ModuleId)
    (options : CompileOptions) (compiled : CompiledStaticWordProgram)
    (success : compileStaticWordChecked program entryModule options =
      .ok compiled) (root : CompiledStaticWordRoot)
    (member : root ∈ compiled.roots) :
    root.entry.HasCanonicalRoot ∧
      root.entry.HasPublicResultProjection := by
  obtain ⟨roots, _discovered, certified⟩ :=
    compileStaticWordChecked_certifies program entryModule options compiled
      success
  obtain ⟨sourceRoot, _sourceMember, _metadata, compiledEntry⟩ :=
    certified_static_word_member certified member
  exact ⟨compileChecked_hasCanonicalRoot program sourceRoot.seed options
      root.entry compiledEntry,
    compileChecked_hasPublicResultProjection program sourceRoot.seed options
      root.entry compiledEntry⟩

/-- Check a raw workspace once, derive its canonical entry module, then
discover and compile its exported Static Word ABI roots. -/
def compileStaticWord (raw : Workspace.RawWorkspace)
    (options : CheckingOptions := {}) :
    Except StaticWordCompileError CompiledStaticWordProgram := do
  let (program, entryModule) ←
    (checkWorkspaceAtEntry raw options.checkingFuel).mapError
      StaticWordCompileError.checking
  compileStaticWordChecked program entryModule options.toCompileOptions

/-- Raw ABI compilation retains checker provenance for every exported root,
not merely the discovery order and selector metadata. -/
theorem compileStaticWord_root_certificates
    (raw : Workspace.RawWorkspace) (options : CheckingOptions)
    (compiled : CompiledStaticWordProgram)
    (success : compileStaticWord raw options = .ok compiled)
    (root : CompiledStaticWordRoot) (member : root ∈ compiled.roots) :
    root.entry.HasCheckedSourceWitness ∧ root.entry.HasCanonicalRoot ∧
      root.entry.HasPublicResultProjection := by
  unfold compileStaticWord at success
  cases checkedEntry : checkWorkspaceAtEntry raw options.checkingFuel with
  | error errors =>
      rw [checkedEntry] at success
      cases success
  | ok pair =>
      obtain ⟨program, entryModule⟩ := pair
      rw [checkedEntry] at success
      simp only [Except.mapError, bind, Except.bind] at success
      obtain ⟨roots, _discovered, certified⟩ :=
        compileStaticWordChecked_certifies program entryModule
          options.toCompileOptions compiled success
      obtain ⟨sourceRoot, _sourceMember, _metadata, compiledEntry⟩ :=
        certified_static_word_member certified member
      have checked := checkWorkspaceAtEntry_checked raw options.checkingFuel
        program entryModule checkedEntry
      have sourceWitness : root.entry.HasCheckedSourceWitness := by
        refine ⟨raw, options.checkingFuel, ?_⟩
        simpa [compileChecked_program program sourceRoot.seed
          options.toCompileOptions root.entry compiledEntry] using checked
      exact ⟨sourceWitness,
        compileChecked_hasCanonicalRoot program sourceRoot.seed
          options.toCompileOptions root.entry compiledEntry,
        compileChecked_hasPublicResultProjection program sourceRoot.seed
          options.toCompileOptions root.entry compiledEntry⟩

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

/-!
## Consolidated module: `Solcore.Frontend.SourceCompilerProperties`
-/

/-! Small interface laws for the restricted public source compiler. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

@[simp] theorem Invocation.coreFresh_kind (arguments : List Core.Value) :
    (Invocation.coreFresh arguments).kind = .coreValues := by
  rfl

@[simp] theorem Invocation.typedFresh_kind
    (arguments : List SourceTypedRuntime.Value) :
    (Invocation.typedFresh arguments).kind = .typedValues := by
  rfl

theorem CompiledEntry.runCore_eq_run (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store) :
    compiled.runCore arguments options store =
      compiled.run (.coreValues arguments store) options := by
  rfl

theorem CompiledEntry.runTyped_eq_run (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.runTyped arguments options state =
      compiled.run (.typedValues arguments state) options := by
  rfl

/-- A successful direct-Core facade result inherits the checked Core body's
deep result/store preservation theorem. -/
theorem CompiledEntry.run_core_done_preserves_type
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    {value : Core.Value} {finalStore : Core.Store}
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.core (.done value finalStore))) :
    compiled.SuccessfulResultHasNativeType (.core (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.run? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | done result finalStore =>
              cases ran
              simp only [CompiledEntry.SuccessfulResultHasNativeType]
              exact entry.run?_done_preserves_type arguments
                options.executionFuel store environmentTyped storeTyped exactRun
          | outOfFuel state => cases ran
          | fault error state => cases ran
  | coreRuntime entry =>
      cases result : entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | coreGeneral general =>
      cases result : general.entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | typedSource cached =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- Under the same deep invocation premise, the facade's direct-Core route
cannot expose a machine fault at any finite execution budget. -/
theorem CompiledEntry.run_core_never_faults
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (error : Core.MachineFault) (faultState : Core.State) :
    compiled.run (.coreValues arguments store) options ≠
      .ok (.core (.fault error faultState)) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      intro ran
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.run? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | done result finalStore => cases ran
          | outOfFuel state => cases ran
          | fault foundError foundState =>
              cases ran
              exact entry.run?_never_faults arguments options.executionFuel
                store environmentTyped storeTyped error faultState exactRun
  | coreRuntime entry =>
      intro ran
      cases result : entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | coreGeneral general =>
      intro ran
      cases result : general.entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | typedSource cached =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- A source-value facade result retains the exact original request's deep
boundary certificate from the cached Core observation. -/
private theorem typedSource_done_certificate
    (compiled : CompiledEntry) (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value} {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition (.typedValues arguments initial))
    (ran : compiled.run (.typedValues arguments initial) options =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepExecution arguments initial value finalState := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry | coreRuntime entry | coreGeneral entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource cached =>
      simp only [CompiledEntry.PreservationPrecondition, CompiledEntry.HasCanonicalRoot] at precondition
      simp only [Executable.OwnedBy] at owned
      cases native : cached.run root.key arguments options.inputValidationFuel options.executionFuel initial with
      | error error => simp [CompiledEntry.run, CompiledEntry.key, native, Except.mapError, Except.map] at ran
      | ok result =>
          have done : result.observation = .done value finalState := by
            simpa [CompiledEntry.run, CompiledEntry.key, native, Except.mapError, Except.map] using ran
          obtain ⟨specialized, selected, certificate⟩ :=
            SourceCoreUnifiedPreparationCertificates.run_done_specialization native done
          rw [owned.1, owned.2] at certificate
          rw [owned.2] at selected
          have rootSelected : SourceCompilationPlan.exactSpecialization plan root.key = .ok root := by
            simp [SourceCompilationPlan.exactSpecialization, precondition]
          have same : specialized = root := Except.ok.inj (selected.symm.trans rootSelected)
          subst specialized
          exact certificate

/-- Successful source-value observations have the public result type, final
heap and authentic closure/evidence boundary supplied by the cached Core run. -/
theorem CompiledEntry.run_typedSource_done_preserves_type
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition (.typedValues arguments initial))
    (ran : compiled.run (.typedValues arguments initial) options =
      .ok (.typedSource (.done value finalState))) :
    compiled.SuccessfulResultHasNativeType (.typedSource (.done value finalState)) := by
  have execution := typedSource_done_certificate compiled arguments initial options precondition ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry | coreRuntime entry | coreGeneral entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource cached =>
      exact ⟨execution.prepared, execution.final_state_safe, execution.value_safe⟩

/-- On the typed backend, the common native-type conclusion is exactly the
artifact's public source result type, not a separate runtime declaration. -/
theorem CompiledEntry.runTyped_done_has_public_resultType
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.runTyped arguments options initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedValueHasResultType value := by
  have native := compiled.run_typedSource_done_preserves_type arguments
    initial options precondition ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry | coreRuntime entry | coreGeneral entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource cached =>
      simp only [CompiledEntry.SuccessfulResultHasNativeType] at native
      refine ⟨native.executablePlan, native.prepared, ?_⟩
      exact native.value_safe.typed.outer

/-- A normally completing typed-source artifact exposes its complete
pre/post boundary certificate, including input safety and heap type-layout
extension across mutation and allocation. -/
theorem CompiledEntry.runTyped_done_has_public_deepExecution
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.runTyped arguments options initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepExecution arguments initial value finalState := by
  exact typedSource_done_certificate compiled arguments initial options precondition ran

/-- Canonical-root provenance is the only additional proof needed to use the
typed deep boundary on an already compiled artifact. -/
theorem CompiledEntry.runTyped_done_has_public_deepExecution_of_canonical
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (canonical : compiled.HasCanonicalRoot)
    (typedBackend : compiled.backend = .typedSource)
    (ran : compiled.runTyped arguments options initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepExecution arguments initial value finalState := by
  have precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial) := by
    cases compiled
    rename_i program plan root executable owned
    cases executable <;>
      simp_all [CompiledEntry.backend, CompiledEntry.HasCanonicalRoot,
        CompiledEntry.PreservationPrecondition]
  exact compiled.runTyped_done_has_public_deepExecution arguments initial
    options precondition ran

/-- A normally completing typed-source artifact exposes the full deep result,
final-heap, closure-code, and evidence certificate at its public result type. -/
theorem CompiledEntry.runTyped_done_has_public_deepResult
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.runTyped arguments options initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepResult value finalState := by
  have native := compiled.run_typedSource_done_preserves_type arguments
    initial options precondition ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry | coreRuntime entry | coreGeneral entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource cached =>
      simpa [CompiledEntry.TypedDeepResult,
        CompiledEntry.SuccessfulResultHasNativeType] using native

/-- The deep direct-Core preservation result uses the compiler's public source
result type once its checked backend projection is supplied. -/
theorem CompiledEntry.run_core_done_has_public_resultType
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    {value : Core.Value} {finalStore : Core.Store}
    (projection : compiled.HasPublicResultProjection)
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.core (.done value finalStore))) :
    compiled.CoreResultHasPublicType value finalStore := by
  have native := compiled.run_core_done_preserves_type arguments store
    options precondition ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry =>
      change SourceCoreElaboration.lowerType
        (.declaration root.declaration) root.function.inferredBodyType =
          .ok entry.elaborated.returnType at projection
      simp only [CompiledEntry.SuccessfulResultHasNativeType] at native
      obtain ⟨finalWorld, storeTyped, valueTyped⟩ := native
      simp only [CompiledEntry.CoreResultHasPublicType,
        CompiledEntry.resultType]
      exact ⟨entry.elaborated.returnType, projection, finalWorld,
        storeTyped, valueTyped⟩
  | coreRuntime entry =>
      cases result : entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | coreGeneral general =>
      cases result : general.entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
      | ok result => simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
  | typedSource cached =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- The optional-cell entry checks complete input values and supplies typed
completion, language failure and exhaustion without an extra caller premise. -/
theorem CompiledEntry.run_coreLanguageResult_hasType
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    (observation : Core.LanguageResult.Observation)
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.coreLanguageResult observation)) :
    compiled.SuccessfulResultHasNativeType (.coreLanguageResult observation) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry =>
      cases result : entry.run? arguments options.executionFuel store <;>
        simp [CompiledEntry.run, result] at ran
  | typedSource cached => simp [CompiledEntry.run, Invocation.kind] at ran
  | coreRuntime entry =>
      cases accepted : entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, accepted, Except.mapError, Except.map] at ran
      | ok result =>
          simp [CompiledEntry.run, accepted, Except.mapError, Except.map] at ran
          cases ran
          exact result.typed
  | coreGeneral general =>
      cases accepted : general.entry.run arguments options.executionFuel store with
      | error error => simp [CompiledEntry.run, accepted, Except.mapError, Except.map] at ran
      | ok result =>
          simp [CompiledEntry.run, accepted, Except.mapError, Except.map] at ran
          cases ran
          exact result.typed

/-- All finite ordinary Core outcomes retain the public source type projection. -/
theorem CompiledEntry.run_coreLanguageResult_has_public_resultType
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    (observation : Core.LanguageResult.Observation)
    (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.coreLanguageResult observation)) :
    compiled.CoreLanguageResultHasPublicType observation := by
  have typed := compiled.run_coreLanguageResult_hasType arguments store options observation ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry => simp [CompiledEntry.SuccessfulResultHasNativeType] at typed
  | typedSource cached => simp [CompiledEntry.SuccessfulResultHasNativeType] at typed
  | coreRuntime entry => exact ⟨entry.resultType, projection, typed⟩
  | coreGeneral general => exact ⟨general.entry.resultType, projection, typed⟩

/-- A successful optional-cell result has the public source result projection. -/
theorem CompiledEntry.run_coreLanguageResult_done_has_public_resultType
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store) (options : RunOptions)
    {value : Core.Value} {finalStore : Core.Store}
    (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run (.coreValues arguments store) options =
      .ok (.coreLanguageResult (.succeeded value finalStore))) :
    compiled.CoreResultHasPublicType value finalStore := by
  have typed := compiled.run_coreLanguageResult_hasType arguments store options
    (.succeeded value finalStore) ran
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry => simp [CompiledEntry.SuccessfulResultHasNativeType] at typed
  | typedSource cached => simp [CompiledEntry.SuccessfulResultHasNativeType] at typed
  | coreRuntime entry =>
      exact ⟨entry.resultType, projection, typed⟩
  | coreGeneral general => exact ⟨general.entry.resultType, projection, typed⟩

/-- Whole-compiler successful-result preservation. One theorem covers both
invocation interfaces without erasing their value/store domains.
The precondition is substantial only for direct Core (deep values/store) and
for the typed backend's sealed canonical-root provenance. -/
theorem CompiledEntry.run_preserves_successful_result_native_type
    (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions) (result : ExecutionResult)
    (precondition : compiled.PreservationPrecondition invocation)
    (ran : compiled.run invocation options = .ok result) :
    compiled.SuccessfulResultHasNativeType result := by
  cases result with
  | core result =>
      cases result with
      | done value finalStore =>
          cases invocation with
          | coreValues arguments store =>
              exact compiled.run_core_done_preserves_type arguments store
                options precondition ran
          | typedValues arguments state =>
              cases compiled
              rename_i program plan root executable owned
              cases executable with
              | core entry | coreRuntime entry | coreGeneral entry =>
                  simp [CompiledEntry.run, Invocation.kind] at ran
              | typedSource cached =>
                  cases native : cached.run root.key arguments options.inputValidationFuel options.executionFuel state <;>
                    simp [CompiledEntry.run, CompiledEntry.key, native, Except.mapError, Except.map] at ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | typedSource result =>
      cases result with
      | done value finalState =>
          cases invocation with
          | coreValues arguments store =>
              cases compiled
              rename_i program plan root executable owned
              cases executable with
              | core entry =>
                  simp only [CompiledEntry.run] at ran
                  split at ran <;> cases ran
              | coreRuntime entry =>
                  cases result : entry.run arguments options.executionFuel store <;>
                    simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
              | coreGeneral general =>
                  cases result : general.entry.run arguments options.executionFuel store <;>
                    simp [CompiledEntry.run, result, Except.mapError, Except.map] at ran
              | typedSource cached =>
                  simp [CompiledEntry.run, Invocation.kind] at ran
          | typedValues arguments initial =>
              exact compiled.run_typedSource_done_preserves_type arguments
                initial options precondition ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | coreLanguageResult observation =>
      cases invocation with
      | coreValues arguments store =>
          exact compiled.run_coreLanguageResult_hasType arguments store options observation ran
      | typedValues arguments state =>
          cases compiled
          rename_i program plan root executable owned
          cases executable with
          | core entry | coreRuntime entry | coreGeneral entry => simp [CompiledEntry.run, Invocation.kind] at ran
          | typedSource cached =>
              cases native : cached.run root.key arguments options.inputValidationFuel options.executionFuel state <;>
                simp [CompiledEntry.run, CompiledEntry.key, native, Except.mapError, Except.map] at ran

/-- A source-value artifact rejects Core-domain inputs before Core execution
starts. In particular, execution fuel cannot turn this boundary failure into
a runtime result. -/
theorem CompiledEntry.runCore_of_typedSource (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .typedSource) :
    compiled.runCore arguments options store =
      .error (.invocationKindMismatch .typedSource .coreValues) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runCore,
    CompiledEntry.run, Invocation.kind]

/-- A direct-Core artifact rejects source-typed inputs before execution. -/
theorem CompiledEntry.runTyped_of_core (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .core) :
    compiled.runTyped arguments options state =
      .error (.invocationKindMismatch .core .typedValues) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run, Invocation.kind]

/-- Source faults and exhaustion retain the historical result carrier.
An internal adapter failure remains a distinct facade error. -/
theorem CompiledEntry.runTyped_outcome_of_typedSource (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .typedSource) :
    (∃ result, compiled.runTyped arguments options state = .ok (.typedSource result)) ∨
      (∃ error, compiled.runTyped arguments options state = .error (.typedSourceAdapter error)) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | core entry | coreRuntime entry | coreGeneral entry =>
      simp [CompiledEntry.backend] at hbackend
  | typedSource cached =>
      cases native : cached.run root.key arguments options.inputValidationFuel options.executionFuel state with
      | error error => exact .inr ⟨error, by simp [CompiledEntry.runTyped, CompiledEntry.run,
          CompiledEntry.key, native, Except.mapError, Except.map]⟩
      | ok result => exact .inl ⟨result.observation, by simp [CompiledEntry.runTyped, CompiledEntry.run,
          CompiledEntry.key, native, Except.mapError, Except.map]⟩

/-- Successful checkpoint creation projects to the historical public result. -/
theorem CompiledEntry.runTyped_ok_of_checkpoint (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState) (checkpoint : CompiledEntry.TypedCheckpoint compiled)
    (ran : compiled.runTypedWithCheckpoint arguments options state = .ok checkpoint) :
    compiled.runTyped arguments options state = .ok (.typedSource checkpoint.observation) := by
  unfold CompiledEntry.runTypedWithCheckpoint at ran
  split at ran
  next cached selected =>
    split at ran
    · cases ran
    · next result native =>
      cases ran
      simp [CompiledEntry.runTyped, CompiledEntry.run, selected, CompiledEntry.TypedCheckpoint.observation,
        native, Except.mapError, Except.map]
  next => cases ran

/-- Core-domain execution retains either its direct result, its decoded
language result, or its explicit input-boundary rejection. -/
theorem CompiledEntry.runCore_outcome_of_core (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .core) :
    (∃ result, compiled.runCore arguments options store = .ok (.core result)) ∨
      (∃ observation, compiled.runCore arguments options store =
        .ok (.coreLanguageResult observation)) ∨
      (∃ error, compiled.runCore arguments options store = .error error) := by
  cases compiled
  rename_i program plan root executable owned
  cases executable with
  | typedSource cached => simp [CompiledEntry.backend] at hbackend
  | core entry =>
      cases exactRun : entry.run? arguments options.executionFuel store with
      | none =>
          exact .inr (.inr ⟨.coreInputTypesMismatch entry.elaborated.inputs.values
            (arguments.map Core.Value.type), by simp [CompiledEntry.runCore, CompiledEntry.run, exactRun]⟩)
      | some result =>
          exact .inl ⟨result, by simp [CompiledEntry.runCore, CompiledEntry.run, exactRun]⟩
  | coreRuntime entry =>
      cases accepted : entry.run arguments options.executionFuel store with
      | error error =>
          exact .inr (.inr ⟨.coreRuntimeInput error, by simp [CompiledEntry.runCore, CompiledEntry.run,
            accepted, Except.mapError, Except.map]⟩)
      | ok result =>
          exact .inr (.inl ⟨result.observation, by simp [CompiledEntry.runCore,
            CompiledEntry.run, accepted, Except.mapError, Except.map]⟩)
  | coreGeneral general =>
      cases accepted : general.entry.run arguments options.executionFuel store with
      | error error =>
          exact .inr (.inr ⟨.coreGeneralInput error, by simp [CompiledEntry.runCore, CompiledEntry.run,
            accepted, Except.mapError, Except.map]⟩)
      | ok result =>
          exact .inr (.inl ⟨result.observation, by simp [CompiledEntry.runCore,
            CompiledEntry.run, accepted, Except.mapError, Except.map]⟩)

theorem run_of_compiled (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits) (compiled : CompiledEntry)
    (compiledOk : compile raw seed limits.toCheckingOptions = .ok compiled) :
    run raw seed invocation limits =
      (compiled.run invocation limits.toRunOptions).mapError Error.execution := by
  unfold run
  rw [compiledOk]
  change (do
    let compiled ← Except.ok compiled
    (compiled.run invocation limits.toRunOptions).mapError Error.execution) = _
  rfl

/-- Raw-workspace compilation exposes the same canonical-root certificate as
the already-checked compile-once path. -/
theorem compile_hasCanonicalRoot
    (raw : Workspace.RawWorkspace) (seed : Seed) (options : CheckingOptions)
    (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.HasCanonicalRoot := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      exact compileChecked_hasCanonicalRoot program seed
        options.toCompileOptions compiled compiledOk

/-- Raw-workspace compilation retains the same public/backend result-type
projection certificate as checked-program compilation. -/
theorem compile_hasPublicResultProjection
    (raw : Workspace.RawWorkspace) (seed : Seed) (options : CheckingOptions)
    (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.HasPublicResultProjection := by
  unfold compile at compiledOk
  cases checked : checkProgram raw options.checkingFuel with
  | error errors =>
      rw [checked] at compiledOk
      cases compiledOk
  | ok program =>
      rw [checked] at compiledOk
      simp only [Except.mapError, bind, Except.bind] at compiledOk
      exact compileChecked_hasPublicResultProjection program seed
        options.toCompileOptions compiled compiledOk

/-- A compiler-produced direct-Core entry returns a deeply typed value and
final store at the public source result projection. -/
theorem compileChecked_runCore_done_has_public_resultType
    (program : CheckedProgram) (seed : Seed)
    (compileOptions : CompileOptions) (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (arguments : List Core.Value) (store : Core.Store)
    (runOptions : RunOptions) {value : Core.Value}
    {finalStore : Core.Store}
    (precondition : compiled.PreservationPrecondition
      (.coreValues arguments store))
    (ran : compiled.runCore arguments runOptions store =
      .ok (.core (.done value finalStore))) :
    compiled.CoreResultHasPublicType value finalStore := by
  exact compiled.run_core_done_has_public_resultType arguments store
    runOptions (compileChecked_hasPublicResultProjection program seed
      compileOptions compiled compiledOk) precondition ran

/-- For a compiler-produced typed backend, the root provenance required by
the backend-native preservation theorem is automatic. -/
theorem compileChecked_typed_preservation_precondition
    (program : CheckedProgram) (seed : Seed) (options : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.PreservationPrecondition (.typedValues arguments state) := by
  have canonical := compileChecked_hasCanonicalRoot program seed options
    compiled compiledOk
  cases compiled
  rename_i checked plan root executable owned
  cases executable <;>
    simp_all [CompiledEntry.backend, CompiledEntry.PreservationPrecondition]

/-- The same provenance is available after one-shot raw-workspace
compilation, independently of the chosen validation and execution fuels. -/
theorem compile_typed_preservation_precondition
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed options = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (state : SourceTypedRuntime.RuntimeState) :
    compiled.PreservationPrecondition (.typedValues arguments state) := by
  have canonical := compile_hasCanonicalRoot raw seed options compiled compiledOk
  cases compiled
  rename_i checked plan root executable owned
  cases executable <;>
    simp_all [CompiledEntry.backend, CompiledEntry.PreservationPrecondition]

/-- A compiler-produced typed entry needs no caller-supplied root certificate:
normal completion has the artifact's public source result type. -/
theorem compileChecked_runTyped_done_has_public_resultType
    (program : CheckedProgram) (seed : Seed) (compileOptions : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : compiled.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedValueHasResultType value := by
  exact compiled.runTyped_done_has_public_resultType arguments initial
    runOptions
    (compileChecked_typed_preservation_precondition program seed
      compileOptions compiled compiledOk typedBackend arguments initial)
    ran

/-- The same compiler-produced typed entry exposes the stronger deep
prepared-plan certificate without any caller-supplied provenance proof. -/
theorem compileChecked_runTyped_done_has_public_deepResult
    (program : CheckedProgram) (seed : Seed) (compileOptions : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : compiled.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepResult value finalState := by
  exact compiled.runTyped_done_has_public_deepResult arguments initial
    runOptions
    (compileChecked_typed_preservation_precondition program seed
      compileOptions compiled compiledOk typedBackend arguments initial)
    ran

/-- Compiler-produced typed artifacts also expose the complete initial/input
and final/result certificate, including heap type-layout extension. -/
theorem compileChecked_runTyped_done_has_public_deepExecution
    (program : CheckedProgram) (seed : Seed) (compileOptions : CompileOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : compiled.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepExecution arguments initial value finalState := by
  exact compiled.runTyped_done_has_public_deepExecution arguments initial
    runOptions
    (compileChecked_typed_preservation_precondition program seed
      compileOptions compiled compiledOk typedBackend arguments initial)
    ran

/-- Every typed member of a checked multi-root artifact inherits the complete
deep execution certificate. -/
theorem compileManyChecked_entry_runTyped_done_has_public_deepExecution
    (program : CheckedProgram) (seeds : List Seed)
    (compileOptions : CompileOptions) (compiled : CompiledProgram)
    (compiledOk : compileManyChecked program seeds compileOptions = .ok compiled)
    (entry : CompiledEntry) (member : entry ∈ compiled.entries)
    (typedBackend : entry.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : entry.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    entry.TypedDeepExecution arguments initial value finalState := by
  have certificates := compileManyChecked_entry_certificates program seeds
    compileOptions compiled compiledOk entry member
  exact entry.runTyped_done_has_public_deepExecution_of_canonical arguments
    initial runOptions certificates.1 typedBackend ran

/-- Raw-workspace multi-root compilation retains the same deep runtime
certificate for every typed member. -/
theorem compileMany_entry_runTyped_done_has_public_deepExecution
    (raw : Workspace.RawWorkspace) (seeds : List Seed)
    (compileOptions : CheckingOptions) (compiled : CompiledProgram)
    (compiledOk : compileMany raw seeds compileOptions = .ok compiled)
    (entry : CompiledEntry) (member : entry ∈ compiled.entries)
    (typedBackend : entry.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : entry.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    entry.TypedDeepExecution arguments initial value finalState := by
  have certificates := compileMany_entry_certificates raw seeds compileOptions
    compiled compiledOk entry member
  exact entry.runTyped_done_has_public_deepExecution_of_canonical arguments
    initial runOptions certificates.2.1 typedBackend ran

/-- Automatic conventional-entry compilation lifts the typed deep certificate
without exposing its internally selected checked program or seed. -/
theorem compileEntry_runTyped_done_has_public_deepExecution
    (raw : Workspace.RawWorkspace) (compileOptions : CheckingOptions)
    (compiled : CompiledEntry)
    (compiledOk : compileEntry raw compileOptions = .ok compiled)
    (typedBackend : compiled.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : compiled.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    compiled.TypedDeepExecution arguments initial value finalState := by
  have certificates := compileEntry_certificates raw compileOptions compiled
    compiledOk
  exact compiled.runTyped_done_has_public_deepExecution_of_canonical arguments
    initial runOptions certificates.2.1 typedBackend ran

/-- Every exported Static Word root which selects the typed backend inherits
the same public pre/post certificate as an ordinary compiled entry. -/
theorem compileStaticWord_root_runTyped_done_has_public_deepExecution
    (raw : Workspace.RawWorkspace) (compileOptions : CheckingOptions)
    (compiled : CompiledStaticWordProgram)
    (compiledOk : compileStaticWord raw compileOptions = .ok compiled)
    (root : CompiledStaticWordRoot) (member : root ∈ compiled.roots)
    (typedBackend : root.entry.backend = .typedSource)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (runOptions : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (ran : root.entry.runTyped arguments runOptions initial =
      .ok (.typedSource (.done value finalState))) :
    root.entry.TypedDeepExecution arguments initial value finalState := by
  have certificates := compileStaticWord_root_certificates raw compileOptions
    compiled compiledOk root member
  exact root.entry.runTyped_done_has_public_deepExecution_of_canonical arguments
    initial runOptions certificates.2.1 typedBackend ran

/-- End-to-end one-shot execution inherits successful-result preservation from
the exact artifact produced in its compile phase. -/
theorem run_of_compiled_preserves_successful_result_native_type
    (raw : Workspace.RawWorkspace) (seed : Seed) (invocation : Invocation)
    (limits : Limits) (compiled : CompiledEntry) (result : ExecutionResult)
    (compiledOk : compile raw seed limits.toCheckingOptions = .ok compiled)
    (precondition : compiled.PreservationPrecondition invocation)
    (ran : SourceCompiler.run raw seed invocation limits = .ok result) :
    compiled.SuccessfulResultHasNativeType result := by
  rw [run_of_compiled raw seed invocation limits compiled compiledOk] at ran
  cases executed : compiled.run invocation limits.toRunOptions with
  | error error =>
      rw [executed] at ran
      cases ran
  | ok actual =>
      rw [executed] at ran
      cases ran
      exact compiled.run_preserves_successful_result_native_type invocation
        limits.toRunOptions result precondition executed

/-- Whole-program checking failures retain their phase and exact payload; no
seed resolution or specialization step can relabel them. -/
theorem compile_of_checking_error (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (errors : List ProgramCheckError)
    (failed : checkProgram raw options.checkingFuel = .error errors) :
    compile raw seed options = .error (.checking errors) := by
  unfold compile
  rw [failed]
  rfl

/-- Seed-resolution failures are reported before the worklist is entered. -/
theorem compileChecked_of_seed_error (program : CheckedProgram) (seed : Seed)
    (options : CompileOptions) (error : SourceProgramExecution.SeedError)
    (failed : SourceProgramExecution.resolveSeed program seed = .error error) :
    compileChecked program seed options = .error (.seed error) := by
  unfold compileChecked
  rw [failed]
  rfl

/-- Zero distinct-specialization budget exposes the first canonical root and
its one-element pending frontier.  Staging fuel is independent and is never
consulted on this path. -/
theorem compileChecked_zero_specializationBudget
    (program : CheckedProgram) (seed : Seed)
    (request : SourceSpecializationWorklist.Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (stagingFuel : Nat)
    (seedOk : SourceProgramExecution.resolveSeed program seed = .ok request)
    (resolved : SourceSpecializationWorklist.resolveRequest program request =
      .ok specialized) :
    compileChecked program seed {
      specializationBudget := 0
      stagingFuel
    } = .error (.specializationBudgetExhausted specialized.key 1) := by
  unfold compileChecked
  rw [seedOk]
  simp only [Except.mapError, bind, Except.bind]
  rw [SourceSpecializationWorklist.run_zero_single program request specialized
    resolved]
  rfl

/-- Raw-workspace compilation preserves the root identity fixed after checking
and exact seed resolution. -/
theorem compile_key_of_resolved (raw : Workspace.RawWorkspace) (seed : Seed)
    (options : CheckingOptions) (program : CheckedProgram)
    (request : SourceSpecializationWorklist.Request)
    (specialized : SourceSpecialization.SpecializedFunction)
    (compiled : CompiledEntry)
    (checked : checkProgram raw options.checkingFuel = .ok program)
    (seedOk : SourceProgramExecution.resolveSeed program seed = .ok request)
    (resolved : SourceSpecializationWorklist.resolveRequest program request =
      .ok specialized)
    (compiledOk : compile raw seed options = .ok compiled) :
    compiled.key = specialized.key := by
  unfold compile at compiledOk
  rw [checked] at compiledOk
  simp only [Except.mapError, bind, Except.bind] at compiledOk
  exact compileChecked_key_of_resolved program seed options.toCompileOptions
    request specialized compiled seedOk resolved compiledOk

/-- One-shot execution preserves an exact compilation failure and never
reclassifies it as a runtime-domain failure. -/
theorem run_of_compile_error (raw : Workspace.RawWorkspace) (seed : Seed)
    (invocation : Invocation) (limits : Limits) (error : CompileError)
    (failed : compile raw seed limits.toCheckingOptions = .error error) :
    run raw seed invocation limits = .error (.compilation error) := by
  unfold run
  rw [failed]
  rfl

end Solcore.Frontend.SourceCompiler
