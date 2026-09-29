import Solcore.Frontend.SourceProgramExecution
import Solcore.Frontend.SourceSpecializationWorklist
import Solcore.Frontend.SourceTypedRuntime
import Solcore.Frontend.SourceRuntimeLinking
import Solcore.Frontend.SourceRuntimeDeepProperties
import Solcore.Core.Safety
import Solcore.Frontend.SourceCoreDirectLinking
import Solcore.Frontend.SourceRuntimeEntryDeepProperties
import Solcore.Frontend.ProgramInterfaces
import Solcore.Abi.StaticWord

/-!
The restricted public source compiler boundary.

Single-root compilation resolves a ground root and discovers its finite
specialization plan.  The whole-program facade can also discover conventional
`main` and exported Static Word ABI roots, or compile an ordered explicit root
set after checking the workspace once.  Automatic selection prefers direct
Core and otherwise uses the source-typed runtime.  Clients may instead request
an exact backend; the structural runtime call graph remains available through
that explicit preference for compatibility testing and comparison.  Resulting
artifacts can be run repeatedly without repeating checking or specialization.

Core stores/values and source-typed heaps/values are intentionally separate
invocation carriers.  This boundary does not guess a conversion between them.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

open TypeSystem

abbrev SeedTarget := SourceProgramExecution.SeedTarget
abbrev Seed := SourceProgramExecution.Seed

/-- The exact runtime selected for a compiled root. -/
inductive Backend where
  | core
  | callGraph
  | typedSource
  deriving Repr, BEq, DecidableEq

/-- Backend policy for one compilation.  Automatic selection deliberately
keeps the legacy Core path first but otherwise chooses the broader typed-source
runtime.  The finite call graph is retained as an explicit comparison target. -/
inductive BackendPreference where
  | automatic
  | core
  | callGraph
  | typedSource
  deriving Repr, BEq, DecidableEq

namespace BackendPreference

/-- The exact backend requested by a non-automatic preference. -/
def requested? : BackendPreference → Option Backend
  | .automatic => none
  | .core => some .core
  | .callGraph => some .callGraph
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
  | callGraph (error : SourceRuntimeLinking.Error)
  | typedSource (error : SourceTypedRuntime.RuntimeError)
  deriving Repr

namespace BackendRejection

def backend : BackendRejection → Backend
  | .core _ => .core
  | .callGraph _ => .callGraph
  | .typedSource _ => .typedSource

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
  | publicCoreResultMismatch (expected actual : Core.Ty)
  | publicGraphResultMismatch (expected actual : Ty)
  | noBackend (rejections : List BackendRejection)
  | backendRejected (rejection : BackendRejection)
  deriving Repr

/-- Backend-specific payload retained behind the compiled artifact's private
constructor. -/
private inductive Executable where
  | core (entry : SourceCoreDirectLinking.LinkedEntry)
  | callGraph (entry : SourceRuntimeLinking.LinkedEntry)
  | typedSource
  deriving Repr

private def Executable.backend : Executable → Backend
  | .core _ => .core
  | .callGraph _ => .callGraph
  | .typedSource => .typedSource

private def Executable.HasPublicResultProjection
    (root : SourceSpecialization.SpecializedFunction) : Executable → Prop
  | .core entry =>
      SourceCoreElaboration.lowerType
        (.declaration root.declaration) root.function.inferredBodyType =
          .ok entry.elaborated.returnType
  | .callGraph entry =>
      root.function.inferredBodyType = entry.sourceBodyType
  | .typedSource => True

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

/-- The retained root is the unique specialization with the canonical seed
key.  Successful compilation establishes this provenance fact; it is kept
explicit because the sealed artifact's constructor itself carries no proof
fields. -/
def HasCanonicalRoot (compiled : CompiledEntry) : Prop :=
  compiled.plan.specializations.filter (fun candidate =>
    decide (candidate.key = compiled.root.key)) = [compiled.root]

/-- The retained source program really came from a successful raw-workspace
check. This provenance is not automatic for `compileChecked`, whose caller can
provide an arbitrary `CheckedProgram` record. -/
def HasCheckedSourceWitness (compiled : CompiledEntry) : Prop :=
  ∃ raw fuel, checkProgram raw fuel = .ok compiled.program

/-- The sealed plan passed the typed-source runtime's executable-profile
preflight. Successful compilation guarantees this when that backend is
selected; it is not asserted for Core or graph artifacts. -/
def HasValidatedTypedPlan (compiled : CompiledEntry) : Prop :=
  SourceTypedRuntime.validateExecutablePlanEvidence compiled.program
    compiled.plan = .ok ()

/-- A source-typed runtime value has this artifact's public source result type
in the complete executable plan deterministically prepared from the sealed
specialization plan.  This includes first-class globals discovered through
selected methods.  It does not validate a closure body or heap. -/
def TypedValueHasResultType (compiled : CompiledEntry)
    (value : SourceTypedRuntime.Value) : Prop :=
  value.HasPreparedType compiled.program compiled.plan compiled.resultType

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
          Core.StoreHasTypes finalWorld finalStore ∧
            Core.RuntimeValueHasType finalWorld value publicType
  | .callGraph _ | .typedSource => False

/-- The finite graph's shallow value tag is the projection of the compiler's
public result type, in the selected checked runtime table. -/
def GraphValueHasPublicType (compiled : CompiledEntry)
    (value : SourceRuntime.Value) : Prop :=
  match compiled.executable with
  | .callGraph entry =>
      ∃ publicType,
        SourceRuntimeLinking.lowerType compiled.resultType = .ok publicType ∧
          SourceRuntime.Value.HasType entry.program.program value publicType
  | .core _ | .typedSource => False

/-- Semantic graph input premise for a whole-language deep preservation
theorem. A shallow runtime tag alone cannot validate a supplied Core closure
or an arbitrary initial store. -/
def GraphDeepInput (compiled : CompiledEntry)
    (arguments : List Core.Value) (store : Core.Store) : Prop :=
  match compiled.executable with
  | .callGraph entry =>
      ∃ world,
        Core.RuntimeEnvironmentHasTypes world arguments
          (entry.inputs.map Prod.snd) ∧
        Core.StoreHasTypes world store
  | .core _ | .typedSource => False

/-- The exact selected-definition premise consumed by graph evaluator safety
proofs. Successful linking certifies both table checking and signature
identity, so only deep caller inputs and store typing remain external. -/
def GraphRuntimeDeepInput (compiled : CompiledEntry)
    (arguments : List Core.Value) (store : Core.Store) : Prop :=
  match compiled.executable with
  | .callGraph entry =>
      ∃ world definition,
        entry.program.RuntimeInputsHaveType entry.key arguments store
          definition world
  | .core _ | .typedSource => False

/-- Deep finite-graph result and final-store typing at the public source
result projection, retaining extension of the caller's initial Core world.
Unlike the shallow graph result tag, this validates source closures and their
captures as well as Core-projectable values. -/
def GraphDeepResult (compiled : CompiledEntry)
    (initialWorld : Core.StoreTyping) (value : SourceRuntime.Value)
    (finalStore : Core.Store) : Prop :=
  match compiled.executable with
  | .callGraph entry =>
      ∃ publicType finalWorld,
        SourceRuntimeLinking.lowerType compiled.resultType = .ok publicType ∧
        Core.WorldExtends initialWorld finalWorld ∧
        Core.StoreHasTypes finalWorld finalStore ∧
        SourceRuntime.Value.GraphHasType entry.program.program finalWorld
          value publicType
  | .core _ | .typedSource => False

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

/-- The extra semantic premise needed to lift executable runtime checks to a
preservation theorem.  Direct Core needs genuinely typed values and store;
the graph runtime enforces its successful result tag dynamically, while the
typed-source runtime needs the retained canonical-root certificate. -/
def PreservationPrecondition (compiled : CompiledEntry) : Invocation → Prop
  | .coreValues arguments store =>
      match compiled.executable with
      | .core entry =>
          ∃ world,
            Core.RuntimeEnvironmentHasTypes world arguments
                entry.elaborated.inputs.values ∧
              Core.StoreHasTypes world store
      | .callGraph _ => True
      | .typedSource => False
  | .typedValues _ _ =>
      match compiled.executable with
      | .typedSource => compiled.HasCanonicalRoot
      | .core _ | .callGraph _ => False

/-- Successful finite-graph results carry the result type declared by the
runtime table selected for that exact entry. -/
def GraphResultHasType (checked : SourceRuntime.CheckedProgram)
    (entry : SourceRuntime.Key) : SourceRuntime.RunResult → Prop
  | .done value _ =>
      ∃ signature,
        checked.entrySignature? entry = some signature ∧
          SourceRuntime.Value.HasType checked.program value
            signature.resultType
  | .outOfFuel _ | .fault _ _ => True

/-- Backend-native typing for every successful result carrier.  The direct
Core branch is deep and includes final-store typing; finite-graph and
typed-source branches currently record only their runtime-checked result tags.
They do not yet claim closure/capture or final store/heap preservation.  Fault
and exhaustion cases are intentionally outside this predicate. -/
def SuccessfulResultHasNativeType (compiled : CompiledEntry) : ExecutionResult → Prop
  | .core (.done value finalStore) =>
      match compiled.executable with
      | .core entry =>
          ∃ finalWorld,
            Core.StoreHasTypes finalWorld finalStore ∧
              Core.RuntimeValueHasType finalWorld value
                entry.elaborated.returnType
      | .callGraph _ | .typedSource => False
  | .core (.outOfFuel _) | .core (.fault _ _) => True
  | .callGraph result@(.done _ _) =>
      match compiled.executable with
      | .core entry =>
          match entry.runtime with
          | some checked => GraphResultHasType checked entry.key result
          | none => False
      | .callGraph entry => GraphResultHasType entry.program entry.key result
      | .typedSource => False
  | .callGraph (.outOfFuel _) | .callGraph (.fault _ _) => True
  | .typedSource (.done value _) =>
      match compiled.executable with
      | .typedSource =>
          value.HasPreparedType compiled.program compiled.plan
            compiled.root.function.inferredBodyType
      | .core _ | .callGraph _ => False
  | .typedSource (.outOfFuel _) | .typedSource (.fault _ _) => True

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
        compiled.program compiled.plan compiled.root.key arguments
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
by the typed runtime's successful-result preservation theorem. -/
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

private def selectCoreBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat) :
    Except CompileError Executable :=
  let complete : SourceSpecializationWorklist.Outcome := .complete plan
  match SourceCoreDirectLinking.linkWithStagingFuel program complete
      stagingFuel with
  | .ok linked =>
      match linked.entries with
      | [entry] => .ok (.core entry)
      | entries => .error (.backendEntryCountMismatch .core entries.length)
  | .error error => .error (.backendRejected (.core error))

private def selectCallGraphBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) :
    Except CompileError Executable :=
  let complete : SourceSpecializationWorklist.Outcome := .complete plan
  match SourceRuntimeLinking.link program complete with
  | .ok linked =>
      match linked.entries with
      | [entry] => .ok (.callGraph entry)
      | entries => .error
          (.backendEntryCountMismatch .callGraph entries.length)
  | .error error => .error (.backendRejected (.callGraph error))

private def selectTypedSourceBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) :
    Except CompileError Executable :=
  match SourceTypedRuntime.validateExecutablePlanEvidence program plan with
  | .ok _ => .ok .typedSource
  | .error error => .error (.backendRejected (.typedSource error))

private def selectBackend (program : CheckedProgram)
    (plan : SourceSpecializationWorklist.Plan) (stagingFuel : Nat)
    (preference : BackendPreference) : Except CompileError Executable :=
  match preference with
  | .core => selectCoreBackend program plan stagingFuel
  | .callGraph => selectCallGraphBackend program plan
  | .typedSource => selectTypedSourceBackend program plan
  | .automatic =>
      match selectCoreBackend program plan stagingFuel with
      | .ok executable => .ok executable
      | .error (.backendRejected (.core directError)) =>
          match selectTypedSourceBackend program plan with
          | .ok executable => .ok executable
          | .error (.backendRejected (.typedSource typedSourceError)) =>
              .error (.noBackend [
                .core directError,
                .typedSource typedSourceError
              ])
          | .error error => .error error
      | .error error => .error error

private theorem selectCoreBackend_success_backend
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (executable : Executable)
    (selected : selectCoreBackend program plan stagingFuel = .ok executable) :
    executable.backend = .core := by
  unfold selectCoreBackend at selected
  cases linkedResult : SourceCoreDirectLinking.linkWithStagingFuel program
      (.complete plan) stagingFuel with
  | error error => simp [linkedResult] at selected
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

private theorem selectCallGraphBackend_success_backend
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (executable : Executable)
    (selected : selectCallGraphBackend program plan = .ok executable) :
    executable.backend = .callGraph := by
  unfold selectCallGraphBackend at selected
  cases linkedResult : SourceRuntimeLinking.link program (.complete plan) with
  | error error => simp [linkedResult] at selected
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

private theorem selectTypedSourceBackend_success_backend
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (executable : Executable)
    (selected : selectTypedSourceBackend program plan = .ok executable) :
    executable.backend = .typedSource := by
  cases validated : SourceTypedRuntime.validateExecutablePlanEvidence program
      plan with
  | error error =>
      simp [selectTypedSourceBackend, validated] at selected
  | ok value =>
      cases value
      have executableEq : executable = .typedSource := by
        simpa [selectTypedSourceBackend, validated] using selected.symm
      subst executable
      rfl

private theorem selectTypedSourceBackend_success_validation
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (executable : Executable)
    (selected : selectTypedSourceBackend program plan = .ok executable) :
    SourceTypedRuntime.validateExecutablePlanEvidence program plan = .ok () := by
  cases validated : SourceTypedRuntime.validateExecutablePlanEvidence program
      plan with
  | error error =>
      simp [selectTypedSourceBackend, validated] at selected
  | ok value =>
      cases value
      rfl

/-- An explicit backend preference cannot silently fall through to another
runtime. -/
private theorem selectBackend_backend_of_preference
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (preference : BackendPreference)
    (backend : Backend) (executable : Executable)
    (requested : preference.requested? = some backend)
    (selected : selectBackend program plan stagingFuel preference =
      .ok executable) :
    executable.backend = backend := by
  cases preference with
  | automatic => simp [BackendPreference.requested?] at requested
  | core =>
      have backendEq : backend = .core := by
        simpa [BackendPreference.requested?] using requested.symm
      subst backend
      exact selectCoreBackend_success_backend program plan stagingFuel
        executable (by simpa [selectBackend] using selected)
  | callGraph =>
      have backendEq : backend = .callGraph := by
        simpa [BackendPreference.requested?] using requested.symm
      subst backend
      exact selectCallGraphBackend_success_backend program plan executable
        (by simpa [selectBackend] using selected)
  | typedSource =>
      have backendEq : backend = .typedSource := by
        simpa [BackendPreference.requested?] using requested.symm
      subst backend
      exact selectTypedSourceBackend_success_backend program plan executable
        (by simpa [selectBackend] using selected)

private theorem selectBackend_automatic_typed_source
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat)
    (selected : selectBackend program plan stagingFuel .automatic =
      .ok .typedSource) :
    selectTypedSourceBackend program plan = .ok .typedSource := by
  cases direct : SourceCoreDirectLinking.linkWithStagingFuel program
      (.complete plan) stagingFuel with
  | error error =>
      cases validated : SourceTypedRuntime.validateExecutablePlanEvidence
          program plan with
      | ok value =>
          cases value
          simp [selectTypedSourceBackend, validated]
      | error typedError =>
          simp [selectBackend, selectCoreBackend, direct,
            selectTypedSourceBackend, validated] at selected
  | ok linked =>
      cases entries : linked.entries with
      | nil =>
          simp [selectBackend, selectCoreBackend, direct, entries] at selected
      | cons entry rest =>
          cases rest with
          | nil =>
              simp [selectBackend, selectCoreBackend, direct, entries] at selected
          | cons another tail =>
              simp [selectBackend, selectCoreBackend, direct, entries] at selected

private theorem selectBackend_typed_plan
    (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (stagingFuel : Nat) (preference : BackendPreference)
    (selected : selectBackend program plan stagingFuel preference =
      .ok .typedSource) :
    SourceTypedRuntime.validateExecutablePlanEvidence program plan = .ok () := by
  cases preference with
  | core =>
      have impossible := selectCoreBackend_success_backend program plan
        stagingFuel .typedSource (by simpa [selectBackend] using selected)
      cases impossible
  | callGraph =>
      have impossible := selectCallGraphBackend_success_backend program plan
        .typedSource (by simpa [selectBackend] using selected)
      cases impossible
  | typedSource =>
      exact selectTypedSourceBackend_success_validation program plan
        .typedSource (by simpa [selectBackend] using selected)
  | automatic =>
      exact selectTypedSourceBackend_success_validation program plan
        .typedSource
        (selectBackend_automatic_typed_source program plan stagingFuel selected)

/-- Guard the public result signature against an inconsistent linker payload.
The graph entry separately certifies projection from its source type to its
Core result type; here we identify that source type with the canonical root. -/
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
  | .callGraph entry =>
      if root.function.inferredBodyType = entry.sourceBodyType then
        pure ()
      else
        throw (.publicGraphResultMismatch root.function.inferredBodyType
          entry.sourceBodyType)
  | .typedSource => pure ()

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
  | callGraph entry =>
      simp only [Executable.HasPublicResultProjection]
      by_cases same : root.function.inferredBodyType = entry.sourceBodyType
      · exact same
      · simp [validatePublicResultType, same] at accepted
  | typedSource =>
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
  let executable ← selectBackend program plan options.stagingFuel
    options.backendPreference
  validatePublicResultType root executable
  pure ⟨program, plan, root, executable⟩

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
                      cases backend : selectBackend program plan
                          options.stagingFuel options.backendPreference with
                      | error error =>
                          rw [backend] at compiledOk
                          cases compiledOk
                      | ok executable =>
                          rw [backend] at compiledOk
                          simp at compiledOk
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
                      cases backendSelection : selectBackend program plan
                          options.stagingFuel options.backendPreference with
                      | error error =>
                          rw [backendSelection] at compiledOk
                          cases compiledOk
                      | ok executable =>
                          have exactBackend :=
                            selectBackend_backend_of_preference program plan
                              options.stagingFuel options.backendPreference
                              backend executable requested backendSelection
                          rw [backendSelection] at compiledOk
                          simp at compiledOk
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
                      cases backend : selectBackend program plan
                          options.stagingFuel options.backendPreference with
                      | error error =>
                          rw [backend] at compiledOk
                          cases compiledOk
                      | ok executable =>
                          rw [backend] at compiledOk
                          simp at compiledOk
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
                      cases backendSelected : selectBackend program plan
                          options.stagingFuel options.backendPreference with
                      | error error =>
                          rw [backendSelected] at compiledOk
                          cases compiledOk
                      | ok executable =>
                          rw [backendSelected] at compiledOk
                          simp at compiledOk
                          cases publicResult : validatePublicResultType root
                              executable with
                          | error error =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                          | ok checkedResult =>
                              rw [publicResult] at compiledOk
                              cases compiledOk
                              cases executable with
                              | core entry =>
                                  simp [CompiledEntry.backend] at typedBackend
                              | callGraph entry =>
                                  simp [CompiledEntry.backend] at typedBackend
                              | typedSource =>
                                  exact selectBackend_typed_plan program plan
                                    options.stagingFuel options.backendPreference
                                    backendSelected

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
                      cases backend : selectBackend program plan
                          options.stagingFuel options.backendPreference with
                      | error error =>
                          rw [backend] at compiledOk
                          cases compiledOk
                      | ok executable =>
                          rw [backend] at compiledOk
                          simp at compiledOk
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
                  cases executable : selectBackend program plan
                      options.stagingFuel options.backendPreference with
                  | error error =>
                      rw [executable] at compiledOk
                      cases compiledOk
                  | ok backend =>
                      rw [executable] at compiledOk
                      simp at compiledOk
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

/-- Check a raw workspace once, derive its canonical entry module, then
discover and compile its exported Static Word ABI roots. -/
def compileStaticWord (raw : Workspace.RawWorkspace)
    (options : CheckingOptions := {}) :
    Except StaticWordCompileError CompiledStaticWordProgram := do
  let (program, entryModule) ←
    (checkWorkspaceAtEntry raw options.checkingFuel).mapError
      StaticWordCompileError.checking
  compileStaticWordChecked program entryModule options.toCompileOptions

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
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.runExact? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | core result =>
              cases ran
              simp only [CompiledEntry.SuccessfulResultHasNativeType]
              exact entry.runExact?_core_done_preserves_type arguments
                options.executionFuel store environmentTyped storeTyped exactRun
          | runtime result =>
              cases ran
  | callGraph entry =>
      simp only [CompiledEntry.run] at ran
      cases ran
  | typedSource =>
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
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      obtain ⟨world, environmentTyped, storeTyped⟩ := precondition
      intro ran
      simp only [CompiledEntry.run] at ran
      cases exactRun : entry.runExact? arguments options.executionFuel store with
      | none =>
          rw [exactRun] at ran
          cases ran
      | some result =>
          rw [exactRun] at ran
          cases result with
          | core result =>
              cases ran
              exact entry.runExact?_core_never_faults arguments
                options.executionFuel store environmentTyped storeTyped
                error faultState exactRun
          | runtime result =>
              cases ran
  | callGraph entry =>
      simp [CompiledEntry.run]
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- Either facade route which reaches the finite call-graph runtime preserves
the result type declared by the exact selected runtime signature. -/
theorem CompiledEntry.run_callGraph_done_preserves_type
    (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions) {value : SourceRuntime.Value}
    {finalStore : Core.Store}
    (ran : compiled.run invocation options =
      .ok (.callGraph (.done value finalStore))) :
    compiled.SuccessfulResultHasNativeType
      (.callGraph (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      cases invocation with
      | coreValues arguments store =>
          simp only [CompiledEntry.run] at ran
          cases exactRun : entry.runExact? arguments options.executionFuel store with
          | none =>
              rw [exactRun] at ran
              cases ran
          | some result =>
              rw [exactRun] at ran
              cases result with
              | core result =>
                  cases ran
              | runtime result =>
                  cases ran
                  cases runtime : entry.runtime with
                  | none =>
                      simp [SourceCoreDirectLinking.LinkedEntry.runExact?,
                        runtime] at exactRun
                  | some checked =>
                      have completed : checked.run options.executionFuel
                          entry.key arguments store =
                            .done value finalStore := by
                        have dispatched :
                            arguments.map Core.Value.type =
                                entry.elaborated.inputs.values ∧
                              checked.run options.executionFuel entry.key
                                  arguments store = .done value finalStore := by
                          simpa [SourceCoreDirectLinking.LinkedEntry.runExact?,
                            runtime] using exactRun
                        exact dispatched.2
                      obtain ⟨definition, _, signature, valueTyped⟩ :=
                        checked.run_done_hasType options.executionFuel entry.key
                          arguments store finalStore value completed
                      simp only [CompiledEntry.SuccessfulResultHasNativeType, runtime,
                        CompiledEntry.GraphResultHasType]
                      exact ⟨definition.signature, signature, valueTyped⟩
      | typedValues arguments state =>
          simp [CompiledEntry.run, Invocation.kind] at ran
  | callGraph entry =>
      cases invocation with
      | coreValues arguments store =>
          have completed : entry.program.run options.executionFuel entry.key
              arguments store = .done value finalStore := by
            simpa [CompiledEntry.run] using ran
          obtain ⟨definition, _, signature, valueTyped⟩ :=
            entry.program.run_done_hasType options.executionFuel entry.key
              arguments store finalStore value completed
          simp only [CompiledEntry.SuccessfulResultHasNativeType,
            CompiledEntry.GraphResultHasType]
          exact ⟨definition.signature, signature, valueTyped⟩
      | typedValues arguments state =>
          simp [CompiledEntry.run, Invocation.kind] at ran
  | typedSource =>
      cases invocation <;> simp [CompiledEntry.run, Invocation.kind] at ran

/-- A successful source-typed facade result has the inferred result type of
the unique retained root specialization. -/
theorem CompiledEntry.run_typedSource_done_preserves_type
    (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value)
    (initial : SourceTypedRuntime.RuntimeState) (options : RunOptions)
    {value : SourceTypedRuntime.Value}
    {finalState : SourceTypedRuntime.RuntimeState}
    (precondition : compiled.PreservationPrecondition
      (.typedValues arguments initial))
    (ran : compiled.run (.typedValues arguments initial) options =
      .ok (.typedSource (.done value finalState))) :
    compiled.SuccessfulResultHasNativeType
      (.typedSource (.done value finalState)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | callGraph entry =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition
      have completed : SourceTypedRuntime.runWithValidationFuel
          program plan root.key arguments
            options.inputValidationFuel options.executionFuel initial =
          .done value finalState := by
        simpa [CompiledEntry.run] using ran
      simp only [CompiledEntry.SuccessfulResultHasNativeType]
      exact SourceTypedRuntime.runWithValidationFuel_done_has_inferredBodyType
        program plan root.key arguments options.inputValidationFuel
        options.executionFuel initial finalState value root precondition completed

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
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | callGraph entry =>
      simp [CompiledEntry.PreservationPrecondition] at precondition
  | typedSource =>
      simpa [CompiledEntry.TypedValueHasResultType,
        CompiledEntry.SuccessfulResultHasNativeType,
        CompiledEntry.resultType] using native

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
  rename_i program plan root executable
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
  | callGraph entry =>
      simp only [CompiledEntry.SuccessfulResultHasNativeType] at native
  | typedSource =>
      simp only [CompiledEntry.PreservationPrecondition] at precondition

/-- A successful selected graph result has the projection of the compiler's
public source result type, not merely an unrelated runtime-table tag. -/
theorem CompiledEntry.run_callGraph_done_has_public_resultType
    (compiled : CompiledEntry) (invocation : Invocation)
    (options : RunOptions) {value : SourceRuntime.Value}
    {finalStore : Core.Store}
    (backend : compiled.backend = .callGraph)
    (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run invocation options =
      .ok (.callGraph (.done value finalStore))) :
    compiled.GraphValueHasPublicType value := by
  have native := compiled.run_callGraph_done_preserves_type invocation
    options ran
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp [CompiledEntry.backend] at backend
  | callGraph entry =>
      simp only [CompiledEntry.SuccessfulResultHasNativeType,
        CompiledEntry.GraphResultHasType] at native
      obtain ⟨signature, selected, valueTyped⟩ := native
      obtain ⟨entrySignature, entrySelected, entryResult⟩ :=
        entry.signatureResultType
      have sameSignature : signature = entrySignature := by
        rw [entrySelected] at selected
        exact (Option.some.inj selected).symm
      subst signature
      change root.function.inferredBodyType = entry.sourceBodyType at projection
      simp only [CompiledEntry.GraphValueHasPublicType,
        CompiledEntry.resultType]
      refine ⟨entry.resultType, ?_, ?_⟩
      · simpa [projection] using entry.resultType_eq_source
      · simpa [entryResult] using valueTyped
  | typedSource =>
      simp [CompiledEntry.backend] at backend

/-- The compiler-level deep graph input premise entails the exact
selected-definition input relation used by the graph safety induction. -/
theorem CompiledEntry.graphDeepInput_to_runtime
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (store : Core.Store)
    (typing : compiled.GraphDeepInput arguments store) :
    compiled.GraphRuntimeDeepInput arguments store := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry =>
      simp only [CompiledEntry.GraphDeepInput] at typing
  | callGraph entry =>
      simp only [CompiledEntry.GraphDeepInput] at typing
      obtain ⟨world, argumentsTyped, storeTyped⟩ := typing
      obtain ⟨definition, runtimeTyped⟩ :=
        entry.runtimeInputsHaveType arguments store world
          argumentsTyped storeTyped
      simp only [CompiledEntry.GraphRuntimeDeepInput]
      exact ⟨world, definition, runtimeTyped⟩
  | typedSource =>
      simp only [CompiledEntry.GraphDeepInput] at typing

/-- Whole-compiler successful-result preservation.  One theorem now covers
all three selected runtimes without erasing their native value/store domains.
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
              rename_i program plan root executable
              cases executable <;>
                simp [CompiledEntry.run, Invocation.kind] at ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | callGraph result =>
      cases result with
      | done value finalStore =>
          exact compiled.run_callGraph_done_preserves_type invocation options ran
      | outOfFuel store =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error store =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
  | typedSource result =>
      cases result with
      | done value finalState =>
          cases invocation with
          | coreValues arguments store =>
              cases compiled
              rename_i program plan root executable
              cases executable with
              | core entry =>
                  simp only [CompiledEntry.run] at ran
                  split at ran <;> cases ran
              | callGraph entry =>
                  simp [CompiledEntry.run] at ran
              | typedSource =>
                  simp [CompiledEntry.run, Invocation.kind] at ran
          | typedValues arguments initial =>
              exact compiled.run_typedSource_done_preserves_type arguments
                initial options precondition ran
      | outOfFuel state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]
      | fault error state =>
          simp [CompiledEntry.SuccessfulResultHasNativeType]

/-- A typed-source artifact rejects Core-domain inputs before either runtime
starts.  In particular, execution fuel cannot turn this boundary failure into
a runtime result. -/
theorem CompiledEntry.runCore_of_typedSource (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .typedSource) :
    compiled.runCore arguments options store =
      .error (.invocationKindMismatch .typedSource .coreValues) := by
  cases compiled
  rename_i program plan root executable
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
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run, Invocation.kind]

/-- A structural-call-graph artifact rejects source-typed inputs before
execution. -/
theorem CompiledEntry.runTyped_of_callGraph (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .callGraph) :
    compiled.runTyped arguments options state =
      .error (.invocationKindMismatch .callGraph .typedValues) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run, Invocation.kind]

/-- Once a typed-source artifact receives typed inputs, validation failures,
runtime faults, and either fuel exhaustion are retained inside its native
result carrier rather than being relabeled as facade errors. -/
theorem CompiledEntry.runTyped_ok_of_typedSource (compiled : CompiledEntry)
    (arguments : List SourceTypedRuntime.Value) (options : RunOptions)
    (state : SourceTypedRuntime.RuntimeState)
    (hbackend : compiled.backend = .typedSource) :
    ∃ result, compiled.runTyped arguments options state =
      .ok (.typedSource result) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runTyped,
    CompiledEntry.run]

/-- A structural call-graph runtime likewise retains faults and exhaustion in
its native result carrier after the invocation domain has matched. -/
theorem CompiledEntry.runCore_ok_of_callGraph (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .callGraph) :
    ∃ result, compiled.runCore arguments options store =
      .ok (.callGraph result) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend, CompiledEntry.runCore,
    CompiledEntry.run]

/-- After a Core-domain invocation reaches the direct backend, the only
facade-level rejection is the explicit input-type mismatch.  Every runtime
outcome remains in one of the exact backend result carriers. -/
theorem CompiledEntry.runCore_outcome_of_core (compiled : CompiledEntry)
    (arguments : List Core.Value) (options : RunOptions) (store : Core.Store)
    (hbackend : compiled.backend = .core) :
    (∃ result, compiled.runCore arguments options store =
        .ok (.core result)) ∨
      (∃ result, compiled.runCore arguments options store =
        .ok (.callGraph result)) ∨
      (∃ expected actual, compiled.runCore arguments options store =
        .error (.coreInputTypesMismatch expected actual)) := by
  cases compiled
  rename_i program plan root executable
  cases executable <;> simp_all [CompiledEntry.backend]
  rename_i entry
  simp only [CompiledEntry.runCore, CompiledEntry.run]
  cases hresult : entry.runExact? arguments options.executionFuel store with
  | none =>
      exact Or.inr (Or.inr ⟨entry.elaborated.inputs.values,
        arguments.map Core.Value.type, by simp⟩)
  | some result =>
      cases result with
      | core result => exact Or.inl ⟨result, by simp⟩
      | runtime result => exact Or.inr (Or.inl ⟨result, by simp⟩)

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

/-- A compiler-produced finite graph entry returns a value whose checked
runtime tag is the projection of the public source result type. -/
theorem compileChecked_runGraph_done_has_public_resultType
    (program : CheckedProgram) (seed : Seed)
    (compileOptions : CompileOptions) (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (backend : compiled.backend = .callGraph)
    (invocation : Invocation) (runOptions : RunOptions)
    {value : SourceRuntime.Value} {finalStore : Core.Store}
    (ran : compiled.run invocation runOptions =
      .ok (.callGraph (.done value finalStore))) :
    compiled.GraphValueHasPublicType value := by
  exact compiled.run_callGraph_done_has_public_resultType invocation
    runOptions backend
    (compileChecked_hasPublicResultProjection program seed compileOptions
      compiled compiledOk) ran

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
  rename_i checked plan root executable
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
  rename_i checked plan root executable
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

/-- End-to-end one-shot execution inherits the three-backend successful-result
preservation theorem from the exact artifact produced in its compile phase. -/
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

/-!
## Consolidated module: `Solcore.Frontend.SourceCompilerGraphDeepProperties`
-/

/-! Conditional deep preservation through the public graph-backend facade. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompiler

namespace CompiledEntry

/-- The public deep graph result refines the existing native result-tag
certificate when the artifact's public result projection is known. -/
theorem GraphDeepResult.native
    (compiled : CompiledEntry) (initialWorld : Core.StoreTyping)
    (value : SourceRuntime.Value) (finalStore : Core.Store)
    (projection : compiled.HasPublicResultProjection)
    (deep : compiled.GraphDeepResult initialWorld value finalStore) :
    compiled.SuccessfulResultHasNativeType
      (.callGraph (.done value finalStore)) := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry => simp only [GraphDeepResult] at deep
  | typedSource => simp only [GraphDeepResult] at deep
  | callGraph entry =>
      obtain ⟨publicType, finalWorld, lowered, _, _, valueTyping⟩ := deep
      obtain ⟨signature, found, resultType⟩ :=
        entry.signatureResultType
      change root.function.inferredBodyType = entry.sourceBodyType at projection
      have publicEqualsEntry : publicType = entry.resultType := by
        have loweredEntry :
            SourceRuntimeLinking.lowerType entry.sourceBodyType =
              .ok publicType := by
          simpa [CompiledEntry.resultType, projection] using lowered
        rw [entry.resultType_eq_source] at loweredEntry
        exact (Except.ok.inj loweredEntry).symm
      simp only [SuccessfulResultHasNativeType, GraphResultHasType]
      exact ⟨signature, found, by
        simpa [publicEqualsEntry, resultType] using valueTyping.hasType⟩

/-- The actual public `CompiledEntry.run` graph branch preserves deep source
value and final-store typing after checker-certified compilation, deep caller
input typing, and a public-result projection certificate. -/
theorem run_callGraph_done_deep
    (compiled : CompiledEntry) (arguments : List Core.Value)
    (initialStore : Core.Store) (options : RunOptions)
    (value : SourceRuntime.Value) (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (projection : compiled.HasPublicResultProjection)
    (ran : compiled.run (.coreValues arguments initialStore) options =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  cases compiled
  rename_i program plan root executable
  cases executable with
  | core entry => simp only [GraphDeepInput] at input
  | typedSource => simp only [GraphDeepInput] at input
  | callGraph entry =>
      obtain ⟨world, argumentsTyping, storeTyping⟩ := input
      have completed : entry.program.run options.executionFuel entry.key
          arguments initialStore = .done value finalStore := by
        simpa [CompiledEntry.run] using ran
      obtain ⟨finalWorld, extension, finalStoreTyping, valueTyping⟩ :=
        entry.run_done_deep argumentsTyping storeTyping completed
      change root.function.inferredBodyType = entry.sourceBodyType at projection
      have lowered : SourceRuntimeLinking.lowerType
          root.function.inferredBodyType = .ok entry.resultType := by
        simpa [projection] using entry.resultType_eq_source
      refine ⟨world, ?_⟩
      simp only [GraphDeepResult]
      exact ⟨entry.resultType, finalWorld, lowered, extension,
        finalStoreTyping, valueTyping⟩

end CompiledEntry

/-- Successful checked-program compilation supplies the public-result
projection certificate required by the graph deep-preservation facade. -/
theorem compileChecked_runGraph_done_deep
    (program : CheckedProgram) (seed : Seed)
    (compileOptions : CompileOptions) (compiled : CompiledEntry)
    (compiledOk : compileChecked program seed compileOptions = .ok compiled)
    (arguments : List Core.Value) (initialStore : Core.Store)
    (runOptions : RunOptions) (value : SourceRuntime.Value)
    (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (ran : compiled.run (.coreValues arguments initialStore) runOptions =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  exact compiled.run_callGraph_done_deep arguments initialStore runOptions
    value finalStore input
    (compileChecked_hasPublicResultProjection program seed compileOptions
      compiled compiledOk) ran

/-- The one-shot raw-workspace compiler likewise supplies the public-result
projection certificate; the caller still provides genuinely deep arguments
and an initial store in one Core world. -/
theorem compile_runGraph_done_deep
    (raw : Workspace.RawWorkspace) (seed : Seed)
    (checkingOptions : CheckingOptions) (compiled : CompiledEntry)
    (compiledOk : compile raw seed checkingOptions = .ok compiled)
    (arguments : List Core.Value) (initialStore : Core.Store)
    (runOptions : RunOptions) (value : SourceRuntime.Value)
    (finalStore : Core.Store)
    (input : compiled.GraphDeepInput arguments initialStore)
    (ran : compiled.run (.coreValues arguments initialStore) runOptions =
      .ok (.callGraph (.done value finalStore))) :
    ∃ initialWorld,
      compiled.GraphDeepResult initialWorld value finalStore := by
  exact compiled.run_callGraph_done_deep arguments initialStore runOptions
    value finalStore input
    (compile_hasPublicResultProjection raw seed checkingOptions compiled
      compiledOk) ran

end Solcore.Frontend.SourceCompiler

/-!
## Consolidated module: `Solcore.Frontend.SourceCompilerSignatureProperties`
-/

/-! Type-projection coherence shared by the direct-Core and finite-graph
backends.  The finite graph additionally supports source function types, so
the implication runs from the smaller direct-Core domain to the graph domain. -/

set_option autoImplicit false

namespace Solcore.Frontend

open TypeSystem

/-- Every result type admitted by direct Core has the same backend-native
projection in the finite call graph. -/
theorem sourceCore_lowerType_implies_graph_lowerType
    (site : SourceCoreElaboration.ErrorSite) (sourceType : Ty)
    (coreType : Core.Ty)
    (accepted : SourceCoreElaboration.lowerType site sourceType = .ok coreType) :
    SourceRuntimeLinking.lowerType sourceType = .ok coreType := by
  induction sourceType generalizing coreType with
  | «variable» id =>
      exact nomatch accepted
  | parameter id =>
      exact nomatch accepted
  | constructor id =>
      cases id with
      | builtin builtin =>
          cases builtin with
          | unit => cases accepted; rfl
          | bool => cases accepted; rfl
          | word => cases accepted; rfl
          | integer => exact nomatch accepted
      | declaration id =>
          exact nomatch accepted
  | application function argument ihFunction ihArgument =>
      unfold SourceCoreElaboration.lowerType at accepted
      split at accepted <;> exact nomatch accepted
  | function parameter result ihParameter ihResult =>
      exact nomatch accepted
  | product left right ihLeft ihRight =>
      simp only [SourceCoreElaboration.lowerType] at accepted
      cases leftProjection : SourceCoreElaboration.lowerType site left with
      | error error =>
          simp [leftProjection, bind, Except.bind] at accepted
      | ok loweredLeft =>
          cases rightProjection : SourceCoreElaboration.lowerType site right with
          | error error =>
              simp [leftProjection, rightProjection, bind, Except.bind] at accepted
          | ok loweredRight =>
              simp [leftProjection, rightProjection, bind, Except.bind] at accepted
              cases accepted
              simp [SourceRuntimeLinking.lowerType,
                ihLeft loweredLeft leftProjection,
                ihRight loweredRight rightProjection, bind, Except.bind,
                pure, Pure.pure, Except.pure]
  | mapping key value ihKey ihValue =>
      exact nomatch accepted
  | proxy inner ih =>
      exact nomatch accepted
  | comptime inner ih =>
      exact nomatch accepted
  | error =>
      exact nomatch accepted

/-- The graph-only closure/function case extends the direct-Core projection. -/
theorem graph_lowerType_function {parameter result : Ty}
    {loweredParameter loweredResult : Core.Ty}
    (parameterAccepted : SourceRuntimeLinking.lowerType parameter =
      .ok loweredParameter)
    (resultAccepted : SourceRuntimeLinking.lowerType result =
      .ok loweredResult) :
    SourceRuntimeLinking.lowerType (.function parameter result) =
      .ok (.function loweredParameter loweredResult) := by
  simp [SourceRuntimeLinking.lowerType, parameterAccepted, resultAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure]

/-- Both backends agree on products, including products whose components are
themselves function types only in the graph backend. -/
theorem graph_lowerType_product {left right : Ty}
    {loweredLeft loweredRight : Core.Ty}
    (leftAccepted : SourceRuntimeLinking.lowerType left = .ok loweredLeft)
    (rightAccepted : SourceRuntimeLinking.lowerType right = .ok loweredRight) :
    SourceRuntimeLinking.lowerType (.product left right) =
      .ok (.product loweredLeft loweredRight) := by
  simp [SourceRuntimeLinking.lowerType, leftAccepted, rightAccepted,
    bind, Except.bind, pure, Pure.pure, Except.pure]

end Solcore.Frontend
