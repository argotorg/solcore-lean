import Solcore.Frontend.SourceCoreUnifiedPreparationCertificates
import Solcore.Frontend.SourceProgramExecution

/-! One compiler entry for an ordered source root set. Every root shares the
actual cached compatible/indexed Core program. The options select finite
checking and compilation bounds; they contain no runtime backend choice.
Owned session opening is a separate boundary. An empty root set retains its
validated empty plan and has no callable code to install.
`compileChecked` authenticates the plan but does not invent a raw checker
witness for a caller-supplied `CheckedProgram` record. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompiler

abbrev Seed := SourceProgramExecution.Seed
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Cached := SourceCoreUnifiedCompilation.Compiled
abbrev Plan := SourceSpecializationWorklist.Plan

namespace Seed
def declaration (id : Resolved.DeclarationId) (arguments : List TypeSystem.Ty := []) : Seed :=
  SourceProgramExecution.Seed.declaration id arguments
def named (moduleId : Workspace.ModuleId) (name : String) (arguments : List TypeSystem.Ty := []) : Seed :=
  SourceProgramExecution.Seed.named moduleId name arguments
end Seed

structure Options where
  checkingFuel : Nat := 1024
  specializationBudget : Nat := 1024
  compilationFuel : Nat := 1024
  deriving Repr, DecidableEq

inductive Error where
  | checking (errors : List ProgramCheckError)
  | seed (index : Nat) (seed : Seed) (error : SourceProgramExecution.SeedError)
  | worklist (error : SourceSpecializationWorklist.Error)
  | specializationBudgetExhausted (next : Key) (pendingCount : Nat)
  | invalidPlan (error : SourceCoreDirectLinking.Error)
  | planEvidence (error : SourceCompilationPlan.Error)
  | compilation (error : SourceCoreUnifiedCompilation.Error)
  | root (key : Key) (error : SourceCompilationPlan.Error)
  | rootCountMismatch (expected actual : Nat)
  | rootOrderMismatch
  deriving Repr

/-- Metadata comes from the exact original canonical specialization in this
artifact's validation plan, rather than from a native type projection. -/
structure Root (plan : Plan) where private mk ::
  seed : Seed
  key : Key
  private specialized : SourceSpecialization.SpecializedFunction
  private selected : SourceCompilationPlan.exactSpecialization plan key = .ok specialized

def Root.inputTypes {plan : Plan} (root : Root plan) : List TypeSystem.Ty :=
  root.specialized.function.typedBody.inputs.map (·.scheme.body)
def Root.resultType {plan : Plan} (root : Root plan) : TypeSystem.Ty :=
  root.specialized.function.inferredBodyType

/-- A root has an actual source-plan receipt, including its raw source types. -/
theorem Root.source_metadata {plan : Plan} (root : Root plan) :
    ∃ specialized,
      SourceCompilationPlan.exactSpecialization plan root.key = .ok specialized ∧
      root.inputTypes = specialized.function.typedBody.inputs.map (·.scheme.body) ∧
      root.resultType = specialized.function.inferredBodyType :=
  ⟨root.specialized, root.selected, rfl, rfl⟩

structure Compiled where private mk ::
  private sourceProgram : CheckedProgram
  private sourcePlan : Plan
  private cached : Option Cached
  private orderedRoots : List (Root sourcePlan)
  private matched : match cached with
    | none => orderedRoots = [] ∧ sourcePlan.seedKeys = []
    | some artifact => artifact.sourceProgram = sourceProgram ∧ artifact.validationPlan = sourcePlan ∧
        orderedRoots.map (·.key) = artifact.keys
  private validated : SourceCompilationPlan.validateExecutablePlanEvidence
    sourceProgram sourcePlan = .ok ()

/-- The cached code is the exact artifact used by all owned sessions opened
from this compilation. This accessor never compiles a root again. -/
def Compiled.artifact? (compiled : Compiled) : Option Cached := compiled.cached
def Compiled.program (compiled : Compiled) : CheckedProgram := compiled.sourceProgram
def Compiled.plan (compiled : Compiled) : Plan := compiled.sourcePlan
def Compiled.roots (compiled : Compiled) : List (Root compiled.plan) := compiled.orderedRoots
def Compiled.keys (compiled : Compiled) : List Key := compiled.roots.map (·.key)
def Compiled.rootCount (compiled : Compiled) : Nat := compiled.roots.length
def Compiled.root? (compiled : Compiled) (index : Nat) : Option (Root compiled.plan) :=
  compiled.roots[index]?

theorem Compiled.artifact_fields (compiled : Compiled) {cached : Cached}
    (selected : compiled.artifact? = some cached) :
    cached.sourceProgram = compiled.program ∧ cached.validationPlan = compiled.plan ∧ compiled.keys = cached.keys := by
  have matched := compiled.matched
  change compiled.cached = some cached at selected
  simpa only [selected, Compiled.program, Compiled.plan, Compiled.keys, Compiled.roots] using matched
theorem Compiled.no_artifact_empty (compiled : Compiled) (empty : compiled.artifact? = none) :
    compiled.roots = [] ∧ compiled.plan.seedKeys = [] := by
  have matched := compiled.matched
  change compiled.cached = none at empty
  simpa only [empty, Compiled.roots, Compiled.plan] using matched
theorem Compiled.plan_validated (compiled : Compiled) :
    SourceCompilationPlan.validateExecutablePlanEvidence compiled.program compiled.plan = .ok () := compiled.validated

private def requests (program : CheckedProgram) (seeds : List Seed) :
    Except Error (List SourceSpecializationWorklist.Request) :=
  seeds.zipIdx.mapM fun (seed, index) =>
    (SourceProgramExecution.resolveSeed program seed).mapError (Error.seed index seed)

private def root (plan : Plan) (seed : Seed) (key : Key) : Except Error (Root plan) :=
  match selected : SourceCompilationPlan.exactSpecialization plan key with
  | .error error => .error (.root key error)
  | .ok specialized => .ok ⟨seed, key, specialized, selected⟩

/-- Check each seed and discover one canonical frontier, then prepare one Core
artifact. Duplicate requested roots keep their positions in the root list. -/
def compileChecked (program : CheckedProgram) (seeds : List Seed) (options : Options := {}) :
    Except Error Compiled := do
  let requests ← requests program seeds
  let outcome ← (SourceSpecializationWorklist.run program requests options.specializationBudget).mapError Error.worklist
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending => throw (.specializationBudgetExhausted next pending.length)
  (SourceCoreDirectLinking.validatePlan program plan).mapError Error.invalidPlan
  match validated : SourceCompilationPlan.validateExecutablePlanEvidence program plan with
  | .error error => throw (.planEvidence error)
  | .ok () =>
    if seeds = [] then
      if empty : plan.seedKeys = [] then
        pure ⟨program, plan, none, [], ⟨rfl, empty⟩, validated⟩
      else throw (.rootCountMismatch 0 plan.seedKeys.length)
    else
      let cached ← match accepted : SourceCoreUnifiedCompilation.prepare program plan options.compilationFuel with
        | .error error => throw (.compilation error)
        | .ok cached => pure (⟨cached, SourceCoreUnifiedPreparationCertificates.prepare_fields accepted⟩ :
            {cached : Cached // cached.sourceProgram = program ∧ cached.validationPlan = plan ∧
              cached.compilationFuel = options.compilationFuel})
      if seeds.length = cached.val.keys.length then
        let roots ← (seeds.zip cached.val.keys).mapM fun (seed, key) => root plan seed key
        if ordered : roots.map (·.key) = cached.val.keys then
          pure ⟨program, plan, some cached.val, roots,
            ⟨cached.property.1, cached.property.2.1, ordered⟩, validated⟩
        else throw .rootOrderMismatch
      else throw (.rootCountMismatch seeds.length cached.val.keys.length)

def compile (raw : Workspace.RawWorkspace) (seeds : List Seed) (options : Options := {}) :
    Except Error Compiled := do
  let program ← (checkProgram raw options.checkingFuel).mapError Error.checking
  compileChecked program seeds options

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : (action >>= next) = .ok output) :
    ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

set_option linter.unusedSimpArgs false in
theorem compileChecked_program {program : CheckedProgram} {seeds : List Seed} {options : Options}
    {compiled : Compiled} (accepted : compileChecked program seeds options = .ok compiled) :
    compiled.program = program := by
  unfold compileChecked at accepted
  obtain ⟨requests, _, accepted⟩ := bind_ok accepted
  obtain ⟨outcome, _, accepted⟩ := bind_ok accepted
  cases outcome with
  | budgetExhausted partialPlan next pending =>
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
  | complete plan =>
    simp only [pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨checkedUnit, _, accepted⟩ := bind_ok accepted
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · split at accepted
      · split at accepted
        · cases accepted
          rfl
        · simp [throw, throwThe, MonadExceptOf.throw] at accepted
      · split at accepted
        · simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted
        · split at accepted
          · obtain ⟨roots, _, accepted⟩ := bind_ok accepted
            split at accepted
            · cases accepted
              rfl
            · simp [throw, throwThe, MonadExceptOf.throw] at accepted
          · simp [throw, throwThe, MonadExceptOf.throw] at accepted

/-- Raw compilation retains actual checking provenance. This statement does
not substitute a checker witness for the independent source typing proof. -/
theorem compile_checked_source {raw : Workspace.RawWorkspace} {seeds : List Seed} {options : Options}
    {compiled : Compiled} (accepted : compile raw seeds options = .ok compiled) :
    checkProgram raw options.checkingFuel = .ok compiled.program := by
  unfold compile at accepted
  cases checked : checkProgram raw options.checkingFuel with
  | error error => simp [checked, Except.mapError, bind, Except.bind] at accepted
  | ok program =>
    simp only [checked, Except.mapError, bind, Except.bind] at accepted
    rw [compileChecked_program accepted]

end Solcore.Frontend.SourceCoreCompiler
