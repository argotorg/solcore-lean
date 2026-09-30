import Solcore.Frontend.SourceCoreSession
import Solcore.Frontend.SourceProgramExecution

/-! Compile an explicit root set into one cached Core catalog and ownership
domain. This facade enables a function returned by one root to be passed to
another root in the same typed session. Its preparation uses one canonical
specialization frontier; opening only mints an artifact identity. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCompilerSession

abbrev Seed := SourceProgramExecution.Seed
abbrev Key := SourceSpecialization.SpecializationKey

namespace Seed
def declaration := SourceProgramExecution.Seed.declaration
def named := SourceProgramExecution.Seed.named
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
  | preparation (error : SourceCorePlanCatalog.Error)
  | rootCountMismatch (expected actual : Nat)
  deriving Repr

structure Root where
  seed : Seed
  key : Key
  inputTypes : List TypeSystem.Ty
  resultType : TypeSystem.Ty
  deriving Repr

/-- Sealed compilation result. Root metadata follows caller order, including
duplicates; every entry shares the recipe's checked catalog and function code. -/
structure Compiled where private mk ::
  private recipe : SourceCoreSession.Recipe
  private roots : List Root
  private sourceSignatures : ProgramSignatures

def Compiled.keys (compiled : Compiled) : List Key := compiled.roots.map (·.key)
def Compiled.rootCount (compiled : Compiled) : Nat := compiled.roots.length
def Compiled.root? (compiled : Compiled) (index : Nat) : Option Root := compiled.roots[index]?
def Compiled.signatures (compiled : Compiled) : ProgramSignatures := compiled.sourceSignatures
def Compiled.checked (compiled : Compiled) : SourceCoreDataCatalog.Checked := compiled.recipe.checked
def Compiled.dataContext (compiled : Compiled) : SourceCoreDataValues.Context :=
  ⟨compiled.checked, compiled.sourceSignatures⟩

private def requests (program : CheckedProgram) (seeds : List Seed) :
    Except Error (List SourceSpecializationWorklist.Request) :=
  seeds.zipIdx.mapM fun (seed, index) =>
    (SourceProgramExecution.resolveSeed program seed).mapError (Error.seed index seed)

/-- Source checking is the caller's responsibility for this checked-program
entry point. Preparation authenticates the resulting specialization plan and
checks all native entry bodies under the complete discovered catalog. -/
def compileChecked (program : CheckedProgram) (seeds : List Seed) (options : Options := {}) :
    Except Error Compiled := do
  let requests ← requests program seeds
  let outcome ← (SourceSpecializationWorklist.run program requests options.specializationBudget).mapError Error.worklist
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending => throw (.specializationBudgetExhausted next pending.length)
  (SourceCoreDirectLinking.validatePlan program plan).mapError Error.invalidPlan
  let recipe ← (SourceCoreSession.Recipe.prepareAutomatic program plan options.compilationFuel).mapError Error.preparation
  if recipe.program.entries.length ≠ seeds.length then
    throw (.rootCountMismatch seeds.length recipe.program.entries.length)
  let roots := seeds.zip recipe.program.entries |>.map fun (seed, entry) =>
    { seed, key := entry.key, inputTypes := entry.inputs.map (·.sourceType), resultType := entry.sourceResultType }
  pure ⟨recipe, roots, program.signatures⟩

/-- Check the raw workspace once, then compile all requested roots together. -/
def compile (raw : Workspace.RawWorkspace) (seeds : List Seed) (options : Options := {}) : Except Error Compiled := do
  let program ← (checkProgram raw options.checkingFuel).mapError Error.checking
  compileChecked program seeds options

/-- Opening creates a separate ownership domain from cached code. All roots
inside the opened artifact can exchange authenticated values in one session. -/
def Compiled.open (compiled : Compiled) : IO SourceCoreSession.Artifact := compiled.recipe.open

end Solcore.Frontend.SourceCompilerSession
