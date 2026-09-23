import Solcore.Frontend.SourceRuntimeLinking

/-!
The first public raw-source execution pipeline.

Entry selection is explicit.  A caller either supplies a stable declaration
identity or an exact module-local function name, together with ground generic
arguments in declaration order.  The workspace entry source is never searched
for a conventional function name.

The pipeline deliberately composes the existing checked boundaries: whole-
program checking, finite specialization discovery, evidence-aware finite
linking, and the linked entry's runtime type guard.  When finite inlining meets
a runtime cycle, lexical lambda, or indirect application, an additive checked
runtime table retains those calls instead.  Each failure retains the stage
that produced it.  Completion, fuel exhaustion, and runtime faults remain
ordinary runtime results rather than pipeline errors.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceProgramExecution

open TypeSystem

/-- An explicit root selector.  Named roots are exact module-local catalog
lookups; overload resolution is not performed at this boundary. -/
inductive SeedTarget where
  | declaration (id : Resolved.DeclarationId)
  | named (moduleId : Workspace.ModuleId) (name : String)
  deriving Repr, DecidableEq

/-- One root specialization request.  `arguments` are ground generic type
arguments in the selected signature's declaration order, not runtime values. -/
structure Seed where
  target : SeedTarget
  arguments : List Ty := []
  deriving Repr, DecidableEq

namespace Seed

/-- Select a root by stable declaration identity. -/
def declaration (id : Resolved.DeclarationId)
    (arguments : List Ty := []) : Seed := {
  target := .declaration id
  arguments
}

/-- Select a root by an exact name in one explicit module. -/
def named (moduleId : Workspace.ModuleId) (name : String)
    (arguments : List Ty := []) : Seed := {
  target := .named moduleId name
  arguments
}

end Seed

/-- Independent finite bounds for checking, specialization, compile-time
evaluation, and runtime execution. -/
structure Limits where
  checkingFuel : Nat := 1024
  specializationBudget : Nat := 1024
  stagingFuel : Nat := 1024
  executionFuel : Nat := 1024
  deriving Repr, DecidableEq

/-- Exact failures while translating a public seed to the internal worklist
request representation. -/
inductive SeedError where
  | unknownDeclaration (declaration : Resolved.DeclarationId)
  | declarationNotFunction
      (declaration : Resolved.DeclarationId) (kind : ProgramDeclarationKind)
  | missingSignature (declaration : Resolved.DeclarationId)
  | duplicateSignatures
      (declaration : Resolved.DeclarationId) (count : Nat)
  | unknownModule (moduleId : Workspace.ModuleId)
  | unknownName (moduleId : Workspace.ModuleId) (name : String)
  | ambiguousName
      (moduleId : Workspace.ModuleId) (name : String)
      (candidates : List Resolved.DeclarationId)
  | typeArgumentArityMismatch
      (declaration : Resolved.DeclarationId) (expected actual : Nat)
  deriving Repr, DecidableEq

/-- Stage-preserving failures of the explicit source-program pipeline. -/
inductive Error where
  | checking (errors : List ProgramCheckError)
  | seed (error : SeedError)
  | worklist (error : SourceSpecializationWorklist.Error)
  | specializationBudgetExhausted
      (next : SourceSpecialization.SpecializationKey) (pendingCount : Nat)
  | linking (error : SourceCoreDirectLinking.Error)
  | linkedEntryCountMismatch (actual : Nat)
  | inputTypesMismatch (expected actual : List Core.Ty)
  deriving Repr

/-- One checked, specialized, and linked explicit root. -/
structure PreparedEntry where
  entry : SourceCoreDirectLinking.LinkedEntry
  deriving Repr

namespace PreparedEntry

/-- Canonical specialization identity of the prepared root. -/
def key (prepared : PreparedEntry) : SourceSpecialization.SpecializationKey :=
  prepared.entry.key

/-- Exact runtime input types retained by checked Core elaboration. -/
def inputTypes (prepared : PreparedEntry) : List Core.Ty :=
  prepared.entry.elaborated.inputs.values

/-- Whether execution uses the finite named-function table instead of the
acyclic Core body retained in the compatibility inspection view. -/
def usesRuntimeCallGraph (prepared : PreparedEntry) : Bool :=
  prepared.entry.runtime.isSome

/-- Execute without conflating a runtime-call-graph continuation or fault with
a Core machine state. -/
def runExact? (prepared : PreparedEntry) (inputs : List Core.Value)
    (fuel : Nat) (store : Core.Store := []) :
    Option SourceCoreDirectLinking.ExecutionResult :=
  prepared.entry.runExact? inputs fuel store

/-- Compatibility projection to the historical Core-only result carrier.
Prefer `runExact?` for runtime-call-graph entries. -/
def run? (prepared : PreparedEntry) (inputs : List Core.Value)
    (fuel : Nat) (store : Core.Store := []) :
    Option Core.StatefulRunResult :=
  prepared.entry.run? inputs fuel store

end PreparedEntry

private def moduleExists (program : CheckedProgram)
    (moduleId : Workspace.ModuleId) : Bool :=
  program.environment.modules.any fun module => decide (module.id = moduleId)

private def exactSignature (program : CheckedProgram)
    (declaration : Resolved.DeclarationId) :
    Except SeedError ProgramFunctionSignature :=
  let candidates := program.signatures.functions.filter fun signature =>
    decide (signature.id = declaration)
  match candidates with
  | [] => .error (.missingSignature declaration)
  | [signature] => .ok signature
  | signatures =>
      .error (.duplicateSignatures declaration signatures.length)

private def signatureForDeclaration (program : CheckedProgram)
    (declaration : Resolved.DeclarationId) :
    Except SeedError ProgramFunctionSignature := do
  let catalogEntry ← match program.environment.declaration? declaration with
    | none => throw (.unknownDeclaration declaration)
    | some catalogEntry => pure catalogEntry
  if catalogEntry.kind != .function then
    throw (.declarationNotFunction declaration catalogEntry.kind)
  exactSignature program declaration

private def signatureForName (program : CheckedProgram)
    (moduleId : Workspace.ModuleId) (name : String) :
    Except SeedError ProgramFunctionSignature := do
  unless moduleExists program moduleId do
    throw (.unknownModule moduleId)
  match program.signatures.localFunctionsNamed moduleId name with
  | [] => throw (.unknownName moduleId name)
  | [signature] => pure signature
  | signatures =>
      throw (.ambiguousName moduleId name (signatures.map (·.id)))

private def requestForSignature (signature : ProgramFunctionSignature)
    (arguments : List Ty) :
    Except SeedError SourceSpecializationWorklist.Request := do
  if signature.scheme.parameters.length != arguments.length then
    throw (.typeArgumentArityMismatch signature.id
      signature.scheme.parameters.length arguments.length)
  pure {
    declaration := signature.id
    parameterSubstitution := signature.scheme.parameters.zip arguments
  }

/-- Resolve an explicit public seed into the internal specialization request.
The selected function and generic arity are fixed before worklist discovery. -/
def resolveSeed (program : CheckedProgram) (seed : Seed) :
    Except SeedError SourceSpecializationWorklist.Request := do
  let signature ← match seed.target with
    | .declaration declaration =>
        signatureForDeclaration program declaration
    | .named moduleId name => signatureForName program moduleId name
  requestForSignature signature seed.arguments

/-- Check, specialize, and link one explicit source root. -/
def prepare (raw : Workspace.RawWorkspace) (seed : Seed)
    (limits : Limits := {}) : Except Error PreparedEntry := do
  let program ← (checkProgram raw limits.checkingFuel).mapError Error.checking
  let request ← (resolveSeed program seed).mapError Error.seed
  let outcome ← (SourceSpecializationWorklist.run program [request]
    limits.specializationBudget).mapError Error.worklist
  let plan ← match outcome with
    | .complete plan => pure plan
    | .budgetExhausted _ next pending =>
        throw (.specializationBudgetExhausted next pending.length)
  let complete : SourceSpecializationWorklist.Outcome := .complete plan
  let linked ← match SourceCoreDirectLinking.linkWithStagingFuel program
      complete limits.stagingFuel with
    | .ok linked => pure linked
    | .error directError =>
        -- The established linker remains authoritative whenever it succeeds.
        -- The graph linker is an additive fallback; if its deliberately
        -- narrower structural profile also rejects, preserve the original
        -- evidence-aware diagnostic.
        match SourceRuntimeLinking.link program complete with
        | .ok runtime =>
            match runtime.toCoreLinkedProgram with
            | .ok linked => pure linked
            | .error _ => throw (.linking directError)
        | .error _ => throw (.linking directError)
  match linked.entries with
  | [entry] => pure { entry }
  | entries => throw (.linkedEntryCountMismatch entries.length)

/-- Execute one explicit source root from a raw workspace.  Runtime input type
mismatches are explicit errors; all Core machine outcomes remain successful
pipeline results. -/
def run (raw : Workspace.RawWorkspace) (seed : Seed)
    (inputs : List Core.Value) (limits : Limits := {})
    (store : Core.Store := []) : Except Error Core.StatefulRunResult := do
  let prepared ← prepare raw seed limits
  match prepared.run? inputs limits.executionFuel store with
  | some result => pure result
  | none => throw (.inputTypesMismatch prepared.inputTypes
      (inputs.map Core.Value.type))

/-- Execute one explicit source root while retaining the selected backend's
exact result carrier. -/
def runExact (raw : Workspace.RawWorkspace) (seed : Seed)
    (inputs : List Core.Value) (limits : Limits := {})
    (store : Core.Store := []) :
    Except Error SourceCoreDirectLinking.ExecutionResult := do
  let prepared ← prepare raw seed limits
  match prepared.runExact? inputs limits.executionFuel store with
  | some result => pure result
  | none => throw (.inputTypesMismatch prepared.inputTypes
      (inputs.map Core.Value.type))

end Solcore.Frontend.SourceProgramExecution

/-!
## Consolidated module: `Solcore.Frontend.SourceProgramExecutionProperties`
-/

/-! Small checked laws for the public single-seed source execution pipeline. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceProgramExecution

@[simp] theorem PreparedEntry.key_eq_entry (prepared : PreparedEntry) :
    prepared.key = prepared.entry.key := by
  rfl

@[simp] theorem PreparedEntry.inputTypes_eq_entry (prepared : PreparedEntry) :
    prepared.inputTypes = prepared.entry.elaborated.inputs.values := by
  rfl

@[simp] theorem PreparedEntry.usesRuntimeCallGraph_eq_entry
    (prepared : PreparedEntry) :
    prepared.usesRuntimeCallGraph = prepared.entry.runtime.isSome := by
  rfl

@[simp] theorem PreparedEntry.run?_eq_entry (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store) :
    prepared.run? inputs fuel store = prepared.entry.run? inputs fuel store := by
  rfl

@[simp] theorem PreparedEntry.runExact?_eq_entry (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store) :
    prepared.runExact? inputs fuel store =
      prepared.entry.runExact? inputs fuel store := by
  rfl

theorem PreparedEntry.run?_of_matching_types (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (finite : prepared.entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = prepared.inputTypes) :
    prepared.run? inputs fuel store = some (Core.runStateful fuel
      (Core.State.initial prepared.entry.elaborated.core inputs store)) := by
  simp [PreparedEntry.run?, SourceCoreDirectLinking.LinkedEntry.run?,
    SourceCoreDirectLinking.LinkedEntry.runExact?,
    PreparedEntry.inputTypes, finite, typesEqual]

theorem PreparedEntry.run?_of_mismatched_types (prepared : PreparedEntry)
    (inputs : List Core.Value) (fuel : Nat) (store : Core.Store)
    (mismatch : inputs.map Core.Value.type ≠ prepared.inputTypes) :
    prepared.run? inputs fuel store = none := by
  change inputs.map Core.Value.type ≠
    prepared.entry.elaborated.inputs.values at mismatch
  simp [PreparedEntry.run?, SourceCoreDirectLinking.LinkedEntry.run?,
    SourceCoreDirectLinking.LinkedEntry.runExact?, mismatch]

theorem run_of_prepared (raw : Workspace.RawWorkspace) (seed : Seed)
    (inputs : List Core.Value) (limits : Limits) (store : Core.Store)
    (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared) :
    run raw seed inputs limits store =
      match prepared.run? inputs limits.executionFuel store with
      | some result => .ok result
      | none => .error (.inputTypesMismatch prepared.inputTypes
          (inputs.map Core.Value.type)) := by
  unfold run
  rw [preparedOk]
  rfl

theorem run_of_prepared_matching_types (raw : Workspace.RawWorkspace)
    (seed : Seed) (inputs : List Core.Value) (limits : Limits)
    (store : Core.Store) (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared)
    (finite : prepared.entry.runtime = none)
    (typesEqual : inputs.map Core.Value.type = prepared.inputTypes) :
    run raw seed inputs limits store = .ok (Core.runStateful
      limits.executionFuel
      (Core.State.initial prepared.entry.elaborated.core inputs store)) := by
  rw [run_of_prepared raw seed inputs limits store prepared preparedOk]
  rw [PreparedEntry.run?_of_matching_types prepared inputs
    limits.executionFuel store finite typesEqual]

theorem run_of_prepared_mismatched_types (raw : Workspace.RawWorkspace)
    (seed : Seed) (inputs : List Core.Value) (limits : Limits)
    (store : Core.Store) (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared)
    (mismatch : inputs.map Core.Value.type ≠ prepared.inputTypes) :
    run raw seed inputs limits store = .error (.inputTypesMismatch
      prepared.inputTypes (inputs.map Core.Value.type)) := by
  rw [run_of_prepared raw seed inputs limits store prepared preparedOk]
  rw [PreparedEntry.run?_of_mismatched_types prepared inputs
    limits.executionFuel store mismatch]

theorem runExact_of_prepared (raw : Workspace.RawWorkspace) (seed : Seed)
    (inputs : List Core.Value) (limits : Limits) (store : Core.Store)
    (prepared : PreparedEntry)
    (preparedOk : prepare raw seed limits = .ok prepared) :
    runExact raw seed inputs limits store =
      match prepared.runExact? inputs limits.executionFuel store with
      | some result => .ok result
      | none => .error (.inputTypesMismatch prepared.inputTypes
          (inputs.map Core.Value.type)) := by
  unfold runExact
  rw [preparedOk]
  rfl

end Solcore.Frontend.SourceProgramExecution
