import Solcore.Frontend.SourceCoreScalar
import Solcore.Frontend.SourceCoreControl
import Solcore.Frontend.SourceCorePrimitive
import Solcore.Frontend.SourceCoreLoops
import Solcore.Frontend.SourceCoreFaultSites
import Solcore.Frontend.SourceCoreRuntimeFaultSites
import Solcore.Frontend.SourceCoreAssignmentPolicy
import Solcore.Frontend.SourceCompilationPlan

/-! Prepared scalar/product seed entries. Plan validation and Core compilation
happen once; invocation only checks values and builds optional input cells.
The entry body remains open over references, with source-order allocation and
newest-first lexical lookup. This slice accepts an empty initial store only. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreBasicEntry

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan

structure Input where
  id : Resolved.LocalId
  sourceType : TypeSystem.Ty
  type : Core.Ty
  comptime : Bool
  deriving Repr

def inputScope (inputs : List Input) : SourceCoreBasic.Scope :=
  (inputs.map fun input => (input.id, input.type)).reverse

def inputContext (inputs : List Input) : Core.Context :=
  (inputs.map fun input => Core.OptionalCell.referenceType input.type).reverse

theorem inputScope_context (inputs : List Input) :
    SourceCoreLocalCell.coreContext (inputScope inputs) = inputContext inputs := by
  simp [inputScope, inputContext, SourceCoreLocalCell.coreContext, Core.OptionalCell.referenceType,
    List.map_reverse, List.map_map]

structure Entry where
  key : Key
  /-- Source parameter order; allocation follows this order. -/
  inputs : List Input
  sourceResultType : TypeSystem.Ty
  resultType : Core.Ty
  resultProjection : SourceCoreScalar.lowerType (.declaration key.declaration) sourceResultType = .ok resultType
  faultSites : SourceCoreFaultSites.Table
  body : Core.Expr
  bodyTyped : Core.HasType (inputContext inputs) body (Core.LanguageResult.resultType resultType)
  deriving Repr

structure PreparedProgram where
  plan : Plan
  /-- Seed order and duplicate seeds are retained. -/
  entries : List Entry
  deriving Repr

inductive Error where
  | preparation (error : SourceCompilationPlan.Error)
  | lowering (error : SourceCoreBasic.Error)
  | faultSites (error : SourceCoreFaultSites.Error)
  | assignmentFaultSites (error : SourceCoreAssignmentFaultSites.Error)
  | invalidFunctionType (key : Key)
  | resultMetadataMismatch (key : Key)
  | stagedResultUnsupported (key : Key)
  | assumptionsUnsupported (key : Key) (count : Nat)
  | expectedStatementRoot (id : ExpressionId)
  | coreCheckFailed (key : Key) (expected : Core.Ty) (actual : Option Core.Ty)
  | argumentCountMismatch (expected actual : Nat)
  | inputShape (index : Nat) (expected : Core.Ty)
  | inputTypeMismatch (index : Nat) (expected actual : Core.Ty)
  | initialStoreUnsupported (length : Nat)
  deriving Repr, DecidableEq

private def lowerInputs (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List Input)
  | _, [] => pure []
  | scope, binder :: rest => do
      -- Comptime parameter markers retain the same deep runtime value boundary.
      -- Their elaboration and compile-time evaluation remain separate.
      let type ← (SourceCoreScalar.lowerBinder source scope { binder with comptime := false }).mapError Error.lowering
      let inputs ← lowerInputs source ((binder.id, type) :: scope) rest
      pure ({ id := binder.id, sourceType := binder.scheme.body, type, comptime := binder.comptime } :: inputs)

/-- Reuse the same parameter validation for prepared program entries. -/
def prepareInputs (source : TypedSource) : Except Error (List Input) :=
  lowerInputs source [] source.inputs

private def compileEntry (compilationFuel : Nat)
    (specialized : SourceSpecialization.SpecializedFunction) : Except Error Entry := do
  let function := specialized.function
  if function.returnComptime then throw (.stagedResultUnsupported specialized.key)
  unless specialized.assumptions.isEmpty do
    throw (.assumptionsUnsupported specialized.key specialized.assumptions.length)
  let sourceResultType ← match function.type with
    | .function _ result => pure result
    | _ => .error (.invalidFunctionType specialized.key)
  if sourceResultType ≠ function.inferredBodyType then
    throw (.resultMetadataMismatch specialized.key)
  let result ← match projection : SourceCoreScalar.lowerType
      (.declaration specialized.key.declaration) sourceResultType with
    | .ok type => pure (⟨type, projection⟩ : { type : Core.Ty //
        SourceCoreScalar.lowerType (.declaration specialized.key.declaration) sourceResultType = .ok type })
    | .error error => .error (.lowering (.typeProjection error))
  let resultType := result.val
  let source := function.typedBody
  let sites ← (SourceCoreRuntimeFaultSites.prepare source sourceResultType).mapError fun
    | .sites error => Error.faultSites error
    | .assignments error => Error.assignmentFaultSites error
  let faultSites := sites.table
  let inputs ← lowerInputs source [] source.inputs
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => .error (.expectedStatementRoot id)
  let policy := SourceCoreAssignmentPolicy.attach {
    lowerExpression := fun fuel source scope id reasonAt => SourceCorePrimitive.lowerExpressionWithReasons
      fuel ⟨function.solvedRequirements⟩ source scope id reasonAt
  } sites.assignments
  let body ← (SourceCoreLoops.lowerStatementsWithPolicy policy
    compilationFuel source (inputScope inputs) statements resultType faultSites.reasonAt
    Core.Word.zero faultSites.escapedReason).mapError Error.lowering
  if checked : Core.infer? (inputContext inputs) body = some (Core.LanguageResult.resultType resultType) then
    pure { key := specialized.key, inputs, sourceResultType, resultType, resultProjection := result.property,
           faultSites, body
           bodyTyped := Core.infer_sound checked }
  else
    throw (.coreCheckFailed specialized.key (Core.LanguageResult.resultType resultType)
      (Core.infer? (inputContext inputs) body))

/-- Authenticate the complete input plan and selected evidence before compiling
its seeds. Calls and other constructs outside SourceCoreControl remain errors.
The legacy reason argument is retained for callers; prepared entries assign a
distinct diagnostic reason to each local-read and assignment site. -/
def prepare (program : CheckedProgram) (plan : Plan) (compilationFuel : Nat)
    (_reason : Core.Word) : Except Error PreparedProgram := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.preparation
  let entries ← executablePlan.seedKeys.mapM fun key => do
    let specialized ← (SourceCompilationPlan.exactSpecialization executablePlan key).mapError Error.preparation
    compileEntry compilationFuel specialized
  pure { plan := executablePlan, entries }

def PreparedProgram.findEntry? (program : PreparedProgram) (key : Key) : Option Entry :=
  program.entries.find? fun entry => decide (entry.key = key)

def Entry.failureDiagnostic? (entry : Entry) (reason : Core.Word) :
    Option SourceCoreFaultSites.Diagnostic :=
  entry.faultSites.diagnostic? reason

/-- A checked input frame keeps the store world and lexical references aligned.
Its context index records only already prepared inputs. -/
private structure InputFrame (context : Core.Context) where
  world : Core.StoreTyping
  store : Core.Store
  environment : Core.Environment
  storeTyped : Core.RuntimeStoreHasTypes world store
  environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context

private def InputFrame.empty : InputFrame [] := {
  world := [], store := [], environment := []
  storeTyped := .nil [], environmentTyped := .nil
}

private def InputFrame.push {context : Core.Context} (frame : InputFrame context)
    (type : Core.Ty) (value : SourceCoreScalar.Value)
    (sameType : SourceCoreScalar.Value.type value = type) :
    InputFrame (Core.OptionalCell.referenceType type :: context) := by
  let payloadType := Core.OptionalCell.cellType type
  have extension : Core.WorldExtends frame.world (frame.world ++ [payloadType]) := ⟨_, rfl⟩
  have valueTyped : Core.RuntimeValueHasType frame.world
      (.inRight .unit (SourceCoreScalar.Value.toCore value)) payloadType := by
    apply Core.RuntimeValueHasType.inRight
    exact sameType ▸ SourceCoreScalar.Value.typed value frame.world
  exact {
    world := frame.world ++ [payloadType]
    store := frame.store ++ [.inRight .unit (SourceCoreScalar.Value.toCore value)]
    environment := .cellRef payloadType frame.store.length :: frame.environment
    storeTyped := frame.storeTyped.allocate valueTyped
    environmentTyped := .cons
      (.cellRef (by simp [← frame.storeTyped.length_eq]))
      (frame.environmentTyped.weaken extension)
  }

private def prepareArguments {context : Core.Context} (index : Nat)
    (frame : InputFrame context) : (inputs : List Input) → List Core.Value →
      Except Error (InputFrame (inputContext inputs ++ context))
  | [], [] => pure (by simpa [inputContext] using frame)
  | input :: inputs, argument :: arguments => do
      let value ← match SourceCoreScalar.Value.ofCore? argument with
        | some value => pure value
        | none => .error (.inputShape index input.type)
      if sameType : SourceCoreScalar.Value.type value = input.type then
        let extended := frame.push input.type value sameType
        let prepared ← prepareArguments (index + 1) extended inputs arguments
        pure (by simpa [inputContext, List.reverse_cons, List.append_assoc] using prepared)
      else
        throw (.inputTypeMismatch index input.type (SourceCoreScalar.Value.type value))
  | inputs, arguments => .error (.argumentCountMismatch (index + inputs.length) (index + arguments.length))

structure Checkpoint (resultType : Core.Ty) where
  state : Core.State
  typed : Core.StateHasType state (Core.LanguageResult.resultType resultType)
  deriving Repr

structure Result (resultType : Core.Ty) where
  observation : Core.LanguageResult.Observation
  typed : observation.HasType resultType
  deriving Repr

/-- Check complete scalar/product shapes, then append input cells in source
parameter order. No code generation or plan replay occurs at this boundary. -/
def Entry.start (entry : Entry) (arguments : List Core.Value)
    (initialStore : Core.Store := []) : Except Error (Checkpoint entry.resultType) := do
  match initialStore with
  | _ :: _ => throw (.initialStoreUnsupported initialStore.length)
  | [] =>
      if entry.inputs.length ≠ arguments.length then
        throw (.argumentCountMismatch entry.inputs.length arguments.length)
      let frame ← prepareArguments 0 InputFrame.empty entry.inputs arguments
      let environmentTyped : Core.RuntimeEnvironmentHasTypes frame.world frame.environment
          (inputContext entry.inputs) := by simpa using frame.environmentTyped
      pure {
        state := .initial entry.body frame.environment frame.store
        typed := .eval frame.storeTyped environmentTyped entry.bodyTyped .nil
      }

def Checkpoint.resume {type : Core.Ty} (checkpoint : Checkpoint type) (fuel : Nat) : Result type := {
  observation := Core.LanguageResult.observeResult (Core.runStateful fuel checkpoint.state)
  typed := Core.LanguageResult.observeResult_hasType
    (Core.well_typed_runStateful_has_type checkpoint.typed fuel)
}

theorem Checkpoint.resume_after_exhaustion {type : Core.Ty}
    (checkpoint next : Checkpoint type) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  congrArg Core.LanguageResult.observeResult (Core.runStateful_resume exhausted additional)

def Result.checkpoint? {type : Core.Ty} (result : Result type) : Option (Checkpoint type) :=
  match observation : result.observation with
  | .outOfFuel state => some ⟨state, by
      have typed := result.typed
      rw [observation] at typed
      exact typed⟩
  | _ => none

def Entry.run (entry : Entry) (arguments : List Core.Value) (executionFuel : Nat)
    (initialStore : Core.Store := []) : Except Error (Result entry.resultType) := do
  let checkpoint ← entry.start arguments initialStore
  pure (checkpoint.resume executionFuel)

theorem Result.ne_internalFault {type : Core.Ty} (result : Result type)
    (error : Core.MachineFault) (state : Core.State) :
    result.observation ≠ .internalFault error state := by
  intro wrong
  have typed := result.typed
  rw [wrong] at typed
  exact typed

theorem Result.ne_invalidCarrier {type : Core.Ty} (result : Result type)
    (value : Core.Value) (store : Core.Store) :
    result.observation ≠ .invalidCarrier value store := by
  intro wrong
  have typed := result.typed
  rw [wrong] at typed
  exact typed

theorem Result.success_typed {type : Core.Ty} (result : Result type)
    {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store ∧ Core.RuntimeValueHasType world value type := by
  have typed := result.typed
  rw [success] at typed
  exact typed

theorem Result.success_type {type : Core.Ty} (result : Result type)
    {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) : value.type = type := by
  obtain ⟨_, _, typed⟩ := result.success_typed success
  exact typed.type_eq

theorem Result.failure_typed {type : Core.Ty} (result : Result type)
    {reason : Core.Word} {store : Core.Store}
    (failure : result.observation = .failed reason store) :
    ∃ world, Core.RuntimeStoreHasTypes world store := by
  have typed := result.typed
  rw [failure] at typed
  exact typed

theorem Result.suspension_typed {type : Core.Ty} (result : Result type)
    {state : Core.State} (suspended : result.observation = .outOfFuel state) :
    Core.StateHasType state (Core.LanguageResult.resultType type) := by
  have typed := result.typed
  rw [suspended] at typed
  exact typed

end Solcore.Frontend.SourceCoreBasicEntry
