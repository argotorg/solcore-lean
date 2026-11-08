import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCore.Internal.FaultSites
import Solcore.Frontend.SourceCompilationPlan
import Solcore.Frontend.SourceCore.Data
import Solcore.Core.Internal.ConventionLaws
import Std.Sync.Mutex

/-!
# Prepared entries and public values

Prepared scalar, recursive, function and general entries, the catalog-backed public values, and the
assignment policy.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreAssignmentPolicy
/-! Attach absent-operand diagnostics to the compound/unary CPS callbacks.
Equal assignment continues through the entry profile's own target projector. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreAssignmentPolicy

def attach (policy : SourceCoreLoops.Policy) (sites : SourceCoreAssignmentFaultSites.Table) :
    SourceCoreLoops.Policy := { policy with
  assignValue := some fun expression fuel source scope site assignment operator rhs outputType next reasonAt =>
    SourceCoreAssignments.assignValueWithReasons expression fuel source scope assignment operator rhs outputType
      next (sites.reasonAt site assignment.target.root (.value operator)) reasonAt
  assignBitNot := some fun source scope site assignment outputType next =>
    SourceCoreAssignments.assignBitNot source scope assignment outputType next
      (sites.reasonAt site assignment.target.root .bitNot)
}

end Solcore.Frontend.SourceCoreAssignmentPolicy
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreBasicEntry
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreGeneralEntry
/-! Prepared entries indexed by their actual data definitions. Raw public
inputs are checked through their complete value trees and cannot supply code,
references, or host functions. Constructor payload typing does not authenticate
source constructor metadata: that belongs to the source-value adapter. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreGeneralEntry

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Checked := SourceCoreDataCatalog.Checked

def definitions (checked : Checked) : Core.DataEnvironment := checked.catalog.definitions

structure TypeProjection (checked : Checked) (sourceType : TypeSystem.Ty) where
  type : Core.Ty
  typed : type.WellFormed (definitions checked)
  generated : checked.catalog.project sourceType = .ok type
  deriving Repr

private theorem checkedProject_generated {checked : Checked} {sourceType : TypeSystem.Ty}
    {projection : SourceCoreDataCatalog.Projection checked.catalog.definitions}
    (accepted : checked.project sourceType = .ok projection) :
    checked.catalog.project sourceType = .ok projection.type := by
  unfold SourceCoreDataCatalog.Checked.project at accepted
  cases generated : checked.catalog.project sourceType with
  | error error => simp [generated, bind, Except.bind] at accepted
  | ok type =>
    simp only [generated, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
      rfl
    · simp at accepted

def projectType (checked : Checked) (sourceType : TypeSystem.Ty) :
    Except SourceCoreDataCatalog.Error (TypeProjection checked sourceType) :=
  match accepted : checked.project sourceType with
  | .error error => .error error
  | .ok projection => .ok ⟨projection.type, projection.typed, checkedProject_generated accepted⟩

structure Input (checked : Checked) where
  id : Resolved.LocalId
  sourceType : TypeSystem.Ty
  projection : TypeProjection checked sourceType
  deriving Repr

def Input.type {checked : Checked} (input : Input checked) : Core.Ty := input.projection.type

def inputScope {checked : Checked} (inputs : List (Input checked)) : SourceCoreBasic.Scope :=
  (inputs.map fun input => (input.id, input.type)).reverse

def inputContext {checked : Checked} (inputs : List (Input checked)) : Core.Context :=
  (inputs.map fun input => Core.OptionalCell.referenceType input.type).reverse

theorem inputScope_context {checked : Checked} (inputs : List (Input checked)) :
    SourceCoreLocalCell.coreContext (inputScope inputs) = inputContext inputs := by
  simp [inputScope, inputContext, SourceCoreLocalCell.coreContext, Core.OptionalCell.referenceType,
    List.map_reverse, List.map_map]

/-- The callback runs once at compilation. It may assemble ordinary globals,
helpers, and source body code under these input references; invocation never
replays the source graph or regenerates Core code. -/
structure BodyRequest (checked : Checked) where
  plan : Plan
  specialized : SourceSpecialization.SpecializedFunction
  inputs : List (Input checked)
  sourceResultType : TypeSystem.Ty
  result : TypeProjection checked sourceResultType
  deriving Repr

structure LoweredBody where
  expression : Core.Expr
  faultSites : SourceCoreFaultSites.Table
  deriving Repr

abbrev BodyLowerer (checked : Checked) (error : Type) :=
  Nat → BodyRequest checked → Except error LoweredBody

inductive CompileError (error : Type) where
  | plan (error : SourceCompilationPlan.Error)
  | catalog (error : SourceCoreDataCatalog.Error)
  | lowering (error : error)
  | invalidFunctionType (key : Key)
  | resultMetadataMismatch (key : Key)
  | assumptionsUnsupported (key : Key)
  | stagedResultUnsupported (key : Key)
  | stagedInputUnsupported (id : Resolved.LocalId)
  | inputOwnerMismatch (id : Resolved.LocalId) (expected : Resolved.DeclarationId)
  | duplicateInput (id : Resolved.LocalId)
  | polymorphicInput (id : Resolved.LocalId)
  | inputRequirements (id : Resolved.LocalId)
  | coreCheckFailed (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

structure Entry (checked : Checked) where
  key : Key
  inputs : List (Input checked)
  sourceResultType : TypeSystem.Ty
  result : TypeProjection checked sourceResultType
  faultSites : SourceCoreFaultSites.Table
  body : Core.Expr
  bodyTyped : Core.HasType (inputContext inputs) body
    (Core.LanguageResult.resultType result.type) (definitions checked)
  deriving Repr

def Entry.resultType {checked : Checked} (entry : Entry checked) : Core.Ty := entry.result.type

private def prepareInputs {error : Type} (checked : Checked) (owner : Resolved.DeclarationId) :
    List Resolved.LocalId → List TypedBinder → Except (CompileError error) (List (Input checked))
  | _, [] => .ok []
  | seen, binder :: rest => do
    if binder.id.owner ≠ owner then throw (.inputOwnerMismatch binder.id owner)
    if binder.id ∈ seen then throw (.duplicateInput binder.id)
    unless binder.scheme.quantified.isEmpty do throw (.polymorphicInput binder.id)
    unless binder.schemeRequirements.isEmpty do throw (.inputRequirements binder.id)
    if binder.comptime && !checked.catalog.callableContracts then throw (.stagedInputUnsupported binder.id)
    let projection ← (projectType checked binder.scheme.body).mapError CompileError.catalog
    let inputs ← prepareInputs checked owner (binder.id :: seen) rest
    pure ({ id := binder.id, sourceType := binder.scheme.body, projection } :: inputs)

/-- A callback's output is accepted only by the checker for the actual catalog.
The returned entry retains both source projection and complete body typing.
`prepare` authenticates the plan before calling this lower-level constructor;
direct users are responsible for source-plan authenticity. -/
def compile {error : Type} (checked : Checked) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction) (compilationFuel : Nat)
    (lowerBody : BodyLowerer checked error) (allowClosedAssumptions : Bool := false) :
    Except (CompileError error) (Entry checked) := do
  unless specialized.assumptions.isEmpty || allowClosedAssumptions do throw (.assumptionsUnsupported specialized.key)
  if specialized.function.returnComptime && !checked.catalog.callableContracts then throw (.stagedResultUnsupported specialized.key)
  let sourceResultType ← match specialized.function.type with
    | .function _ result => pure result
    | _ => throw (.invalidFunctionType specialized.key)
  if sourceResultType ≠ specialized.function.inferredBodyType then
    throw (.resultMetadataMismatch specialized.key)
  let result ← (projectType checked sourceResultType).mapError CompileError.catalog
  let source := specialized.function.typedBody
  let inputs ← prepareInputs checked source.owner [] source.inputs
  let lowered ← (lowerBody compilationFuel {plan, specialized, inputs, sourceResultType, result}).mapError CompileError.lowering
  if accepted : Core.infer? (inputContext inputs) lowered.expression (definitions checked) =
      some (Core.LanguageResult.resultType result.type) then
    pure {
      key := specialized.key, inputs, sourceResultType, result,
      faultSites := lowered.faultSites, body := lowered.expression, bodyTyped := Core.infer_sound accepted
    }
  else throw (.coreCheckFailed (Core.LanguageResult.resultType result.type)
    (Core.infer? (inputContext inputs) lowered.expression (definitions checked)))

structure PreparedProgram (checked : Checked) where
  plan : Plan
  entries : List (Entry checked)
  deriving Repr

/-- Assemble an already authenticated executable plan. The caller owns source
plan provenance; every native body is still checked under the actual catalog. -/
def prepareValidated {error : Type} (plan : Plan) (checked : Checked)
    (compilationFuel : Nat) (lowerBody : BodyLowerer checked error) (allowClosedAssumptions : Bool := false) :
    Except (CompileError error) (PreparedProgram checked) := do
  let entries ← plan.seedKeys.mapM fun key => do
    let specialized ← (SourceCompilationPlan.exactSpecialization plan key).mapError CompileError.plan
    compile checked plan specialized compilationFuel lowerBody allowClosedAssumptions
  pure { plan, entries }

def prepare {error : Type} (program : CheckedProgram) (plan : Plan) (checked : Checked)
    (compilationFuel : Nat) (lowerBody : BodyLowerer checked error) (allowClosedAssumptions : Bool := false) :
    Except (CompileError error) (PreparedProgram checked) := do
  let plan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError CompileError.plan
  prepareValidated plan checked compilationFuel lowerBody allowClosedAssumptions

def PreparedProgram.findEntry? {checked : Checked} (program : PreparedProgram checked) (key : Key) :
    Option (Entry checked) := program.entries.find? fun entry => decide (entry.key = key)

inductive InputPath where
  | pairLeft | pairRight | sumPayload | constructorPayload
  deriving Repr, DecidableEq

inductive ValueErrorCode where
  | shapeMismatch (expected actual : Core.Ty)
  | sumAnnotationMismatch (expected actual : Core.Ty)
  | constructorOwnerMismatch (expected actual : Core.DataTypeId)
  | unknownConstructor (constructor : Core.ConstructorId)
  | functionHandleRequired
  | externalReferenceUnsupported
  | externalHostUnsupported
  deriving Repr, DecidableEq

structure ValueError where
  path : List InputPath := []
  code : ValueErrorCode
  deriving Repr, DecidableEq

private def ValueError.at (step : InputPath) (error : ValueError) : ValueError :=
  { error with path := step :: error.path }

/-- Public values are heap-independent. A successful deep check provides the
runtime typing proof in every world, including worlds extended by input cells. -/
structure ValidatedValue (definitions : Core.DataEnvironment) (value : Core.Value) (type : Core.Ty) : Type where
  typed : ∀ world, Core.RuntimeValueHasType world value type definitions

def validateValue (definitions : Core.DataEnvironment) : (value : Core.Value) → (expected : Core.Ty) →
    Except ValueError (ValidatedValue definitions value expected)

  | .closure .., _ => throw ⟨[], .functionHandleRequired⟩
  | .cellRef .., _ => throw ⟨[], .externalReferenceUnsupported⟩
  | .hostFunction .., _ => throw ⟨[], .externalHostUnsupported⟩
  | .unit, .unit => pure ⟨fun _ => .unit⟩
  | .bool _, .bool => pure ⟨fun _ => .bool⟩
  | .word _, .word => pure ⟨fun _ => .word⟩
  | .integer _, .integer => pure ⟨fun _ => .integer⟩
  | .pair left right, .product leftType rightType => do
    let left ← (validateValue definitions left leftType).mapError (ValueError.at .pairLeft)
    let right ← (validateValue definitions right rightType).mapError (ValueError.at .pairRight)
    pure ⟨fun world => .pair (left.typed world) (right.typed world)⟩
  | .inLeft annotation payload, .sum leftType rightType => do
    if same : annotation = rightType then
      let payload ← (validateValue definitions payload leftType).mapError (ValueError.at .sumPayload)
      pure ⟨fun world => by cases same; exact Core.RuntimeValueHasType.inLeft (payload.typed world)⟩
    else throw ⟨[], .sumAnnotationMismatch rightType annotation⟩
  | .inRight annotation payload, .sum leftType rightType => do
    if same : annotation = leftType then
      let payload ← (validateValue definitions payload rightType).mapError (ValueError.at .sumPayload)
      pure ⟨fun world => by cases same; exact Core.RuntimeValueHasType.inRight (payload.typed world)⟩
    else throw ⟨[], .sumAnnotationMismatch leftType annotation⟩
  | .constructed constructor payload, .namedData id => do
    if same : constructor.owner = id then
      match found : definitions.lookupConstructorPayloadType? constructor with
      | none => throw ⟨[], .unknownConstructor constructor⟩
      | some payloadType =>
        let payload ← (validateValue definitions payload payloadType).mapError (ValueError.at .constructorPayload)
        pure ⟨fun world => same ▸ Core.RuntimeValueHasType.constructed found (payload.typed world)⟩
    else throw ⟨[], .constructorOwnerMismatch id constructor.owner⟩
  | value, expected => throw ⟨[], .shapeMismatch expected value.type⟩
termination_by value _ => value

inductive RunError where
  | argumentCountMismatch (expected actual : Nat)
  | input (index : Nat) (error : ValueError)
  | initialStoreUnsupported (length : Nat)
  deriving Repr, DecidableEq

structure InputFrame (definitions : Core.DataEnvironment) (context : Core.Context) where
  world : Core.StoreTyping
  store : Core.Store
  environment : Core.Environment
  storeTyped : Core.RuntimeStoreHasTypes world store definitions
  environmentTyped : Core.RuntimeEnvironmentHasTypes world environment context definitions

private def InputFrame.empty (definitions : Core.DataEnvironment) : InputFrame definitions [] := {
  world := [], store := [], environment := []
  storeTyped := .nil definitions, environmentTyped := .nil
}

private def InputFrame.push {definitions : Core.DataEnvironment} {context : Core.Context}
    (frame : InputFrame definitions context) (type : Core.Ty) (value : Core.Value)
    (validated : ValidatedValue definitions value type) :
    InputFrame definitions (Core.OptionalCell.referenceType type :: context) := by
  let payloadType := Core.OptionalCell.cellType type
  have extension : Core.WorldExtends frame.world (frame.world ++ [payloadType]) := ⟨_, rfl⟩
  have valueTyped : Core.RuntimeValueHasType frame.world (.inRight .unit value) payloadType definitions :=
    .inRight (validated.typed frame.world)
  exact {
    world := frame.world ++ [payloadType]
    store := frame.store ++ [.inRight .unit value]
    environment := .cellRef payloadType frame.store.length :: frame.environment
    storeTyped := frame.storeTyped.allocate valueTyped
    environmentTyped := .cons (.cellRef (by simp [← frame.storeTyped.length_eq]))
      (frame.environmentTyped.weaken extension)
  }

/-- Input preparation depends on the actual Core types and definitions. Both
strict and source-compatible artifacts share this checked native boundary. -/
def nativeInputContext (types : List Core.Ty) : Core.Context :=
  (types.map Core.OptionalCell.referenceType).reverse

def prepareNativeArguments {definitions : Core.DataEnvironment} {context : Core.Context} (index : Nat)
    (frame : InputFrame definitions context) : (types : List Core.Ty) → List Core.Value →
      Except RunError (InputFrame definitions (nativeInputContext types ++ context))
  | [], [] => pure (by simpa [nativeInputContext] using frame)
  | type :: types, argument :: arguments => do
    let value ← (validateValue definitions argument type).mapError (RunError.input index)
    let prepared ← prepareNativeArguments (index + 1) (frame.push type argument value) types arguments
    pure (by simpa [nativeInputContext, List.reverse_cons, List.append_assoc] using prepared)
  | types, arguments => throw (.argumentCountMismatch (index + types.length) (index + arguments.length))


structure Checkpoint (definitions : Core.DataEnvironment) (resultType : Core.Ty) where
  state : Core.State
  typed : Core.StateHasType state (Core.LanguageResult.resultType resultType) definitions
  deriving Repr

structure Result (definitions : Core.DataEnvironment) (resultType : Core.Ty) where
  observation : Core.LanguageResult.Observation
  typed : observation.HasType resultType definitions
  deriving Repr

/-- A native body is checked against its actual definitions independently of
which source representation supplied the input/result projections. -/
structure NativeEntry (definitions : Core.DataEnvironment) where
  inputTypes : List Core.Ty
  resultType : Core.Ty
  body : Core.Expr
  bodyTyped : Core.HasType (nativeInputContext inputTypes) body
    (Core.LanguageResult.resultType resultType) definitions
  deriving Repr

inductive NativeCompileError where
  | coreCheckFailed (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

def NativeEntry.compile (definitions : Core.DataEnvironment) (inputTypes : List Core.Ty)
    (resultType : Core.Ty) (body : Core.Expr) : Except NativeCompileError (NativeEntry definitions) :=
  if accepted : Core.infer? (nativeInputContext inputTypes) body definitions =
      some (Core.LanguageResult.resultType resultType) then
    .ok ⟨inputTypes, resultType, body, Core.infer_sound accepted⟩
  else .error (.coreCheckFailed (Core.LanguageResult.resultType resultType)
    (Core.infer? (nativeInputContext inputTypes) body definitions))

theorem NativeEntry.compile_fields {definitions : Core.DataEnvironment}
    {inputTypes : List Core.Ty} {resultType : Core.Ty} {body : Core.Expr}
    {entry : NativeEntry definitions}
    (accepted : NativeEntry.compile definitions inputTypes resultType body = .ok entry) :
    entry.inputTypes = inputTypes ∧ entry.resultType = resultType ∧ entry.body = body := by
  unfold NativeEntry.compile at accepted
  split at accepted
  · cases accepted
    exact ⟨rfl, rfl, rfl⟩
  · cases accepted

/-- Fresh native inputs are administrative cells in source argument order.
Existing public Core stores retain their historical rejection behavior. -/
def NativeEntry.start {definitions : Core.DataEnvironment} (entry : NativeEntry definitions)
    (arguments : List Core.Value) (initialStore : Core.Store := []) :
    Except RunError (Checkpoint definitions entry.resultType) := do
  match initialStore with
  | _ :: _ => throw (.initialStoreUnsupported initialStore.length)
  | [] =>
    if entry.inputTypes.length ≠ arguments.length then
      throw (.argumentCountMismatch entry.inputTypes.length arguments.length)
    let frame ← prepareNativeArguments 0 (InputFrame.empty definitions) entry.inputTypes arguments
    let environmentTyped : Core.RuntimeEnvironmentHasTypes frame.world frame.environment
        (nativeInputContext entry.inputTypes) definitions := by simpa using frame.environmentTyped
    pure {
      state := .initial entry.body frame.environment frame.store
      typed := .eval frame.storeTyped environmentTyped entry.bodyTyped .nil
    }

def Entry.native {checked : Checked} (entry : Entry checked) : NativeEntry (definitions checked) := {
  inputTypes := entry.inputs.map (·.type)
  resultType := entry.resultType
  body := entry.body
  bodyTyped := by
    simpa [nativeInputContext, inputContext, Entry.resultType, List.map_map, Function.comp_def] using entry.bodyTyped
}

def Entry.start {checked : Checked} (entry : Entry checked) (arguments : List Core.Value)
    (initialStore : Core.Store := []) : Except RunError (Checkpoint (definitions checked) entry.resultType) :=
  entry.native.start arguments initialStore

def Checkpoint.resume {definitions : Core.DataEnvironment} {type : Core.Ty}
    (checkpoint : Checkpoint definitions type) (fuel : Nat) : Result definitions type := {
  observation := Core.LanguageResult.observeResult (Core.runStateful fuel checkpoint.state)
  typed := Core.LanguageResult.observeResult_hasType
    (Core.well_typed_runStateful_has_type checkpoint.typed fuel)
}

theorem Checkpoint.resume_after_exhaustion {definitions : Core.DataEnvironment} {type : Core.Ty}
    (checkpoint next : Checkpoint definitions type) (spent additional : Nat)
    (exhausted : Core.runStateful spent checkpoint.state = .outOfFuel next.state) :
    (next.resume additional).observation = (checkpoint.resume (spent + additional)).observation :=
  congrArg Core.LanguageResult.observeResult (Core.runStateful_resume exhausted additional)

def Result.checkpoint? {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) : Option (Checkpoint definitions type) :=
  match observation : result.observation with
  | .outOfFuel state => some ⟨state, by
    have typed := result.typed
    rw [observation] at typed
    exact typed⟩
  | _ => none

def NativeEntry.run {definitions : Core.DataEnvironment} (entry : NativeEntry definitions)
    (arguments : List Core.Value) (executionFuel : Nat) (initialStore : Core.Store := []) :
    Except RunError (Result definitions entry.resultType) := do
  let checkpoint ← entry.start arguments initialStore
  pure (checkpoint.resume executionFuel)

def Entry.run {checked : Checked} (entry : Entry checked) (arguments : List Core.Value) (executionFuel : Nat)
    (initialStore : Core.Store := []) : Except RunError (Result (definitions checked) entry.resultType) := do
  let checkpoint ← entry.start arguments initialStore
  pure (checkpoint.resume executionFuel)

def Entry.failureDiagnostic? {checked : Checked} (entry : Entry checked) (reason : Core.Word) :
    Option SourceCoreFaultSites.Diagnostic := entry.faultSites.diagnostic? reason

theorem Result.success_typed {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) :
    ∃ world, Core.RuntimeStoreHasTypes world store definitions ∧ Core.RuntimeValueHasType world value type definitions := by
  have typed := result.typed
  rw [success] at typed
  exact typed

theorem Result.failure_typed {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) {reason : Core.Word} {store : Core.Store}
    (failure : result.observation = .failed reason store) :
    ∃ world, Core.RuntimeStoreHasTypes world store definitions := by
  have typed := result.typed
  rw [failure] at typed
  exact typed

theorem Result.suspension_typed {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) {state : Core.State} (suspended : result.observation = .outOfFuel state) :
    Core.StateHasType state (Core.LanguageResult.resultType type) definitions := by
  have typed := result.typed
  rw [suspended] at typed
  exact typed

theorem Result.ne_internalFault {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) (error : Core.MachineFault) (state : Core.State) :
    result.observation ≠ .internalFault error state := by
  intro wrong
  have typed := result.typed
  rw [wrong] at typed
  exact typed

theorem Result.ne_invalidCarrier {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) (value : Core.Value) (store : Core.Store) :
    result.observation ≠ .invalidCarrier value store := by
  intro wrong
  have typed := result.typed
  rw [wrong] at typed
  exact typed

theorem Result.success_type {definitions : Core.DataEnvironment} {type : Core.Ty}
    (result : Result definitions type) {value : Core.Value} {store : Core.Store}
    (success : result.observation = .succeeded value store) : value.type = type := by
  obtain ⟨_, _, typed⟩ := result.success_typed success
  exact typed.type_eq

theorem Entry.definitions_wellFormed {checked : Checked} (_entry : Entry checked) :
    (definitions checked).WellFormed := checked.definitionsTyped

end Solcore.Frontend.SourceCoreGeneralEntry
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataValues
/-! Independent public source values for the catalog-backed Core runtime.
This boundary carries data and source constructor metadata, never executable
Core code or references. Outer comptime wrappers are projected at runtime;
nominal arguments and the raw inner type of a proxy keep their identities.
No comptime expression is evaluated here. Program-owned function handles are a
separate future boundary and are explicitly rejected by this adapter. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataValues

open SourceInference TypeSystem

structure Context where
  checked : SourceCoreDataCatalog.Checked
  signatures : ProgramSignatures
  deriving Repr

inductive Value where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : Value)
  | constructed (instantiation : DataConstructorInstantiation) (payloads : List Value)
  | mapping (keyType valueType : Ty) (entries : List (Value × Value))
  | proxy (inner : Ty)
  deriving Repr

mutual
  def Value.decEq (left right : Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case unit.unit => exact isTrue rfl
    case bool.bool left right => exact decidable_of_iff (left = right) (by simp)
    case word.word left right => exact decidable_of_iff (left = right) (by simp)
    case integer.integer left right => exact decidable_of_iff (left = right) (by simp)
    case proxy.proxy left right => exact decidable_of_iff (left = right) (by simp)
    case product.product leftA leftB rightA rightB =>
      letI := Value.decEq leftA rightA
      letI := Value.decEq leftB rightB
      exact decidable_of_iff (leftA = rightA ∧ leftB = rightB) (by simp)
    case constructed.constructed leftMetadata leftPayloads rightMetadata rightPayloads =>
      letI := Value.listDecEq leftPayloads rightPayloads
      exact decidable_of_iff (leftMetadata = rightMetadata ∧ leftPayloads = rightPayloads) (by simp)
    case mapping.mapping leftKey leftValue leftEntries rightKey rightValue rightEntries =>
      letI := Value.entriesDecEq leftEntries rightEntries
      exact decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue ∧ leftEntries = rightEntries) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.listDecEq (left right : List Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      letI := Value.decEq leftHead rightHead
      letI := Value.listDecEq leftTail rightTail
      exact decidable_of_iff (leftHead = rightHead ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.entriesDecEq (left right : List (Value × Value)) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      rcases leftHead with ⟨leftKey, leftValue⟩
      rcases rightHead with ⟨rightKey, rightValue⟩
      letI := Value.decEq leftKey rightKey
      letI := Value.decEq leftValue rightValue
      letI := Value.entriesDecEq leftTail rightTail
      letI : Decidable ((leftKey, leftValue) = (rightKey, rightValue)) :=
        decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue) (by simp)
      exact decidable_of_iff ((leftKey, leftValue) = (rightKey, rightValue) ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega
end

instance : DecidableEq Value := Value.decEq
instance : BEq Value := ⟨fun left right => decide (left = right)⟩
instance : LawfulBEq Value where
  eq_of_beq := of_decide_eq_true
  rfl := by intro value; exact decide_eq_true rfl

def Value.type : Value → Ty
  | .unit => .unit
  | .bool _ => .bool
  | .word _ => .word
  | .integer _ => .integer
  | .product left right => .product left.type right.type
  | .constructed instantiation _ => instantiation.resultType
  | .mapping key value _ => .mapping key value
  | .proxy inner => .proxy inner

inductive PathStep where
  | productLeft | productRight
  | constructorPayload (index : Nat)
  | mappingKey (index : Nat) | mappingValue (index : Nat) | mappingTail
  | rawCore (step : SourceCoreGeneralEntry.InputPath)
  deriving Repr, DecidableEq

inductive ErrorCode where
  | exhausted
  | catalog (error : SourceCoreDataCatalog.Error)
  | rawValue (error : SourceCoreGeneralEntry.ValueError)
  | sourceTypeMismatch (expected actual : Ty)
  | coreShapeMismatch (expected actual : Core.Ty)
  | payloadCountMismatch (expected actual : Nat)
  | invalidConstructor (constructor : Core.ConstructorId)
  | constructorMetadataMismatch
  | mappingMetadataMismatch (expectedKey expectedValue actualKey actualValue : Ty)
  | proxyIdentityMismatch (expected actual : Ty)
  | functionHandleRequired
  | externalReferenceUnsupported
  | externalHostUnsupported
  | nonCanonicalSourceValue
  | nonCanonicalCoreValue
  deriving Repr, DecidableEq

structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr, DecidableEq

def Error.at (step : PathStep) (error : Error) : Error :=
  { error with path := step :: error.path }

private def catalogError (error : SourceCoreDataCatalog.Error) : Error := ⟨[], .catalog error⟩
private def rawError (error : SourceCoreGeneralEntry.ValueError) : Error :=
  let path := error.path.map PathStep.rawCore
  match error.code with
  | .functionHandleRequired => ⟨path, .functionHandleRequired⟩
  | .externalReferenceUnsupported => ⟨path, .externalReferenceUnsupported⟩
  | .externalHostUnsupported => ⟨path, .externalHostUnsupported⟩
  | _ => ⟨path, .rawValue error⟩

def namedIdentity (context : Context) (type : Ty) : Except Error Core.DataTypeId := do
  match ← context.checked.catalog.project type |>.mapError catalogError with
  | .namedData identity => pure identity
  | actual => throw ⟨[], .coreShapeMismatch (.namedData ⟨0⟩) actual⟩

private def exactData (signatures : ProgramSignatures) (id : Resolved.DeclarationId) :
    Except Error ProgramDataSignature :=
  match signatures.dataTypes.filter fun signature => decide (signature.id = id) with
  | [] => throw (catalogError (.missingData id))
  | [signature] => pure signature
  | _ => throw (catalogError (.ambiguousData id))

/-- Reconstruct source metadata from the requested nominal type and exact
signature. The raw Core tag never supplies a parameter substitution. -/
def constructorMetadata (context : Context) (expected : Ty) (constructor : Core.ConstructorId) :
    Except Error DataConstructorInstantiation := do
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts expected with
    | none => throw ⟨[], .sourceTypeMismatch expected expected⟩
    | some parts => pure parts
  let signature ← exactData context.signatures declaration
  if signature.parameters.length ≠ arguments.length then
    throw (catalogError (.parameterCount declaration signature.parameters.length arguments.length))
  unless signature.parameters.Nodup do throw ⟨[], .constructorMetadataMismatch⟩
  let identity ← namedIdentity context expected
  unless constructor.owner = identity do throw ⟨[], .invalidConstructor constructor⟩
  let entry ← match context.checked.catalog.entries[identity.index]? with
    | none => throw ⟨[], .invalidConstructor constructor⟩
    | some entry => pure entry
  let sourceConstructor ← match entry.constructors[constructor.index]? with
    | none => throw ⟨[], .invalidConstructor constructor⟩
    | some sourceConstructor => pure sourceConstructor
  let signatureConstructor ← match signature.constructors.filter fun item => decide (item.id = sourceConstructor) with
    | [item] => pure item
    | _ => throw ⟨[], .invalidConstructor constructor⟩
  let substitution : ParameterSubstitution := signature.parameters.zip arguments
  let metadata : DataConstructorInstantiation := {
    constructor := sourceConstructor, parameterSubstitution := substitution,
    payloadTypes := signatureConstructor.payloadTypes.map substitution.apply, resultType := expected }
  let resolved ← (context.checked.catalog.resolveConstructor context.signatures metadata).mapError catalogError
  unless resolved = constructor do throw ⟨[], .invalidConstructor constructor⟩
  pure metadata



private def shapeError (context : Context) (expected : Ty) (actual : Core.Value) : Except Error Value := do
  let projection ← context.checked.catalog.project expected |>.mapError catalogError
  throw ⟨[], .coreShapeMismatch projection actual.type⟩

mutual
  /-- Structural source authentication and lowering. The public encoder below
  also checks the complete projected Core value and the exact reverse image. -/
  def encodeRaw : Nat → Context → Ty → Value → Except Error Core.Value
    | 0, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, expected, value => do
      match expected, value with
      | .comptime inner, value => encodeRaw fuel context inner value
      | .function .., _ => throw ⟨[], .functionHandleRequired⟩
      | .constructor (.builtin .unit), .unit => pure .unit
      | .constructor (.builtin .bool), .bool value => pure (.bool value)
      | .constructor (.builtin .word), .word value => pure (.word value)
      | .constructor (.builtin .integer), .integer value => pure (.integer value)
      | .product leftType rightType, .product left right => do
          let left ← (encodeRaw fuel context leftType left).mapError (Error.at .productLeft)
          let right ← (encodeRaw fuel context rightType right).mapError (Error.at .productRight)
          pure (.pair left right)
      | .mapping keyType valueType, .mapping actualKey actualValue entries => do
          unless actualKey = keyType ∧ actualValue = valueType do
            throw ⟨[], .mappingMetadataMismatch keyType valueType actualKey actualValue⟩
          let identity ← namedIdentity context expected
          encodeEntriesRaw fuel context keyType valueType identity entries 0
      | .proxy inner, .proxy actual => do
          unless actual = inner do throw ⟨[], .proxyIdentityMismatch inner actual⟩
          let identity ← namedIdentity context expected
          pure (.constructed ⟨identity, 0⟩ .unit)
      | expected, .constructed metadata payloads => do
          unless metadata.resultType = expected do
            throw ⟨[], .sourceTypeMismatch expected metadata.resultType⟩
          let constructor ← (context.checked.catalog.resolveConstructor context.signatures metadata).mapError catalogError
          let payload ← encodePayloadsRaw fuel context metadata.payloadTypes payloads 0
          pure (.constructed constructor payload)
      | expected, value => throw ⟨[], .sourceTypeMismatch expected value.type⟩

  /-- Source constructor arguments retain their order. Core's zero/single/many
  payload convention is Unit/direct/right-associated product respectively. -/
  def encodePayloadsRaw (fuel : Nat) (context : Context) (types : List Ty) (values : List Value)
      (index : Nat) : Except Error Core.Value := do
    if types.length ≠ values.length then throw ⟨[], .payloadCountMismatch types.length values.length⟩
    match fuel, types, values with
    | _, [], [] => pure .unit
    | 0, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, [type], [value] =>
        (encodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))
    | fuel + 1, type :: types, value :: values => do
        let value ← (encodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))
        let rest ← encodePayloadsRaw fuel context types values (index + 1)
        pure (.pair value rest)
    | _, _, _ => throw ⟨[], .payloadCountMismatch types.length values.length⟩

  /-- This is an ordered list representation. It neither sorts nor deduplicates
  keys, including when two equal keys have different associated values. -/
  def encodeEntriesRaw : Nat → Context → Ty → Ty → Core.DataTypeId → List (Value × Value) →
      Nat → Except Error Core.Value
    | _, _, _, _, identity, [], _ => pure (.constructed ⟨identity, 0⟩ .unit)
    | 0, _, _, _, _, _ :: _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, keyType, valueType, identity, (key, value) :: rest, index => do
        let key ← (encodeRaw fuel context keyType key).mapError (Error.at (.mappingKey index))
        let value ← (encodeRaw fuel context valueType value).mapError (Error.at (.mappingValue index))
        let rest ← encodeEntriesRaw fuel context keyType valueType identity rest (index + 1)
        pure (.constructed ⟨identity, 1⟩ (.pair (.pair key value) rest))
end

mutual
  /-- Decode according to the authenticated expected source type. Core tags do
  not determine a source constructor substitution or proxy inner identity. -/
  def decodeRaw : Nat → Context → Ty → Core.Value → Except Error Value
    | 0, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, expected, value => do
      match expected, value with
      | _, .closure .. => throw ⟨[], .functionHandleRequired⟩
      | _, .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
      | _, .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
      | .comptime inner, value => decodeRaw fuel context inner value
      | .function .., _ => throw ⟨[], .functionHandleRequired⟩
      | .constructor (.builtin .unit), .unit => pure .unit
      | .constructor (.builtin .bool), .bool value => pure (.bool value)
      | .constructor (.builtin .word), .word value => pure (.word value)
      | .constructor (.builtin .integer), .integer value => pure (.integer value)
      | .product leftType rightType, .pair left right => do
          let left ← (decodeRaw fuel context leftType left).mapError (Error.at .productLeft)
          let right ← (decodeRaw fuel context rightType right).mapError (Error.at .productRight)
          pure (.product left right)
      | .mapping keyType valueType, value => do
          let identity ← namedIdentity context expected
          let entries ← decodeEntriesRaw fuel context keyType valueType identity value 0
          pure (.mapping keyType valueType entries)
      | .proxy inner, .constructed constructor .unit => do
          let identity ← namedIdentity context expected
          unless constructor = ⟨identity, 0⟩ do throw ⟨[], .invalidConstructor constructor⟩
          pure (.proxy inner)
      | expected, .constructed constructor payload => do
          let metadata ← constructorMetadata context expected constructor
          let payloads ← decodePayloadsRaw fuel context metadata.payloadTypes payload 0
          pure (.constructed metadata payloads)
      | expected, value => shapeError context expected value

  def decodePayloadsRaw : Nat → Context → List Ty → Core.Value → Nat → Except Error (List Value)
    | _, _, [], .unit, _ => pure []
    | 0, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, [type], value, index => do
        let value ← (decodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))
        pure [value]
    | fuel + 1, context, type :: rest, .pair value tail, index => do
        let value ← (decodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))
        let tail ← decodePayloadsRaw fuel context rest tail (index + 1)
        pure (value :: tail)
    | _, _, _, _, _ => throw ⟨[], .constructorMetadataMismatch⟩

  def decodeEntriesRaw : Nat → Context → Ty → Ty → Core.DataTypeId → Core.Value → Nat →
      Except Error (List (Value × Value))
    | 0, _, _, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, keyType, valueType, identity, value, index => do
        match value with
        | .constructed constructor .unit =>
            unless constructor = ⟨identity, 0⟩ do throw ⟨[], .invalidConstructor constructor⟩
            pure []
        | .constructed constructor (.pair (.pair key value) tail) => do
            unless constructor = ⟨identity, 1⟩ do throw ⟨[], .invalidConstructor constructor⟩
            let key ← (decodeRaw fuel context keyType key).mapError (Error.at (.mappingKey index))
            let value ← (decodeRaw fuel context valueType value).mapError (Error.at (.mappingValue index))
            let tail ← (decodeEntriesRaw fuel context keyType valueType identity tail (index + 1)).mapError
              (Error.at .mappingTail)
            pure ((key, value) :: tail)
        | .closure .. => throw ⟨[], .functionHandleRequired⟩
        | .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
        | .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
        | _ => throw ⟨[], .constructorMetadataMismatch⟩
end

/-- Encode only values whose complete catalog projection is typed and whose
source metadata is the decoder's exact canonical reverse image. -/
def encode (fuel : Nat) (context : Context) (expected : Ty) (value : Value) : Except Error Core.Value := do
  let projection ← (context.checked.project expected).mapError catalogError
  let core ← encodeRaw fuel context expected value
  let _validated ← (SourceCoreGeneralEntry.validateValue context.checked.catalog.definitions core projection.type).mapError rawError
  let decoded ← decodeRaw fuel context expected core
  if decoded = value then pure core else throw ⟨[], .nonCanonicalSourceValue⟩

/-- Decode only fully typed public data with an exact re-encoding. Raw function
values, references, and host functions cannot pass through a deep payload. -/
def decode (fuel : Nat) (context : Context) (expected : Ty) (core : Core.Value) : Except Error Value := do
  let projection ← (context.checked.project expected).mapError catalogError
  let _validated ← (SourceCoreGeneralEntry.validateValue context.checked.catalog.definitions core projection.type).mapError rawError
  let value ← decodeRaw fuel context expected core
  let encoded ← encodeRaw fuel context expected value
  if encoded = core then pure value else throw ⟨[], .nonCanonicalCoreValue⟩



private theorem bind_ok {α β ε : Type} {computation : Except ε α} {next : α → Except ε β}
    {result : β} (accepted : computation >>= next = .ok result) :
    ∃ value, computation = .ok value ∧ next value = .ok result := by
  cases computation with
  | error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem mapError_ok {α ε δ : Type} {computation : Except ε α} {convert : ε → δ} {value : α}
    (accepted : computation.mapError convert = .ok value) : computation = .ok value := by
  cases computation <;> cases accepted
  rfl

private theorem projection_generated {context : Context} {expected : Ty}
    {projection : SourceCoreDataCatalog.Projection context.checked.catalog.definitions}
    (accepted : context.checked.project expected = .ok projection) :
    context.checked.catalog.project expected = .ok projection.type := by
  unfold SourceCoreDataCatalog.Checked.project at accepted
  cases generated : context.checked.catalog.project expected with
  | error error => simp [generated, bind, Except.bind] at accepted
  | ok type =>
      simp only [generated, bind, Except.bind] at accepted
      split at accepted
      · cases accepted; rfl
      · simp at accepted

/-- An authenticated encoding graph also records its exact source reverse
image. This graph can connect the public carrier to an independent semantic
value relation without exposing Core code or a heap reference as source data. -/
structure Encodes (fuel : Nat) (context : Context) (expected : Ty) (value : Value) (core : Core.Value) : Prop where
  generated : encodeRaw fuel context expected value = .ok core
  reversed : decodeRaw fuel context expected core = .ok value
  typed : ∃ type, context.checked.catalog.project expected = .ok type ∧
    ∀ world, Core.RuntimeValueHasType world core type context.checked.catalog.definitions

private theorem encode_details {fuel : Nat} {context : Context} {expected : Ty}
    {value : Value} {core : Core.Value}
    (accepted : encode fuel context expected value = .ok core) :
    ∃ projection : SourceCoreDataCatalog.Projection context.checked.catalog.definitions,
      context.checked.project expected = .ok projection ∧
      encodeRaw fuel context expected value = .ok core ∧
      (∃ validated, SourceCoreGeneralEntry.validateValue context.checked.catalog.definitions core projection.type = .ok validated) ∧
      decodeRaw fuel context expected core = .ok value := by
  unfold encode at accepted
  obtain ⟨projection, projected, accepted⟩ := bind_ok accepted
  obtain ⟨encoded, generated, accepted⟩ := bind_ok accepted
  obtain ⟨validated, checked, accepted⟩ := bind_ok accepted
  obtain ⟨decoded, reversed, accepted⟩ := bind_ok accepted
  split at accepted
  · rename_i canonical
    subst decoded
    cases accepted
    exact ⟨projection, mapError_ok projected, generated, ⟨validated, mapError_ok checked⟩, reversed⟩
  · cases accepted

private theorem decode_details {fuel : Nat} {context : Context} {expected : Ty}
    {value : Value} {core : Core.Value}
    (accepted : decode fuel context expected core = .ok value) :
    ∃ projection : SourceCoreDataCatalog.Projection context.checked.catalog.definitions,
      context.checked.project expected = .ok projection ∧
      (∃ validated, SourceCoreGeneralEntry.validateValue context.checked.catalog.definitions core projection.type = .ok validated) ∧
      decodeRaw fuel context expected core = .ok value ∧
      encodeRaw fuel context expected value = .ok core := by
  unfold decode at accepted
  obtain ⟨projection, projected, accepted⟩ := bind_ok accepted
  obtain ⟨validated, checked, accepted⟩ := bind_ok accepted
  obtain ⟨decoded, reversed, accepted⟩ := bind_ok accepted
  obtain ⟨encoded, generated, accepted⟩ := bind_ok accepted
  split at accepted
  · rename_i canonical
    subst encoded
    cases accepted
    exact ⟨projection, mapError_ok projected, ⟨validated, mapError_ok checked⟩, reversed, generated⟩
  · cases accepted

theorem encodes_of_encode {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context expected value = .ok core) : Encodes fuel context expected value core := by
  obtain ⟨projection, projected, generated, ⟨validated, _⟩, reversed⟩ := encode_details accepted
  exact ⟨generated, reversed, projection.type, projection_generated projected, validated.typed⟩

theorem encodes_of_decode {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : decode fuel context expected core = .ok value) : Encodes fuel context expected value core := by
  obtain ⟨projection, projected, ⟨validated, _⟩, reversed, generated⟩ := decode_details accepted
  exact ⟨generated, reversed, projection.type, projection_generated projected, validated.typed⟩

/-- Encoding preserves the source carrier exactly, including constructor
metadata, mapping order/duplicate keys and raw proxy inner identity. -/
theorem decode_encode {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context expected value = .ok core) :
    decode fuel context expected core = .ok value := by
  obtain ⟨projection, projected, generated, ⟨validated, checked⟩, reversed⟩ := encode_details accepted
  simp [decode, projected, generated, checked, reversed, bind, Except.bind, Except.mapError]

/-- A decoded public value re-encodes to the complete original Core data tree,
without erasing capabilities or replacing nominal tags. -/
theorem encode_decode {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : decode fuel context expected core = .ok value) :
    encode fuel context expected value = .ok core := by
  obtain ⟨projection, projected, ⟨validated, checked⟩, reversed, generated⟩ := decode_details accepted
  simp [encode, projected, generated, checked, reversed, bind, Except.bind, Except.mapError]

theorem encode_typed {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : encode fuel context expected value = .ok core) :
    ∃ type, context.checked.catalog.project expected = .ok type ∧
      ∀ world, Core.RuntimeValueHasType world core type context.checked.catalog.definitions :=
  (encodes_of_encode accepted).typed

theorem decode_typed {fuel : Nat} {context : Context} {expected : Ty} {value : Value} {core : Core.Value}
    (accepted : decode fuel context expected core = .ok value) :
    ∃ type, context.checked.catalog.project expected = .ok type ∧
      ∀ world, Core.RuntimeValueHasType world core type context.checked.catalog.definitions :=
  (encodes_of_decode accepted).typed



/-- The nominal branch exposes authenticated constructor selection and ordered
payload packing for composition with an independent semantic value relation. -/
theorem encodeRaw_constructed {fuel : Nat} {context : Context} {expected : Ty}
    {declaration : Resolved.DeclarationId} {arguments : List Ty}
    {metadata : DataConstructorInstantiation} {payloads : List Value} {core : Core.Value}
    (nominal : SourceCoreDataCatalog.nominalParts expected = some (declaration, arguments))
    (accepted : encodeRaw fuel context expected (.constructed metadata payloads) = .ok core) :
    metadata.resultType = expected ∧ ∃ constructor payload,
      context.checked.catalog.resolveConstructor context.signatures metadata = .ok constructor ∧
      encodePayloadsRaw (fuel - 1) context metadata.payloadTypes payloads 0 = .ok payload ∧
      core = .constructed constructor payload := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases expected <;> try (solve | cases nominal)
      case constructor constructor =>
        cases constructor <;> try (solve | cases nominal)
        case declaration declaration =>
          simp only [encodeRaw] at accepted
          by_cases same : metadata.resultType = .constructor (.declaration declaration)
          · simp only [same, ↓reduceIte,
              pure, bind, Except.bind] at accepted
            obtain ⟨constructor, resolved, accepted⟩ := bind_ok accepted
            obtain ⟨payload, generated, accepted⟩ := bind_ok accepted
            cases accepted
            exact ⟨same, constructor, payload, mapError_ok resolved, generated, rfl⟩
          · simp [same, bind, Except.bind] at accepted
      case application function argument =>
        simp only [encodeRaw] at accepted
        by_cases same : metadata.resultType = .application function argument
        · simp only [same, ↓reduceIte,
            pure, bind, Except.bind] at accepted
          obtain ⟨constructor, resolved, accepted⟩ := bind_ok accepted
          obtain ⟨payload, generated, accepted⟩ := bind_ok accepted
          cases accepted
          exact ⟨same, constructor, payload, mapError_ok resolved, generated, rfl⟩
        · simp [same, bind, Except.bind] at accepted



/-- Successful metadata authentication selects the same catalog tag and a
registered Core payload. These facts support semantic constructor matching. -/
theorem resolveConstructor_facts {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : Core.ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    catalog.constructor? metadata = some tag ∧
      ∃ payload, catalog.definitions.lookupConstructorPayloadType? tag = some payload := by
  unfold SourceCoreDataCatalog.Catalog.resolveConstructor at accepted
  obtain ⟨signature, _, accepted⟩ := bind_ok accepted
  simp only [pure, Except.pure, bind, Except.bind, throw] at accepted
  split at accepted
  · split at accepted
    · split at accepted
      · split at accepted
        · split at accepted
          · split at accepted
            · rename_i identity selected
              cases computed : metadata.payloadTypes.mapM catalog.project with
              | error error => simp [computed] at accepted
              | ok payloads =>
                  simp only [computed] at accepted
                  split at accepted
                  · rename_i registered
                    cases accepted
                    exact ⟨selected, _, registered⟩
                  · cases accepted
            · cases accepted
          · cases accepted
        · cases accepted
      · cases accepted
    · cases accepted
  · cases accepted

theorem resolveConstructor_lookup {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : Core.ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    catalog.constructor? metadata = some tag := (resolveConstructor_facts accepted).1

theorem resolveConstructor_registered {catalog : SourceCoreDataCatalog.Catalog}
    {signatures : ProgramSignatures} {metadata : DataConstructorInstantiation} {tag : Core.ConstructorId}
    (accepted : catalog.resolveConstructor signatures metadata = .ok tag) :
    ∃ payload, catalog.definitions.lookupConstructorPayloadType? tag = some payload :=
  (resolveConstructor_facts accepted).2

end Solcore.Frontend.SourceCoreDataValues
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreRecursiveEntry
/-! Prepared scalar/product programs with monomorphic named recursion.
Compilation installs ordinary optional function cells before entering a seed.
Closures retain the shared global references and allocate source parameters in
source order on every call. Invocation reuses BasicEntry's checked input and
checkpoint APIs; it does not compile or interpret source code.

The resulting Core store also contains wrapper inputs and administrative
function cells. This module proves Core typing through the checker; it does
not assert the old equal-index source/Core heap correspondence. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRecursiveEntry

open SourceInference

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Input := SourceCoreBasicEntry.Input
abbrev Entry := SourceCoreBasicEntry.Entry
abbrev PreparedProgram := SourceCoreBasicEntry.PreparedProgram

inductive Error where
  | preparation (error : SourceCompilationPlan.Error)
  | entry (error : SourceCoreBasicEntry.Error)
  | lowering (error : SourceCoreBasic.Error)
  | programFaultSites (error : SourceCoreProgramFaultSites.Error)
  | missingDiagnostics (key : Key)
  | missingGlobal (key : Key)
  | stagedInputUnsupported (key : Key) (binder : Resolved.LocalId)
  deriving Repr, DecidableEq

/-- All metadata required to compile one closed specialization. -/
structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List Input
  sourceResultType : TypeSystem.Ty
  resultProjection : SourceCoreScalar.lowerType (.declaration signature.key.declaration)
    sourceResultType = .ok signature.resultType
  deriving Repr

private def prepareFunction (specialized : SourceSpecialization.SpecializedFunction) : Except Error Function := do
  let key := specialized.key
  let function := specialized.function
  if function.returnComptime then throw (.entry (.stagedResultUnsupported key))
  unless specialized.assumptions.isEmpty do
    throw (.entry (.assumptionsUnsupported key specialized.assumptions.length))
  let (sourceParameterType, sourceResultType) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.entry (.invalidFunctionType key))
  if sourceResultType ≠ function.inferredBodyType then throw (.entry (.resultMetadataMismatch key))
  let parameterType ← (SourceCoreScalar.lowerType (.declaration key.declaration) sourceParameterType).mapError (Error.lowering ∘ SourceCoreBasic.Error.typeProjection)
  let projected ← match projection : SourceCoreScalar.lowerType (.declaration key.declaration) sourceResultType with
    | .ok resultType => pure (⟨resultType, projection⟩ : { resultType : Core.Ty //
        SourceCoreScalar.lowerType (.declaration key.declaration) sourceResultType = .ok resultType })
    | .error error => .error (.lowering (.typeProjection error))
  let inputs ← (SourceCoreBasicEntry.prepareInputs function.typedBody).mapError Error.entry
  for input in inputs do
    if input.comptime then throw (.stagedInputUnsupported key input.id)
  pure {
    specialized, inputs, sourceResultType
    signature := { key, parameterType, resultType := projected.val }
    resultProjection := projected.property
  }

/-- Select one argument from source's Unit/single/right-product bundle.
Only indices below the original parameter count are used by bindParameters. -/
def argumentProjection (index : Nat) : Nat → Core.Expr → Core.Expr
  | 0, _ => .unit
  | 1, bundle => bundle
  | count + 2, bundle =>
      if index = 0 then .first bundle
      else argumentProjection (index - 1) (count + 1) (.second bundle)

/-- The incoming raw bundle follows the already allocated parameter cells.
The helper's weakening accounts for its temporary successful payload. -/
def bindParameters (inputs : List Input) (resultType : Core.Ty) (body : Core.Expr) : Core.Expr :=
  inputs.zipIdx.foldr (fun (input, index) continuation =>
    Core.LocalSequence.letInitialized resultType input.type
      (Core.LanguageResult.success (argumentProjection index inputs.length (.var index))) continuation) body

/-- Allocate in plan order, producing global references in newest-first order. -/
def allocateGlobals (planOrder : List Signature) (body : Core.Expr) : Core.Expr :=
  planOrder.foldr (fun signature continuation =>
    .letE (Core.OptionalCell.allocate signature.functionType) continuation) body

/-- Every write is expressed in the same global environment. Its Unit result
is weakened into the remainder, including any subsequent closure bodies. -/
def installFunctions (closures : List Core.Expr) (body : Core.Expr) : Core.Expr :=
  closures.zipIdx.foldr (fun (closure, index) continuation =>
    .letE (.storeCell (.var index) (.inRight .unit closure)) (continuation.weakenAt 0)) body

private def compileClosure (plan : Plan) (globals : List Signature)
    (diagnostics : SourceCoreProgramFaultSites.Program) (compilationFuel : Nat)
    (function : Function) : Except Error Core.Expr := do
  let source := function.specialized.function.typedBody
  let ownSites ← match diagnostics.find? function.signature.key with
    | some sites => pure sites
    | none => .error (.missingDiagnostics function.signature.key)
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => .error (.entry (.expectedStatementRoot id))
  let context : SourceCoreCalls.Context := {
    plan, globals
    owner := function.signature.key
    administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let policy := SourceCoreAssignmentPolicy.attach {
    lowerExpression := fun fuel source scope id reasonAt =>
      SourceCoreCalls.lowerExpressionWithReasons fuel context source scope id reasonAt
  } ownSites.assignments
  let body ← (SourceCoreLoops.lowerStatementsWithPolicy policy
    compilationFuel source (SourceCoreBasicEntry.inputScope function.inputs) statements
    function.signature.resultType ownSites.table.reasonAt ownSites.fellThroughReason
    ownSites.table.escapedReason).mapError Error.lowering
  pure (.lambda function.signature.parameterType
    (Core.LanguageResult.resultType function.signature.resultType)
    (bindParameters function.inputs function.signature.resultType body))

/-- Wrapper input cells are read in original parameter order. The seed callee
then allocates its own source parameter cells just like every other call. -/
def seedArguments (globals : List Signature) (inputs : List Input) : SourceCoreBasic.LoweredExpr :=
  SourceCoreCalls.packArguments (inputs.zipIdx.map fun (input, index) =>
    ⟨input.type, Core.OptionalCell.read input.type
      (.var (globals.length + (inputs.length - 1 - index))) Core.Word.zero⟩)

private def assembleEntry (plan : Plan) (functions : List Function)
    (globals : List Signature) (closures : List Core.Expr) (key : Key) : Except Error Entry := do
  let (function, index) ← match functions.zipIdx.find? (fun item => decide (item.1.signature.key = key)) with
    | some item => pure item
    | none => .error (.missingGlobal key)
  let diagnostics ← (SourceCoreProgramFaultSites.prepare plan key).mapError Error.programFaultSites
  let arguments := seedArguments globals function.inputs
  (SourceCoreBasic.ensureType (.declaration key.declaration) function.signature.parameterType arguments.type).mapError Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  let body := allocateGlobals globals.reverse (installFunctions closures invoked)
  if checked : Core.infer? (SourceCoreBasicEntry.inputContext function.inputs) body =
      some (Core.LanguageResult.resultType function.signature.resultType) then
    pure {
      key := function.signature.key
      inputs := function.inputs
      sourceResultType := function.sourceResultType
      resultType := function.signature.resultType
      resultProjection := function.resultProjection
      faultSites := diagnostics.rootTable
      body
      bodyTyped := Core.infer_sound checked
    }
  else
    throw (.entry (.coreCheckFailed key (Core.LanguageResult.resultType function.signature.resultType)
      (Core.infer? (SourceCoreBasicEntry.inputContext function.inputs) body)))

/-- Canonical preparation and closure compilation happen once. Every seed
gets the same global installation and its own complete diagnostic projection.
Local lambdas, indirect calls, staged inputs/results, assumption dictionaries
and non-scalar/product source types remain explicit preparation failures. -/
def prepare (program : CheckedProgram) (plan : Plan) (compilationFuel : Nat)
    (_reason : Core.Word) : Except Error PreparedProgram := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError Error.preparation
  let functions ← executablePlan.specializations.reverse.mapM prepareFunction
  let globals := functions.map (·.signature)
  match executablePlan.seedKeys with
  | [] => pure { plan := executablePlan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreProgramFaultSites.prepare executablePlan first).mapError Error.programFaultSites
      let closures ← functions.mapM (compileClosure executablePlan globals diagnostics compilationFuel)
      let entries ← executablePlan.seedKeys.mapM (assembleEntry executablePlan functions globals closures)
      pure { plan := executablePlan, entries }

end Solcore.Frontend.SourceCoreRecursiveEntry
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreFunctionEntry
/-! Prepared programs whose internal cells and signatures include monomorphic
function values. Global installation, parameter allocation, and entry invocation
reuse the ordinary recursive-entry helpers. The public seed boundary retains
BasicEntry's scalar/product input validation and result projection; function
inputs and outputs are currently rejected there.

Core checking establishes machine type safety for the generated body. A source
heap relation for captured closures and administrative cells remains separate;
this module does not claim complete source semantic preservation. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreFunctionEntry

open SourceInference

abbrev Key := SourceCoreRecursiveEntry.Key
abbrev Plan := SourceCoreRecursiveEntry.Plan
abbrev Signature := SourceCoreCalls.Signature
abbrev Input := SourceCoreBasicEntry.Input
abbrev Entry := SourceCoreBasicEntry.Entry
abbrev PreparedProgram := SourceCoreBasicEntry.PreparedProgram
abbrev Error := SourceCoreRecursiveEntry.Error

structure Function where
  specialized : SourceSpecialization.SpecializedFunction
  signature : Signature
  inputs : List Input
  sourceResultType : TypeSystem.Ty
  deriving Repr

private def prepareInputs (key : Key) (source : TypedSource) :
    SourceCoreBasic.Scope → List TypedBinder → Except Error (List Input)
  | _, [] => pure []
  | scope, binder :: rest => do
      let type ← (SourceCoreFunctionTypes.lowerBinder source scope { binder with comptime := false }).mapError SourceCoreRecursiveEntry.Error.lowering
      let inputs ← prepareInputs key source ((binder.id, type) :: scope) rest
      pure ({ id := binder.id, sourceType := binder.scheme.body, type, comptime := binder.comptime } :: inputs)

private def prepareFunction (specialized : SourceSpecialization.SpecializedFunction) : Except Error Function := do
  let key := specialized.key
  let function := specialized.function
  if function.returnComptime then throw (.entry (.stagedResultUnsupported key))
  unless specialized.assumptions.isEmpty do
    throw (.entry (.assumptionsUnsupported key specialized.assumptions.length))
  let (sourceParameterType, sourceResultType) ← match function.type with
    | .function parameter result => pure (parameter, result)
    | _ => .error (.entry (.invalidFunctionType key))
  if sourceResultType ≠ function.inferredBodyType then throw (.entry (.resultMetadataMismatch key))
  let parameterType ← (SourceCoreFunctionTypes.projectType (.declaration key.declaration) sourceParameterType).mapError SourceCoreRecursiveEntry.Error.lowering
  let resultType ← (SourceCoreFunctionTypes.projectType (.declaration key.declaration) sourceResultType).mapError SourceCoreRecursiveEntry.Error.lowering
  let inputs ← prepareInputs key function.typedBody [] function.typedBody.inputs
  pure { specialized, inputs, sourceResultType, signature := { key, parameterType, resultType } }

/-- Lambda bodies and global bodies share the same function-value policy. -/
def bodyLowerer : SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } fuel source scope statements result reasonAt fellThrough escaped

/-- Nested lambdas retain their owning function's assignment reason provider. -/
def bodyLowererWithAssignments (assignments : SourceCoreAssignmentFaultSites.Table) :
    SourceCoreFunctions.BodyLowerer :=
  fun expression fuel source scope statements result reasonAt fellThrough escaped =>
    SourceCoreLoops.lowerStatementsWithPolicy (SourceCoreAssignmentPolicy.attach {
      lowerExpression := expression
      readStatement := SourceCoreFunctionTypes.readStatement
      lowerBinder := SourceCoreFunctionTypes.lowerBinder
      lowerAssignment := SourceCoreFunctionTypes.lowerAssignment
    } assignments) fuel source scope statements result reasonAt fellThrough escaped

private def compileClosure (plan : Plan) (globals : List Signature)
    (diagnostics : SourceCoreProgramFaultSites.Program) (compilationFuel : Nat)
    (function : Function) : Except Error Core.Expr := do
  let source := function.specialized.function.typedBody
  let ownSites ← match diagnostics.find? function.signature.key with
    | some sites => pure sites
    | none => .error (.missingDiagnostics function.signature.key)
  let statements ← source.roots.mapM fun
    | .statement id => pure id
    | .expression id => .error (.entry (.expectedStatementRoot id))
  let context : SourceCoreFunctions.Context := {
    plan, globals, owner := function.signature.key, administrativePrefix := 1
    solvedRequirements := function.specialized.function.solvedRequirements
    internalReason := Core.Word.zero
  }
  let lowerBody := bodyLowererWithAssignments ownSites.assignments
  let body ← (lowerBody
    (fun fuel source scope id reasonAt =>
      SourceCoreFunctions.lowerExpressionWithReasons lowerBody fuel context source scope id reasonAt)
    compilationFuel source (SourceCoreBasicEntry.inputScope function.inputs) statements
    function.signature.resultType ownSites.table.reasonAt ownSites.fellThroughReason
    ownSites.table.escapedReason).mapError SourceCoreRecursiveEntry.Error.lowering
  pure (.lambda function.signature.parameterType
    (Core.LanguageResult.resultType function.signature.resultType)
    (SourceCoreRecursiveEntry.bindParameters function.inputs function.signature.resultType body))

private def assembleEntry (plan : Plan) (functions : List Function)
    (globals : List Signature) (closures : List Core.Expr) (key : Key) : Except Error Entry := do
  let (function, index) ← match functions.zipIdx.find? (fun item => decide (item.1.signature.key = key)) with
    | some item => pure item
    | none => .error (.missingGlobal key)
  -- Retain the existing public value boundary, even though internal function
  -- parameters and returned closures have broader representations.
  let inputs ← (SourceCoreBasicEntry.prepareInputs function.specialized.function.typedBody).mapError SourceCoreRecursiveEntry.Error.entry
  let projected ← match projection : SourceCoreScalar.lowerType
      (.declaration function.signature.key.declaration) function.sourceResultType with
    | .ok resultType => pure (⟨resultType, projection⟩ : { resultType : Core.Ty //
        SourceCoreScalar.lowerType (.declaration function.signature.key.declaration)
          function.sourceResultType = .ok resultType })
    | .error error => .error (.lowering (.typeProjection error))
  (SourceCoreBasic.ensureType (.declaration key.declaration) projected.val function.signature.resultType).mapError SourceCoreRecursiveEntry.Error.lowering
  let diagnostics ← (SourceCoreProgramFaultSites.prepare plan key).mapError SourceCoreRecursiveEntry.Error.programFaultSites
  let arguments := SourceCoreRecursiveEntry.seedArguments globals inputs
  (SourceCoreBasic.ensureType (.declaration key.declaration) function.signature.parameterType arguments.type).mapError SourceCoreRecursiveEntry.Error.lowering
  let invoked := SourceCoreCalls.call function.signature index arguments.expression Core.Word.zero
  let body := SourceCoreRecursiveEntry.allocateGlobals globals.reverse
    (SourceCoreRecursiveEntry.installFunctions closures invoked)
  if checked : Core.infer? (SourceCoreBasicEntry.inputContext inputs) body =
      some (Core.LanguageResult.resultType projected.val) then
    pure {
      key := function.signature.key, inputs
      sourceResultType := function.sourceResultType
      resultType := projected.val, resultProjection := projected.property
      faultSites := diagnostics.rootTable
      body, bodyTyped := Core.infer_sound checked
    }
  else
    throw (.entry (.coreCheckFailed key (Core.LanguageResult.resultType projected.val)
      (Core.infer? (SourceCoreBasicEntry.inputContext inputs) body)))

/-- Authenticate the plan and compile every reachable global once. Public seed
values remain scalar/product; the internal policy admits monomorphic function
parameters, returned closures, shared captures, and indirect calls. -/
def prepare (program : CheckedProgram) (plan : Plan) (compilationFuel : Nat)
    (_reason : Core.Word) : Except Error PreparedProgram := do
  let executablePlan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError SourceCoreRecursiveEntry.Error.preparation
  let functions ← executablePlan.specializations.reverse.mapM prepareFunction
  let globals := functions.map (·.signature)
  match executablePlan.seedKeys with
  | [] => pure { plan := executablePlan, entries := [] }
  | first :: _ =>
      let diagnostics ← (SourceCoreProgramFaultSites.prepare executablePlan first).mapError SourceCoreRecursiveEntry.Error.programFaultSites
      let closures ← functions.mapM (compileClosure executablePlan globals diagnostics compilationFuel)
      let entries ← executablePlan.seedKeys.mapM (assembleEntry executablePlan functions globals closures)
      pure { plan := executablePlan, entries }

end Solcore.Frontend.SourceCoreFunctionEntry
end

section
-- leanmerge: from Solcore.Frontend.SourceCorePublicValues
/-! One public source value carrier. Callable handles carry no Core code or
references. Their artifact, session, export generation and slot fields are
sealed; numeric identities cannot be supplied by a caller. Ownership issuers
are retained privately by the execution adapters that mint handles. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicValues
open SourceInference TypeSystem

private initialize identityCounter : Std.Mutex Nat ← Std.Mutex.new 0
private def fresh : IO Nat := identityCounter.atomically do
  let index ← get
  set (index + 1)
  pure index

structure ArtifactAuthority where private mk ::
  private identity : Nat
  deriving Repr, DecidableEq
structure SessionAuthority where private mk ::
  private artifact : ArtifactAuthority
  private identity : Nat
  deriving Repr, DecidableEq
structure ExportGeneration where private mk ::
  private identity : Nat
  deriving Repr, DecidableEq

def ArtifactAuthority.mint : IO ArtifactAuthority := return ⟨← fresh⟩
def ArtifactAuthority.newSession (artifact : ArtifactAuthority) : IO SessionAuthority :=
  return ⟨artifact, ← fresh⟩
def ExportGeneration.mint : IO ExportGeneration := return ⟨← fresh⟩

structure Handle where private mk ::
  private artifact : ArtifactAuthority
  private session : SessionAuthority
  private generation : ExportGeneration
  private slot : Nat
  private rawType : Ty
  deriving Repr, DecidableEq

/-- Requires the private issuer retained by a session. A newly minted foreign
issuer cannot issue a handle belonging to an existing artifact/session. -/
def SessionAuthority.issue (session : SessionAuthority) (generation : ExportGeneration)
    (slot : Nat) (sourceType : Ty) : Handle :=
  ⟨session.artifact, session, generation, slot, sourceType⟩
def Handle.sourceType (handle : Handle) : Ty := handle.rawType
def Handle.belongsToArtifact (handle : Handle) (artifact : ArtifactAuthority) : Bool :=
  decide (handle.artifact = artifact)
def Handle.belongsToSession (handle : Handle) (session : SessionAuthority) : Bool :=
  decide (handle.session = session)

inductive Value where
  | unit | bool (value : Bool) | word (value : Core.Word) | integer (value : Int)
  | product (left right : Value)
  | constructed (instantiation : DataConstructorInstantiation) (payloads : List Value)
  | mapping (keyType valueType : Ty) (entries : List (Value × Value))
  | proxy (inner : Ty)
  | function (handle : Handle)
  deriving Repr

mutual
  def Value.decEq (left right : Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case unit.unit => exact isTrue rfl
    case bool.bool left right => exact decidable_of_iff (left = right) (by simp)
    case word.word left right => exact decidable_of_iff (left = right) (by simp)
    case integer.integer left right => exact decidable_of_iff (left = right) (by simp)
    case proxy.proxy left right => exact decidable_of_iff (left = right) (by simp)
    case function.function left right => exact decidable_of_iff (left = right) (by simp)
    case product.product leftA leftB rightA rightB =>
      letI := Value.decEq leftA rightA
      letI := Value.decEq leftB rightB
      exact decidable_of_iff (leftA = rightA ∧ leftB = rightB) (by simp)
    case constructed.constructed leftMetadata leftPayloads rightMetadata rightPayloads =>
      letI := Value.listDecEq leftPayloads rightPayloads
      exact decidable_of_iff (leftMetadata = rightMetadata ∧ leftPayloads = rightPayloads) (by simp)
    case mapping.mapping leftKey leftValue leftEntries rightKey rightValue rightEntries =>
      letI := Value.entriesDecEq leftEntries rightEntries
      exact decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue ∧ leftEntries = rightEntries) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.listDecEq (left right : List Value) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      letI := Value.decEq leftHead rightHead
      letI := Value.listDecEq leftTail rightTail
      exact decidable_of_iff (leftHead = rightHead ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega

  def Value.entriesDecEq (left right : List (Value × Value)) : Decidable (left = right) := by
    cases left <;> cases right <;> try (solve | apply isFalse; intro equality; cases equality)
    case nil.nil => exact isTrue rfl
    case cons.cons leftHead leftTail rightHead rightTail =>
      rcases leftHead with ⟨leftKey, leftValue⟩
      rcases rightHead with ⟨rightKey, rightValue⟩
      letI := Value.decEq leftKey rightKey
      letI := Value.decEq leftValue rightValue
      letI := Value.entriesDecEq leftTail rightTail
      letI : Decidable ((leftKey, leftValue) = (rightKey, rightValue)) :=
        decidable_of_iff (leftKey = rightKey ∧ leftValue = rightValue) (by simp)
      exact decidable_of_iff ((leftKey, leftValue) = (rightKey, rightValue) ∧ leftTail = rightTail) (by simp)
  termination_by sizeOf left
  decreasing_by all_goals simp_wf; omega
end

instance : DecidableEq Value := Value.decEq
instance : BEq Value := ⟨fun left right => decide (left = right)⟩
instance : LawfulBEq Value where
  eq_of_beq := of_decide_eq_true
  rfl := by intro value; exact decide_eq_true rfl

def Value.type : Value → Ty
  | .unit => .unit | .bool _ => .bool | .word _ => .word | .integer _ => .integer
  | .product left right => .product left.type right.type
  | .constructed instantiation _ => instantiation.resultType
  | .mapping key value _ => .mapping key value
  | .proxy inner => .proxy inner
  | .function handle => handle.sourceType


end Solcore.Frontend.SourceCorePublicValues

namespace Solcore.Frontend.SourceCorePublicValues

/-- The original session issuer belongs to this artifact. This is a proof
receipt, not an operational authority accessor. -/
def SessionAuthority.IssuedFor (session : SessionAuthority) (artifact : ArtifactAuthority) : Prop :=
  session.artifact = artifact

/-- Mint once and retain the artifact association of that same authority. -/
def ArtifactAuthority.newSessionWithReceipt (artifact : ArtifactAuthority) :
    IO { session : SessionAuthority // session.IssuedFor artifact } := do
  let identity ← fresh
  pure ⟨⟨artifact, identity⟩, rfl⟩

theorem SessionAuthority.issue_artifact {session : SessionAuthority} {artifact : ArtifactAuthority}
    (issued : session.IssuedFor artifact) (generation : ExportGeneration) (index : Nat) (type : TypeSystem.Ty) :
    (session.issue generation index type).belongsToArtifact artifact = true := by
  change decide (session.artifact = artifact) = true
  exact decide_eq_true issued

theorem SessionAuthority.issue_session (session : SessionAuthority)
    (generation : ExportGeneration) (index : Nat) (type : TypeSystem.Ty) :
    (session.issue generation index type).belongsToSession session = true := by
  simp [SessionAuthority.issue, Handle.belongsToSession]

theorem SessionAuthority.issue_sourceType (session : SessionAuthority)
    (generation : ExportGeneration) (index : Nat) (type : TypeSystem.Ty) :
    (session.issue generation index type).sourceType = type := rfl

theorem SessionAuthority.issue_index {session : SessionAuthority}
    {leftGeneration rightGeneration : ExportGeneration} {leftIndex rightIndex : Nat}
    {leftType rightType : TypeSystem.Ty}
    (same : session.issue leftGeneration leftIndex leftType =
      session.issue rightGeneration rightIndex rightType) : leftIndex = rightIndex := by
  exact congrArg Handle.slot same

end Solcore.Frontend.SourceCorePublicValues
end
