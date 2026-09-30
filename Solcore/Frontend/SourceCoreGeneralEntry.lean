import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.Frontend.SourceCoreFaultSites
import Solcore.Core.OptionalCell

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
    if binder.comptime then throw (.stagedInputUnsupported binder.id)
    let projection ← (projectType checked binder.scheme.body).mapError CompileError.catalog
    let inputs ← prepareInputs checked owner (binder.id :: seen) rest
    pure ({ id := binder.id, sourceType := binder.scheme.body, projection } :: inputs)

/-- A callback's output is accepted only by the checker for the actual catalog.
The returned entry retains both source projection and complete body typing.
`prepare` authenticates the plan before calling this lower-level constructor;
direct users are responsible for source-plan authenticity. -/
def compile {error : Type} (checked : Checked) (plan : Plan)
    (specialized : SourceSpecialization.SpecializedFunction) (compilationFuel : Nat)
    (lowerBody : BodyLowerer checked error) : Except (CompileError error) (Entry checked) := do
  unless specialized.assumptions.isEmpty do throw (.assumptionsUnsupported specialized.key)
  if specialized.function.returnComptime then throw (.stagedResultUnsupported specialized.key)
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

def prepare {error : Type} (program : CheckedProgram) (plan : Plan) (checked : Checked)
    (compilationFuel : Nat) (lowerBody : BodyLowerer checked error) :
    Except (CompileError error) (PreparedProgram checked) := do
  let plan ← (SourceCompilationPlan.prepareExecutablePlanEvidence program plan).mapError CompileError.plan
  let entries ← plan.seedKeys.mapM fun key => do
    let specialized ← (SourceCompilationPlan.exactSpecialization plan key).mapError CompileError.plan
    compile checked plan specialized compilationFuel lowerBody
  pure { plan, entries }

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

private def prepareArguments {checked : Checked} {context : Core.Context} (index : Nat)
    (frame : InputFrame (definitions checked) context) : (inputs : List (Input checked)) → List Core.Value →
      Except RunError (InputFrame (definitions checked) (inputContext inputs ++ context))
  | [], [] => pure (by simpa [inputContext] using frame)
  | input :: inputs, argument :: arguments => do
    let value ← (validateValue (definitions checked) argument input.type).mapError (RunError.input index)
    let prepared ← prepareArguments (index + 1) (frame.push input.type argument value) inputs arguments
    pure (by simpa [inputContext, List.reverse_cons, List.append_assoc] using prepared)
  | inputs, arguments => throw (.argumentCountMismatch (index + inputs.length) (index + arguments.length))

structure Checkpoint (definitions : Core.DataEnvironment) (resultType : Core.Ty) where
  state : Core.State
  typed : Core.StateHasType state (Core.LanguageResult.resultType resultType) definitions
  deriving Repr

structure Result (definitions : Core.DataEnvironment) (resultType : Core.Ty) where
  observation : Core.LanguageResult.Observation
  typed : observation.HasType resultType definitions
  deriving Repr

/-- Fresh input locations follow source parameter order; references in the
lexical environment are newest first. Existing public stores are rejected. -/
def Entry.start {checked : Checked} (entry : Entry checked) (arguments : List Core.Value)
    (initialStore : Core.Store := []) : Except RunError (Checkpoint (definitions checked) entry.resultType) := do
  match initialStore with
  | _ :: _ => throw (.initialStoreUnsupported initialStore.length)
  | [] =>
    if entry.inputs.length ≠ arguments.length then
      throw (.argumentCountMismatch entry.inputs.length arguments.length)
    let frame ← prepareArguments 0 (InputFrame.empty (definitions checked)) entry.inputs arguments
    let environmentTyped : Core.RuntimeEnvironmentHasTypes frame.world frame.environment
        (inputContext entry.inputs) (definitions checked) := by simpa using frame.environmentTyped
    pure {
      state := .initial entry.body frame.environment frame.store
      typed := .eval frame.storeTyped environmentTyped entry.bodyTyped .nil
    }

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
