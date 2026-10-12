import Solcore.Frontend.SourceCorePublicValues
import Solcore.Core.FuelResumptionProperties
import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.Frontend.SourceCoreCallableIndexedTemplates
import Solcore.Frontend.SourceCoreHeapSnapshot
import Solcore.Frontend.SourceCoreIndexedHeapMigration

/-! Persistent typed Core sessions for the source-compatible indexed program.
Bootstrap installs the owned context cell and global closures once. Subsequent
calls retain that environment, raw metadata registry and captured references.
The public carrier contains data and opaque handles, never source/Core code.
This session boundary establishes native typing and ownership; it is not the
complete source/Core meaning theorem. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem
abbrev Value := SourceCorePublicValues.Value
abbrev Handle := SourceCorePublicValues.Handle
abbrev ArtifactAuthority := SourceCorePublicValues.ArtifactAuthority
abbrev SessionAuthority := SourceCorePublicValues.SessionAuthority
abbrev ExportGeneration := SourceCorePublicValues.ExportGeneration
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Values := SourceCoreCompatibleValues.Context
abbrev PathStep := SourceCoreDataValues.PathStep

inductive ErrorCode where
  | data (error : SourceCoreDataValues.ErrorCode)
  | compatible (error : SourceCoreCompatibleValues.Error)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | foreignArtifact | foreignSession | unknownHandle
  | handleTypeMismatch (expected actual : Ty)
  | invalidNativeValue (expected actual : Core.Ty)
  | missingEntry (key : Key)
  | argumentCountMismatch (expected actual : Nat)
  | checkFailed (expected : Core.Ty) (actual : Option Core.Ty)
  | globals (error : SourceCoreCallableNativeSlots.Error)
  | templates (error : SourceCoreCallableIndexedTemplates.Error)
  | callable (error : SourceCompilationPlan.Error)
  | missingBuiltin (function : BuiltinFunctionId)
  | missingContract (origin : SourceCoreStageCodebook.Origin)
  | identitySpaceExhausted
  | notFunction (type : Ty)
  | malformedCallable
  | stagedInvocationRequired (origin : SourceCoreStageCodebook.Origin)
  | diagnostics (error : SourceCoreCompatibleDataPlaceFaultSites.Error)
  | invalidBootstrap
  | heap (error : SourceCoreAllocationLedger.Error)
  | cellHeader (error : SourceCoreCallableIndexedCellHeaders.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | heapMigration (error : SourceCoreIndexedHeapMigration.Error)
  | invalidExportedPrefix (validationFuel : Nat)
  deriving Repr
structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr
private def Error.at (step : PathStep) (error : Error) : Error := { error with path := step :: error.path }
private def fromData (error : SourceCoreDataValues.Error) : Error := ⟨error.path, .data error.code⟩
private def fromCatalog (error : SourceCoreCompatibleCatalog.Error) : Error := ⟨[], .catalog error⟩

private structure TypedValue (definitions : Core.DataEnvironment) (world : Core.StoreTyping)
    (value : Core.Value) (type : Core.Ty) : Type where
  typed : Core.RuntimeValueHasType world value type definitions

private structure TypedEnvironment (definitions : Core.DataEnvironment) (world : Core.StoreTyping)
    (environment : Core.Environment) : Type where
  typed : Core.RuntimeEnvironmentHasTypes world environment (environment.map Core.Value.type) definitions

mutual
  /-- Internal validation of finite value trees. References check the existing
  world; closures check captured values and their actual bodies. This operation
  is never an external closure-registration API. -/
  private def validateAt (definitions : Core.DataEnvironment) (world : Core.StoreTyping) :
      (value : Core.Value) → (type : Core.Ty) → Except Error (TypedValue definitions world value type)
    | .unit, .unit => pure ⟨.unit⟩
    | .bool _, .bool => pure ⟨.bool⟩
    | .word _, .word => pure ⟨.word⟩
    | .integer _, .integer => pure ⟨.integer⟩
    | .pair left right, .product leftType rightType => do
        let left ← (validateAt definitions world left leftType).mapError (Error.at .productLeft)
        let right ← (validateAt definitions world right rightType).mapError (Error.at .productRight)
        pure ⟨.pair left.typed right.typed⟩
    | .inLeft annotation payload, .sum leftType rightType => do
        if same : annotation = rightType then
          let payload ← validateAt definitions world payload leftType
          pure ⟨by cases same; exact .inLeft payload.typed⟩
        else throw ⟨[], .invalidNativeValue (.sum leftType rightType) (.sum payload.type annotation)⟩
    | .inRight annotation payload, .sum leftType rightType => do
        if same : annotation = leftType then
          let payload ← validateAt definitions world payload rightType
          pure ⟨by cases same; exact .inRight payload.typed⟩
        else throw ⟨[], .invalidNativeValue (.sum leftType rightType) (.sum annotation payload.type)⟩
    | .constructed constructor payload, .namedData id => do
        if same : constructor.owner = id then
          match found : definitions.lookupConstructorPayloadType? constructor with
          | none => throw ⟨[], .data (.invalidConstructor constructor)⟩
          | some payloadType =>
              let payload ← (validateAt definitions world payload payloadType).mapError (Error.at (.constructorPayload 0))
              pure ⟨same ▸ Core.RuntimeValueHasType.constructed found payload.typed⟩
        else throw ⟨[], .data (.invalidConstructor constructor)⟩
    | .cellRef annotation location, .cell payload =>
        if same : annotation = payload then
          if found : world[location]? = some payload then
            pure ⟨by cases same; exact .cellRef found⟩
          else throw ⟨[], .data .externalReferenceUnsupported⟩
        else throw ⟨[], .data .externalReferenceUnsupported⟩
    | .closure input output body captured, .function parameter result => do
        if same : input = parameter ∧ output = result then
          let validation ← validateEnvironment definitions world captured
          if inferred : Core.infer? (input :: captured.map Core.Value.type) body definitions = some output then
            pure ⟨by rcases same with ⟨rfl, rfl⟩; exact .closure validation.typed (Core.infer_sound inferred)⟩
          else throw ⟨[], .invalidNativeValue (.function parameter result) (.function input output)⟩
        else throw ⟨[], .invalidNativeValue (.function parameter result) (.function input output)⟩
    | .hostFunction .., _ => throw ⟨[], .data .externalHostUnsupported⟩
    | value, type => throw ⟨[], .invalidNativeValue type value.type⟩
  termination_by value _ => sizeOf value
  decreasing_by all_goals simp_wf; omega

  private def validateEnvironment (definitions : Core.DataEnvironment) (world : Core.StoreTyping) :
      (environment : Core.Environment) → Except Error (TypedEnvironment definitions world environment)
    | [] => pure ⟨.nil⟩
    | head :: tail => do
        let head ← validateAt definitions world head head.type
        let tail ← validateEnvironment definitions world tail
        pure ⟨.cons head.typed tail.typed⟩
  termination_by environment => sizeOf environment
  decreasing_by all_goals simp_wf; omega
end


structure Root (compiled : SourceCoreUnifiedCompilation.Compiled) where private mk ::
  key : Key
  inputs : List Ty
  types : List Core.Ty
  result : Ty
  type : Core.Ty
  generated : compiled.compatible.checked.catalog.project result = .ok type
  body : Core.Expr
  typed : Core.HasType (types.reverse ++ (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed).map Core.Value.type)
    body (Core.LanguageResult.resultType type) compiled.indexed.layouts.definitions

private def prepareRoot (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts) : Except Error (Root compiled) := do
  let (function, index) ← match compiled.indexed.base.functions.zipIdx.find? (fun item => decide (item.1.signature.key = entry.key)) with
    | some selected => pure selected | none => throw ⟨[], .missingEntry entry.key⟩
  let types := function.inputs.map Prod.snd
  let arguments := SourceCoreCalls.packArguments (types.zipIdx.map fun (type, index) =>
    ⟨type, Core.LanguageResult.success (.var (types.length - 1 - index))⟩)
  let body := SourceCoreCalls.call function.signature (index + types.length) arguments.expression Core.Word.zero
  let expected := Core.LanguageResult.resultType function.signature.resultType
  let context := types.reverse ++ (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed).map Core.Value.type
  match projection : compiled.compatible.checked.catalog.project entry.sourceResultType with
  | .error error => throw (fromCatalog error)
  | .ok resultType =>
    if same : resultType = function.signature.resultType then
      if accepted : Core.infer? context body compiled.indexed.layouts.definitions = some expected then
        pure ⟨entry.key, entry.inputs.map (·.scheme.body), types, entry.sourceResultType,
          function.signature.resultType, same ▸ projection, body, Core.infer_sound accepted⟩
      else throw ⟨[], .checkFailed expected (Core.infer? context body compiled.indexed.layouts.definitions)⟩
    else throw ⟨[], .invalidBootstrap⟩

/-- Compiler-owned callable imports. A named row retains the exact installed
slot; a builtin retains its closed native template. Callers never supply either
piece of code, an identity word or a descriptor. -/
private structure CallableFactory (compiled : SourceCoreUnifiedCompilation.Compiled) where
  sourceType : Ty
  type : Core.Ty
  generated : compiled.compatible.checked.catalog.project sourceType = .ok type
  value : Core.Value
  slot : Option (Nat × Core.Value)

private def callableIdentity (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? (index + 1) with
  | some identity => pure identity
  | none => throw ⟨[], .identitySpaceExhausted⟩

private def callableDescriptor (compiled : SourceCoreUnifiedCompilation.Compiled)
    (origin : SourceCoreStageCodebook.Origin) : Except Error Core.Word := do
  let table ← match compiled.indexed.base.callableContext with
    | some context => pure context.table
    | none => throw ⟨[], .missingContract origin⟩
  let id ← match table.idAt? origin with
    | some id => pure id
    | none => throw ⟨[], .missingContract origin⟩
  let entry ← match table.entryAt? id with
    | some entry => pure entry
    | none => throw ⟨[], .missingContract origin⟩
  unless entry.origin = origin do throw ⟨[], .missingContract origin⟩
  pure id

private def prepareCallable (compiled : SourceCoreUnifiedCompilation.Compiled)
    (sourceType : Ty) (identity descriptor : Core.Word) (closure : Core.Value)
    (slot : Option (Nat × Core.Value)) : Except Error (CallableFactory compiled) :=
  match generated : compiled.compatible.checked.catalog.project sourceType with
  | .error error => .error (fromCatalog error)
  | .ok type =>
      let value := Core.Value.pair (.pair (.inRight .unit (.word identity)) closure) (.word descriptor)
      if value.type = type then .ok ⟨sourceType, type, generated, value, slot⟩
      else .error ⟨[], .invalidNativeValue type value.type⟩

private def prepareNamed (compiled : SourceCoreUnifiedCompilation.Compiled)
    (templates : SourceCoreCallableIndexedTemplates.Cache compiled.indexed) :
    Except Error (List (Key × CallableFactory compiled)) :=
  compiled.indexed.base.globals.zipIdx.mapM fun (signature, index) => do
    let specialized ← (SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan signature.key)
      |>.mapError (fun error => ⟨[], .callable error⟩)
    let (location, installed) ← match templates.nativeGlobals[index]? with
      | some slot => pure slot
      | none => throw ⟨[], .invalidBootstrap⟩
    let .inRight .unit closure := installed | throw ⟨[], .invalidBootstrap⟩
    let factory ← prepareCallable compiled specialized.function.type (← callableIdentity index)
      (← callableDescriptor compiled (.named signature.key)) closure (some (location, installed))
    pure (signature.key, factory)

private def prepareBuiltins (compiled : SourceCoreUnifiedCompilation.Compiled) :
    Except Error (List (BuiltinFunctionId × CallableFactory compiled)) :=
  BuiltinFunctionId.all.zipIdx.mapM fun (function, index) => do
    let .lambda input output body := SourceCoreInteger.builtinClosure function
      | throw ⟨[], .missingBuiltin function⟩
    let factory ← prepareCallable compiled function.type
      (← callableIdentity (compiled.indexed.base.globals.length + index))
      (← callableDescriptor compiled (.builtin function)) (.closure input output body []) none
    pure (function, factory)

structure Recipe where private mk ::
  compiled : SourceCoreUnifiedCompilation.Compiled
  roots : List (Root compiled)
  templates : SourceCoreCallableIndexedTemplates.Cache compiled.indexed
  private named : List (Key × CallableFactory compiled)
  private builtins : List (BuiltinFunctionId × CallableFactory compiled)
  bootstrap : Core.Expr
  bootstrapTyped : Core.HasType [] bootstrap (Core.LanguageResult.resultType .unit) compiled.indexed.layouts.definitions

def Recipe.program (recipe : Recipe) := recipe.compiled.indexed

def Recipe.prepare (compiled : SourceCoreUnifiedCompilation.Compiled) : Except Error Recipe := do
  let roots ← compiled.indexed.entries.mapM (prepareRoot compiled)
  let templates ← (SourceCoreCallableIndexedTemplates.prepare compiled.indexed).mapError (fun error => ⟨[], .templates error⟩)
  let named ← prepareNamed compiled templates
  let builtins ← prepareBuiltins compiled
  let bootstrap := SourceCoreCallableIndexedFrames.allocate compiled.indexed.ancestry.layout.frame
    (SourceCoreRecursiveEntry.allocateGlobals compiled.indexed.base.globals.reverse
      (SourceCoreRecursiveEntry.installFunctions compiled.indexed.secondPass.closures (Core.LanguageResult.success .unit)))
  if accepted : Core.infer? [] bootstrap compiled.indexed.layouts.definitions = some (Core.LanguageResult.resultType .unit) then
    pure ⟨compiled, roots, templates, named, builtins, bootstrap, Core.infer_sound accepted⟩
  else throw ⟨[], .checkFailed (Core.LanguageResult.resultType .unit)
      (Core.infer? [] bootstrap compiled.indexed.layouts.definitions)⟩

/-- Actual factory provenance. Compiled code includes proofs and is never
compared using executable equality. -/
theorem Recipe.prepare_compiled {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) : recipe.compiled = compiled := by
  unfold Recipe.prepare at accepted
  cases roots : compiled.indexed.entries.mapM (prepareRoot compiled) with
  | error error => simp [roots, bind, Except.bind] at accepted
  | ok roots =>
    cases templates : SourceCoreCallableIndexedTemplates.prepare compiled.indexed with
    | error error => simp [roots, templates, Except.mapError, bind, Except.bind] at accepted
    | ok cache =>
      simp only [roots, templates, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      cases named : prepareNamed compiled cache with
      | error error => simp [named] at accepted
      | ok named =>
        simp only [named] at accepted
        cases builtins : prepareBuiltins compiled with
        | error error => simp [builtins] at accepted
        | ok builtins =>
          simp only [builtins] at accepted
          split at accepted
          · cases accepted; rfl
          · contradiction

structure Artifact where private mk ::
  private authority : ArtifactAuthority
  private recipe : Recipe

/-- Proof-only association with the very Recipe used by artifact creation. -/
def Artifact.RecipeAt (artifact : Artifact) (recipe : Recipe) : Prop := artifact.recipe = recipe

/-- The original authority mint runs once; the association proof is erased. -/
def Recipe.openWithReceipt (recipe : Recipe) : IO { artifact : Artifact // artifact.RecipeAt recipe } := do
  let authority ← SourceCorePublicValues.ArtifactAuthority.mint
  let artifact : Artifact := ⟨authority, recipe⟩
  pure ⟨artifact, rfl⟩

def Recipe.open (recipe : Recipe) : IO Artifact := return (← recipe.openWithReceipt).val
def Artifact.program (artifact : Artifact) := artifact.recipe.program

def Artifact.keys (artifact : Artifact) : List Key := artifact.program.entries.map (·.key)
private def environment (artifact : Artifact) : Core.Environment :=
  SourceCoreCallableIndexedTemplates.globalEnvironment artifact.program
private def context (artifact : Artifact) : Core.Context := (environment artifact).map Core.Value.type

/-- The old source sourcePrefix remains inert. No locations in it are imported into
native captures, and bootstrap always starts at native location zero. -/
structure InertPrefix (artifact : Artifact) where private mk ::
  state : SourceTypedRuntime.RuntimeState
  validationFuel : Nat
  accepted : state.isDeeplySafe validationFuel artifact.program.base.sourceProgram.signatures artifact.program.base.plan = true

def InertPrefix.prepare (artifact : Artifact) (state : SourceTypedRuntime.RuntimeState)
    (fuel : Nat) : Option (InertPrefix artifact) :=
  if accepted : state.isDeeplySafe fuel artifact.program.base.sourceProgram.signatures artifact.program.base.plan = true then
    some ⟨state, fuel, accepted⟩ else none

private structure Slot (artifact : Artifact) (world : Core.StoreTyping) where
  handle : Handle
  value : Core.Value
  type : Core.Ty
  generated : artifact.recipe.compiled.compatible.checked.catalog.project handle.sourceType = .ok type
  typed : Core.RuntimeValueHasType world value type artifact.program.layouts.definitions
private abbrev Registry (artifact : Artifact) (world : Core.StoreTyping) := List (Slot artifact world)
private def Registry.weaken {artifact : Artifact} {world future : Core.StoreTyping}
    (extension : Core.WorldExtends world future) (slots : Registry artifact world) : Registry artifact future :=
  slots.map fun slot => {slot with typed := slot.typed.weaken extension}

structure Session (artifact : Artifact) where private mk ::
  private authority : SessionAuthority
  private world : Core.StoreTyping
  private store : Core.Store
  private stored : Core.RuntimeStoreHasTypes world store artifact.program.layouts.definitions
  private environmentTyped : Core.RuntimeEnvironmentHasTypes world (environment artifact) (context artifact) artifact.program.layouts.definitions
  private registry : Registry artifact world
  private values : Values
  private owner : values.checked = artifact.recipe.compiled.compatible.checked
  private sourcePrefix : InertPrefix artifact

def Session.heapSize {artifact : Artifact} (session : Session artifact) : Nat := session.store.length
def Session.functionCount {artifact : Artifact} (session : Session artifact) : Nat := session.registry.length
def Session.inertPrefix {artifact : Artifact} (session : Session artifact) : SourceTypedRuntime.RuntimeState := session.sourcePrefix.state

theorem Session.heap_typed {artifact : Artifact} (session : Session artifact) :
    Core.RuntimeStoreHasTypes session.world session.store artifact.program.layouts.definitions := session.stored

def Session.installedGlobalsPresent {artifact : Artifact} (session : Session artifact) : Bool :=
  (SourceCoreCallableNativeSlots.checkPreparedGlobals artifact.recipe.templates.nativeGlobals
    artifact.recipe.templates.nativeGlobalsGenerated session.store).isOk

theorem Session.frame_location_zero {artifact : Artifact} (session : Session artifact) :
    session.world[0]? = some artifact.program.ancestry.layout.frame.type := by
  have environmentLookup : (environment artifact)[artifact.program.base.globals.length]? =
      some (.cellRef artifact.program.ancestry.layout.frame.type 0) := by
    simp [environment, SourceCoreCallableIndexedTemplates.globalEnvironment, SourceCoreLambdaTemplates.freshGlobals]
  have contextLookup : (context artifact)[artifact.program.base.globals.length]? =
      some (.cell artifact.program.ancestry.layout.frame.type) := by
    simp only [context, List.getElem?_map, environmentLookup]
    rfl
  obtain ⟨value, found, typed⟩ := session.environmentTyped.lookup contextLookup
  rw [environmentLookup] at found
  cases found
  cases typed with
  | cellRef lookup => exact lookup

theorem Session.prefix_unchanged {artifact : Artifact} (session : Session artifact) :
    session.inertPrefix = session.sourcePrefix.state := rfl

structure Bootstrap (artifact : Artifact) where private mk ::
  private authority : SessionAuthority
  private state : Core.State
  private typed : Core.StateHasType state (Core.LanguageResult.resultType .unit) artifact.program.layouts.definitions
  private sourcePrefix : InertPrefix artifact

/-- The actual new checkpoint starts with the selected Recipe and prefix. -/
def Bootstrap.InitialAt {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (recipe : Recipe) (sourceState : SourceTypedRuntime.RuntimeState) : Prop :=
  artifact.RecipeAt recipe ∧ checkpoint.state = .initial recipe.bootstrap [] [] ∧
    checkpoint.sourcePrefix.state = sourceState

/-- Shared original construction; proof arguments do not change the IO action. -/
private def Artifact.bootstrapReceiptCore (artifact : Artifact)
    (initialTyped : Core.StateHasType ⟨.eval artifact.recipe.bootstrap [], [], []⟩
      (Core.LanguageResult.resultType .unit) artifact.program.layouts.definitions)
    (recipe : Recipe) (atRecipe : artifact.RecipeAt recipe) (sourcePrefix : InertPrefix artifact) :
    IO { checkpoint : Bootstrap artifact // checkpoint.InitialAt recipe sourcePrefix.state } := do
  let authority ← artifact.authority.newSession
  let checkpoint : Bootstrap artifact := ⟨authority, .initial artifact.recipe.bootstrap [] [], initialTyped, sourcePrefix⟩
  pure ⟨checkpoint, atRecipe, by
    change Core.State.initial artifact.recipe.bootstrap [] [] = Core.State.initial recipe.bootstrap [] []
    rw [atRecipe], rfl⟩

/-- One original session-authority mint and one original initial state. -/
def Artifact.bootstrapWithReceipt (artifact : Artifact) (recipe : Recipe)
    (atRecipe : artifact.RecipeAt recipe) (sourcePrefix : InertPrefix artifact) :
    IO { checkpoint : Bootstrap artifact // checkpoint.InitialAt recipe sourcePrefix.state } :=
  artifact.bootstrapReceiptCore (.eval (.nil _) .nil artifact.recipe.bootstrapTyped .nil)
    recipe atRecipe sourcePrefix

def Artifact.bootstrap (artifact : Artifact) (sourcePrefix : InertPrefix artifact) : IO (Bootstrap artifact) :=
  return (← artifact.bootstrapReceiptCore (.eval (.nil _) .nil artifact.recipe.bootstrapTyped .nil)
    artifact.recipe rfl sourcePrefix).val

/-- Fresh source sessions need no legacy heap/carrier argument. The native
frame and global slots are still installed by the resumable bootstrap. -/
def Artifact.bootstrapFresh (artifact : Artifact) : IO (Bootstrap artifact) :=
  artifact.bootstrap ⟨{}, 1, rfl⟩

/-- Fresh creation retains the same opaque checkpoint and empty Source prefix. -/
def Artifact.bootstrapFreshWithReceipt (artifact : Artifact) (recipe : Recipe)
    (atRecipe : artifact.RecipeAt recipe) :
    IO { checkpoint : Bootstrap artifact // checkpoint.InitialAt recipe {} } :=
  artifact.bootstrapWithReceipt recipe atRecipe ⟨{}, 1, rfl⟩

/-- A proof observation of this checkpoint's original native machine. -/
def Bootstrap.NativeDone {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (fuel : Nat) (value : Core.Value) (store : Core.Store) : Prop :=
  Core.runStateful fuel checkpoint.state = .done value store

/-- The actual native world and store, without an operational accessor. -/
def Session.NativeAt {artifact : Artifact} (session : Session artifact)
    (world : Core.StoreTyping) (store : Core.Store) : Prop :=
  session.world = world ∧ session.store = store

/-- Original successful finish keeps this exact authority, store and prefix. -/
def Session.BootstrappedFrom {artifact : Artifact} (session : Session artifact)
    (checkpoint : Bootstrap artifact) (store : Core.Store) : Prop :=
  session.authority = checkpoint.authority ∧ session.world = store.map Core.Value.type ∧
    session.store = store ∧ session.sourcePrefix = checkpoint.sourcePrefix ∧
    session.registry = [] ∧
    session.values = SourceCoreCompatibleValues.Context.initial artifact.recipe.compiled.compatible.checked


inductive BootResult (artifact : Artifact) where
  | ready (session : Session artifact)
  | outOfFuel (checkpoint : Bootstrap artifact)
  | error (error : Error)

private def checkGlobals (artifact : Artifact) (store : Core.Store) : Except Error Unit := do
  discard <| (SourceCoreCallableNativeSlots.checkPreparedGlobals artifact.recipe.templates.nativeGlobals
    artifact.recipe.templates.nativeGlobalsGenerated store).mapError (fun error => ⟨[], .globals error⟩)

private def Bootstrap.finish {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (fuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store) : BootResult artifact := by
  let world := store.map Core.Value.type
  have stored : Core.RuntimeStoreHasTypes world store artifact.program.layouts.definitions := by
    obtain ⟨future, typedStore, _⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed finished
    simpa only [typedStore.world_eq] using typedStore
  exact match value with
  | .inRight .word .unit =>
      match checkGlobals artifact store with
      | .error error => .error error
      | .ok _ => match validateEnvironment artifact.program.layouts.definitions world (environment artifact) with
        | .error error => .error error
        | .ok validated => .ready ⟨checkpoint.authority, world, store, stored, validated.typed, [],
            .initial artifact.recipe.compiled.compatible.checked, rfl, checkpoint.sourcePrefix⟩
  | _ => .error ⟨[], .invalidBootstrap⟩

def Bootstrap.resume {artifact : Artifact} (checkpoint : Bootstrap artifact) (fuel : Nat) : BootResult artifact :=
  match executed : Core.runStateful fuel checkpoint.state with
  | .done value store => checkpoint.finish fuel value store executed
  | .outOfFuel state => .outOfFuel ⟨checkpoint.authority, state,
      Core.well_typed_runStateful_preserves_checkpoint_type checkpoint.typed executed, checkpoint.sourcePrefix⟩
  | .fault _ _ => False.elim (Core.well_typed_runStateful_never_faults checkpoint.typed executed)

theorem Bootstrap.native_safe {artifact : Artifact} (checkpoint : Bootstrap artifact) (fuel : Nat) :
    (Core.runStateful fuel checkpoint.state).HasType (Core.LanguageResult.resultType .unit) artifact.program.layouts.definitions :=
  Core.well_typed_runStateful_has_type checkpoint.typed fuel



private def compatibleError (error : SourceCoreCompatibleValues.Error) : Error := ⟨error.path, .compatible error⟩
private def compatibleCode (code : SourceCoreCompatibleValues.ErrorCode) : Error := compatibleError ⟨[], code⟩

private def resolve {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (slots : Registry artifact world) (expected : Ty) (handle : Handle) : Except Error Core.Value := do
  unless handle.belongsToArtifact artifact.authority do throw ⟨[], .foreignArtifact⟩
  unless handle.belongsToSession authority do throw ⟨[], .foreignSession⟩
  let slot ← match slots.find? (fun slot => decide (slot.handle = handle)) with
    | some slot => pure slot | none => throw ⟨[], .unknownHandle⟩
  unless SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType handle.sourceType do
    throw ⟨[], .handleTypeMismatch expected handle.sourceType⟩
  pure slot.value

mutual
  private def encodeRaw {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (slots : Registry artifact world) : (fuel : Nat) → (registry : SourceCoreRawMetadata.Registry) → Ty → Value →
      Except Error (SourceCoreCompatibleValues.Extended registry Core.Value)
    | 0, _, _, _ => throw (compatibleCode .exhausted)
    | fuel + 1, registry, expected, value => do
      let checked := artifact.recipe.compiled.compatible.checked
      match SourceCoreRawMetadata.runtimeType expected, value with
      | .function .., .function handle => pure (.pure registry (← resolve authority slots expected handle))
      | .constructor (.builtin .unit), .unit => pure (.pure registry .unit)
      | .constructor (.builtin .bool), .bool value => pure (.pure registry (.bool value))
      | .constructor (.builtin .word), .word value => pure (.pure registry (.word value))
      | .constructor (.builtin .integer), .integer value => pure (.pure registry (.integer value))
      | .product leftType rightType, .product left right =>
          let left ← (encodeRaw authority slots fuel registry leftType left).mapError (Error.at .productLeft)
          let right ← (encodeRaw authority slots fuel left.registry rightType right).mapError (Error.at .productRight)
          pure ⟨right.registry, left.preserves.trans right.preserves, .pair left.value right.value⟩
      | .proxy _, .proxy inner =>
          (SourceCoreCompatibleValues.encodeRaw (fuel + 1) checked registry expected (.proxy inner)).mapError compatibleError
      | .mapping key value, .mapping actualKey actualValue entries =>
          let header ← (registry.intern expected (.mapping actualKey actualValue)).mapError (fun error => compatibleCode (.metadata error))
          let layout ← (checked.catalog.mappingLayout key value).mapError fromCatalog
          let entries ← encodeEntries authority slots fuel header.registry actualKey actualValue layout entries
          let fallback ← (SourceCoreCompatibleValues.encodeDefaultRaw fuel checked entries.registry actualValue layout.valueType).mapError compatibleError
          pure ⟨fallback.registry, header.preserves.trans (entries.preserves.trans fallback.preserves),
            .pair (.word header.id) (.pair fallback.value entries.value)⟩
      | _, .constructed instantiation payloads =>
          let header ← (registry.intern expected (.constructor instantiation)).mapError (fun error => compatibleCode (.metadata error))
          let tag ← (checked.resolveConstructor instantiation).mapError fromCatalog
          let payload ← encodePayloads authority slots fuel header.registry instantiation.payloadTypes payloads
          pure ⟨payload.registry, header.preserves.trans payload.preserves, .constructed tag (.pair (.word header.id) payload.value)⟩
      | _, value => throw (compatibleCode (.sourceTypeMismatch expected value.type))
  private def encodePayloads {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (slots : Registry artifact world) (fuel : Nat) (registry : SourceCoreRawMetadata.Registry)
      (types : List Ty) (payloads : List Value) : Except Error (SourceCoreCompatibleValues.Extended registry Core.Value) := do
    match fuel, types, payloads with
    | _, [], [] => pure (.pure registry .unit)
    | 0, _, _ => throw (compatibleCode .exhausted)
    | fuel + 1, [type], [value] => encodeRaw authority slots fuel registry type value
    | fuel + 1, type :: types, value :: values =>
        let value ← encodeRaw authority slots fuel registry type value
        let rest ← encodePayloads authority slots fuel value.registry types values
        pure ⟨rest.registry, value.preserves.trans rest.preserves, .pair value.value rest.value⟩
    | _, _, _ => throw (compatibleCode (.payloadCountMismatch types.length payloads.length))
  private def encodeEntries {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (slots : Registry artifact world) : (fuel : Nat) → (registry : SourceCoreRawMetadata.Registry) → Ty → Ty → Core.OrderedMapping.Layout →
      List (Value × Value) → Except Error (SourceCoreCompatibleValues.Extended registry Core.Value)
    | _, registry, _, _, layout, [] => pure (.pure registry (Core.OrderedMapping.encode layout []))
    | 0, _, _, _, _, _ :: _ => throw (compatibleCode .exhausted)
    | fuel + 1, registry, keyType, valueType, layout, (key, value) :: rest => do
        let key ← encodeRaw authority slots fuel registry keyType key
        let value ← encodeRaw authority slots fuel key.registry valueType value
        let rest ← encodeEntries authority slots fuel value.registry keyType valueType layout rest
        pure ⟨rest.registry, key.preserves.trans (value.preserves.trans rest.preserves),
          .constructed layout.consConstructor (.pair (.pair key.value value.value) rest.value)⟩
end

private def register {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (generation : ExportGeneration) (slots : Registry artifact world) (expected : Ty) (value : Core.Value) :
    Except Error (Handle × Registry artifact world) := do
  match slots.find? (fun slot => decide (slot.handle.sourceType = expected ∧ slot.value = value)) with
  | some slot => pure (slot.handle, slots)
  | none =>
      match generated : artifact.recipe.compiled.compatible.checked.catalog.project expected with
      | .error error => throw (fromCatalog error)
      | .ok type =>
          let checked ← validateAt artifact.program.layouts.definitions world value type
          let handle := authority.issue generation slots.length expected
          pure (handle, slots ++ [⟨handle, value, type, generated, checked.typed⟩])

private def metadata (values : Values) (expected : Ty) (id : Core.Word) : Except Error SourceCoreRawMetadata.Metadata := do
  let item ← match values.registry.lookup id with
    | some item => pure item | none => throw (compatibleCode (.unknownMetadata id))
  unless SourceCoreRawMetadata.runtimeType item.type = SourceCoreRawMetadata.runtimeType expected do
    throw (compatibleCode (.sourceTypeMismatch expected item.type))
  pure item

mutual
  private def decodeRaw {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (generation : ExportGeneration) (values : Values) : Nat → Registry artifact world → Ty → Core.Value → Except Error (Value × Registry artifact world)
    | 0, _, _, _ => throw (compatibleCode .exhausted)
    | fuel + 1, slots, expected, value => do
      match SourceCoreRawMetadata.runtimeType expected, value with
      | .function .., value =>
          let (handle, slots) ← register authority generation slots expected value
          pure (.function handle, slots)
      | .constructor (.builtin .unit), .unit => pure (.unit, slots)
      | .constructor (.builtin .bool), .bool value => pure (.bool value, slots)
      | .constructor (.builtin .word), .word value => pure (.word value, slots)
      | .constructor (.builtin .integer), .integer value => pure (.integer value, slots)
      | .product leftType rightType, .pair left right =>
          let (left, slots) ← (decodeRaw authority generation values fuel slots leftType left).mapError (Error.at .productLeft)
          let (right, slots) ← (decodeRaw authority generation values fuel slots rightType right).mapError (Error.at .productRight)
          pure (.product left right, slots)
      | .proxy _, core =>
          let data ← (SourceCoreCompatibleValues.decodeRaw (fuel + 1) values expected core).mapError compatibleError
          match data with
          | .proxy inner => pure (.proxy inner, slots)
          | _ => throw (compatibleCode .nonCanonicalCoreValue)
      | .mapping _ _, .pair (.word id) (.pair fallback stored) =>
          let header ← metadata values expected id
          let (key, valueType) ← match header with
            | .mapping key value => pure (key, value) | _ => throw (compatibleCode (.metadataKindMismatch id))
          let layout ← (values.checked.catalog.mappingLayout key valueType).mapError fromCatalog
          let (entries, slots) ← decodeEntries authority generation values fuel slots key valueType layout stored
          let actualDefault ← (SourceCoreCompatibleValues.decodeDefaultRaw fuel values valueType layout.valueType fallback).mapError compatibleError
          unless actualDefault = SourceCoreCompatibleValues.defaultValue? (valueType.size + 1) valueType do
            throw (compatibleCode .transportedDefaultMismatch)
          pure (.mapping key valueType entries, slots)
      | _, .constructed constructor (.pair (.word id) payload) =>
          let header ← metadata values expected id
          let instantiation ← match header with
            | .constructor instantiation => pure instantiation | _ => throw (compatibleCode (.metadataKindMismatch id))
          let tag ← (values.checked.resolveConstructor instantiation).mapError fromCatalog
          unless constructor = tag do throw (compatibleCode (.constructorMismatch constructor))
          let (payloads, slots) ← decodePayloads authority generation values fuel slots instantiation.payloadTypes payload
          pure (.constructed instantiation payloads, slots)
      | _, value => throw (compatibleCode (.coreShapeMismatch (← values.checked.catalog.project expected |>.mapError fromCatalog) value.type))
  private def decodePayloads {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (generation : ExportGeneration) (values : Values) : Nat → Registry artifact world → List Ty → Core.Value → Except Error (List Value × Registry artifact world)
    | _, slots, [], .unit => pure ([], slots)
    | 0, _, _, _ => throw (compatibleCode .exhausted)
    | fuel + 1, slots, [type], value => do
        let (value, slots) ← decodeRaw authority generation values fuel slots type value
        pure ([value], slots)
    | fuel + 1, slots, type :: types, .pair value rest => do
        let (value, slots) ← decodeRaw authority generation values fuel slots type value
        let (rest, slots) ← decodePayloads authority generation values fuel slots types rest
        pure (value :: rest, slots)
    | _, _, _, _ => throw (compatibleCode .malformedPayload)
  private def decodeEntries {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
      (generation : ExportGeneration) (values : Values) : Nat → Registry artifact world → Ty → Ty → Core.OrderedMapping.Layout → Core.Value →
      Except Error (List (Value × Value) × Registry artifact world)
    | 0, _, _, _, _, _ => throw (compatibleCode .exhausted)
    | fuel + 1, slots, keyType, valueType, layout, stored => do
      match stored with
      | .constructed tag .unit =>
          unless tag = layout.nilConstructor do throw (compatibleCode (.constructorMismatch tag))
          pure ([], slots)
      | .constructed tag (.pair (.pair key value) rest) =>
          unless tag = layout.consConstructor do throw (compatibleCode (.constructorMismatch tag))
          let (key, slots) ← decodeRaw authority generation values fuel slots keyType key
          let (value, slots) ← decodeRaw authority generation values fuel slots valueType value
          let (rest, slots) ← decodeEntries authority generation values fuel slots keyType valueType layout rest
          pure ((key, value) :: rest, slots)
      | _ => throw (compatibleCode .malformedPayload)
end

private theorem environment_append {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {left right : Core.Environment} {leftTypes rightTypes : Core.Context}
    (leftTyped : Core.RuntimeEnvironmentHasTypes world left leftTypes definitions)
    (rightTyped : Core.RuntimeEnvironmentHasTypes world right rightTypes definitions) :
    Core.RuntimeEnvironmentHasTypes world (left ++ right) (leftTypes ++ rightTypes) definitions := by
  induction left generalizing leftTypes with
  | nil => cases leftTyped; exact rightTyped
  | cons head tail inductionHypothesis =>
      cases leftTyped with
      | cons valueTyped tailTyped => exact .cons valueTyped (inductionHypothesis tailTyped)

private theorem environment_reverse {definitions : Core.DataEnvironment} {world : Core.StoreTyping}
    {values : Core.Environment} {types : Core.Context}
    (typed : Core.RuntimeEnvironmentHasTypes world values types definitions) :
    Core.RuntimeEnvironmentHasTypes world values.reverse types.reverse definitions := by
  induction values generalizing types with
  | nil => cases typed; exact .nil
  | cons head tail inductionHypothesis =>
    cases typed with
    | cons valueTyped tailTyped =>
      simpa only [List.reverse_cons] using environment_append (inductionHypothesis tailTyped) (.cons valueTyped .nil)

private structure Arguments (artifact : Artifact) (world : Core.StoreTyping) (types : List Core.Ty) where
  values : Values
  owner : values.checked = artifact.recipe.compiled.compatible.checked
  native : Core.Environment
  typed : Core.RuntimeEnvironmentHasTypes world native types artifact.program.layouts.definitions

private def encodeArguments {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (slots : Registry artifact world) (fuel : Nat) (values : Values)
    (owner : values.checked = artifact.recipe.compiled.compatible.checked) :
    (sourceTypes : List Ty) → (types : List Core.Ty) → List Value → Except Error (Arguments artifact world types)
  | [], [], [] => pure ⟨values, owner, [], .nil⟩
  | expected :: expectedRest, type :: types, value :: rest => do
      match artifact.recipe.compiled.compatible.checked.catalog.project expected with
      | .ok actual => unless actual = type do throw ⟨[], .invalidBootstrap⟩
      | .error error => throw (fromCatalog error)
      let encoded ← encodeRaw authority slots fuel values.registry expected value
      let updated := values.extend encoded.registry encoded.preserves
      let validated ← validateAt artifact.program.layouts.definitions world encoded.value type
      let tail ← encodeArguments authority slots fuel updated owner expectedRest types rest
      pure ⟨tail.values, tail.owner, encoded.value :: tail.native, .cons validated.typed tail.typed⟩
  | sourceTypes, _, args => throw ⟨[], .argumentCountMismatch sourceTypes.length args.length⟩

private structure Request (compiled : SourceCoreUnifiedCompilation.Compiled) where
  result : Ty
  type : Core.Ty
  generated : compiled.compatible.checked.catalog.project result = .ok type
  diagnosticKey : Option Key

private def Root.request {compiled : SourceCoreUnifiedCompilation.Compiled} (root : Root compiled) : Request compiled :=
  ⟨root.result, root.type, root.generated, some root.key⟩

structure Checkpoint (artifact : Artifact) where private mk ::
  private origin : Session artifact
  private request : Request artifact.recipe.compiled
  private world : Core.StoreTyping
  private state : Core.State
  private stored : Core.RuntimeStoreHasTypes world state.store artifact.program.layouts.definitions
  private typed : Core.StateHasType state (Core.LanguageResult.resultType request.type) artifact.program.layouts.definitions
  private extension : Core.WorldExtends origin.world world
  private registry : Registry artifact world
  private values : Values
  private owner : values.checked = artifact.recipe.compiled.compatible.checked

/-- Native allocation count at this actual suspended checkpoint. -/
def Checkpoint.heapSize {artifact : Artifact} (checkpoint : Checkpoint artifact) : Nat := checkpoint.state.store.length

private def functionParts : Ty → Option (Ty × Ty)
  | .function parameter result => some (parameter, result)
  | .comptime type => functionParts type
  | _ => none

private structure CallableSelection (artifact : Artifact) (world : Core.StoreTyping) where
  parameter : Ty
  nativeParameter : Core.Ty
  request : Request artifact.recipe.compiled
  value : Core.Value
  typed : Core.RuntimeValueHasType world value
    (Core.CallableContract.functionType nativeParameter request.type) artifact.program.layouts.definitions

/-- Resolve the actual retained callable before validating its packed input.
The host boundary has runtime availability; it supplies no staged caller
receipt. Existing compiled source calls keep their own exact stage guards. -/
private def selectCallable {artifact : Artifact} (session : Session artifact) (handle : Handle) :
    Except Error (CallableSelection artifact session.world) := do
  let value ← resolve session.authority session.registry handle.sourceType handle
  let .pair (.pair _ _) (.word descriptor) := value | throw ⟨[], .malformedCallable⟩
  let table ← match artifact.program.base.callableContext with
    | some native => pure native.table
    | none => throw ⟨[], .malformedCallable⟩
  let entry ← match table.entryAt? descriptor with
    | some entry => pure entry
    | none => throw ⟨[], .malformedCallable⟩
  match entry.contract with
  | none => pure ()
  | some contract =>
      if contract.stagedResult || contract.parameterStages.any id then
        throw ⟨[], .stagedInvocationRequired entry.origin⟩
  let (parameter, result) ← match functionParts handle.sourceType with
    | some signature => pure signature
    | none => throw ⟨[], .notFunction handle.sourceType⟩
  let nativeParameter ← (artifact.recipe.compiled.compatible.checked.catalog.project parameter).mapError fromCatalog
  match generated : artifact.recipe.compiled.compatible.checked.catalog.project result with
  | .error error => throw (fromCatalog error)
  | .ok nativeResult =>
      let validated ← validateAt artifact.program.layouts.definitions session.world value
        (Core.CallableContract.functionType nativeParameter nativeResult)
      let key := match entry.origin with
        | .named key | .lambda key .. => some key
        | .builtin _ => none
      pure ⟨parameter, nativeParameter, ⟨result, nativeResult, generated, key⟩, value, validated.typed⟩

private def packedInvocation : Core.Expr :=
  .apply (.second (.first (.var 0))) (.var 1)

private theorem packedInvocation_typed {definitions : Core.DataEnvironment} {context : Core.Context}
    (parameter result : Core.Ty) : Core.HasType
      (Core.CallableContract.functionType parameter result :: parameter :: context)
      packedInvocation (Core.LanguageResult.resultType result) definitions :=
  .apply (.second (.first (.var rfl))) (.var rfl)

/-- Invoke one packed source parameter value: Unit for zero parameters, the
value itself for one, and a right-associated product for multiple parameters.
The actual descriptor owns source arity; tuple grouping is never inferred from
a host list. Contracts needing staged availability are rejected before input
encoding. Only an owned registry handle supplies native code. -/
def Session.startHandlePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (fuel : Nat := 1024) : Except Error (Checkpoint artifact) := do
  let selected ← selectCallable session handle
  discard <| checkGlobals artifact session.store
  let encoded ← encodeArguments session.authority session.registry fuel session.values session.owner
    [selected.parameter] [selected.nativeParameter] [argument]
  let native := selected.value :: encoded.native ++ environment artifact
  have inputs : Core.RuntimeEnvironmentHasTypes session.world native
      (Core.CallableContract.functionType selected.nativeParameter selected.request.type :: selected.nativeParameter :: context artifact)
      artifact.program.layouts.definitions :=
    .cons selected.typed (environment_append encoded.typed session.environmentTyped)
  pure ⟨session, selected.request, session.world, .initial packedInvocation native session.store, session.stored,
    .eval session.stored inputs (packedInvocation_typed _ _) .nil, .refl _, session.registry, encoded.values, encoded.owner⟩

/-- Start only a cached root body. Arguments enter the native environment as
proved values; source parameter allocations still occur in the compiled body.
The stable global references and frame cell are reused without installation. -/
def Session.start {artifact : Artifact} (session : Session artifact) (key : Key)
    (arguments : List Value) (fuel : Nat := 1024) : Except Error (Checkpoint artifact) := do
  let root ← match artifact.recipe.roots.find? (fun root => decide (root.key = key)) with
    | some root => pure root | none => throw ⟨[], .missingEntry key⟩
  discard <| checkGlobals artifact session.store
  unless root.inputs.length = arguments.length do
    throw ⟨[], .argumentCountMismatch root.inputs.length arguments.length⟩
  let encoded ← encodeArguments session.authority session.registry fuel session.values session.owner root.inputs root.types arguments
  let native := encoded.native.reverse ++ environment artifact
  have reversed : Core.RuntimeEnvironmentHasTypes session.world encoded.native.reverse root.types.reverse artifact.program.layouts.definitions :=
    environment_reverse encoded.typed
  have inputs : Core.RuntimeEnvironmentHasTypes session.world native (root.types.reverse ++ context artifact) artifact.program.layouts.definitions :=
    environment_append reversed session.environmentTyped
  pure ⟨session, root.request, session.world, .initial root.body native session.store, session.stored,
    .eval session.stored inputs root.typed .nil, .refl _, session.registry, encoded.values, encoded.owner⟩

private def diagnosticTable (artifact : Artifact) (request : Request artifact.recipe.compiled)
    (values : Values) (owner : values.checked = artifact.recipe.compiled.compatible.checked) :
    Except Error SourceCoreFaultSites.Table := do
  have extension : SourceCoreRawMetadata.Extends artifact.recipe.compiled.compatible.checked.staticRegistry values.registry := by
    simpa only [owner] using values.extension
  let table ← match artifact.program.base.diagnostics with
    | some diagnostics => (diagnostics.tableForRegistry values.registry extension).mapError (fun error => ⟨[], .diagnostics error⟩)
    | none => match request.diagnosticKey with
      | some key => pure { owner := key.declaration, resultType := request.result, reads := [], escapedReason := Core.Word.zero }
      | none => throw ⟨[], .invalidBootstrap⟩
  pure <| match artifact.program.base.callableDiagnostics with
    | none => table
    | some diagnostics => {table with additional := table.additional ++
        diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val)}

/-- Decode an actual language reason against the session's retained raw
metadata IDs and cached source sites. Unknown reasons remain explicit. -/
def Session.diagnostic {artifact : Artifact} (session : Session artifact) (key : Key)
    (reason : Core.Word) : Except Error (Option SourceCoreFaultSites.Diagnostic) := do
  let root ← match artifact.recipe.roots.find? (fun root => decide (root.key = key)) with
    | some root => pure root | none => throw ⟨[], .missingEntry key⟩
  let table ← diagnosticTable artifact root.request session.values session.owner
  pure (table.diagnostic? reason)

/-- A failed direct handle call retains its owned callable origin and raw
metadata registry, including writes made before the language failure. -/
def Session.handleDiagnostic {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (reason : Core.Word) : Except Error (Option SourceCoreFaultSites.Diagnostic) := do
  let selected ← selectCallable session handle
  let table ← diagnosticTable artifact selected.request session.values session.owner
  pure (table.diagnostic? reason)

/-- A pending request retains newly interned input metadata even before it
finishes; diagnostic lookup uses that registry rather than its origin's. -/
def Checkpoint.diagnostic {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (reason : Core.Word) : Except Error (Option SourceCoreFaultSites.Diagnostic) := do
  let table ← diagnosticTable artifact checkpoint.request checkpoint.values checkpoint.owner
  pure (table.diagnostic? reason)

private structure Exported {artifact : Artifact} (world : Core.StoreTyping)
    (authority : SessionAuthority) (fuel : Nat) (values : Values) (expected : Ty) (core : Core.Value) where
  value : Value
  slots : Registry artifact world
  encoded : SourceCoreCompatibleValues.Extended values.registry Core.Value
  reencoded : encodeRaw authority slots fuel values.registry expected value = .ok encoded
  recovered : encoded.value = core

private def exportValue {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (generation : ExportGeneration) (fuel : Nat) (values : Values) (slots : Registry artifact world)
    (expected : Ty) (core : Core.Value) : Except Error (Exported (artifact := artifact) world authority fuel values expected core) := do
  let (value, slots) ← decodeRaw authority generation values fuel slots expected core
  match generated : encodeRaw authority slots fuel values.registry expected value with
  | .error error => throw error
  | .ok encoded =>
      if same : encoded.value = core then pure ⟨value, slots, encoded, generated, same⟩
      else throw (compatibleCode .nonCanonicalCoreValue)

def Session.Authenticates {artifact : Artifact} (session : Session artifact) (fuel : Nat) (expected : Ty) (value : Value) : Prop :=
  ∃ encoded type, encodeRaw session.authority session.registry fuel session.values.registry expected value = .ok encoded ∧
    artifact.recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
    Core.RuntimeValueHasType session.world encoded.value type artifact.program.layouts.definitions

structure Authentication {artifact : Artifact} (session : Session artifact) (fuel : Nat) (expected : Ty) (value : Value) : Type where private mk ::
  typed : session.Authenticates fuel expected value

def Session.authenticate {artifact : Artifact} (session : Session artifact) (fuel : Nat) (expected : Ty) (value : Value) :
    Except Error (Authentication session fuel expected value) := do
  match generated : artifact.recipe.compiled.compatible.checked.catalog.project expected with
  | .error error => throw (fromCatalog error)
  | .ok type =>
      match encoded : encodeRaw session.authority session.registry fuel session.values.registry expected value with
      | .error error => throw error
      | .ok output =>
          let checked ← validateAt artifact.program.layouts.definitions session.world output.value type
          pure ⟨output, type, encoded, generated, checked.typed⟩

structure Completion (artifact : Artifact) where private mk ::
  value : Value
  sourceType : Ty
  session : Session artifact
  boundaryFuel : Nat
  authenticated : session.Authenticates boundaryFuel sourceType value
  private origin : Session artifact
  private extension : Core.WorldExtends origin.world session.world

private def issueCallable {artifact : Artifact} (session : Session artifact)
    (factory : CallableFactory artifact.recipe.compiled) (generation : ExportGeneration)
    (boundaryFuel : Nat) : Except Error (Completion artifact) := do
  discard <| checkGlobals artifact session.store
  match factory.slot with
  | some (location, expected) =>
      unless session.store[location]? = some expected do throw ⟨[], .invalidBootstrap⟩
  | none => pure ()
  let validated ← validateAt artifact.program.layouts.definitions session.world factory.value factory.type
  let exported ← exportValue session.authority generation boundaryFuel session.values session.registry factory.sourceType factory.value
  let updated : Session artifact := {session with registry := exported.slots}
  pure ⟨exported.value, factory.sourceType, updated, boundaryFuel,
    ⟨exported.encoded, factory.type, exported.reencoded, factory.generated, by
      change Core.RuntimeValueHasType session.world exported.encoded.value factory.type artifact.program.layouts.definitions
      rw [exported.recovered]
      exact validated.typed⟩,
    session, .refl _⟩

/-- Proof-only provenance of the one selected cached named factory and the
single generation minted by this actual issuance operation. -/
def Session.NamedIssuedAt {artifact : Artifact} (session : Session artifact)
    (key : Key) (fuel : Nat) (completion : Completion artifact) : Prop :=
  ∃ (row : Key × CallableFactory artifact.recipe.compiled) (generation : ExportGeneration),
    artifact.recipe.named.find? (fun row => decide (row.1 = key)) = some row ∧
    issueCallable session row.2 generation fuel = .ok completion

/-- Builtin issuance retains the same compiler-owned factory selection. -/
def Session.BuiltinIssuedAt {artifact : Artifact} (session : Session artifact)
    (function : BuiltinFunctionId) (fuel : Nat) (completion : Completion artifact) : Prop :=
  ∃ (row : BuiltinFunctionId × CallableFactory artifact.recipe.compiled) (generation : ExportGeneration),
    artifact.recipe.builtins.find? (fun row => decide (row.1 = function)) = some row ∧
    issueCallable session row.2 generation fuel = .ok completion

/-- The original issuance path mints once; retaining its proof does not replay IO. -/
def Session.namedWithReceipt {artifact : Artifact} (session : Session artifact) (key : Key)
    (boundaryFuel : Nat := 1024) :
    IO (Except Error {completion : Completion artifact // session.NamedIssuedAt key boundaryFuel completion}) := do
  match selected : artifact.recipe.named.find? (fun row => decide (row.1 = key)) with
  | none => pure (.error ⟨[], .missingEntry key⟩)
  | some row =>
      let generation ← SourceCorePublicValues.ExportGeneration.mint
      match issued : issueCallable session row.2 generation boundaryFuel with
      | .error error => pure (.error error)
      | .ok completion => pure (.ok ⟨completion, row, generation, selected, issued⟩)

def Session.named {artifact : Artifact} (session : Session artifact) (key : Key)
    (boundaryFuel : Nat := 1024) : IO (Except Error (Completion artifact)) := do
  pure ((← session.namedWithReceipt key boundaryFuel).map Subtype.val)

/-- The builtin wrapper retains the one minted generation and its real result. -/
def Session.builtinWithReceipt {artifact : Artifact} (session : Session artifact) (function : BuiltinFunctionId)
    (boundaryFuel : Nat := 1024) :
    IO (Except Error {completion : Completion artifact // session.BuiltinIssuedAt function boundaryFuel completion}) := do
  match selected : artifact.recipe.builtins.find? (fun row => decide (row.1 = function)) with
  | none => pure (.error ⟨[], .missingBuiltin function⟩)
  | some row =>
      let generation ← SourceCorePublicValues.ExportGeneration.mint
      match issued : issueCallable session row.2 generation boundaryFuel with
      | .error error => pure (.error error)
      | .ok completion => pure (.ok ⟨completion, row, generation, selected, issued⟩)

def Session.builtin {artifact : Artifact} (session : Session artifact) (function : BuiltinFunctionId)
    (boundaryFuel : Nat := 1024) : IO (Except Error (Completion artifact)) := do
  pure ((← session.builtinWithReceipt function boundaryFuel).map Subtype.val)

inductive Outcome (artifact : Artifact) where
  | succeeded (completion : Completion artifact)
  | failed (reason : Core.Word) (session : Session artifact)
  | outOfFuel (checkpoint : Checkpoint artifact)
  | exportError (error : Error) (session : Session artifact)

private def complete {artifact : Artifact} (checkpoint : Checkpoint artifact) (generation : ExportGeneration)
    (fuel boundaryFuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store) : Outcome artifact := by
  let world := store.map Core.Value.type
  have stored : Core.RuntimeStoreHasTypes world store artifact.program.layouts.definitions := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, _, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using typed
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, extension, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using extension
  have typed : Core.RuntimeValueHasType world value (Core.LanguageResult.resultType checkpoint.request.type)
      artifact.program.layouts.definitions := by
    obtain ⟨future, typedStore, typedValue⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed finished
    simpa only [typedStore.world_eq] using typedValue
  let registry := checkpoint.registry.weaken extension
  let session : Session artifact := ⟨checkpoint.origin.authority, world, store, stored,
    checkpoint.origin.environmentTyped.weaken (checkpoint.extension.trans extension), registry,
    checkpoint.values, checkpoint.owner, checkpoint.origin.sourcePrefix⟩
  exact match decoded : Core.LanguageResult.decode? value with
  | none => False.elim (by
      obtain ⟨_, found, _⟩ := Core.LanguageResult.decode?_runtime_typed typed
      rw [decoded] at found
      cases found)
  | some outcome =>
      have related : outcome.RuntimeHasType world checkpoint.request.type artifact.program.layouts.definitions := by
        obtain ⟨actual, found, related⟩ := Core.LanguageResult.decode?_runtime_typed typed
        rw [decoded] at found
        cases found
        exact related
      match outcome with
      | .failed reason => .failed reason session
      | .succeeded payload =>
          match exportValue checkpoint.origin.authority generation boundaryFuel checkpoint.values registry checkpoint.request.result payload with
          | .error error => .exportError error session
          | .ok exported => by
              let session : Session artifact := {session with registry := exported.slots}
              exact .succeeded ⟨exported.value, checkpoint.request.result, session, boundaryFuel,
                ⟨exported.encoded, checkpoint.request.type, exported.reencoded, checkpoint.request.generated, by
                  change Core.RuntimeValueHasType world exported.encoded.value checkpoint.request.type artifact.program.layouts.definitions
                  rw [exported.recovered]
                  exact related⟩,
                checkpoint.origin, checkpoint.extension.trans extension⟩

private def suspend {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (state : Core.State) (exhausted : Core.runStateful fuel checkpoint.state = .outOfFuel state) : Checkpoint artifact := by
  let world := state.store.map Core.Value.type
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨future, extension, stored⟩ := Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored exhausted
    simpa only [stored.world_eq] using extension
  have stored : Core.RuntimeStoreHasTypes world state.store artifact.program.layouts.definitions := by
    obtain ⟨future, _, stored⟩ := Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored exhausted
    simpa only [stored.world_eq] using stored
  exact ⟨checkpoint.origin, checkpoint.request, world, state, stored,
    Core.well_typed_runStateful_preserves_checkpoint_type checkpoint.typed exhausted,
    checkpoint.extension.trans extension, checkpoint.registry.weaken extension, checkpoint.values, checkpoint.owner⟩

/-- The same original resume action either completes at its actual native
store and export generation, or retains its actual suspended state. -/
def Checkpoint.ResumeAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (fuel boundaryFuel : Nat) (outcome : Outcome artifact) : Prop :=
  (∃ (generation : ExportGeneration) (value : Core.Value) (store : Core.Store)
      (finished : Core.runStateful fuel checkpoint.state = .done value store),
    complete checkpoint generation fuel boundaryFuel value store finished = outcome) ∨
  (∃ (state : Core.State) (exhausted : Core.runStateful fuel checkpoint.state = .outOfFuel state),
    outcome = .outOfFuel (suspend checkpoint fuel state exhausted))

/-- Retain a proof receipt from the original native match and mint once. -/
def Checkpoint.resumeWithReceipt {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO {outcome : Outcome artifact // checkpoint.ResumeAt fuel boundaryFuel outcome} := do
  match executed : Core.runStateful fuel checkpoint.state with
  | .done value store =>
      let generation ← SourceCorePublicValues.ExportGeneration.mint
      pure ⟨complete checkpoint generation fuel boundaryFuel value store executed,
        .inl ⟨generation, value, store, executed, rfl⟩⟩
  | .outOfFuel state => pure ⟨.outOfFuel (suspend checkpoint fuel state executed),
      .inr ⟨state, executed, rfl⟩⟩
  | .fault _ _ => pure (False.elim (Core.well_typed_runStateful_never_faults checkpoint.typed executed))

def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := do
  pure (← checkpoint.resumeWithReceipt fuel boundaryFuel).val

def Session.run {artifact : Artifact} (session : Session artifact) (key : Key) (arguments : List Value)
    (fuel : Nat) (boundaryFuel : Nat := 1024) : IO (Except Error (Outcome artifact)) := do
  match session.start key arguments boundaryFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume fuel boundaryFuel))

/-- Direct host runtime invocation of the retained callable. It shares the
same typed completion, language-failure, mutable heap and resume machinery as
cached source roots. Staged source invocations remain compiled-root operations. -/
def Session.invokePacked {artifact : Artifact} (session : Session artifact) (handle : Handle)
    (argument : Value) (fuel : Nat) (boundaryFuel : Nat := 1024) : IO (Except Error (Outcome artifact)) := do
  match session.startHandlePacked handle argument boundaryFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume fuel boundaryFuel))

theorem Completion.typed {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value := completion.authenticated

theorem Completion.world_extension {artifact : Artifact} (completion : Completion artifact) :
    Core.WorldExtends completion.origin.world completion.session.world := completion.extension

theorem Checkpoint.native_safe {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) :
    (Core.runStateful fuel checkpoint.state).HasType (Core.LanguageResult.resultType checkpoint.request.type) artifact.program.layouts.definitions :=
  Core.well_typed_runStateful_has_type checkpoint.typed fuel

private abbrev HeapRow (artifact : Artifact) (store : Core.Store) :=
  SourceCoreAllocationLedger.Row artifact.program.layouts store

private inductive HeapCellRelated {artifact : Artifact} {world : Core.StoreTyping}
    {store : Core.Store} (values : Values) (authority : SessionAuthority)
    (row : HeapRow artifact store) : SourceCoreHeapSnapshot.Cell → Prop where
  | absent (selected : SourceCoreCallableIndexedCellHeaders.Selected
      artifact.recipe.compiled.runtime.output.headers row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      (absent : row.payload = none) :
      HeapCellRelated values authority row
        ⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body, none⟩
  | present (selected : SourceCoreCallableIndexedCellHeaders.Selected
      artifact.recipe.compiled.runtime.output.headers row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      {native : Core.Value} (present : row.payload = some native)
      (projected : artifact.recipe.compiled.compatible.checked.catalog.project
        selected.header.raw.binder.scheme.body = .ok row.entry.key.payloadType)
      {fuel : Nat} (exported : Exported (artifact := artifact) world authority fuel values
        selected.header.raw.binder.scheme.body native) :
      HeapCellRelated values authority row
        ⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body, some (.data exported.value)⟩
  | principal (selected : SourceCoreCallableIndexedCellHeaders.Selected
      artifact.recipe.compiled.runtime.output.headers row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored
        artifact.recipe.compiled.runtime.output.output.headers row)
      (rawType : restored.cell.type = selected.header.raw.binder.scheme.body) :
      HeapCellRelated values authority row
        ⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body,
          some (.principal (SourceCoreHeapSnapshot.Principal.ofRestored restored))⟩

private structure HeapCellExport {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    (values : Values) (authority : SessionAuthority) (row : HeapRow artifact store) where
  cell : SourceCoreHeapSnapshot.Cell
  slots : Registry artifact world
  related : HeapCellRelated (world := world) values authority row cell

private def observeRow {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    (values : Values) (authority : SessionAuthority) (generation : ExportGeneration)
    (slots : Registry artifact world) (row : HeapRow artifact store) (fuel : Nat) :
    Except Error (HeapCellExport (world := world) values authority row) := do
  let selected ← (SourceCoreCallableIndexedCellHeaders.select
    artifact.recipe.compiled.runtime.output.headers row).mapError fun error => ⟨[], .cellHeader error⟩
  if monomorphic : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body, none⟩,
        slots, .absent selected monomorphic present⟩
    | some native =>
      match projected : artifact.recipe.compiled.compatible.checked.catalog.project selected.header.raw.binder.scheme.body with
      | .error error => throw (fromCatalog error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let exported ← exportValue authority generation fuel values slots selected.header.raw.binder.scheme.body native
          pure ⟨⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body, some (.data exported.value)⟩,
            exported.slots, .present selected monomorphic present (by simpa only [same] using projected) exported⟩
        else throw ⟨[], .invalidNativeValue row.entry.key.payloadType type⟩
  else
    let restored ← (SourceCoreCallableIndexedPrincipalAllocations.restore
      artifact.recipe.compiled.runtime.output.output.headers row).mapError fun error => ⟨[], .principal error⟩
    if rawType : restored.cell.type = selected.header.raw.binder.scheme.body then
      pure ⟨⟨row.sourceLocation.index, selected.header.raw.binder.scheme.body,
          some (.principal (SourceCoreHeapSnapshot.Principal.ofRestored restored))⟩,
        slots, .principal selected monomorphic restored rawType⟩
    else throw ⟨[], .handleTypeMismatch selected.header.raw.binder.scheme.body restored.cell.type⟩

private inductive HeapCellsRelated {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    (values : Values) (authority : SessionAuthority) : List (HeapRow artifact store) → List SourceCoreHeapSnapshot.Cell → Prop where
  | nil : HeapCellsRelated values authority [] []
  | cons {row rows cell cells} (head : HeapCellRelated (world := world) values authority row cell)
      (tail : HeapCellsRelated (world := world) values authority rows cells) : HeapCellsRelated (world := world) values authority (row :: rows) (cell :: cells)

private theorem HeapCellsRelated.length {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    {values : Values} {authority : SessionAuthority} {rows : List (HeapRow artifact store)}
    {cells : List SourceCoreHeapSnapshot.Cell}
    (related : HeapCellsRelated (world := world) values authority rows cells) : cells.length = rows.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

private theorem HeapCellsRelated.locations {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    {values : Values} {authority : SessionAuthority} {rows : List (HeapRow artifact store)}
    {cells : List SourceCoreHeapSnapshot.Cell}
    (related : HeapCellsRelated (world := world) values authority rows cells) :
    cells.map SourceCoreHeapSnapshot.Cell.location = rows.map (fun row => row.sourceLocation.index) := by
  induction related with
  | nil => rfl
  | cons head _ ih => cases head <;> simp only [List.map_cons, ih]

private structure HeapCellsExport {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    (values : Values) (authority : SessionAuthority) (rows : List (HeapRow artifact store)) where
  cells : List SourceCoreHeapSnapshot.Cell
  slots : Registry artifact world
  related : HeapCellsRelated (world := world) values authority rows cells

private def observeRows {artifact : Artifact} {world : Core.StoreTyping} {store : Core.Store}
    (values : Values) (authority : SessionAuthority) (generation : ExportGeneration) (fuel : Nat) :
    (slots : Registry artifact world) → (rows : List (HeapRow artifact store)) →
    Except Error (HeapCellsExport (world := world) values authority rows)
  | slots, [] => pure ⟨[], slots, .nil⟩
  | slots, row :: rows => do
    let head ← observeRow values authority generation slots row fuel
    let tail ← observeRows values authority generation fuel head.slots rows
    pure ⟨head.cell :: tail.cells, tail.slots, .cons head.related tail.related⟩

private structure HeapObservation {artifact : Artifact} (session : Session artifact) where
  ledger : SourceCoreAllocationLedger.TypedLedger artifact.program.layouts session.sourcePrefix.state.heap session.world session.store
  native : HeapCellsExport (world := session.world) session.values session.authority ledger.ledger.rows
  prefixCells : List SourceCoreHeapSnapshot.Cell
  prefixExact : prefixCells = SourceCoreHeapSnapshot.Legacy.observeAccepted artifact.program.base.sourceProgram.signatures
    artifact.program.base.plan session.sourcePrefix.state session.sourcePrefix.validationFuel session.sourcePrefix.accepted

private def observeHeap {artifact : Artifact} (session : Session artifact) (generation : ExportGeneration)
    (fuel : Nat) : Except Error (HeapObservation session) := do
  let ledger ← (SourceCoreAllocationLedger.scanTyped artifact.program.layouts session.sourcePrefix.state.heap
    session.world session.store session.stored).mapError fun error => ⟨[], .heap error⟩
  let native ← observeRows session.values session.authority generation fuel session.registry ledger.ledger.rows
  pure ⟨ledger, native, SourceCoreHeapSnapshot.Legacy.observeAccepted artifact.program.base.sourceProgram.signatures
    artifact.program.base.plan session.sourcePrefix.state session.sourcePrefix.validationFuel session.sourcePrefix.accepted, rfl⟩

private inductive Saved (artifact : Artifact) where
  | ready (session : Session artifact)
  | suspended (checkpoint : Checkpoint artifact)

private def Saved.session {artifact : Artifact} : Saved artifact → Session artifact
  | .ready session => session
  | .suspended checkpoint => ⟨checkpoint.origin.authority, checkpoint.world, checkpoint.state.store,
      checkpoint.stored, checkpoint.origin.environmentTyped.weaken checkpoint.extension,
      checkpoint.registry, checkpoint.values, checkpoint.owner, checkpoint.origin.sourcePrefix⟩

/-- An accepted inert source prefix. Source callable code and source locations
remain private sidecar data; they are never imported into the native world. -/
structure PrefixSnapshot (artifact : Artifact) where private mk ::
  private sourcePrefix : InertPrefix artifact

def PrefixSnapshot.cells {artifact : Artifact} (snapshot : PrefixSnapshot artifact) : List SourceCoreHeapSnapshot.Cell :=
  SourceCoreHeapSnapshot.Legacy.observeAccepted artifact.program.base.sourceProgram.signatures
    artifact.program.base.plan snapshot.sourcePrefix.state snapshot.sourcePrefix.validationFuel snapshot.sourcePrefix.accepted
def PrefixSnapshot.heapSize {artifact : Artifact} (snapshot : PrefixSnapshot artifact) : Nat := snapshot.cells.length

/-- Start a new owned native world at frame zero while keeping the accepted
source prefix opaque and unchanged. No old closure becomes a native input. -/
def Artifact.bootstrapFromPrefix (artifact : Artifact) (snapshot : PrefixSnapshot artifact) : IO (Bootstrap artifact) :=
  artifact.bootstrap snapshot.sourcePrefix

namespace Legacy
/-- Explicit migration adapter for the historical raw-state input API. The
predicate and admission budget are exactly those of `InertPrefix.prepare`. -/
def preparePrefix (artifact : Artifact) (state : SourceTypedRuntime.RuntimeState)
    (validationFuel : Nat) : Option (PrefixSnapshot artifact) :=
  (InertPrefix.prepare artifact state validationFuel).map fun sourcePrefix => ⟨sourcePrefix⟩
end Legacy

theorem PrefixSnapshot.source_length {artifact : Artifact} (snapshot : PrefixSnapshot artifact) :
    snapshot.heapSize = snapshot.sourcePrefix.state.heap.length :=
  SourceCoreHeapSnapshot.Legacy.observeAccepted_length snapshot.sourcePrefix.accepted

theorem Legacy.preparePrefix_admission (artifact : Artifact) (state : SourceTypedRuntime.RuntimeState)
    (validationFuel : Nat) :
    (preparePrefix artifact state validationFuel).isSome =
      state.isDeeplySafe validationFuel artifact.program.base.sourceProgram.signatures artifact.program.base.plan := by
  simp only [preparePrefix, Option.isSome_map, InertPrefix.prepare]
  split <;> simp_all

/-- A snapshot privately retains the exact typed native store, registry, raw
metadata and optional continuation. Its source heap view omits administrative
cells. Neither raw source callable code nor native references are exposed. -/
structure Snapshot (artifact : Artifact) where private mk ::
  private saved : Saved artifact
  private observed : HeapObservation saved.session

def Snapshot.cells {artifact : Artifact} (snapshot : Snapshot artifact) : List SourceCoreHeapSnapshot.Cell :=
  snapshot.observed.prefixCells ++ snapshot.observed.native.cells
def Snapshot.prefix {artifact : Artifact} (snapshot : Snapshot artifact) : PrefixSnapshot artifact :=
  ⟨snapshot.saved.session.sourcePrefix⟩

/-- Export all recorded source cells as a new inert prefix. Actual native
callables are reconstructed through cached code/capture receipts, then the
unchanged deep source validator authenticates the complete exported heap.
The original `Snapshot.prefix` continues to mean the initial sidecar only. -/
def Snapshot.exportPrefix {artifact : Artifact} (snapshot : Snapshot artifact)
    (validationFuel : Nat := 1024) (boundaryFuel : Nat := 1024) : Except Error (PrefixSnapshot artifact) := do
  let session := snapshot.saved.session
  let exported ← (SourceCoreIndexedHeapMigration.exportHeap artifact.recipe.compiled.runtime.output
    snapshot.observed.ledger session.values session.owner boundaryFuel).mapError fun error => ⟨[], .heapMigration error⟩
  let state : SourceTypedRuntime.RuntimeState := ⟨exported.heap⟩
  if accepted : state.isDeeplySafe validationFuel artifact.program.base.sourceProgram.signatures artifact.program.base.plan = true then
    pure ⟨⟨state, validationFuel, accepted⟩⟩
  else throw ⟨[], .invalidExportedPrefix validationFuel⟩

def Snapshot.prefixSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat := snapshot.observed.prefixCells.length
def Snapshot.heapSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat := snapshot.cells.length
def Snapshot.nativeHeapSize {artifact : Artifact} (snapshot : Snapshot artifact) : Nat := snapshot.saved.session.heapSize
def Snapshot.pendingAllocation {artifact : Artifact} (snapshot : Snapshot artifact) : Bool := snapshot.observed.ledger.ledger.pending.isSome
def Snapshot.cellAt? {artifact : Artifact} (snapshot : Snapshot artifact) (sourceLocation : Nat) : Option SourceCoreHeapSnapshot.Cell :=
  snapshot.cells[sourceLocation]?

inductive RestoredSnapshot (artifact : Artifact) where
  | ready (session : Session artifact)
  | suspended (checkpoint : Checkpoint artifact)

def Snapshot.restore {artifact : Artifact} (snapshot : Snapshot artifact) : RestoredSnapshot artifact := by
  rcases snapshot with ⟨saved, observed⟩
  cases saved with
  | ready session => exact .ready {session with registry := observed.native.slots}
  | suspended checkpoint => exact .suspended {checkpoint with registry := observed.native.slots}

/-- Restoring into a foreign session cannot transfer registry ownership. -/
def Session.restoreSnapshot {artifact : Artifact} (session : Session artifact) (snapshot : Snapshot artifact) :
    Except Error (RestoredSnapshot artifact) :=
  if session.authority = snapshot.saved.session.authority then .ok snapshot.restore
  else .error ⟨[], .foreignSession⟩

/-- The exact successful heap observation of this ready session. The saved
native state remains opaque, while the actual observation is retained. -/
def Session.SnapshotAt {artifact : Artifact} (session : Session artifact)
    (boundaryFuel : Nat) (snapshot : Snapshot artifact) : Prop :=
  ∃ (generation : ExportGeneration) (observed : HeapObservation session),
    observeHeap session generation boundaryFuel = .ok observed ∧
    snapshot = ⟨.ready session, observed⟩

/-- Snapshot once and retain the original successful observation receipt. -/
def Session.snapshotWithReceipt {artifact : Artifact} (session : Session artifact)
    (boundaryFuel : Nat := 1024) :
    IO (Except Error { snapshot : Snapshot artifact // session.SnapshotAt boundaryFuel snapshot }) := do
  let generation ← SourceCorePublicValues.ExportGeneration.mint
  match observedAt : observeHeap session generation boundaryFuel with
  | .error error => pure (.error error)
  | .ok observed =>
      pure (.ok ⟨⟨.ready session, observed⟩, generation, observed, observedAt, rfl⟩)

def Session.snapshot {artifact : Artifact} (session : Session artifact) (boundaryFuel : Nat := 1024) :
    IO (Except Error (Snapshot artifact)) := do
  pure ((← session.snapshotWithReceipt boundaryFuel).map Subtype.val)

def Checkpoint.snapshot {artifact : Artifact} (checkpoint : Checkpoint artifact) (boundaryFuel : Nat := 1024) :
    IO (Except Error (Snapshot artifact)) := do
  let generation ← SourceCorePublicValues.ExportGeneration.mint
  pure <| (observeHeap (Saved.session (.suspended checkpoint)) generation boundaryFuel).map
    fun observed => ⟨.suspended checkpoint, observed⟩

theorem Snapshot.prefix_length {artifact : Artifact} (snapshot : Snapshot artifact) :
    snapshot.prefixSize = snapshot.saved.session.sourcePrefix.state.heap.length := by
  rw [Snapshot.prefixSize, snapshot.observed.prefixExact]
  exact SourceCoreHeapSnapshot.Legacy.observeAccepted_length _

theorem Snapshot.source_length {artifact : Artifact} (snapshot : Snapshot artifact) :
    snapshot.heapSize = snapshot.prefixSize + snapshot.observed.ledger.ledger.rows.length := by
  simp only [Snapshot.heapSize, Snapshot.cells, List.length_append, Snapshot.prefixSize]
  rw [snapshot.observed.native.related.length]

theorem Snapshot.restore_native_size {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => session.heapSize = snapshot.nativeHeapSize
    | .suspended checkpoint => checkpoint.heapSize = snapshot.nativeHeapSize := by
  rcases snapshot with ⟨saved, observed⟩
  cases saved <;> rfl

theorem Snapshot.restore_world {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => session.world = snapshot.saved.session.world
    | .suspended checkpoint => checkpoint.world = snapshot.saved.session.world := by
  rcases snapshot with ⟨saved, observed⟩
  cases saved <;> rfl

theorem Snapshot.restore_authority {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => session.authority = snapshot.saved.session.authority
    | .suspended checkpoint => checkpoint.origin.authority = snapshot.saved.session.authority := by
  rcases snapshot with ⟨saved, observed⟩
  cases saved <;> rfl

theorem Snapshot.restore_typed {artifact : Artifact} (snapshot : Snapshot artifact) :
    match snapshot.restore with
    | .ready session => Core.RuntimeStoreHasTypes snapshot.saved.session.world session.store artifact.program.layouts.definitions
    | .suspended checkpoint => Core.RuntimeStoreHasTypes snapshot.saved.session.world checkpoint.state.store artifact.program.layouts.definitions := by
  rcases snapshot with ⟨saved, observed⟩
  cases saved with
  | ready session => exact session.stored
  | suspended checkpoint => exact checkpoint.stored

theorem Session.restoreSnapshot_self {artifact : Artifact} (session : Session artifact)
    {snapshot : Snapshot artifact} (same : snapshot.saved.session.authority = session.authority) :
    session.restoreSnapshot snapshot = .ok snapshot.restore := by
  simp only [Session.restoreSnapshot, same, ↓reduceIte]

theorem PrefixSnapshot.deeply_safe {artifact : Artifact} (snapshot : PrefixSnapshot artifact) :
    snapshot.sourcePrefix.state.DeeplySafe artifact.program.base.sourceProgram.signatures artifact.program.base.plan :=
  SourceTypedRuntime.RuntimeState.isDeeplySafe_sound snapshot.sourcePrefix.accepted

theorem Snapshot.exportPrefix_length {artifact : Artifact} {snapshot : Snapshot artifact}
    {validationFuel boundaryFuel : Nat} {exported : PrefixSnapshot artifact}
    (accepted : snapshot.exportPrefix validationFuel boundaryFuel = .ok exported) :
    exported.heapSize = snapshot.heapSize := by
  unfold Snapshot.exportPrefix at accepted
  cases migration : SourceCoreIndexedHeapMigration.exportHeap artifact.recipe.compiled.runtime.output
      snapshot.observed.ledger snapshot.saved.session.values snapshot.saved.session.owner boundaryFuel with
  | error error => simp [migration, Except.mapError, bind, Except.bind] at accepted
  | ok result =>
    simp only [migration, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
      rw [PrefixSnapshot.source_length]
      change result.heap.length = snapshot.heapSize
      rw [result.length, snapshot.source_length, snapshot.prefix_length]
      rfl
    · cases accepted

theorem Snapshot.exportPrefix_original {artifact : Artifact} {snapshot : Snapshot artifact}
    {validationFuel boundaryFuel : Nat} {exported : PrefixSnapshot artifact}
    (accepted : snapshot.exportPrefix validationFuel boundaryFuel = .ok exported) :
    exported.sourcePrefix.state.heap.take snapshot.prefixSize = snapshot.saved.session.sourcePrefix.state.heap := by
  unfold Snapshot.exportPrefix at accepted
  cases migration : SourceCoreIndexedHeapMigration.exportHeap artifact.recipe.compiled.runtime.output
      snapshot.observed.ledger snapshot.saved.session.values snapshot.saved.session.owner boundaryFuel with
  | error error => simp [migration, Except.mapError, bind, Except.bind] at accepted
  | ok result =>
    simp only [migration, Except.mapError, bind, Except.bind] at accepted
    split at accepted
    · cases accepted
      rw [snapshot.prefix_length]
      exact result.prefix
    · cases accepted
end Solcore.Frontend.SourceCoreIndexedSession


namespace Solcore.Frontend.SourceCoreIndexedSession

/-- The actual public root retains its selected function, original entry and
argument order. Native typing alone does not identify any source declaration. -/
def Root.FactoryShape (compiled : SourceCoreUnifiedCompilation.Compiled)
    (entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts)
    (root : Root compiled) : Prop :=
  ∃ function index,
    compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) = some (function, index) ∧
    function.signature.key = entry.key ∧
    root.key = entry.key ∧
    root.inputs = entry.inputs.map (·.scheme.body) ∧
    root.types = function.inputs.map Prod.snd ∧
    root.result = entry.sourceResultType ∧
    root.type = function.signature.resultType ∧
    compiled.compatible.checked.catalog.project entry.sourceResultType = .ok function.signature.resultType ∧
    root.body = SourceCoreCalls.call function.signature (index + root.types.length)
      (SourceCoreCalls.packArguments (root.types.zipIdx.map fun (type, index) =>
        ⟨type, Core.LanguageResult.success (.var (root.types.length - 1 - index))⟩)).expression Core.Word.zero ∧
    Core.infer? (root.types.reverse ++
      (SourceCoreCallableIndexedTemplates.globalEnvironment compiled.indexed).map Core.Value.type)
      root.body compiled.indexed.layouts.definitions = some (Core.LanguageResult.resultType root.type)

/-- Every root in a successfully prepared recipe comes from a real indexed
entry and the exact public call factory. This receipt contains static facts. -/
def Root.Issued (compiled : SourceCoreUnifiedCompilation.Compiled) (root : Root compiled) : Prop :=
  ∃ entry, entry ∈ compiled.indexed.entries ∧ root.FactoryShape compiled entry

private theorem root_factory_shape {compiled : SourceCoreUnifiedCompilation.Compiled}
    {entry : SourceCoreCallableIndexedPrograms.Entry compiled.indexed.layouts} {root : Root compiled}
    (accepted : prepareRoot compiled entry = .ok root) : root.FactoryShape compiled entry := by
  unfold prepareRoot at accepted
  cases selected : compiled.indexed.base.functions.zipIdx.find?
      (fun item => decide (item.1.signature.key = entry.key)) with
  | none => simp [selected, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  | some pair =>
    rcases pair with ⟨function, index⟩
    simp only [selected, bind, Except.bind, pure, Except.pure] at accepted
    split at accepted
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted
    · rename_i resultType projection
      split at accepted
      · rename_i same
        split at accepted
        · rename_i inferred
          cases accepted
          refine ⟨function, index, selected, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, inferred⟩
          · simpa using List.find?_some selected
          · simpa only [same] using projection
        · contradiction
      · contradiction

private theorem root_factory_bind_ok {α β ε : Type} {action : Except ε α}
    {next : α → Except ε β} {result : β}
    (accepted : action >>= next = .ok result) :
    ∃ value, action = .ok value ∧ next value = .ok result := by
  cases action with
  | error error => simp [bind, Except.bind] at accepted
  | ok value => exact ⟨value, rfl, accepted⟩

private theorem root_factory_mapM_member {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {output : β}
    (accepted : inputs.mapM action = .ok outputs) (member : output ∈ outputs) :
    ∃ input, input ∈ inputs ∧ action input = .ok output := by
  induction inputs generalizing outputs with
  | nil => simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted; subst outputs; cases member
  | cons first rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨head, headEq, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨tail, tailEq, accepted⟩ := root_factory_bind_ok accepted
    cases accepted
    rcases List.mem_cons.mp member with same | member
    · subst output; exact ⟨first, .head _, headEq⟩
    · obtain ⟨input, found, selected⟩ := ih tailEq member
      exact ⟨input, .tail _ found, selected⟩

/-- Successful preparation authenticates each public root's full entry and
emitted call shape, including the real reversed input slots and global index. -/
theorem Recipe.prepare_roots {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (accepted : Recipe.prepare compiled = .ok recipe) {root : Root recipe.compiled}
    (member : root ∈ recipe.roots) : root.Issued recipe.compiled := by
  unfold Recipe.prepare at accepted
  cases roots : compiled.indexed.entries.mapM (prepareRoot compiled) with
  | error error => simp [roots, bind, Except.bind] at accepted
  | ok roots =>
    cases templates : SourceCoreCallableIndexedTemplates.prepare compiled.indexed with
    | error error => simp [roots, templates, Except.mapError, bind, Except.bind] at accepted
    | ok cache =>
      simp only [roots, templates, Except.mapError, bind, Except.bind, pure, Except.pure] at accepted
      cases named : prepareNamed compiled cache with
      | error error => simp [named] at accepted
      | ok named =>
        simp only [named] at accepted
        cases builtins : prepareBuiltins compiled with
        | error error => simp [builtins] at accepted
        | ok builtins =>
          simp only [builtins] at accepted
          split at accepted
          · cases accepted
            obtain ⟨entry, entryMember, prepared⟩ := root_factory_mapM_member roots member
            exact ⟨entry, entryMember, root_factory_shape prepared⟩
          · contradiction

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession

/-- Successful public startup records the actual selected root and encoder.
Its native arity is not a claim about independent source representations.
The checkpoint keeps the same session, request, registry and encoded values. -/
def Checkpoint.RootStart {artifact : Artifact} (session : Session artifact)
    (key : Key) (arguments : List Value) (fuel : Nat) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ root : Root artifact.recipe.compiled,
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    root.key = key ∧ root.inputs.length = arguments.length ∧
    ∃ encoded : Arguments artifact session.world root.types,
      encodeArguments session.authority session.registry fuel session.values session.owner
        root.inputs root.types arguments = .ok encoded ∧
      checkpoint.origin = session ∧ checkpoint.request = root.request ∧
      checkpoint.world = session.world ∧
      checkpoint.state = .initial root.body (encoded.native.reverse ++ environment artifact) session.store ∧
      HEq checkpoint.registry session.registry ∧ checkpoint.values = encoded.values

/-- The public start equation supplies every static receipt and the original
native initial state; it never invokes an independent source evaluator. -/
theorem Session.start_root_receipt {artifact : Artifact} (session : Session artifact)
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (accepted : session.start key arguments fuel = .ok checkpoint) :
    checkpoint.RootStart session key arguments fuel := by
  unfold Session.start at accepted
  cases found : artifact.recipe.roots.find? (fun root => decide (root.key = key)) with
  | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  | some root =>
    simp only [found, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨checked, globals, accepted⟩ := root_factory_bind_ok accepted
    split at accepted
    · rename_i lengths
      obtain ⟨encoded, encodedEq, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact ⟨root, found, by simpa using List.find?_some found, lengths,
        encoded, encodedEq, rfl, rfl, rfl, rfl, HEq.rfl, rfl⟩
    · simp [throw, throwThe, MonadExceptOf.throw] at accepted

/-- A proof-only observation of the actual native machine completion. -/
def Checkpoint.NativeDone {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (fuel : Nat) (value : Core.Value) (store : Core.Store) : Prop :=
  Core.runStateful fuel checkpoint.state = .done value store

/-- Original checkpoint completion exposes the same root and native prefix
selected by startup. The encoder's typing is used without source attribution. -/
theorem Checkpoint.RootStart.native_completed {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments boundaryFuel)
    {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (completed : checkpoint.NativeDone fuel value store) :
    ∃ root : Root artifact.recipe.compiled,
      artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧ root.key = key ∧
      ∃ native : Core.Environment,
        Core.RuntimeEnvironmentHasTypes session.world native root.types artifact.program.layouts.definitions ∧
        Core.runStateful fuel (.initial root.body (native.reverse ++ environment artifact) session.store) = .done value store := by
  obtain ⟨root, found, keyEq, _, encoded, _, _, _, _, initial, _, _⟩ := receipt
  exact ⟨root, found, keyEq, encoded.native, encoded.typed, by
    simpa only [Checkpoint.NativeDone, initial] using completed⟩

/-- Startup reuses the complete original store, including native globals and
all shared captures; no heap-prefix inference enters this equality. -/
theorem Checkpoint.RootStart.heap_size {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments fuel) :
    checkpoint.heapSize = session.heapSize := by
  obtain ⟨root, _, _, _, encoded, _, _, _, _, initial, _, _⟩ := receipt
  simp only [Checkpoint.heapSize, Session.heapSize, initial, Core.State.initial]

end Solcore.Frontend.SourceCoreIndexedSession


namespace Solcore.Frontend.SourceCoreIndexedSession

/-- Scalar and product inputs need no handle or metadata allocation. This is
a structural admission predicate; it contains no execution or typing law. -/
inductive SimplePublic : Value → Prop where
  | unit : SimplePublic .unit
  | bool (value : Bool) : SimplePublic (.bool value)
  | word (value : Core.Word) : SimplePublic (.word value)
  | integer (value : Int) : SimplePublic (.integer value)
  | product {left right : Value} :
      SimplePublic left → SimplePublic right → SimplePublic (.product left right)

/-- The raw type view and native bytes selected by the actual input encoder.
Source interpretation is supplied separately by the semantic boundary. -/
inductive SimpleInput : TypeSystem.Ty → Value → Core.Value → Prop where
  | unit {expected : TypeSystem.Ty}
      (view : SourceCoreRawMetadata.runtimeType expected = .unit) :
      SimpleInput expected .unit .unit
  | bool {expected : TypeSystem.Ty} (value : Bool)
      (view : SourceCoreRawMetadata.runtimeType expected = .bool) :
      SimpleInput expected (.bool value) (.bool value)
  | word {expected : TypeSystem.Ty} (value : Core.Word)
      (view : SourceCoreRawMetadata.runtimeType expected = .word) :
      SimpleInput expected (.word value) (.word value)
  | integer {expected : TypeSystem.Ty} (value : Int)
      (view : SourceCoreRawMetadata.runtimeType expected = .integer) :
      SimpleInput expected (.integer value) (.integer value)
  | product {expected leftType rightType : TypeSystem.Ty} {left right : Value}
      {first second : Core.Value}
      (view : SourceCoreRawMetadata.runtimeType expected = .product leftType rightType)
      (leftInput : SimpleInput leftType left first) (rightInput : SimpleInput rightType right second) :
      SimpleInput expected (.product left right) (.pair first second)

private theorem simple_mapError_ok {α ε δ : Type} {action : Except ε α}
    {convert : ε → δ} {value : α} (accepted : action.mapError convert = .ok value) :
    action = .ok value := by
  cases action <;> cases accepted
  rfl

private theorem simple_raw_input {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world}
    {publicValue : Value} (simple : SimplePublic publicValue)
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : TypeSystem.Ty}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : encodeRaw authority slots fuel registry expected publicValue = .ok encoded) :
    SimpleInput expected publicValue encoded.value ∧ encoded.registry = registry := by
  induction simple generalizing fuel registry expected encoded with
  | unit =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin =>
          cases builtin <;> try (solve | cases accepted)
          cases accepted
          exact ⟨.unit view, rfl⟩
  | bool value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin =>
          cases builtin <;> try (solve | cases accepted)
          cases accepted
          exact ⟨.bool value view, rfl⟩
  | word value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin =>
          cases builtin <;> try (solve | cases accepted)
          cases accepted
          exact ⟨.word value view, rfl⟩
  | integer value =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin =>
          cases builtin <;> try (solve | cases accepted)
          cases accepted
          exact ⟨.integer value view, rfl⟩
  | product left right first second =>
    cases fuel with
    | zero => cases accepted
    | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin => cases builtin <;> cases accepted
      case product leftType rightType =>
        obtain ⟨a, acceptedA, accepted⟩ := root_factory_bind_ok accepted
        obtain ⟨b, acceptedB, accepted⟩ := root_factory_bind_ok accepted
        cases accepted
        obtain ⟨relatedA, registryA⟩ := first (simple_mapError_ok acceptedA)
        obtain ⟨relatedB, registryB⟩ := second (simple_mapError_ok acceptedB)
        exact ⟨.product view relatedA relatedB, registryB.trans registryA⟩

inductive SimpleInputs : List TypeSystem.Ty → List Value → Core.Environment → Prop where
  | nil : SimpleInputs [] [] []
  | cons {expected : TypeSystem.Ty} {value : Value} {native : Core.Value}
      {types : List TypeSystem.Ty} {values : List Value} {natives : Core.Environment}
      (head : SimpleInput expected value native) (tail : SimpleInputs types values natives) :
      SimpleInputs (expected :: types) (value :: values) (native :: natives)

private theorem simple_arguments {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {values : Values} {owner : values.checked = artifact.recipe.compiled.compatible.checked}
    {sourceTypes : List TypeSystem.Ty} {types : List Core.Ty} {arguments : List Value}
    {encoded : Arguments artifact world types}
    (simple : ∀ argument ∈ arguments, SimplePublic argument)
    (accepted : encodeArguments authority slots fuel values owner sourceTypes types arguments = .ok encoded) :
    SimpleInputs sourceTypes arguments encoded.native ∧
      sourceTypes.mapM artifact.recipe.compiled.compatible.checked.catalog.project = .ok types := by
  induction sourceTypes generalizing types arguments values encoded with
  | nil =>
    cases types <;> cases arguments <;> try (solve | cases accepted)
    cases accepted
    exact ⟨.nil, rfl⟩
  | cons expected rest ih =>
    cases types with
    | nil => cases accepted
    | cons type types =>
      cases arguments with
      | nil => cases accepted
      | cons argument arguments =>
        have head := simple argument (by simp)
        have tail : ∀ value ∈ arguments, SimplePublic value :=
          fun value member => simple value (List.mem_cons_of_mem _ member)
        simp only [encodeArguments] at accepted
        cases projected : artifact.recipe.compiled.compatible.checked.catalog.project expected with
        | error error => simp [projected, bind, Except.bind, throw, throwThe] at accepted
        | ok actual =>
          simp only [projected, bind, Except.bind] at accepted
          split at accepted
          · rename_i same
            subst actual
            obtain ⟨raw, rawEq, accepted⟩ := root_factory_bind_ok accepted
            obtain ⟨validated, _, accepted⟩ := root_factory_bind_ok accepted
            obtain ⟨encodedTail, tailEq, accepted⟩ := root_factory_bind_ok accepted
            cases accepted
            obtain ⟨related, _⟩ := simple_raw_input head rawEq
            obtain ⟨relatedTail, projectedTail⟩ := ih tail tailEq
            exact ⟨.cons related relatedTail, by simp [List.mapM_cons, projected, projectedTail, bind, Except.bind]⟩
          · simp [throw, throwThe] at accepted

/-- This proof-only view fixes the exact prefix chosen by startup. It does not
expose the private state through an executable accessor. -/
def Checkpoint.SimpleInputs {artifact : Artifact} (session : Session artifact)
    (key : Key) (arguments : List Value) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ (root : Root artifact.recipe.compiled) (native : Core.Environment),
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    Solcore.Frontend.SourceCoreIndexedSession.SimpleInputs root.inputs arguments native ∧
    root.inputs.mapM artifact.recipe.compiled.compatible.checked.catalog.project = .ok root.types ∧
    checkpoint.state = .initial root.body (native.reverse ++ environment artifact) session.store

/-- Accepted encoding supplies the raw views and exact bytes for every scalar
and product argument, in order. No independent source meaning is assumed. -/
theorem Checkpoint.RootStart.simple_inputs {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments fuel)
    (simple : ∀ argument ∈ arguments, SimplePublic argument) : checkpoint.SimpleInputs session key arguments := by
  obtain ⟨root, selected, _, _, encoded, accepted, _, _, _, initial, _, _⟩ := receipt
  obtain ⟨related, projected⟩ := simple_arguments simple accepted
  exact ⟨root, encoded.native, selected, related, projected, initial⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession

namespace DataInput
mutual
  def publicValue : SourceCoreDataValues.Value → Value
    | .unit => .unit
    | .bool value => .bool value
    | .word value => .word value
    | .integer value => .integer value
    | .product left right => .product (publicValue left) (publicValue right)
    | .proxy inner => .proxy inner
    | .constructed metadata payloads => .constructed metadata (publicValues payloads)
    | .mapping key value entries => .mapping key value (publicEntries entries)
  termination_by value => sizeOf value
  decreasing_by all_goals simp_wf; omega

  def publicValues : List SourceCoreDataValues.Value → List Value
    | [] => []
    | head :: tail => publicValue head :: publicValues tail
  termination_by values => sizeOf values
  decreasing_by all_goals simp_wf; omega

  def publicEntries : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value) → List (Value × Value)
    | [] => []
    | (key, value) :: tail => (publicValue key, publicValue value) :: publicEntries tail
  termination_by entries => sizeOf entries
  decreasing_by all_goals simp_wf; omega
end
end DataInput

open SourceInference TypeSystem

private theorem data_applyMany_not_function (head : Ty) (arguments : List Ty)
    (nonfunction : ∀ left right, SourceCoreRawMetadata.runtimeType head ≠ .function left right) :
    ∀ left right, SourceCoreRawMetadata.runtimeType (Ty.applyMany head arguments) ≠ .function left right := by
  induction arguments generalizing head with
  | nil => exact nonfunction
  | cons argument rest ih =>
    exact ih (.application head argument) (by intro left right; simp [SourceCoreRawMetadata.runtimeType])

private theorem data_constructor_not_function {registry : SourceCoreRawMetadata.Registry}
    {expected : Ty} {metadata : DataConstructorInstantiation}
    (inserted : SourceCoreRawMetadata.Inserted registry expected (.constructor metadata)) :
    ∀ left right, SourceCoreRawMetadata.runtimeType expected ≠ .function left right := by
  have authentic := inserted.authenticated
  change SourceCoreRawMetadata.constructorAuthentic registry.signatures metadata = true at authentic
  unfold SourceCoreRawMetadata.constructorAuthentic at authentic
  split at authentic <;> try cases authentic
  split at authentic <;> try cases authentic
  split at authentic <;> try cases authentic
  split at authentic <;> try cases authentic
  rename_i arguments found
  simp only [Bool.and_eq_true, decide_eq_true_eq] at authentic
  rw [inserted.runtime_compatible, SourceCoreRawMetadata.Metadata.type, authentic.2]
  exact data_applyMany_not_function _ arguments (by intro left right; simp [SourceCoreRawMetadata.runtimeType])

private def RawDataCorrespondence (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (slots : Registry artifact world) (registry : SourceCoreRawMetadata.Registry) (expected : Ty)
    (carrier : SourceCoreDataValues.Value) (encoded : SourceCoreCompatibleValues.Extended registry Core.Value),
    encodeRaw authority slots fuel registry expected (DataInput.publicValue carrier) = .ok encoded →
    SourceCoreCompatibleValues.encodeRaw fuel artifact.recipe.compiled.compatible.checked registry expected carrier = .ok encoded

private def PayloadDataCorrespondence (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (slots : Registry artifact world) (registry : SourceCoreRawMetadata.Registry) (types : List Ty)
    (carriers : List SourceCoreDataValues.Value) (encoded : SourceCoreCompatibleValues.Extended registry Core.Value),
    encodePayloads authority slots fuel registry types (DataInput.publicValues carriers) = .ok encoded →
    ∀ index, SourceCoreCompatibleValues.encodePayloadsRaw fuel artifact.recipe.compiled.compatible.checked
      registry types carriers index = .ok encoded

private def EntriesDataCorrespondence (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (slots : Registry artifact world) (registry : SourceCoreRawMetadata.Registry) (key value : Ty)
    (layout : Core.OrderedMapping.Layout) (carriers : List (SourceCoreDataValues.Value × SourceCoreDataValues.Value))
    (encoded : SourceCoreCompatibleValues.Extended registry Core.Value),
    encodeEntries authority slots fuel registry key value layout (DataInput.publicEntries carriers) = .ok encoded →
    ∀ index, SourceCoreCompatibleValues.encodeEntriesRaw fuel artifact.recipe.compiled.compatible.checked
      registry key value layout carriers index = .ok encoded

private theorem raw_data_succ {fuel : Nat} (raw : RawDataCorrespondence fuel)
    (payload : PayloadDataCorrespondence fuel) (entries : EntriesDataCorrespondence fuel) :
    RawDataCorrespondence (fuel + 1) := by
  intro artifact world authority slots registry expected carrier encoded accepted
  cases carrier with
  | unit | bool value | word value | integer value =>
    simp only [DataInput.publicValue] at accepted
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    all_goals try (solve | cases accepted)
    case constructor id =>
      cases id with
      | declaration => cases accepted
      | builtin builtin =>
        cases builtin <;> try (solve | cases accepted)
        all_goals cases accepted; simp [SourceCoreCompatibleValues.encodeRaw, erased]
  | product left right =>
    simp only [DataInput.publicValue] at accepted
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case product leftType rightType =>
      obtain ⟨a, aEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨b, bEq, accepted⟩ := root_factory_bind_ok accepted
      have first := raw authority slots registry leftType left a (simple_mapError_ok aEq)
      have second := raw authority slots a.registry rightType right b (simple_mapError_ok bEq)
      cases accepted
      unfold SourceCoreCompatibleValues.encodeRaw
      rw [erased]
      simp only [first, second, Except.mapError, bind, Except.bind, pure, Except.pure]
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | proxy inner =>
    simp only [DataInput.publicValue] at accepted
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case proxy expectedInner => exact simple_mapError_ok accepted
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | mapping key value carriers =>
    simp only [DataInput.publicValue] at accepted
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case mapping keyType valueType =>
      obtain ⟨inserted, insertEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨layout, layoutEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨encodedEntries, entriesEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨fallback, fallbackEq, accepted⟩ := root_factory_bind_ok accepted
      have insertedEq := simple_mapError_ok insertEq
      have selectedLayout := simple_mapError_ok layoutEq
      have encodedEntriesEq := entries authority slots inserted.registry key value layout carriers encodedEntries entriesEq 0
      have actualFallback := simple_mapError_ok fallbackEq
      cases accepted
      unfold SourceCoreCompatibleValues.encodeRaw
      rw [erased]
      simp only [insertedEq, selectedLayout, encodedEntriesEq, actualFallback, Except.mapError, bind, Except.bind, pure, Except.pure]
    all_goals try (solve | cases accepted)
    case constructor id => cases id <;> try (solve | cases accepted)
                           rename_i builtin; cases builtin <;> cases accepted
  | constructed metadata carriers =>
    simp only [DataInput.publicValue] at accepted
    have step : ∀ (inserted : SourceCoreRawMetadata.Inserted registry expected (.constructor metadata))
        tag (fields : SourceCoreCompatibleValues.Extended inserted.registry Core.Value),
        registry.intern expected (.constructor metadata) = .ok inserted →
        artifact.recipe.compiled.compatible.checked.resolveConstructor metadata = .ok tag →
        encodePayloads authority slots fuel inserted.registry metadata.payloadTypes
          (DataInput.publicValues carriers) = .ok fields →
        encoded = ⟨fields.registry, inserted.preserves.trans fields.preserves,
          .constructed tag (.pair (.word inserted.id) fields.value)⟩ →
        SourceCoreCompatibleValues.encodeRaw (fuel + 1) artifact.recipe.compiled.compatible.checked
          registry expected (.constructed metadata carriers) = .ok encoded := by
      intro inserted tag fields insertedEq resolved fieldsEq same
      have fieldEncoding := payload authority slots inserted.registry metadata.payloadTypes carriers fields fieldsEq 0
      have nonfunction := data_constructor_not_function inserted
      subst encoded
      cases erased : SourceCoreRawMetadata.runtimeType expected
      case function left right => exact False.elim (nonfunction left right erased)
      all_goals
        unfold SourceCoreCompatibleValues.encodeRaw
        rw [erased]
      all_goals try (solve | simp only [insertedEq, resolved, fieldEncoding, Except.mapError, bind, Except.bind, pure, Except.pure])
    cases erased : SourceCoreRawMetadata.runtimeType expected <;>
      (unfold encodeRaw at accepted; rw [erased] at accepted)
    case constructor id =>
      cases id <;> try (rename_i builtin; cases builtin)
      all_goals
        obtain ⟨inserted, insertedEq, accepted⟩ := root_factory_bind_ok accepted
        obtain ⟨tag, resolved, accepted⟩ := root_factory_bind_ok accepted
        obtain ⟨fields, fieldsEq, accepted⟩ := root_factory_bind_ok accepted
        cases accepted
        exact step inserted tag fields (simple_mapError_ok insertedEq) (simple_mapError_ok resolved) fieldsEq rfl
    all_goals
      obtain ⟨inserted, insertedEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨tag, resolved, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨fields, fieldsEq, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact step inserted tag fields (simple_mapError_ok insertedEq) (simple_mapError_ok resolved) fieldsEq rfl

private theorem data_payloads_length {fuel index : Nat} {checked : SourceCoreCompatibleCatalog.Checked}
    {registry : SourceCoreRawMetadata.Registry} {types : List Ty} {carriers : List SourceCoreDataValues.Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : SourceCoreCompatibleValues.encodePayloadsRaw fuel checked registry types carriers index = .ok encoded) :
    types.length = carriers.length := by
  by_cases same : types.length = carriers.length
  · exact same
  · unfold SourceCoreCompatibleValues.encodePayloadsRaw at accepted
    split at accepted <;> simp_all [throw, throwThe, bind, Except.bind]

private theorem payload_data_succ {fuel : Nat} (raw : RawDataCorrespondence fuel)
    (payload : PayloadDataCorrespondence fuel) : PayloadDataCorrespondence (fuel + 1) := by
  intro artifact world authority slots registry types carriers encoded accepted index
  cases types with
  | nil => cases carriers with
    | nil =>
      simp only [DataInput.publicValues, encodePayloads] at accepted
      cases accepted
      unfold SourceCoreCompatibleValues.encodePayloadsRaw
      simp only [pure, Except.pure]
      simp
    | cons head tail => simp only [DataInput.publicValues, encodePayloads] at accepted; cases accepted
  | cons type types => cases carriers with
    | nil => simp only [DataInput.publicValues, encodePayloads] at accepted; cases accepted
    | cons head tail =>
      cases types with
      | nil => cases tail with
        | nil =>
          simp only [DataInput.publicValues, encodePayloads] at accepted
          have actual : encodeRaw authority slots fuel registry type (DataInput.publicValue head) = .ok encoded := accepted
          have encodedEq := raw authority slots registry type head encoded actual
          unfold SourceCoreCompatibleValues.encodePayloadsRaw
          simp only [encodedEq, Except.mapError]
          simp
        | cons next rest =>
          simp only [DataInput.publicValues] at accepted
          unfold encodePayloads at accepted
          obtain ⟨first, _, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨remaining, remainingEq, accepted⟩ := root_factory_bind_ok accepted
          have remainingEq := payload authority slots first.registry [] (next :: rest) remaining (by simpa only [DataInput.publicValues] using remainingEq) (index + 1)
          have size := data_payloads_length remainingEq
          simp at size
      | cons nextTypes restTypes => cases tail with
        | nil =>
          simp only [DataInput.publicValues] at accepted
          unfold encodePayloads at accepted
          obtain ⟨first, _, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨remaining, remainingEq, accepted⟩ := root_factory_bind_ok accepted
          have remainingEq := payload authority slots first.registry (nextTypes :: restTypes) [] remaining (by simpa only [DataInput.publicValues] using remainingEq) (index + 1)
          have size := data_payloads_length remainingEq
          simp at size
        | cons next rest =>
          simp only [DataInput.publicValues] at accepted
          unfold encodePayloads at accepted
          obtain ⟨first, firstEq, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨remaining, remainingEq, accepted⟩ := root_factory_bind_ok accepted
          have firstEq := raw authority slots registry type head first firstEq
          have remainingEq := payload authority slots first.registry (nextTypes :: restTypes) (next :: rest) remaining (by simpa only [DataInput.publicValues] using remainingEq) (index + 1)
          have size := data_payloads_length remainingEq
          cases accepted
          unfold SourceCoreCompatibleValues.encodePayloadsRaw
          simp only [List.length_cons, size, firstEq, remainingEq, Except.mapError, bind, Except.bind, pure, Except.pure]
          simp

private theorem entries_data_succ {fuel : Nat} (raw : RawDataCorrespondence fuel)
    (entries : EntriesDataCorrespondence fuel) : EntriesDataCorrespondence (fuel + 1) := by
  intro artifact world authority slots registry keyType valueType layout carriers encoded accepted index
  cases carriers with
  | nil => simp only [DataInput.publicEntries, encodeEntries] at accepted; cases accepted; unfold SourceCoreCompatibleValues.encodeEntriesRaw; rfl
  | cons pair rest =>
    obtain ⟨key, value⟩ := pair
    simp only [DataInput.publicEntries] at accepted
    unfold encodeEntries at accepted
    obtain ⟨keyEncoded, keyEq, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨valueEncoded, valueEq, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨restEncoded, restEq, accepted⟩ := root_factory_bind_ok accepted
    have keyEq := raw authority slots registry keyType key keyEncoded keyEq
    have valueEq := raw authority slots keyEncoded.registry valueType value valueEncoded valueEq
    have restEq := entries authority slots valueEncoded.registry keyType valueType layout rest restEncoded restEq (index + 1)
    cases accepted
    unfold SourceCoreCompatibleValues.encodeEntriesRaw
    simp only [keyEq, valueEq, restEq, Except.mapError, bind, Except.bind, pure, Except.pure]

private theorem data_correspondence (fuel : Nat) : RawDataCorrespondence fuel ∧
    PayloadDataCorrespondence fuel ∧ EntriesDataCorrespondence fuel := by
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro artifact world authority slots registry expected carrier encoded accepted
      cases accepted
    · intro artifact world authority slots registry types carriers encoded accepted index
      cases types <;> cases carriers <;>
        simp_all [encodePayloads, DataInput.publicValues, SourceCoreCompatibleValues.encodePayloadsRaw,
          SourceCoreCompatibleValues.Extended.pure, pure, Except.pure, throw, throwThe]
    · intro artifact world authority slots registry key value layout carriers encoded accepted index
      cases carriers with
      | nil => simp only [DataInput.publicEntries, encodeEntries] at accepted; cases accepted; unfold SourceCoreCompatibleValues.encodeEntriesRaw; rfl
      | cons pair rest =>
        cases pair
        simp only [DataInput.publicEntries, encodeEntries] at accepted
        cases accepted
  | succ fuel ih =>
    exact ⟨raw_data_succ ih.1 ih.2.1 ih.2.2, payload_data_succ ih.1 ih.2.1, entries_data_succ ih.1 ih.2.2⟩

/-- Data inputs retain constructor metadata and ordered mapping entries exactly.
The existence of this carrier excludes opaque handles recursively. -/
def DataPublic (value : Value) : Prop := ∃ carrier, value = DataInput.publicValue carrier

/-- This graph records successful execution of the actual compatible data
codec under its original registry, followed by the real final extension. -/
def EncodedDataInput (checked : SourceCoreCompatibleCatalog.Checked)
    (registry : SourceCoreRawMetadata.Registry) (expected : Ty) (value : Value) (native : Core.Value) : Prop :=
  ∃ (carrier : SourceCoreDataValues.Value) (fuel : Nat) (before : SourceCoreRawMetadata.Registry)
    (encoded : SourceCoreCompatibleValues.Extended before Core.Value),
    value = DataInput.publicValue carrier ∧ before.signatures = checked.signatures ∧
    SourceCoreCompatibleValues.encodeRaw fuel checked before expected carrier = .ok encoded ∧
    encoded.value = native ∧ SourceCoreRawMetadata.Extends encoded.registry registry

inductive EncodedDataInputs (checked : SourceCoreCompatibleCatalog.Checked)
    (registry : SourceCoreRawMetadata.Registry) : List Ty → List Value → Core.Environment → Prop where
  | nil : EncodedDataInputs checked registry [] [] []
  | cons {expected : Ty} {value : Value} {native : Core.Value}
      {types : List Ty} {values : List Value} {natives : Core.Environment}
      (head : EncodedDataInput checked registry expected value native)
      (tail : EncodedDataInputs checked registry types values natives) :
      EncodedDataInputs checked registry (expected :: types) (value :: values) (native :: natives)

private theorem data_arguments {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {values : Values} {owner : values.checked = artifact.recipe.compiled.compatible.checked}
    {sourceTypes : List Ty} {types : List Core.Ty} {arguments : List Value}
    {encoded : Arguments artifact world types}
    (data : ∀ argument ∈ arguments, DataPublic argument)
    (accepted : encodeArguments authority slots fuel values owner sourceTypes types arguments = .ok encoded) :
    EncodedDataInputs artifact.recipe.compiled.compatible.checked encoded.values.registry
      sourceTypes arguments encoded.native ∧
    sourceTypes.mapM artifact.recipe.compiled.compatible.checked.catalog.project = .ok types ∧
    SourceCoreRawMetadata.Extends values.registry encoded.values.registry := by
  induction sourceTypes generalizing types arguments values encoded with
  | nil =>
    cases types <;> cases arguments <;> try (solve | cases accepted)
    cases accepted
    exact ⟨.nil, rfl, .refl _⟩
  | cons expected rest ih =>
    cases types with
    | nil => cases accepted
    | cons type types =>
      cases arguments with
      | nil => cases accepted
      | cons argument arguments =>
        obtain ⟨carrier, carrierEq⟩ := data argument (by simp)
        have tail : ∀ value ∈ arguments, DataPublic value :=
          fun value member => data value (List.mem_cons_of_mem _ member)
        simp only [encodeArguments] at accepted
        cases projected : artifact.recipe.compiled.compatible.checked.catalog.project expected with
        | error error => simp [projected, bind, Except.bind, throw, throwThe] at accepted
        | ok actual =>
          simp only [projected, bind, Except.bind] at accepted
          split at accepted
          · rename_i same
            subst actual
            obtain ⟨raw, rawEq, accepted⟩ := root_factory_bind_ok accepted
            obtain ⟨validated, _, accepted⟩ := root_factory_bind_ok accepted
            obtain ⟨encodedTail, tailEq, accepted⟩ := root_factory_bind_ok accepted
            cases accepted
            obtain ⟨relatedTail, projectedTail, extendedTail⟩ := ih tail tailEq
            have correspondence := (data_correspondence fuel).1 authority slots values.registry expected carrier raw
              (by rw [← carrierEq]; exact rawEq)
            have beforeOwner : values.registry.signatures = artifact.recipe.compiled.compatible.checked.signatures :=
              values.registryOwner.trans (congrArg SourceCoreCompatibleCatalog.Checked.signatures owner)
            refine ⟨.cons ⟨carrier, fuel, values.registry, raw, carrierEq, beforeOwner,
              correspondence, rfl, extendedTail⟩ relatedTail, ?_, raw.preserves.trans extendedTail⟩
            simp [List.mapM_cons, projected, projectedTail, bind, Except.bind]
          · simp [throw, throwThe] at accepted

/-- Same actual root, exact native input prefix and final metadata registry,
expressed as a proposition without a private-state accessor. -/
def Checkpoint.DataInputs {artifact : Artifact} (session : Session artifact)
    (key : Key) (arguments : List Value) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ (root : Root artifact.recipe.compiled) (native : Core.Environment),
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    EncodedDataInputs artifact.recipe.compiled.compatible.checked checkpoint.values.registry
      root.inputs arguments native ∧
    root.inputs.mapM artifact.recipe.compiled.compatible.checked.catalog.project = .ok root.types ∧
    checkpoint.state = .initial root.body (native.reverse ++ environment artifact) session.store

/-- Accepted public startup supplies real data encoder equations for every
argument, including constructors, mappings, proxies and nested products. -/
theorem Checkpoint.RootStart.data_inputs {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments fuel)
    (data : ∀ argument ∈ arguments, DataPublic argument) : checkpoint.DataInputs session key arguments := by
  obtain ⟨root, selected, _, _, encoded, accepted, _, _, _, initial, _, sameValues⟩ := receipt
  obtain ⟨related, projected, _⟩ := data_arguments data accepted
  rw [← sameValues] at related
  exact ⟨root, encoded.native, selected, related, projected, initial⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession

/-- The actual retained metadata registry, expressed only as a proposition. -/
def Session.RegistryAt {artifact : Artifact} (session : Session artifact)
    (registry : SourceCoreRawMetadata.Registry) : Prop :=
  session.values.registry = registry

/-- The diagnostic table selected by the genuine ordinary root lookup and
rebuilt at this session's retained values. This receipt does not expose a
request or add an operational accessor. -/
def Session.DiagnosticTableAt {artifact : Artifact} (session : Session artifact)
    (key : Key) (table : SourceCoreFaultSites.Table) : Prop :=
  ∃ root : Root artifact.recipe.compiled,
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    diagnosticTable artifact root.request session.values session.owner = .ok table

/-- An actual successful public lookup retains the very table that decoded
its reason. The original two binds are inverted without running them again. -/
theorem Session.diagnostic_table_receipt {artifact : Artifact} (session : Session artifact)
    {key : Key} {reason : Core.Word} {diagnostic : SourceCoreFaultSites.Diagnostic}
    (accepted : session.diagnostic key reason = .ok (some diagnostic)) :
    ∃ table, session.DiagnosticTableAt key table ∧ table.diagnostic? reason = some diagnostic := by
  unfold Session.diagnostic at accepted
  cases found : artifact.recipe.roots.find? (fun root => decide (root.key = key)) with
  | none => simp [found, bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at accepted
  | some root =>
    simp only [found, pure, Except.pure, bind, Except.bind] at accepted
    obtain ⟨table, made, accepted⟩ := root_factory_bind_ok accepted
    simp only [Except.ok.injEq] at accepted
    exact ⟨table, ⟨root, found, made⟩, accepted⟩

/-- The retained table comes from the original registry rebuild, or its real
root fallback, followed by exactly the original filtered callable append.
Handle and pending-checkpoint requests are separate interfaces. -/
theorem Session.DiagnosticTableAt.rebuild {artifact : Artifact} {session : Session artifact}
    {key : Key} {table : SourceCoreFaultSites.Table}
    (receipt : session.DiagnosticTableAt key table) :
    ∃ registry, session.RegistryAt registry ∧
      ∃ (extension : SourceCoreRawMetadata.Extends artifact.recipe.compiled.compatible.checked.staticRegistry registry)
        (root : Root artifact.recipe.compiled) (base : SourceCoreFaultSites.Table),
        artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
        root.key = key ∧
        (match artifact.program.base.diagnostics with
          | some diagnostics => diagnostics.tableForRegistry registry extension = .ok base
          | none => base = {
              owner := key.declaration
              resultType := root.result
              reads := []
              escapedReason := Core.Word.zero }) ∧
        table = (match artifact.program.base.callableDiagnostics with
          | none => base
          | some diagnostics => { base with additional := base.additional ++
              diagnostics.rootTable.additional.filter (fun item => diagnostics.unknown.val ≤ item.1.val) }) := by
  obtain ⟨root, found, accepted⟩ := receipt
  have sameKey : root.key = key := by simpa using List.find?_some found
  let extension : SourceCoreRawMetadata.Extends artifact.recipe.compiled.compatible.checked.staticRegistry session.values.registry := by
    simpa only [session.owner] using session.values.extension
  refine ⟨session.values.registry, rfl, extension, root, ?_⟩
  unfold diagnosticTable at accepted
  dsimp only at accepted
  cases present : artifact.program.base.diagnostics with
  | some diagnostics =>
    simp only [present] at accepted
    obtain ⟨base, made, accepted⟩ := root_factory_bind_ok accepted
    refine ⟨base, found, sameKey, ?_, ?_⟩
    · change diagnostics.tableForRegistry session.values.registry extension = .ok base
      cases rebuilt : diagnostics.tableForRegistry session.values.registry extension with
      | error error => simp [rebuilt, Except.mapError] at made
      | ok actual =>
        have same : actual = base := by
          simpa only [rebuilt, Except.mapError, Except.ok.injEq] using made
        exact congrArg Except.ok same
    · exact (Except.ok.inj accepted).symm
  | none =>
    simp only [present, Root.request, pure, Except.pure, bind, Except.bind] at accepted
    cases accepted
    refine ⟨_, found, sameKey, ?_, rfl⟩
    change ({
      owner := root.key.declaration
      resultType := root.result
      reads := []
      escapedReason := Core.Word.zero } : SourceCoreFaultSites.Table) = _
    rw [sameKey]

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession

/-- An actual failed native completion retains its precise value and store,
unchanged metadata values, and the original world weakening of callable slots.
This proof receipt makes no Source-fault or public IO-event attribution. -/
def Checkpoint.FailedResultAt {artifact : Artifact}
    (checkpoint : Checkpoint artifact) (fuel : Nat)
    (native : Core.Value) (store : Core.Store) (reason : Core.Word)
    (returned : Session artifact) : Prop :=
  checkpoint.NativeDone fuel native store ∧
  Core.LanguageResult.decode? native = some (.failed reason) ∧
  returned.store = store ∧
  returned.world = store.map Core.Value.type ∧
  returned.values = checkpoint.values ∧
  HEq returned.owner checkpoint.owner ∧
  returned.authority = checkpoint.origin.authority ∧
  returned.sourcePrefix = checkpoint.origin.sourcePrefix ∧
  ∃ extension : Core.WorldExtends checkpoint.world returned.world,
    HEq returned.registry (checkpoint.registry.weaken extension)

/-- Finite inversion of the same pure completion producer. The returned
session is the one actually constructed from the given done trace. -/
theorem Checkpoint.complete_failed_receipt {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat}
    {generation : ExportGeneration} {native : Core.Value} {store : Core.Store}
    {reason : Core.Word} {returned : Session artifact}
    (completed : checkpoint.NativeDone fuel native store)
    (failed : complete checkpoint generation fuel boundaryFuel native store completed =
      .failed reason returned) :
    checkpoint.FailedResultAt fuel native store reason returned := by
  unfold complete at failed
  dsimp only at failed
  split at failed
  next decoded =>
    obtain ⟨_world, _stored, typed⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed completed
    obtain ⟨_outcome, found, _typed⟩ := Core.LanguageResult.decode?_runtime_typed typed
    rw [decoded] at found
    cases found
  next outcome decoded =>
    cases outcome with
    | failed actualReason =>
      dsimp only at failed
      cases failed
      refine ⟨completed, decoded, rfl, rfl, rfl, HEq.rfl, rfl, rfl, ?_⟩
      have extension : Core.WorldExtends checkpoint.world (store.map Core.Value.type) := by
        obtain ⟨_, _, path⟩ := Core.runStateful_sound completed
        obtain ⟨future, growth, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
        simpa only [typed.world_eq, Core.State.final, Core.State.store] using growth
      exact ⟨extension, HEq.rfl⟩
    | succeeded payload =>
      dsimp only at failed
      split at failed <;> cases failed

/-- Genuine done and decode receipts construct the actual failed session
through the original producer; native execution is not repeated. -/
theorem Checkpoint.native_failed_result_receipt {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat}
    {generation : ExportGeneration} {native : Core.Value} {store : Core.Store}
    {reason : Core.Word}
    (completed : checkpoint.NativeDone fuel native store)
    (decoded : Core.LanguageResult.decode? native = some (.failed reason)) :
    ∃ returned : Session artifact,
      complete checkpoint generation fuel boundaryFuel native store completed =
        .failed reason returned ∧
      checkpoint.FailedResultAt fuel native store reason returned := by
  have actual : ∃ returned : Session artifact,
      complete checkpoint generation fuel boundaryFuel native store completed =
        .failed reason returned := by
    unfold complete
    dsimp only
    split
    next found => simp [decoded] at found
    next outcome found =>
      have same : outcome = .failed reason := by simpa [decoded] using found.symm
      cases same
      exact ⟨_, rfl⟩
  obtain ⟨returned, failed⟩ := actual
  exact ⟨returned, failed, complete_failed_receipt completed failed⟩

end Solcore.Frontend.SourceCoreIndexedSession


namespace Solcore.Frontend.SourceCoreIndexedSession

/-- Initial creation rewrites the observed run to the SAME selected Recipe. -/
theorem Bootstrap.InitialAt.native_done {artifact : Artifact} {checkpoint : Bootstrap artifact}
    {recipe : Recipe} {sourceState : SourceTypedRuntime.RuntimeState}
    (initial : checkpoint.InitialAt recipe sourceState) {fuel : Nat} {value : Core.Value} {store : Core.Store}
    (completed : checkpoint.NativeDone fuel value store) :
    Core.runStateful fuel (.initial recipe.bootstrap [] []) = .done value store := by
  simpa only [Bootstrap.NativeDone, initial.2.1] using completed

theorem Bootstrap.InitialAt.recipe_at {artifact : Artifact} {checkpoint : Bootstrap artifact}
    {recipe : Recipe} {sourceState : SourceTypedRuntime.RuntimeState}
    (initial : checkpoint.InitialAt recipe sourceState) : artifact.RecipeAt recipe := initial.1

private theorem Bootstrap.finish_ready_receipt {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (fuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store)
    {session : Session artifact} (accepted : checkpoint.finish fuel value store finished = .ready session) :
    value = .inRight .word .unit ∧ session.BootstrappedFrom checkpoint store := by
  by_cases same : value = .inRight .word .unit
  · subst value
    dsimp only [Bootstrap.finish] at accepted
    cases globals : checkGlobals artifact store with
    | error error =>
        simp only [globals] at accepted
        cases accepted
    | ok checkedGlobals =>
        cases environment : validateEnvironment artifact.program.layouts.definitions
            (store.map Core.Value.type) (environment artifact) with
        | error error =>
            simp only [globals, environment] at accepted
            cases accepted
        | ok validated =>
            simp only [globals, environment] at accepted
            cases accepted
            exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · cases value <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
    case inRight annotation payload =>
      cases annotation <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
      case word =>
        cases payload <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
        case unit => exact (same rfl).elim

/-- Only an actual ready result yields the original completion and session. -/
theorem Bootstrap.resume_ready_receipt {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (fuel : Nat) {session : Session artifact} (accepted : checkpoint.resume fuel = .ready session) :
    ∃ value store, checkpoint.NativeDone fuel value store ∧ value = .inRight .word .unit ∧
      session.BootstrappedFrom checkpoint store := by
  unfold Bootstrap.resume at accepted
  split at accepted
  · rename_i value store executed
    obtain ⟨valueEq, booted⟩ := checkpoint.finish_ready_receipt fuel value store executed accepted
    exact ⟨value, store, executed, valueEq, booted⟩
  · cases accepted
  · rename_i error state executed
    exact (Core.well_typed_runStateful_never_faults checkpoint.typed executed).elim

/-- A suspended bootstrap retains the original authority and Source prefix,
with exactly the machine returned by the exhausted run. -/
def Bootstrap.ResumedFrom {artifact : Artifact} (checkpoint original : Bootstrap artifact)
    (fuel : Nat) : Prop :=
  Core.runStateful fuel original.state = .outOfFuel checkpoint.state ∧
    checkpoint.authority = original.authority ∧ checkpoint.sourcePrefix = original.sourcePrefix

private theorem Bootstrap.finish_ne_outOfFuel {artifact : Artifact} (checkpoint : Bootstrap artifact)
    (fuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store)
    (pending : Bootstrap artifact) : checkpoint.finish fuel value store finished ≠ .outOfFuel pending := by
  intro accepted
  by_cases same : value = .inRight .word .unit
  · subst value
    dsimp only [Bootstrap.finish] at accepted
    cases globals : checkGlobals artifact store with
    | error error =>
        simp only [globals] at accepted
        cases accepted
    | ok checkedGlobals =>
        cases environment : validateEnvironment artifact.program.layouts.definitions
            (store.map Core.Value.type) (environment artifact) with
        | error error =>
            simp only [globals, environment] at accepted
            cases accepted
        | ok validated =>
            simp only [globals, environment] at accepted
            cases accepted
  · cases value <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
    case inRight annotation payload =>
      cases annotation <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
      case word =>
        cases payload <;> try { dsimp only [Bootstrap.finish] at accepted; cases accepted }
        case unit => exact (same rfl).elim

/-- The receipt comes from the actual suspension equation. -/
theorem Bootstrap.resume_outOfFuel_receipt {artifact : Artifact} (original : Bootstrap artifact)
    (fuel : Nat) {checkpoint : Bootstrap artifact}
    (exhausted : original.resume fuel = .outOfFuel checkpoint) :
    checkpoint.ResumedFrom original fuel := by
  unfold Bootstrap.resume at exhausted
  split at exhausted
  · rename_i value store executed
    exact (original.finish_ne_outOfFuel fuel value store executed checkpoint exhausted).elim
  · rename_i state executed
    cases exhausted
    exact ⟨executed, rfl, rfl⟩
  · rename_i error state executed
    exact (Core.well_typed_runStateful_never_faults original.typed executed).elim

/-- Actual resumption costs add; authority and Source prefix remain those of
that first checkpoint. This composes receipts without executing the machine. -/
theorem Bootstrap.ResumedFrom.completed {artifact : Artifact}
    {checkpoint original : Bootstrap artifact} {spent additional : Nat}
    (resumed : checkpoint.ResumedFrom original spent)
    {session : Session artifact} {value : Core.Value} {store : Core.Store}
    (completed : checkpoint.NativeDone additional value store)
    (booted : session.BootstrappedFrom checkpoint store) :
    original.NativeDone (spent + additional) value store ∧
      session.BootstrappedFrom original store := by
  refine ⟨(Core.runStateful_resume resumed.1 additional).symm.trans completed, ?_⟩
  exact ⟨booted.1.trans resumed.2.1, booted.2.1, booted.2.2.1,
    booted.2.2.2.1.trans resumed.2.2, booted.2.2.2.2⟩

/-- Full native equality remains proof-only. -/
theorem Session.BootstrappedFrom.native_at {artifact : Artifact} {session : Session artifact}
    {checkpoint : Bootstrap artifact} {store : Core.Store} (booted : session.BootstrappedFrom checkpoint store) :
    session.NativeAt (store.map Core.Value.type) store := ⟨booted.2.1, booted.2.2.1⟩

/-- This is the actual metadata registry, distinct from physical handle slots. -/
theorem Session.BootstrappedFrom.registry_at {artifact : Artifact} {session : Session artifact}
    {checkpoint : Bootstrap artifact} {store : Core.Store} (booted : session.BootstrappedFrom checkpoint store)
    {recipe : Recipe} {sourceState : SourceTypedRuntime.RuntimeState}
    (initial : checkpoint.InitialAt recipe sourceState) :
    session.RegistryAt recipe.compiled.compatible.checked.staticRegistry := by
  unfold Session.RegistryAt
  rw [booted.2.2.2.2.2]
  change artifact.recipe.compiled.compatible.checked.staticRegistry = recipe.compiled.compatible.checked.staticRegistry
  rw [initial.1]

theorem Session.BootstrappedFrom.inert_prefix {artifact : Artifact} {session : Session artifact}
    {checkpoint : Bootstrap artifact} {store : Core.Store} (booted : session.BootstrappedFrom checkpoint store)
    {recipe : Recipe} {sourceState : SourceTypedRuntime.RuntimeState}
    (initial : checkpoint.InitialAt recipe sourceState) : session.inertPrefix = sourceState := by
  change session.sourcePrefix.state = sourceState
  rw [booted.2.2.2.1]
  exact initial.2.2

theorem Session.BootstrappedFrom.function_count {artifact : Artifact} {session : Session artifact}
    {checkpoint : Bootstrap artifact} {store : Core.Store} (booted : session.BootstrappedFrom checkpoint store) :
    session.functionCount = 0 := by simp only [Session.functionCount, booted.2.2.2.2.1, List.length_nil]

theorem Session.NativeAt.heap_typed {artifact : Artifact} {session : Session artifact}
    {world : Core.StoreTyping} {store : Core.Store} (atNative : session.NativeAt world store)
    {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) :
    Core.RuntimeStoreHasTypes world store recipe.program.layouts.definitions := by
  have typed := session.heap_typed
  rw [atNative.1, atNative.2] at typed
  change Core.RuntimeStoreHasTypes world store artifact.recipe.program.layouts.definitions at typed
  rw [atRecipe] at typed
  exact typed

end Solcore.Frontend.SourceCoreIndexedSession


namespace Solcore.Frontend.SourceCoreIndexedSession

/-- Successful export retains the actual decoder slots and the original
re-encoding, including the native payload equality checked by the producer. -/
theorem exportValue_success_receipt {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {generation : ExportGeneration} {fuel : Nat}
    {values : Values} {slots : Registry artifact world} {expected : TypeSystem.Ty} {core : Core.Value}
    {exported : Exported (artifact := artifact) world authority fuel values expected core}
    (accepted : exportValue authority generation fuel values slots expected core = .ok exported) :
    decodeRaw authority generation values fuel slots expected core = .ok (exported.value, exported.slots) ∧
    encodeRaw authority exported.slots fuel values.registry expected exported.value = .ok exported.encoded ∧
    exported.encoded.value = core := by
  unfold exportValue at accepted
  obtain ⟨decoded, decodedEq, accepted⟩ := root_factory_bind_ok accepted
  rcases decoded with ⟨value, returnedSlots⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · rename_i encoded generated
    split at accepted
    · rename_i same
      cases accepted
      exact ⟨decodedEq, generated, same⟩
    · cases accepted

/-- An actual public successful completion retains its native done trace,
true export slots, whole Source prefix and the same typed returned session. -/
def Checkpoint.SucceededResultAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (fuel boundaryFuel : Nat) (generation : ExportGeneration) (native : Core.Value)
    (store : Core.Store) (completion : Completion artifact) : Prop :=
  checkpoint.NativeDone fuel native store ∧
  ∃ (payload : Core.Value) (extension : Core.WorldExtends checkpoint.world (store.map Core.Value.type))
    (slots : Registry artifact (store.map Core.Value.type))
    (encoded : SourceCoreCompatibleValues.Extended checkpoint.values.registry Core.Value),
    Core.LanguageResult.decode? native = some (.succeeded payload) ∧
    decodeRaw checkpoint.origin.authority generation checkpoint.values boundaryFuel
      (checkpoint.registry.weaken extension) checkpoint.request.result payload = .ok (completion.value, slots) ∧
    encodeRaw checkpoint.origin.authority slots boundaryFuel checkpoint.values.registry
      checkpoint.request.result completion.value = .ok encoded ∧
    encoded.value = payload ∧
    completion.sourceType = checkpoint.request.result ∧ completion.boundaryFuel = boundaryFuel ∧
    completion.session.store = store ∧ completion.session.world = store.map Core.Value.type ∧
    completion.session.authority = checkpoint.origin.authority ∧
    completion.session.sourcePrefix = checkpoint.origin.sourcePrefix ∧
    completion.session.values = checkpoint.values ∧ HEq completion.session.owner checkpoint.owner ∧
    HEq completion.session.registry slots ∧ completion.origin = checkpoint.origin ∧
    completion.session.Authenticates boundaryFuel checkpoint.request.result completion.value

/-- Invert success of the original pure completion, rather than assuming
native completion suffices for the public export boundary. -/
theorem Checkpoint.complete_succeeded_receipt {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat}
    {generation : ExportGeneration} {native : Core.Value} {store : Core.Store}
    {completion : Completion artifact}
    (completed : checkpoint.NativeDone fuel native store)
    (succeeded : complete checkpoint generation fuel boundaryFuel native store completed = .succeeded completion) :
    checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion := by
  have authenticated := completion.authenticated
  unfold complete at succeeded
  dsimp only at succeeded
  split at succeeded
  next decoded =>
    obtain ⟨_world, _stored, typed⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed completed
    obtain ⟨_outcome, found, _typed⟩ := Core.LanguageResult.decode?_runtime_typed typed
    rw [decoded] at found
    cases found
  next outcome decoded =>
    cases outcome with
    | failed reason => cases succeeded
    | succeeded payload =>
      dsimp only at succeeded
      split at succeeded
      · cases succeeded
      · rename_i exported exportedEq
        have exportedReceipt := exportValue_success_receipt exportedEq
        cases succeeded
        refine ⟨completed, payload, ?_, exported.slots, exported.encoded, decoded,
          exportedReceipt.1, exportedReceipt.2.1, exportedReceipt.2.2,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl, HEq.rfl, HEq.rfl, rfl, ?_⟩
        · obtain ⟨_, _, path⟩ := Core.runStateful_sound completed
          obtain ⟨future, growth, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
          simpa only [typed.world_eq, Core.State.final, Core.State.store] using growth
        · exact authenticated

/-- A returned success receipt derives the original done/store observation
and public export association without running the native machine again. -/
theorem Checkpoint.ResumeAt.succeeded_receipt {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {completion : Completion artifact}
    (receipt : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ generation native store,
      checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion := by
  rcases receipt with ⟨generation, native, store, completed, succeeded⟩ | ⟨state, exhausted, impossible⟩
  · exact ⟨generation, native, store, checkpoint.complete_succeeded_receipt completed succeeded⟩
  · cases impossible

/-- Successful export's native world/store observation is proof-only. -/
theorem Checkpoint.SucceededResultAt.native_at {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion) :
    checkpoint.NativeDone fuel native store ∧ completion.session.NativeAt (store.map Core.Value.type) store := by
  obtain ⟨completed, payload, extension, slots, encoded, decoded, decode, encode, recovered,
    sourceType, boundary, stored, world, authority, sourcePrefixEq, values, owner, registry, origin, authenticated⟩ := receipt
  exact ⟨completed, world, stored⟩


/-- Proof-only observation of the original requested Source result type. -/
def Checkpoint.ResultTypeAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (expected : TypeSystem.Ty) : Prop := checkpoint.request.result = expected

/-- Proof-only observation of the original requested native payload type. -/
def Checkpoint.PayloadTypeAt {artifact : Artifact} (checkpoint : Checkpoint artifact)
    (expected : Core.Ty) : Prop := checkpoint.request.type = expected

/-- The retained first-selected root and exact Recipe identify both original
request types, without exposing the opaque request operationally. -/
theorem Checkpoint.RootStart.request_types_at {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments boundaryFuel)
    {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) {root : Root recipe.compiled}
    (selected : recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root) :
    checkpoint.ResultTypeAt root.result ∧ checkpoint.PayloadTypeAt root.type := by
  change artifact.recipe = recipe at atRecipe
  subst recipe
  obtain ⟨actual, found, sameKey, length, encoded, accepted, origin, request, world,
    initial, registry, values⟩ := receipt
  have same : actual = root := by
    rw [selected] at found
    exact Option.some.inj found.symm
  subst actual
  change checkpoint.request.result = root.result ∧ checkpoint.request.type = root.type
  rw [request]
  exact ⟨rfl, rfl⟩

theorem Checkpoint.RootStart.result_type_at {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments boundaryFuel)
    {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) {root : Root recipe.compiled}
    (selected : recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root) :
    checkpoint.ResultTypeAt root.result := (receipt.request_types_at atRecipe selected).1

theorem Checkpoint.RootStart.payload_type_at {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {boundaryFuel : Nat} {checkpoint : Checkpoint artifact}
    (receipt : checkpoint.RootStart session key arguments boundaryFuel)
    {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe) {root : Root recipe.compiled}
    (selected : recipe.roots.find? (fun candidate => decide (candidate.key = key)) = some root) :
    checkpoint.PayloadTypeAt root.type := (receipt.request_types_at atRecipe selected).2

/-- Returned public type alignment follows the same successful export. -/
theorem Checkpoint.SucceededResultAt.source_type {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact} {expected : TypeSystem.Ty}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt expected) : completion.sourceType = expected := by
  obtain ⟨completed, payload, extension, slots, encoded, decoded, decode, encode, recovered,
    sourceType, rest⟩ := receipt
  exact sourceType.trans requested


/-- Word export succeeds at a genuinely positive boundary budget. The
original decoder and encoder retain exactly the supplied callable slots. -/
theorem exportValue_word_success {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {generation : ExportGeneration} {fuel : Nat}
    {values : Values} {slots : Registry artifact world} {expected : TypeSystem.Ty}
    (positive : 0 < fuel) (wordResult : expected = .word) (value : Core.Word) :
    ∃ exported : Exported (artifact := artifact) world authority fuel values expected (.word value),
      exportValue authority generation fuel values slots expected (.word value) = .ok exported ∧
      exported.value = .word value := by
  subst expected
  cases fuel with
  | zero => omega
  | succ rest =>
    let exported : Exported (artifact := artifact) world authority (rest + 1) values .word (.word value) :=
      ⟨.word value, slots, .pure values.registry (.word value), by
        simp [encodeRaw, TypeSystem.Ty.word, SourceCoreRawMetadata.runtimeType], rfl⟩
    refine ⟨exported, ?_, rfl⟩
    simp [exportValue, decodeRaw, encodeRaw, TypeSystem.Ty.word,
      SourceCoreRawMetadata.runtimeType, exported, pure, Except.pure,
      SourceCoreCompatibleValues.Extended.pure, bind, Except.bind]

/-- An actual native Word completion and actual requested Word type close
this finite export branch; generic native completion is not enough. -/
theorem Checkpoint.native_word_succeeded_receipt {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {value : Core.Word} {store : Core.Store}
    (completed : checkpoint.NativeDone fuel (.inRight .word (.word value)) store)
    (requested : checkpoint.ResultTypeAt .word) (positive : 0 < boundaryFuel) :
    ∃ completion : Completion artifact,
      complete checkpoint generation fuel boundaryFuel (.inRight .word (.word value)) store completed =
        .succeeded completion ∧
      checkpoint.SucceededResultAt fuel boundaryFuel generation (.inRight .word (.word value)) store completion ∧
      completion.value = .word value := by
  change Core.runStateful fuel checkpoint.state = .done (.inRight .word (.word value)) store at completed
  have extension : Core.WorldExtends checkpoint.world (store.map Core.Value.type) := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound completed
    obtain ⟨future, growth, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using growth
  let registry := checkpoint.registry.weaken extension
  obtain ⟨exported, exportedEq, publicEq⟩ := exportValue_word_success
    (authority := checkpoint.origin.authority) (generation := generation)
    (values := checkpoint.values) (slots := registry) positive requested value
  have actual : ∃ completion : Completion artifact,
      complete checkpoint generation fuel boundaryFuel (.inRight .word (.word value)) store completed =
        .succeeded completion ∧ completion.value = .word value := by
    unfold complete
    simp only [Core.LanguageResult.decode?]
    rw [exportedEq]
    exact ⟨_, rfl, publicEq⟩
  obtain ⟨completion, succeeded, publicEq⟩ := actual
  exact ⟨completion, succeeded, checkpoint.complete_succeeded_receipt completed succeeded, publicEq⟩


/-- The successful branch carries both the actual native completion and its
full public export receipt, with the original minted generation retained. -/
theorem Checkpoint.ResumeAt.succeeded {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {completion : Completion artifact}
    (receipt : checkpoint.ResumeAt fuel boundaryFuel (.succeeded completion)) :
    ∃ generation native store, checkpoint.NativeDone fuel native store ∧
      checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion := by
  obtain ⟨generation, native, store, succeeded⟩ := receipt.succeeded_receipt
  exact ⟨generation, native, store, succeeded.1, succeeded⟩

/-- The original failed branch keeps its actual native reason and returned
session; it does not claim an independent Source fault observation. -/
theorem Checkpoint.ResumeAt.failed {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {reason : Core.Word} {returned : Session artifact}
    (receipt : checkpoint.ResumeAt fuel boundaryFuel (.failed reason returned)) :
    ∃ (_generation : ExportGeneration) (native : Core.Value) (store : Core.Store), checkpoint.NativeDone fuel native store ∧
      checkpoint.FailedResultAt fuel native store reason returned := by
  rcases receipt with ⟨generation, native, store, completed, failed⟩ | ⟨state, exhausted, impossible⟩
  · exact ⟨generation, native, store, completed, checkpoint.complete_failed_receipt completed failed⟩
  · cases impossible

/-- A retained resume action whose same native execution returns a Word
successfully exports that Word at the actual positive boundary budget. -/
theorem Checkpoint.ResumeAt.word_succeeded {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {outcome : Outcome artifact}
    {value : Core.Word} {store : Core.Store}
    (receipt : checkpoint.ResumeAt fuel boundaryFuel outcome)
    (completed : checkpoint.NativeDone fuel (.inRight .word (.word value)) store)
    (requested : checkpoint.ResultTypeAt .word) (positive : 0 < boundaryFuel) :
    ∃ completion : Completion artifact, outcome = .succeeded completion ∧
      completion.value = .word value := by
  change Core.runStateful fuel checkpoint.state = .done (.inRight .word (.word value)) store at completed
  rcases receipt with ⟨generation, native, actualStore, executed, same⟩ | ⟨state, exhausted, suspended⟩
  · rw [completed] at executed
    cases executed
    obtain ⟨completion, succeeded, exported, publicValue⟩ :=
      checkpoint.native_word_succeeded_receipt completed requested positive (generation := generation)
    exact ⟨completion, same.symm.trans succeeded, publicValue⟩
  · rw [completed] at exhausted
    cases exhausted

/-- An actual successful Word completion keeps the original decoded public
Word, without exposing or executing the private decoder again. -/
theorem Checkpoint.SucceededResultAt.word_value {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {value : Core.Word} {store : Core.Store} {completion : Completion artifact}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation
      (.inRight .word (.word value)) store completion)
    (requested : checkpoint.ResultTypeAt .word) : completion.value = .word value := by
  obtain ⟨completed, payload, extension, slots, encoded, decoded, decode, rest⟩ := receipt
  simp only [Core.LanguageResult.decode?, Option.some.injEq, Core.LanguageResult.Outcome.succeeded.injEq] at decoded
  cases decoded
  change checkpoint.request.result = .word at requested
  rw [requested] at decode
  cases boundaryFuel with
  | zero => simp [decodeRaw] at decode
  | succ budget =>
    simp [decodeRaw, TypeSystem.Ty.word, SourceCoreRawMetadata.runtimeType,
      pure, Except.pure] at decode
    exact decode.1.symm

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

/-- Issuance changes physical handle slots only. Native memory, authority,
metadata and the inert source prefix retain their actual values. -/
structure Session.SameRuntime {artifact : Artifact} (before after : Session artifact) : Prop where
  authority : before.authority = after.authority
  world : before.world = after.world
  store : before.store = after.store
  metadata : before.values = after.values
  sourcePrefix : before.sourcePrefix = after.sourcePrefix

theorem Session.SameRuntime.refl {artifact : Artifact} (session : Session artifact) :
    session.SameRuntime session := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem Session.SameRuntime.trans {artifact : Artifact} {first second third : Session artifact}
    (left : first.SameRuntime second) (right : second.SameRuntime third) : first.SameRuntime third :=
  ⟨left.authority.trans right.authority, left.world.trans right.world, left.store.trans right.store,
    left.metadata.trans right.metadata, left.sourcePrefix.trans right.sourcePrefix⟩

theorem Session.SameRuntime.native_at {artifact : Artifact} {before after : Session artifact}
    (same : before.SameRuntime after) {world : Core.StoreTyping} {store : Core.Store}
    (initial : before.NativeAt world store) : after.NativeAt world store :=
  ⟨same.world.symm.trans initial.1, same.store.symm.trans initial.2⟩

theorem Session.SameRuntime.registry_at {artifact : Artifact} {before after : Session artifact}
    (same : before.SameRuntime after) {registry : SourceCoreRawMetadata.Registry}
    (initial : before.RegistryAt registry) : after.RegistryAt registry := by
  change after.values.registry = registry
  rw [← same.metadata]
  exact initial

/-- Exact accepted input bytes, retaining the real encoder and session slots. -/
def Session.EncodesAt {artifact : Artifact} (session : Session artifact) (fuel : Nat)
    (expected : Ty) (value : Value) (native : Core.Value) : Prop :=
  ∃ encoded, encodeRaw session.authority session.registry fuel session.values.registry expected value = .ok encoded ∧
    encoded.value = native

/-- Static provenance remains the selected cached named factory. -/
def Recipe.NamedCallableAt (recipe : Recipe) (key : Key) (expected : Ty) (native : Core.Value) : Prop :=
  ∃ row, recipe.named.find? (fun row => decide (row.1 = key)) = some row ∧
    row.2.sourceType = expected ∧ row.2.value = native

/-- Static provenance remains the selected cached builtin factory. -/
def Recipe.BuiltinCallableAt (recipe : Recipe) (function : BuiltinFunctionId)
    (expected : Ty) (native : Core.Value) : Prop :=
  ∃ row, recipe.builtins.find? (fun row => decide (row.1 = function)) = some row ∧
    row.2.sourceType = expected ∧ row.2.value = native

private theorem issue_callable_receipt {artifact : Artifact} {session : Session artifact}
    {factory : CallableFactory artifact.recipe.compiled} {generation : ExportGeneration}
    {fuel : Nat} {completion : Completion artifact}
    (issued : issueCallable session factory generation fuel = .ok completion) :
    session.SameRuntime completion.session ∧ completion.sourceType = factory.sourceType ∧
      completion.boundaryFuel = fuel ∧
      completion.session.EncodesAt fuel factory.sourceType completion.value factory.value := by
  unfold issueCallable at issued
  obtain ⟨_globals, _checked, issued⟩ := root_factory_bind_ok issued
  cases slot : factory.slot with
  | none =>
      simp only [slot] at issued
      obtain ⟨validated, _validated, issued⟩ := root_factory_bind_ok issued
      obtain ⟨exported, _exported, issued⟩ := root_factory_bind_ok issued
      cases issued
      exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
        exported.encoded, exported.reencoded, exported.recovered⟩
  | some pair =>
      rcases pair with ⟨location, expected⟩
      simp only [slot] at issued
      split at issued
      ·
        obtain ⟨validated, _validated, issued⟩ := root_factory_bind_ok issued
        obtain ⟨exported, _exported, issued⟩ := root_factory_bind_ok issued
        cases issued
        exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl,
          exported.encoded, exported.reencoded, exported.recovered⟩
      · simp [bind, Except.bind, throw, throwThe] at issued

theorem Session.NamedIssuedAt.receipt {artifact : Artifact} {session : Session artifact}
    {key : Key} {fuel : Nat} {completion : Completion artifact}
    (issued : session.NamedIssuedAt key fuel completion) :
    ∃ expected native, session.SameRuntime completion.session ∧
      completion.sourceType = expected ∧ completion.boundaryFuel = fuel ∧
      completion.session.EncodesAt fuel expected completion.value native ∧
      artifact.recipe.NamedCallableAt key expected native := by
  obtain ⟨row, generation, selected, accepted⟩ := issued
  obtain ⟨same, sourceType, boundaryFuel, encoded⟩ := issue_callable_receipt accepted
  exact ⟨row.2.sourceType, row.2.value, same, sourceType, boundaryFuel, encoded,
    row, selected, rfl, rfl⟩

theorem Session.BuiltinIssuedAt.receipt {artifact : Artifact} {session : Session artifact}
    {function : BuiltinFunctionId} {fuel : Nat} {completion : Completion artifact}
    (issued : session.BuiltinIssuedAt function fuel completion) :
    ∃ expected native, session.SameRuntime completion.session ∧
      completion.sourceType = expected ∧ completion.boundaryFuel = fuel ∧
      completion.session.EncodesAt fuel expected completion.value native ∧
      artifact.recipe.BuiltinCallableAt function expected native := by
  obtain ⟨row, generation, selected, accepted⟩ := issued
  obtain ⟨same, sourceType, boundaryFuel, encoded⟩ := issue_callable_receipt accepted
  exact ⟨row.2.sourceType, row.2.value, same, sourceType, boundaryFuel, encoded,
    row, selected, rfl, rfl⟩

theorem Session.NamedIssuedAt.same_runtime {artifact : Artifact} {session : Session artifact}
    {key : Key} {fuel : Nat} {completion : Completion artifact}
    (issued : session.NamedIssuedAt key fuel completion) : session.SameRuntime completion.session := by
  obtain ⟨_, _, same, _⟩ := issued.receipt
  exact same

theorem Session.BuiltinIssuedAt.same_runtime {artifact : Artifact} {session : Session artifact}
    {function : BuiltinFunctionId} {fuel : Nat} {completion : Completion artifact}
    (issued : session.BuiltinIssuedAt function fuel completion) : session.SameRuntime completion.session := by
  obtain ⟨_, _, same, _⟩ := issued.receipt
  exact same

private theorem resolved_slot {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world}
    {expected : Ty} {handle : Handle} {native : Core.Value}
    (accepted : resolve authority slots expected handle = .ok native) :
    ∃ slot, slots.find? (fun slot => decide (slot.handle = handle)) = some slot ∧ slot.value = native := by
  by_cases belongsArtifact : handle.belongsToArtifact artifact.authority = true
  · by_cases belongsSession : handle.belongsToSession authority = true
    · cases found : slots.find? (fun slot => decide (slot.handle = handle)) with
      | none => simp [resolve, belongsArtifact, belongsSession, found, bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted
      | some slot =>
          by_cases sameType : SourceCoreRawMetadata.runtimeType expected =
              SourceCoreRawMetadata.runtimeType handle.sourceType
          · refine ⟨slot, rfl, ?_⟩
            simpa [resolve, belongsArtifact, belongsSession, found, sameType, bind, Except.bind, pure, Except.pure, throw, throwThe] using accepted
          · simp [resolve, belongsArtifact, belongsSession, found, sameType, bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted
    · simp [resolve, belongsArtifact, belongsSession, bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted
  · simp [resolve, belongsArtifact, bind, Except.bind, pure, Except.pure, throw, throwThe] at accepted

private theorem resolve_unique {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world}
    {firstType secondType : Ty} {handle : Handle} {first second : Core.Value}
    (left : resolve authority slots firstType handle = .ok first)
    (right : resolve authority slots secondType handle = .ok second) : first = second := by
  obtain ⟨a, foundA, valueA⟩ := resolved_slot left
  obtain ⟨b, foundB, valueB⟩ := resolved_slot right
  have same := Option.some.inj (foundA.symm.trans foundB)
  subst b
  exact valueA.symm.trans valueB

private theorem encoded_function_resolves {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {expected : Ty} {handle : Handle}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : encodeRaw authority slots fuel registry expected (.function handle) = .ok encoded) :
    resolve authority slots expected handle = .ok encoded.value := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin => cases builtin <;> cases accepted
      case function parameter result =>
        obtain ⟨native, resolved, accepted⟩ := root_factory_bind_ok accepted
        cases accepted
        exact resolved

private theorem arguments_function_at {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {values : Values} {owner : values.checked = artifact.recipe.compiled.compatible.checked}
    {sourceTypes : List Ty} {types : List Core.Ty} {arguments : List Value}
    {encoded : Arguments artifact world types} {index : Nat} {handle : Handle}
    {expected : Ty} {native : Core.Value}
    (resolved : resolve authority slots expected handle = .ok native)
    (found : arguments[index]? = some (.function handle))
    (accepted : encodeArguments authority slots fuel values owner sourceTypes types arguments = .ok encoded) :
    encoded.native[index]? = some native := by
  induction sourceTypes generalizing types arguments values encoded index with
  | nil =>
      cases types <;> cases arguments <;> try (solve | cases accepted)
      cases found
  | cons sourceType rest ih =>
      cases types with
      | nil => cases accepted
      | cons type types =>
          cases arguments with
          | nil => cases found
          | cons argument arguments =>
              simp only [encodeArguments] at accepted
              cases projected : artifact.recipe.compiled.compatible.checked.catalog.project sourceType with
              | error error => simp [projected, bind, Except.bind, throw, throwThe] at accepted
              | ok actual =>
                  simp only [projected, bind, Except.bind] at accepted
                  split at accepted
                  · rename_i same
                    subst actual
                    obtain ⟨raw, rawEq, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨validated, _validated, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨tail, tailEq, accepted⟩ := root_factory_bind_ok accepted
                    cases accepted
                    cases index with
                    | zero =>
                        have sameArgument : argument = .function handle := Option.some.inj found
                        subst argument
                        have sameNative := resolve_unique resolved (encoded_function_resolves rawEq)
                        simpa only [List.getElem?_cons_zero] using congrArg some sameNative.symm
                    | succ index =>
                        exact ih (types := types) (arguments := arguments) (encoded := tail)
                          (index := index) (by simpa using found) tailEq
                  · simp [throw, throwThe] at accepted

/-- The actual start used the same authenticated handle and therefore the
same native callable bytes issued earlier. This says nothing about source
meaning until the cached factory's provenance has been interpreted. -/
def Checkpoint.ImportedFunctionAt {artifact : Artifact} (session : Session artifact)
    (key : Key) (index : Nat) (nativeValue : Core.Value) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ (root : Root artifact.recipe.compiled) (native : Core.Environment),
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    native[index]? = some nativeValue ∧
    checkpoint.state = .initial root.body (native.reverse ++ environment artifact) session.store

theorem Checkpoint.RootStart.imported_function {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (started : checkpoint.RootStart session key arguments fuel)
    {issuanceFuel : Nat} {expected : Ty} {handle : Handle} {native : Core.Value}
    (imported : session.EncodesAt issuanceFuel expected (.function handle) native)
    {index : Nat} (found : arguments[index]? = some (.function handle)) :
    checkpoint.ImportedFunctionAt session key index native := by
  obtain ⟨issued, issuedEq, recovered⟩ := imported
  have resolved := encoded_function_resolves issuedEq
  rw [recovered] at resolved
  obtain ⟨root, selected, _, _, encoded, accepted, _, _, _, initial, _, _⟩ := started
  exact ⟨root, encoded.native, selected, arguments_function_at resolved found accepted, initial⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem builtin_factory_descriptor {compiled : SourceCoreUnifiedCompilation.Compiled}
    {origin : SourceCoreStageCodebook.Origin} {id : Core.Word}
    (accepted : callableDescriptor compiled origin = .ok id) :
    ∃ descriptor : SourceCoreCallableContracts.Descriptor
      compiled.indexed.ancestry.graph.inputs.callable.table origin, descriptor.id = id := by
  unfold callableDescriptor at accepted
  rw [compiled.indexed.ancestry.graph.inputs.callableSelected] at accepted
  simp only [bind, Except.bind, pure, Except.pure] at accepted
  cases found : compiled.indexed.ancestry.graph.inputs.callable.table.idAt? origin with
  | none => simp [found, throw, throwThe] at accepted
  | some actual =>
      simp only [found] at accepted
      cases entry : compiled.indexed.ancestry.graph.inputs.callable.table.entryAt? actual with
      | none => simp [entry, throw, throwThe] at accepted
      | some entryValue =>
          simp only [entry] at accepted
          split at accepted
          · have same : actual = id := Except.ok.inj accepted
            subst id
            cases issued : SourceCoreCallableContracts.descriptor
                compiled.indexed.ancestry.graph.inputs.callable.table origin with
            | error error =>
                unfold SourceCoreCallableContracts.descriptor at issued
                split at issued
                · rename_i absent
                  rw [found] at absent
                  contradiction
                · cases issued
            | ok descriptor =>
                refine ⟨descriptor, ?_⟩
                unfold SourceCoreCallableContracts.descriptor at issued
                split at issued
                · cases issued
                · rename_i identifier selected
                  have same : identifier = actual := Option.some.inj (selected.symm.trans found)
                  cases issued
                  exact same
          · cases accepted

private theorem builtin_factory_shape {compiled : SourceCoreUnifiedCompilation.Compiled}
    {builtins : List (BuiltinFunctionId × CallableFactory compiled)}
    (prepared : prepareBuiltins compiled = .ok builtins)
    {function : BuiltinFunctionId} {row : BuiltinFunctionId × CallableFactory compiled}
    (selected : builtins.find? (fun row => decide (row.1 = function)) = some row) :
    row.2.sourceType = function.type ∧
      ∃ (index : Nat) (identity : Core.Word) (descriptor : SourceCoreCallableContracts.Descriptor
        compiled.indexed.ancestry.graph.inputs.callable.table (.builtin function)),
        BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index) ∧
        Core.Word.ofNat? (compiled.indexed.base.globals.length + index + 1) = some identity ∧
        row.2.value = .pair (.pair (.inRight .unit (.word identity))
          (.closure (SourceCoreInteger.builtinParameter function)
            (Core.LanguageResult.resultType (SourceCoreInteger.builtinResult function))
            (Core.LanguageResult.success (SourceCoreInteger.builtinBody function)) [])) (.word descriptor.id) := by
  have rowFunction : row.1 = function := by simpa using List.find?_some selected
  obtain ⟨⟨actual, index⟩, member, produced⟩ :=
    root_factory_mapM_member prepared (List.mem_of_find?_eq_some selected)
  simp only [SourceCoreInteger.builtinClosure] at produced
  obtain ⟨identity, number, produced⟩ := root_factory_bind_ok produced
  obtain ⟨id, descriptor, produced⟩ := root_factory_bind_ok produced
  obtain ⟨factory, callable, produced⟩ := root_factory_bind_ok produced
  cases produced
  change actual = function at rowFunction
  subst actual
  have inventory : BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) =
      some (function, index) := by
    cases function <;> simp_all [BuiltinFunctionId.all, List.zipIdx]
  have identityFound : Core.Word.ofNat? (compiled.indexed.base.globals.length + index + 1) = some identity := by
    unfold callableIdentity at number
    split at number
    · cases number; assumption
    · contradiction
  obtain ⟨descriptor, identifier⟩ := builtin_factory_descriptor descriptor
  unfold prepareCallable at callable
  split at callable
  · contradiction
  · dsimp only at callable
    split at callable
    · cases callable
      exact ⟨rfl, index, identity, descriptor, inventory, identityFound, by rw [identifier]⟩
    · contradiction

/-- The accepted recipe fixes the actual closed builtin code, raw source type,
nonwrapping identity and descriptor in its cached callable factory. -/
theorem Recipe.BuiltinCallableAt.prepared
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {function : BuiltinFunctionId} {expected : Ty} {native : Core.Value}
    (factory : recipe.BuiltinCallableAt function expected native) :
    expected = function.type ∧
      ∃ (index : Nat) (identity : Core.Word) (descriptor : SourceCoreCallableContracts.Descriptor
        compiled.indexed.ancestry.graph.inputs.callable.table (.builtin function)),
        BuiltinFunctionId.all.zipIdx.find? (fun item => decide (item.1 = function)) = some (function, index) ∧
        Core.Word.ofNat? (compiled.indexed.base.globals.length + index + 1) = some identity ∧
        native = .pair (.pair (.inRight .unit (.word identity))
          (.closure (SourceCoreInteger.builtinParameter function)
            (Core.LanguageResult.resultType (SourceCoreInteger.builtinResult function))
            (Core.LanguageResult.success (SourceCoreInteger.builtinBody function)) [])) (.word descriptor.id) := by
  unfold Recipe.prepare at prepared
  obtain ⟨roots, _roots, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨templates, _templates, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨named, _named, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨builtins, builtinsPrepared, prepared⟩ := root_factory_bind_ok prepared
  dsimp only at prepared
  split at prepared
  · cases prepared
    obtain ⟨row, selected, sourceType, nativeValue⟩ := factory
    obtain ⟨actualType, shape⟩ := builtin_factory_shape builtinsPrepared selected
    exact ⟨sourceType.symm.trans actualType, nativeValue ▸ shape⟩
  · contradiction

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem named_factory_shape {compiled : SourceCoreUnifiedCompilation.Compiled}
    {templates : SourceCoreCallableIndexedTemplates.Cache compiled.indexed}
    {named : List (Key × CallableFactory compiled)}
    (prepared : prepareNamed compiled templates = .ok named)
    {key : Key} {row : Key × CallableFactory compiled}
    (selected : named.find? (fun row => decide (row.1 = key)) = some row) :
    ∃ (signature : SourceCoreCalls.Signature) (index : Nat)
      (specialized : SourceSpecialization.SpecializedFunction)
      (location : Nat) (closure : Core.Value) (identity : Core.Word)
      (descriptor : SourceCoreCallableContracts.Descriptor
        compiled.indexed.ancestry.graph.inputs.callable.table (.named key)),
      compiled.indexed.base.globals[index]? = some signature ∧ signature.key = key ∧
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key = .ok specialized ∧
      row.2.sourceType = specialized.function.type ∧
      templates.nativeGlobals[index]? = some (location, .inRight .unit closure) ∧
      Core.Word.ofNat? (index + 1) = some identity ∧
      row.2.value = .pair (.pair (.inRight .unit (.word identity)) closure) (.word descriptor.id) ∧
      compiled.compatible.checked.catalog.project row.2.sourceType = .ok row.2.value.type := by
  have rowKey : row.1 = key := by simpa using List.find?_some selected
  obtain ⟨⟨signature, index⟩, member, produced⟩ :=
    root_factory_mapM_member prepared (List.mem_of_find?_eq_some selected)
  obtain ⟨specialized, specializedAt, produced⟩ := root_factory_bind_ok produced
  have exactSpecialized : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan signature.key =
      .ok specialized := by
    cases actual : SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan signature.key with
    | error error => simp [actual, Except.mapError] at specializedAt
    | ok actualSpecialized =>
        have same : actualSpecialized = specialized := by simpa [actual, Except.mapError] using specializedAt
        exact same ▸ rfl
  cases slot : templates.nativeGlobals[index]? with
  | none => simp [slot, throw, throwThe, bind, Except.bind] at produced
  | some pair =>
      rcases pair with ⟨location, installed⟩
      simp only [slot, bind, Except.bind, pure, Except.pure] at produced
      split at produced
      · rename_i closure
        obtain ⟨identity, number, produced⟩ := root_factory_bind_ok produced
        obtain ⟨id, descriptorAt, produced⟩ := root_factory_bind_ok produced
        obtain ⟨factory, callable, produced⟩ := root_factory_bind_ok produced
        cases produced
        change signature.key = key at rowKey
        subst key
        have globalAt : compiled.indexed.base.globals[index]? = some signature :=
          List.mk_mem_zipIdx_iff_getElem?.mp member
        have identityFound : Core.Word.ofNat? (index + 1) = some identity := by
          unfold callableIdentity at number
          split at number
          · cases number; assumption
          · contradiction
        obtain ⟨descriptor, identifier⟩ := builtin_factory_descriptor descriptorAt
        unfold prepareCallable at callable
        split at callable
        · contradiction
        · rename_i projectedType projection
          dsimp only at callable
          split at callable
          · rename_i actualType
            cases callable
            refine ⟨signature, index, specialized, location, closure, identity, descriptor,
              globalAt, rfl, exactSpecialized, rfl, ?_, identityFound, ?_, ?_⟩
            · exact slot
            · rw [identifier]
            · simpa only [actualType] using projection
          · contradiction
      · contradiction

/-- A named handle's cached factory retains the exact original global slot,
accepted specialization, installed native value, identity and descriptor. -/
theorem Recipe.NamedCallableAt.prepared
    {compiled : SourceCoreUnifiedCompilation.Compiled} {recipe : Recipe}
    (prepared : Recipe.prepare compiled = .ok recipe)
    {key : Key} {expected : Ty} {native : Core.Value}
    (factory : recipe.NamedCallableAt key expected native) :
    ∃ (signature : SourceCoreCalls.Signature) (index : Nat)
      (specialized : SourceSpecialization.SpecializedFunction)
      (location : Nat) (closure : Core.Value) (identity : Core.Word)
      (descriptor : SourceCoreCallableContracts.Descriptor
        compiled.indexed.ancestry.graph.inputs.callable.table (.named key)),
      compiled.indexed.base.globals[index]? = some signature ∧ signature.key = key ∧
      SourceCompilationPlan.exactSpecialization compiled.indexed.base.plan key = .ok specialized ∧
      expected = specialized.function.type ∧
      recipe.templates.nativeGlobals[index]? = some (location, .inRight .unit closure) ∧
      Core.Word.ofNat? (index + 1) = some identity ∧
      native = .pair (.pair (.inRight .unit (.word identity)) closure) (.word descriptor.id) ∧
      compiled.compatible.checked.catalog.project expected = .ok native.type := by
  unfold Recipe.prepare at prepared
  obtain ⟨roots, _roots, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨templates, _templates, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨named, namedPrepared, prepared⟩ := root_factory_bind_ok prepared
  obtain ⟨builtins, _builtins, prepared⟩ := root_factory_bind_ok prepared
  dsimp only at prepared
  split at prepared
  · cases prepared
    obtain ⟨row, selected, sourceType, nativeValue⟩ := factory
    obtain ⟨signature, index, specialized, location, closure, identity, descriptor,
      globalAt, keyAt, specializedAt, actualType, slot, number, shape, projection⟩ := named_factory_shape namedPrepared selected
    exact ⟨signature, index, specialized, location, closure, identity, descriptor,
      globalAt, keyAt, specializedAt, sourceType.symm.trans actualType, slot, number, nativeValue.symm.trans shape,
      by simpa only [sourceType, nativeValue] using projection⟩
  · contradiction

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem named_factory_mapM_at {α β ε : Type} {action : α → Except ε β}
    {inputs : List α} {outputs : List β} {index : Nat} {output : β}
    (accepted : inputs.mapM action = .ok outputs) (found : outputs[index]? = some output) :
    ∃ input, inputs[index]? = some input ∧ action input = .ok output := by
  induction inputs generalizing outputs index with
  | nil =>
      simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
      subst outputs
      simp at found
  | cons first rest ih =>
      rw [List.mapM_cons] at accepted
      obtain ⟨head, headEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨tail, tailEq, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      cases index with
      | zero =>
          have same : head = output := Option.some.inj found
          exact ⟨first, rfl, same ▸ headEq⟩
      | succ index =>
          obtain ⟨input, selected, actual⟩ := ih tailEq found
          exact ⟨input, selected, actual⟩

/-- The original indexed slot generator fixes every physical location. Its
output position is retained through mapM, rather than inferred from a native
type or from membership at an unspecified position. -/
theorem Recipe.native_global_location (recipe : Recipe)
    {index location : Nat} {value : Core.Value}
    (slot : recipe.templates.nativeGlobals[index]? = some (location, value)) :
    location = 1 + recipe.compiled.indexed.base.globals.length - 1 - index := by
  have generated := recipe.templates.nativeGlobalsGenerated
  change SourceCoreCallableNativeSlots.expectedGlobals
    (recipe.compiled.indexed.base.globals.map (fun signature => (signature.parameterType, signature.resultType)))
    (recipe.compiled.indexed.secondPass.closures.zipIdx.map (fun (code, index) => SourceCoreLambdaTemplates.installedTemplate index code))
    (SourceCoreCallableIndexedTemplates.globalEnvironment recipe.compiled.indexed) 1 =
      .ok recipe.templates.nativeGlobals at generated
  unfold SourceCoreCallableNativeSlots.expectedGlobals at generated
  split at generated
  · cases generated
  · obtain ⟨⟨⟨parameter, result⟩, actualIndex⟩, atIndex, emitted⟩ := named_factory_mapM_at generated slot
    have indexEq : actualIndex = index := by
      simp only [List.getElem?_zipIdx] at atIndex
      cases selected : (recipe.compiled.indexed.base.globals.map
          (fun signature => (signature.parameterType, signature.resultType)))[index]? with
      | none => simp [selected] at atIndex
      | some actual =>
          simp only [selected, Option.map_some] at atIndex
          have same := (Prod.mk.inj (Option.some.inj atIndex)).2
          simpa only [Nat.zero_add] using same.symm
    cases found : (recipe.compiled.indexed.secondPass.closures.zipIdx.map
        (fun (code, index) => SourceCoreLambdaTemplates.installedTemplate index code))[actualIndex]? with
    | none => simp [found, bind, Except.bind, throw] at emitted
    | some code =>
        simp only [found, pure, Except.pure, bind, Except.bind] at emitted
        cases code <;> try cases emitted
        rename_i actualParameter actualResult body
        by_cases header : (actualParameter != parameter ||
            actualResult != Core.LanguageResult.resultType result) = true
        · simp [header, throw, throwThe, MonadExceptOf.throw] at emitted
        · simp [header] at emitted
          obtain ⟨locationEq, _valueEq⟩ := emitted
          simp only [indexEq] at locationEq
          omega

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem issuance_encoded_function_view {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {expected : Ty} {handle : Handle}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : encodeRaw authority slots fuel registry expected (.function handle) = .ok encoded) :
    ∃ parameter result, SourceCoreRawMetadata.runtimeType expected = .function parameter result := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      all_goals try (solve | cases accepted)
      case constructor constructor =>
        cases constructor with
        | declaration => cases accepted
        | builtin builtin => cases builtin <;> cases accepted
      case function parameter result => exact ⟨parameter, result, rfl⟩

private theorem issuance_register_append {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {generation : ExportGeneration}
    {slots returned : Registry artifact world} {expected : Ty} {value : Core.Value} {handle : Handle}
    (accepted : register authority generation slots expected value = .ok (handle, returned)) :
    ∃ suffix, returned = slots ++ suffix := by
  unfold register at accepted
  split at accepted
  · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
  · split at accepted
    · cases accepted
    · obtain ⟨checked, _checked, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact ⟨_, rfl⟩

private theorem issuance_export_function_append {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {generation : ExportGeneration} {fuel : Nat}
    {values : Values} {slots : Registry artifact world} {expected : Ty} {core : Core.Value}
    {exported : Exported (artifact := artifact) world authority fuel values expected core}
    (accepted : exportValue authority generation fuel values slots expected core = .ok exported)
    {handle : Handle} (publicValue : exported.value = .function handle) :
    ∃ suffix, exported.slots = slots ++ suffix := by
  obtain ⟨decoded, encoded, _recovered⟩ := exportValue_success_receipt accepted
  rw [publicValue] at decoded encoded
  obtain ⟨parameter, result, view⟩ := issuance_encoded_function_view encoded
  cases fuel with
  | zero => cases decoded
  | succ fuel =>
      unfold decodeRaw at decoded
      rw [view] at decoded
      obtain ⟨⟨actualHandle, returned⟩, registered, decoded⟩ := root_factory_bind_ok decoded
      have same := Prod.mk.inj (Except.ok.inj decoded)
      have slotsEq : returned = exported.slots := same.2
      exact slotsEq ▸ issuance_register_append registered

private theorem issuance_resolve_append {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world}
    {expected : Ty} {handle : Handle} {native : Core.Value}
    (accepted : resolve authority slots expected handle = .ok native)
    (suffix : Registry artifact world) :
    resolve authority (slots ++ suffix) expected handle = .ok native := by
  obtain ⟨slot, found, _value⟩ := resolved_slot accepted
  simpa only [resolve, List.find?_append, found, Option.or] using accepted

private theorem issuance_encode_function_append {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {expected : Ty} {handle : Handle}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : encodeRaw authority slots fuel registry expected (.function handle) = .ok encoded)
    (suffix : Registry artifact world) :
    encodeRaw authority (slots ++ suffix) fuel registry expected (.function handle) = .ok encoded := by
  obtain ⟨parameter, result, view⟩ := issuance_encoded_function_view accepted
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold encodeRaw at accepted ⊢
      rw [view] at accepted ⊢
      obtain ⟨native, resolved, accepted⟩ := root_factory_bind_ok accepted
      dsimp only
      rw [issuance_resolve_append resolved suffix]
      exact accepted

private theorem issuance_callable_preserves_function
    {artifact : Artifact} {session : Session artifact}
    {factory : CallableFactory artifact.recipe.compiled} {generation : ExportGeneration}
    {fuel : Nat} {completion : Completion artifact}
    (issued : issueCallable session factory generation fuel = .ok completion)
    {issuedHandle : Handle} (publicValue : completion.value = .function issuedHandle)
    {inputFuel : Nat} {expected : Ty} {handle : Handle} {native : Core.Value}
    (imported : session.EncodesAt inputFuel expected (.function handle) native) :
    completion.session.EncodesAt inputFuel expected (.function handle) native := by
  unfold issueCallable at issued
  obtain ⟨_globals, _checked, issued⟩ := root_factory_bind_ok issued
  cases slot : factory.slot with
  | none =>
      simp only [slot] at issued
      obtain ⟨validated, _validated, issued⟩ := root_factory_bind_ok issued
      obtain ⟨exported, exportedAt, issued⟩ := root_factory_bind_ok issued
      cases issued
      obtain ⟨suffix, returned⟩ := issuance_export_function_append exportedAt publicValue
      obtain ⟨encoded, encodedAt, recovered⟩ := imported
      refine ⟨encoded, ?_, recovered⟩
      change encodeRaw session.authority exported.slots inputFuel session.values.registry expected (.function handle) = .ok encoded
      rw [returned]
      exact issuance_encode_function_append encodedAt suffix
  | some pair =>
      rcases pair with ⟨location, value⟩
      simp only [slot] at issued
      split at issued
      · obtain ⟨validated, _validated, issued⟩ := root_factory_bind_ok issued
        obtain ⟨exported, exportedAt, issued⟩ := root_factory_bind_ok issued
        cases issued
        obtain ⟨suffix, returned⟩ := issuance_export_function_append exportedAt publicValue
        obtain ⟨encoded, encodedAt, recovered⟩ := imported
        refine ⟨encoded, ?_, recovered⟩
        change encodeRaw session.authority exported.slots inputFuel session.values.registry expected (.function handle) = .ok encoded
        rw [returned]
        exact issuance_encode_function_append encodedAt suffix
      · simp [bind, Except.bind, throw, throwThe] at issued

/-- A finite sequence of actual successful named/builtin handle issuances.
Each step retains its observed handle result; no operation is replayed. -/
inductive Session.IssuanceChain {artifact : Artifact} : Session artifact → Session artifact → Prop where
  | refl (session : Session artifact) : IssuanceChain session session
  | named {first before : Session artifact} {completion : Completion artifact}
      {key : Key} {fuel : Nat} {handle : Handle}
      (prior : IssuanceChain first before)
      (issued : before.NamedIssuedAt key fuel completion)
      (publicValue : completion.value = .function handle) :
      IssuanceChain first completion.session
  | builtin {first before : Session artifact} {completion : Completion artifact}
      {function : BuiltinFunctionId} {fuel : Nat} {handle : Handle}
      (prior : IssuanceChain first before)
      (issued : before.BuiltinIssuedAt function fuel completion)
      (publicValue : completion.value = .function handle) :
      IssuanceChain first completion.session

/-- Concatenating actual issuance sequences retains all their receipts. -/
theorem Session.IssuanceChain.trans {artifact : Artifact} {first second third : Session artifact}
    (left : first.IssuanceChain second) (right : second.IssuanceChain third) :
    first.IssuanceChain third := by
  induction right with
  | refl => exact left
  | named _prior issued publicValue ih => exact .named ih issued publicValue
  | builtin _prior issued publicValue ih => exact .builtin ih issued publicValue

/-- Issuance leaves the actual native heap, metadata, authority and Source
prefix unchanged across the entire retained sequence. -/
theorem Session.IssuanceChain.same_runtime {artifact : Artifact} {before after : Session artifact}
    (chain : before.IssuanceChain after) : before.SameRuntime after := by
  induction chain with
  | refl => exact .refl _
  | named _prior issued _publicValue ih => exact ih.trans issued.same_runtime
  | builtin _prior issued _publicValue ih => exact ih.trans issued.same_runtime

/-- Every previously encoded handle still denotes the same native callable
in the last Session. Actual append-only physical registry growth proves this;
metadata equality or handle authentication alone would not suffice. -/
theorem Session.IssuanceChain.encodes_function
    {artifact : Artifact} {before after : Session artifact}
    (chain : before.IssuanceChain after)
    {fuel : Nat} {expected : Ty} {handle : Handle} {native : Core.Value}
    (imported : before.EncodesAt fuel expected (.function handle) native) :
    after.EncodesAt fuel expected (.function handle) native := by
  induction chain with
  | refl => exact imported
  | named _prior issued publicValue ih =>
      obtain ⟨_row, _generation, _selected, issued⟩ := issued
      exact issuance_callable_preserves_function issued publicValue ih
  | builtin _prior issued publicValue ih =>
      obtain ⟨_row, _generation, _selected, issued⟩ := issued
      exact issuance_callable_preserves_function issued publicValue ih

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

/-- Successful mixed argument encoding extends metadata through every original
input. A selected data argument retains its own original codec equation even
when other positions contain opaque handles. -/
private theorem arguments_data_at {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {values : Values} {owner : values.checked = artifact.recipe.compiled.compatible.checked}
    {sourceTypes : List Ty} {types : List Core.Ty} {arguments : List Value}
    {encoded : Arguments artifact world types}
    (accepted : encodeArguments authority slots fuel values owner sourceTypes types arguments = .ok encoded) :
    SourceCoreRawMetadata.Extends values.registry encoded.values.registry ∧
      ∀ {index : Nat} {expected : Ty} {value : Value},
        sourceTypes[index]? = some expected → arguments[index]? = some value → DataPublic value →
        ∃ native type, encoded.native[index]? = some native ∧ types[index]? = some type ∧
          artifact.recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
          EncodedDataInput artifact.recipe.compiled.compatible.checked encoded.values.registry expected value native := by
  induction sourceTypes generalizing types arguments values encoded with
  | nil =>
      cases types <;> cases arguments <;> try (solve | cases accepted)
      cases accepted
      refine ⟨.refl _, ?_⟩
      intro index expected value found
      simp at found
  | cons expected rest ih =>
      cases types with
      | nil => cases accepted
      | cons type types =>
          cases arguments with
          | nil => cases accepted
          | cons argument arguments =>
              simp only [encodeArguments] at accepted
              cases projected : artifact.recipe.compiled.compatible.checked.catalog.project expected with
              | error error => simp [projected, bind, Except.bind, throw, throwThe] at accepted
              | ok actual =>
                  simp only [projected, bind, Except.bind] at accepted
                  split at accepted
                  · rename_i same
                    subst actual
                    obtain ⟨raw, rawEq, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨validated, _validated, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨tail, tailEq, accepted⟩ := root_factory_bind_ok accepted
                    cases accepted
                    obtain ⟨extended, atIndex⟩ := ih tailEq
                    refine ⟨raw.preserves.trans extended, ?_⟩
                    intro index selectedType selectedValue foundType foundValue data
                    cases index with
                    | zero =>
                        have sameType := Option.some.inj foundType
                        have sameValue := Option.some.inj foundValue
                        subst selectedType
                        subst selectedValue
                        obtain ⟨carrier, image⟩ := data
                        have correspondence := (data_correspondence fuel).1 authority slots values.registry expected carrier raw
                          (by rw [← image]; exact rawEq)
                        have beforeOwner : values.registry.signatures = artifact.recipe.compiled.compatible.checked.signatures :=
                          values.registryOwner.trans (congrArg SourceCoreCompatibleCatalog.Checked.signatures owner)
                        exact ⟨raw.value, type, rfl, rfl, projected, carrier, fuel, values.registry, raw,
                          image, beforeOwner, correspondence, rfl, extended⟩
                    | succ index => exact atIndex foundType foundValue data
                  · simp [throw, throwThe] at accepted

/-- One selected data position in the actual mixed input prefix. Other inputs
need no data-carrier certificate and keep their original order and metadata. -/
def Checkpoint.DataInputAt {artifact : Artifact} (session : Session artifact)
    (key : Key) (index : Nat) (value : Value) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ (root : Root artifact.recipe.compiled) (native : Core.Environment),
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    (∀ expected, root.inputs[index]? = some expected →
      ∃ payload type, native[index]? = some payload ∧ root.types[index]? = some type ∧
        artifact.recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
        EncodedDataInput artifact.recipe.compiled.compatible.checked checkpoint.values.registry expected value payload) ∧
    checkpoint.state = .initial root.body (native.reverse ++ environment artifact) session.store

theorem Checkpoint.RootStart.data_input {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (started : checkpoint.RootStart session key arguments fuel)
    {index : Nat} {value : Value} (found : arguments[index]? = some value) (data : DataPublic value) :
    checkpoint.DataInputAt session key index value := by
  obtain ⟨root, selected, _, _, encoded, accepted, _, _, _, initial, _, sameValues⟩ := started
  obtain ⟨_extended, atIndex⟩ := arguments_data_at accepted
  refine ⟨root, encoded.native, selected, ?_, initial⟩
  intro expected foundType
  obtain ⟨payload, type, actual, typeAt, projected, encodedAt⟩ := atIndex foundType found data
  rw [← sameValues] at encodedAt
  exact ⟨payload, type, actual, typeAt, projected, encodedAt⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

/-- The original raw encoder with this session's authority and physical slots,
retaining its actual input and output metadata registries. -/
def Session.RawEncodedAt {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (registry : SourceCoreRawMetadata.Registry) (expected : Ty) (value : Value)
    (encoded : SourceCoreCompatibleValues.Extended registry Core.Value) : Prop :=
  encodeRaw session.authority session.registry fuel registry expected value = .ok encoded

/-- Original constructor-payload encoding, including singleton erasure. -/
def Session.PayloadsEncodedAt {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (registry : SourceCoreRawMetadata.Registry) (types : List Ty) (values : List Value)
    (encoded : SourceCoreCompatibleValues.Extended registry Core.Value) : Prop :=
  encodePayloads session.authority session.registry fuel registry types values = .ok encoded

/-- Original ordered mapping-row encoding. -/
def Session.EntriesEncodedAt {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (registry : SourceCoreRawMetadata.Registry) (keyType valueType : Ty)
    (layout : Core.OrderedMapping.Layout) (entries : List (Value × Value))
    (encoded : SourceCoreCompatibleValues.Extended registry Core.Value) : Prop :=
  encodeEntries session.authority session.registry fuel registry keyType valueType layout entries = .ok encoded

theorem Session.RawEncodedAt.function_eq {artifact : Artifact} {session : Session artifact}
    {fuel issuedFuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected issuedType : Ty}
    {handle : Handle} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    {native : Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected (.function handle) encoded)
    (issued : session.EncodesAt issuedFuel issuedType (.function handle) native) :
    encoded.value = native := by
  obtain ⟨original, actual, recovered⟩ := issued
  exact (resolve_unique (encoded_function_resolves accepted) (encoded_function_resolves actual)).trans recovered

theorem Session.RawEncodedAt.data {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : Ty} {value : Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected value encoded)
    (owner : registry.signatures = artifact.recipe.compiled.compatible.checked.signatures)
    (data : DataPublic value) :
    EncodedDataInput artifact.recipe.compiled.compatible.checked encoded.registry expected value encoded.value := by
  obtain ⟨carrier, image⟩ := data
  refine ⟨carrier, fuel, registry, encoded, image, owner, ?_, rfl, .refl _⟩
  exact (data_correspondence fuel).1 session.authority session.registry registry expected carrier encoded
    (by rw [← image]; exact accepted)

theorem Session.RawEncodedAt.product {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected leftType rightType : Ty}
    {left right : Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected (.product left right) encoded)
    (view : SourceCoreRawMetadata.runtimeType expected = .product leftType rightType) :
    ∃ remaining, fuel = remaining + 1 ∧
      ∃ (leftEncoded : SourceCoreCompatibleValues.Extended registry Core.Value)
        (rightEncoded : SourceCoreCompatibleValues.Extended leftEncoded.registry Core.Value),
        session.RawEncodedAt remaining registry leftType left leftEncoded ∧
        session.RawEncodedAt remaining leftEncoded.registry rightType right rightEncoded ∧
        encoded = ⟨rightEncoded.registry, leftEncoded.preserves.trans rightEncoded.preserves,
          .pair leftEncoded.value rightEncoded.value⟩ := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold RawEncodedAt encodeRaw at accepted
      rw [view] at accepted
      obtain ⟨a, aEq, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨b, bEq, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact ⟨fuel, rfl, a, b, simple_mapError_ok aEq, simple_mapError_ok bEq, rfl⟩

theorem Session.RawEncodedAt.constructed {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected : Ty}
    {instantiation : DataConstructorInstantiation} {values : List Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected (.constructed instantiation values) encoded) :
    ∃ remaining, fuel = remaining + 1 ∧
      ∃ (header : SourceCoreRawMetadata.Inserted registry expected (.constructor instantiation))
        (tag : Core.ConstructorId) (payload : SourceCoreCompatibleValues.Extended header.registry Core.Value),
        registry.intern expected (.constructor instantiation) = .ok header ∧
        artifact.recipe.compiled.compatible.checked.resolveConstructor instantiation = .ok tag ∧
        session.PayloadsEncodedAt remaining header.registry instantiation.payloadTypes values payload ∧
        encoded = ⟨payload.registry, header.preserves.trans payload.preserves,
          .constructed tag (.pair (.word header.id) payload.value)⟩ := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold RawEncodedAt at accepted
      cases view : SourceCoreRawMetadata.runtimeType expected <;>
        (unfold encodeRaw at accepted; rw [view] at accepted)
      case constructor id =>
        cases id <;> try (rename_i builtin; cases builtin)
        all_goals
          obtain ⟨header, headerAt, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨tag, tagAt, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨payload, payloadAt, accepted⟩ := root_factory_bind_ok accepted
          cases accepted
          exact ⟨fuel, rfl, header, tag, payload, simple_mapError_ok headerAt,
            simple_mapError_ok tagAt, payloadAt, rfl⟩
      all_goals
        obtain ⟨header, headerAt, accepted⟩ := root_factory_bind_ok accepted
        obtain ⟨tag, tagAt, accepted⟩ := root_factory_bind_ok accepted
        obtain ⟨payload, payloadAt, accepted⟩ := root_factory_bind_ok accepted
        cases accepted
        exact ⟨fuel, rfl, header, tag, payload, simple_mapError_ok headerAt,
          simple_mapError_ok tagAt, payloadAt, rfl⟩

theorem Session.RawEncodedAt.mapping {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected keyType valueType : Ty}
    {actualKey actualValue : Ty} {entries : List (Value × Value)}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected (.mapping actualKey actualValue entries) encoded)
    (view : SourceCoreRawMetadata.runtimeType expected = .mapping keyType valueType) :
    ∃ remaining, fuel = remaining + 1 ∧
      ∃ (header : SourceCoreRawMetadata.Inserted registry expected (.mapping actualKey actualValue))
        (layout : Core.OrderedMapping.Layout)
        (rows : SourceCoreCompatibleValues.Extended header.registry Core.Value)
        (fallback : SourceCoreCompatibleValues.Extended rows.registry Core.Value),
        registry.intern expected (.mapping actualKey actualValue) = .ok header ∧
        artifact.recipe.compiled.compatible.checked.catalog.mappingLayout keyType valueType = .ok layout ∧
        session.EntriesEncodedAt remaining header.registry actualKey actualValue layout entries rows ∧
        SourceCoreCompatibleValues.encodeDefaultRaw remaining artifact.recipe.compiled.compatible.checked
          rows.registry actualValue layout.valueType = .ok fallback ∧
        encoded = ⟨fallback.registry, header.preserves.trans (rows.preserves.trans fallback.preserves),
          .pair (.word header.id) (.pair fallback.value rows.value)⟩ := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold RawEncodedAt encodeRaw at accepted
      rw [view] at accepted
      obtain ⟨header, headerAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨layout, layoutAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨rows, rowsAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨fallback, fallbackAt, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact ⟨fuel, rfl, header, layout, rows, fallback, simple_mapError_ok headerAt,
        simple_mapError_ok layoutAt, rowsAt, simple_mapError_ok fallbackAt, rfl⟩

theorem Session.PayloadsEncodedAt.nil {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.PayloadsEncodedAt fuel registry [] [] encoded) :
    encoded = .pure registry .unit := by
  cases fuel <;> cases accepted <;> rfl

theorem Session.PayloadsEncodedAt.singleton {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {type : Ty} {value : Value}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.PayloadsEncodedAt fuel registry [type] [value] encoded) :
    ∃ remaining, fuel = remaining + 1 ∧ session.RawEncodedAt remaining registry type value encoded := by
  cases fuel with
  | zero => cases accepted
  | succ fuel => exact ⟨fuel, rfl, accepted⟩

theorem Session.PayloadsEncodedAt.cons {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {type : Ty} {types : List Ty}
    {value : Value} {values : List Value} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.PayloadsEncodedAt fuel registry (type :: types) (value :: values) encoded)
    (more : types ≠ []) :
    ∃ remaining, fuel = remaining + 1 ∧
      ∃ (head : SourceCoreCompatibleValues.Extended registry Core.Value)
        (tail : SourceCoreCompatibleValues.Extended head.registry Core.Value),
        session.RawEncodedAt remaining registry type value head ∧
        session.PayloadsEncodedAt remaining head.registry types values tail ∧
        encoded = ⟨tail.registry, head.preserves.trans tail.preserves, .pair head.value tail.value⟩ := by
  cases types with
  | nil => exact False.elim (more rfl)
  | cons next rest =>
      cases fuel with
      | zero => cases accepted
      | succ fuel =>
          unfold PayloadsEncodedAt encodePayloads at accepted
          obtain ⟨head, headAt, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨tail, tailAt, accepted⟩ := root_factory_bind_ok accepted
          cases accepted
          exact ⟨fuel, rfl, head, tail, headAt, tailAt, rfl⟩

theorem Session.EntriesEncodedAt.nil {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {keyType valueType : Ty}
    {layout : Core.OrderedMapping.Layout} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.EntriesEncodedAt fuel registry keyType valueType layout [] encoded) :
    encoded = .pure registry (Core.OrderedMapping.encode layout []) := by
  cases fuel <;> cases accepted <;> rfl

theorem Session.EntriesEncodedAt.cons {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {keyType valueType : Ty}
    {layout : Core.OrderedMapping.Layout} {key value : Value} {entries : List (Value × Value)}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.EntriesEncodedAt fuel registry keyType valueType layout ((key, value) :: entries) encoded) :
    ∃ remaining, fuel = remaining + 1 ∧
      ∃ (keyEncoded : SourceCoreCompatibleValues.Extended registry Core.Value)
        (valueEncoded : SourceCoreCompatibleValues.Extended keyEncoded.registry Core.Value)
        (tail : SourceCoreCompatibleValues.Extended valueEncoded.registry Core.Value),
        session.RawEncodedAt remaining registry keyType key keyEncoded ∧
        session.RawEncodedAt remaining keyEncoded.registry valueType value valueEncoded ∧
        session.EntriesEncodedAt remaining valueEncoded.registry keyType valueType layout entries tail ∧
        encoded = ⟨tail.registry, keyEncoded.preserves.trans (valueEncoded.preserves.trans tail.preserves),
          .constructed layout.consConstructor (.pair (.pair keyEncoded.value valueEncoded.value) tail.value)⟩ := by
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold EntriesEncodedAt encodeEntries at accepted
      obtain ⟨keyEncoded, keyAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨valueEncoded, valueAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨tail, tailAt, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      exact ⟨fuel, rfl, keyEncoded, valueEncoded, tail, keyAt, valueAt, tailAt, rfl⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem arguments_raw_at {artifact : Artifact} {world : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world} {fuel : Nat}
    {values : Values} {owner : values.checked = artifact.recipe.compiled.compatible.checked}
    {sourceTypes : List Ty} {types : List Core.Ty} {arguments : List Value}
    {encoded : Arguments artifact world types}
    (accepted : encodeArguments authority slots fuel values owner sourceTypes types arguments = .ok encoded) :
    SourceCoreRawMetadata.Extends values.registry encoded.values.registry ∧
      ∀ {index : Nat} {expected : Ty} {value : Value},
        sourceTypes[index]? = some expected → arguments[index]? = some value →
        ∃ (before : SourceCoreRawMetadata.Registry)
          (raw : SourceCoreCompatibleValues.Extended before Core.Value) (type : Core.Ty),
          encoded.native[index]? = some raw.value ∧ types[index]? = some type ∧
          artifact.recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
          before.signatures = artifact.recipe.compiled.compatible.checked.signatures ∧
          encodeRaw authority slots fuel before expected value = .ok raw ∧
          SourceCoreRawMetadata.Extends raw.registry encoded.values.registry := by
  induction sourceTypes generalizing types arguments values encoded with
  | nil =>
      cases types <;> cases arguments <;> try (solve | cases accepted)
      cases accepted
      refine ⟨.refl _, ?_⟩
      intro index expected value found
      simp at found
  | cons expected rest ih =>
      cases types with
      | nil => cases accepted
      | cons type types =>
          cases arguments with
          | nil => cases accepted
          | cons argument arguments =>
              simp only [encodeArguments] at accepted
              cases projected : artifact.recipe.compiled.compatible.checked.catalog.project expected with
              | error error => simp [projected, bind, Except.bind, throw, throwThe] at accepted
              | ok actual =>
                  simp only [projected, bind, Except.bind] at accepted
                  split at accepted
                  · rename_i same
                    subst actual
                    obtain ⟨raw, rawEq, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨validated, _validated, accepted⟩ := root_factory_bind_ok accepted
                    obtain ⟨tail, tailEq, accepted⟩ := root_factory_bind_ok accepted
                    cases accepted
                    obtain ⟨extended, atIndex⟩ := ih tailEq
                    refine ⟨raw.preserves.trans extended, ?_⟩
                    intro index selectedType selectedValue foundType foundValue
                    cases index with
                    | zero =>
                        have sameType := Option.some.inj foundType
                        have sameValue := Option.some.inj foundValue
                        subst selectedType
                        subst selectedValue
                        have beforeOwner : values.registry.signatures = artifact.recipe.compiled.compatible.checked.signatures :=
                          values.registryOwner.trans (congrArg SourceCoreCompatibleCatalog.Checked.signatures owner)
                        exact ⟨values.registry, raw, type, rfl, rfl, projected, beforeOwner, rawEq, extended⟩
                    | succ index => exact atIndex foundType foundValue
                  · simp [throw, throwThe] at accepted

/-- One original raw input encoding at its actual startup position, with the
metadata before that input and its real extension through the remaining inputs. -/
def Checkpoint.RawInputAt {artifact : Artifact} (session : Session artifact)
    (key : Key) (index fuel : Nat) (value : Value) (checkpoint : Checkpoint artifact) : Prop :=
  ∃ (root : Root artifact.recipe.compiled) (native : Core.Environment),
    artifact.recipe.roots.find? (fun root => decide (root.key = key)) = some root ∧
    (∀ expected, root.inputs[index]? = some expected →
      ∃ (before : SourceCoreRawMetadata.Registry)
        (raw : SourceCoreCompatibleValues.Extended before Core.Value) (type : Core.Ty),
        native[index]? = some raw.value ∧ root.types[index]? = some type ∧
        artifact.recipe.compiled.compatible.checked.catalog.project expected = .ok type ∧
        before.signatures = artifact.recipe.compiled.compatible.checked.signatures ∧
        session.RawEncodedAt fuel before expected value raw ∧
        SourceCoreRawMetadata.Extends raw.registry checkpoint.values.registry) ∧
    checkpoint.state = .initial root.body (native.reverse ++ environment artifact) session.store

theorem Checkpoint.RootStart.raw_input {artifact : Artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {fuel : Nat} {checkpoint : Checkpoint artifact}
    (started : checkpoint.RootStart session key arguments fuel)
    {index : Nat} {value : Value} (found : arguments[index]? = some value) :
    checkpoint.RawInputAt session key index fuel value := by
  obtain ⟨root, selected, _, _, encoded, accepted, _, _, _, initial, _, sameValues⟩ := started
  obtain ⟨_extended, atIndex⟩ := arguments_raw_at accepted
  refine ⟨root, encoded.native, selected, ?_, initial⟩
  intro expected foundType
  obtain ⟨before, raw, type, actual, typeAt, projected, owner, encodedAt, extended⟩ := atIndex foundType found
  rw [← sameValues] at extended
  exact ⟨before, raw, type, actual, typeAt, projected, owner, encodedAt, extended⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open TypeSystem

/-- The returned session reimports the exact payload of this actual success.
This is the original export check, including the decoder's real slot registry. -/
theorem Checkpoint.SucceededResultAt.reimports {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {native : Core.Value} {store : Core.Store} {completion : Completion artifact}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion) :
    ∃ payload, Core.LanguageResult.decode? native = some (.succeeded payload) ∧
      completion.session.EncodesAt boundaryFuel completion.sourceType completion.value payload := by
  obtain ⟨_completed, payload, _extension, slots, encoded, decoded, _decode, encode, recovered,
    sourceType, _boundary, _stored, world, authority, _sourcePrefix, values, _owner, registry,
    _origin, _authenticated⟩ := receipt
  cases completion
  rename_i value result returned outputFuel authenticated origin extension
  cases returned
  rename_i returnedAuthority returnedWorld returnedStore stored environmentTyped returnedRegistry returnedValues owner sourcePrefix
  change returnedWorld = store.map Core.Value.type at world
  subst returnedWorld
  have registryEq : returnedRegistry = slots := eq_of_heq registry
  subst returnedRegistry
  change returnedAuthority = checkpoint.origin.authority at authority
  subst returnedAuthority
  change returnedValues = checkpoint.values at values
  subst returnedValues
  refine ⟨payload, decoded, encoded, ?_, recovered⟩
  change result = checkpoint.request.result at sourceType
  simpa only [sourceType] using encode

/-- The actual request fixes the raw output type while the observed native
success fixes its entire callable payload, including captured references. -/
theorem Checkpoint.SucceededResultAt.reimports_payload {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {native payload : Core.Value} {store : Core.Store} {completion : Completion artifact}
    {expected : Ty}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt expected)
    (decoded : Core.LanguageResult.decode? native = some (.succeeded payload)) :
    completion.sourceType = expected ∧
      completion.session.EncodesAt boundaryFuel expected completion.value payload := by
  obtain ⟨actual, actualDecoded, encoded⟩ := receipt.reimports
  have same : actual = payload := Core.LanguageResult.Outcome.succeeded.inj
    (Option.some.inj (actualDecoded.symm.trans decoded))
  subst actual
  have sourceType := receipt.source_type requested
  exact ⟨sourceType, sourceType ▸ encoded⟩

/-- Later actual factory issuance preserves the exported function handle and
its complete native payload at the completed store; no execution is replayed. -/
theorem Checkpoint.SucceededResultAt.reimports_function_after {artifact : Artifact}
    {checkpoint : Checkpoint artifact} {fuel boundaryFuel : Nat} {generation : ExportGeneration}
    {native payload : Core.Value} {store : Core.Store} {completion : Completion artifact}
    {expected : Ty} {handle : Handle} {session : Session artifact}
    (receipt : checkpoint.SucceededResultAt fuel boundaryFuel generation native store completion)
    (requested : checkpoint.ResultTypeAt expected)
    (decoded : Core.LanguageResult.decode? native = some (.succeeded payload))
    (handleValue : completion.value = .function handle)
    (continued : completion.session.IssuanceChain session) :
    completion.sourceType = expected ∧
      session.NativeAt (store.map Core.Value.type) store ∧
      session.EncodesAt boundaryFuel expected (.function handle) payload := by
  obtain ⟨sourceType, encoded⟩ := receipt.reimports_payload requested decoded
  rw [handleValue] at encoded
  exact ⟨sourceType, continued.same_runtime.native_at receipt.native_at.2,
    continued.encodes_function encoded⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private def DecodedSlotsAppend (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (generation : ExportGeneration) (values : Values) (slots : Registry artifact world)
    (expected : Ty) (native : Core.Value) (value : Value) (returned : Registry artifact world),
    decodeRaw authority generation values fuel slots expected native = .ok (value, returned) →
    ∃ suffix, returned = slots ++ suffix

private def DecodedPayloadSlotsAppend (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (generation : ExportGeneration) (values : Values) (slots : Registry artifact world)
    (types : List Ty) (native : Core.Value) (output : List Value) (returned : Registry artifact world),
    decodePayloads authority generation values fuel slots types native = .ok (output, returned) →
    ∃ suffix, returned = slots ++ suffix

private def DecodedEntrySlotsAppend (fuel : Nat) : Prop :=
  ∀ {artifact : Artifact} {world : Core.StoreTyping} (authority : SessionAuthority)
    (generation : ExportGeneration) (values : Values) (slots : Registry artifact world)
    (keyType valueType : Ty) (layout : Core.OrderedMapping.Layout) (native : Core.Value)
    (output : List (Value × Value)) (returned : Registry artifact world),
    decodeEntries authority generation values fuel slots keyType valueType layout native = .ok (output, returned) →
    ∃ suffix, returned = slots ++ suffix

private theorem decode_raw_append_succ {fuel : Nat} (raw : DecodedSlotsAppend fuel)
    (payloads : DecodedPayloadSlotsAppend fuel) (entries : DecodedEntrySlotsAppend fuel) :
    DecodedSlotsAppend (fuel + 1) := by
  intro artifact world authority generation values slots expected native value returned accepted
  unfold decodeRaw at accepted
  split at accepted
  · obtain ⟨⟨handle, next⟩, registered, accepted⟩ := root_factory_bind_ok accepted
    cases accepted
    exact issuance_register_append registered
  · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
  · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
  · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
  · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
  · obtain ⟨⟨left, first⟩, leftAt, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨⟨right, second⟩, rightAt, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨a, firstEq⟩ := raw authority generation values slots _ _ left first (simple_mapError_ok leftAt)
    obtain ⟨b, secondEq⟩ := raw authority generation values first _ _ right second (simple_mapError_ok rightAt)
    have result : second = slots ++ (a ++ b) := by rw [secondEq, firstEq, List.append_assoc]
    cases accepted
    exact ⟨a ++ b, result⟩
  · obtain ⟨data, _decoded, accepted⟩ := root_factory_bind_ok accepted
    split at accepted
    · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
    · cases accepted
  · obtain ⟨header, _headerAt, accepted⟩ := root_factory_bind_ok accepted
    cases header <;> simp only [pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted
    case proxy => cases accepted
    case constructor => cases accepted
    rename_i keyType valueType
    obtain ⟨layout, _layoutAt, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨⟨decoded, next⟩, decodedAt, accepted⟩ := root_factory_bind_ok accepted
    obtain ⟨fallback, _fallbackAt, accepted⟩ := root_factory_bind_ok accepted
    split at accepted
    · have result := entries authority generation values slots keyType valueType layout _ decoded next decodedAt
      cases accepted
      exact result
    · cases accepted
  · obtain ⟨header, _headerAt, accepted⟩ := root_factory_bind_ok accepted
    cases header <;> simp only [pure, Except.pure, bind, Except.bind, throw, throwThe] at accepted
    case proxy => cases accepted
    case mapping => cases accepted
    rename_i instantiation
    obtain ⟨tag, _tagAt, accepted⟩ := root_factory_bind_ok accepted
    split at accepted
    · obtain ⟨⟨decoded, next⟩, decodedAt, accepted⟩ := root_factory_bind_ok accepted
      have result := payloads authority generation values slots instantiation.payloadTypes _ decoded next decodedAt
      cases accepted
      exact result
    · cases accepted
  · obtain ⟨_projected, _projection, accepted⟩ := root_factory_bind_ok accepted
    cases accepted

private theorem decode_payloads_append_succ {fuel : Nat} (raw : DecodedSlotsAppend fuel)
    (payloads : DecodedPayloadSlotsAppend fuel) : DecodedPayloadSlotsAppend (fuel + 1) := by
  intro artifact world authority generation values slots types native output returned accepted
  cases types with
  | nil =>
      cases native <;> simp only [decodePayloads] at accepted <;> cases accepted
      exact ⟨[], (List.append_nil _).symm⟩
  | cons type types =>
      cases types with
      | nil =>
          simp only [decodePayloads] at accepted
          obtain ⟨⟨value, next⟩, decoded, accepted⟩ := root_factory_bind_ok accepted
          have result := raw authority generation values slots _ _ value next decoded
          cases accepted
          exact result
      | cons type' types =>
          cases native <;> simp only [decodePayloads] at accepted <;> try cases accepted
          obtain ⟨⟨value, first⟩, firstAt, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨⟨rest, second⟩, restAt, accepted⟩ := root_factory_bind_ok accepted
          obtain ⟨a, firstEq⟩ := raw authority generation values slots _ _ value first firstAt
          obtain ⟨b, secondEq⟩ := payloads authority generation values first _ _ rest second restAt
          have result : second = slots ++ (a ++ b) := by rw [secondEq, firstEq, List.append_assoc]
          cases accepted
          exact ⟨a ++ b, result⟩

private theorem decode_entries_append_succ {fuel : Nat} (raw : DecodedSlotsAppend fuel)
    (entries : DecodedEntrySlotsAppend fuel) : DecodedEntrySlotsAppend (fuel + 1) := by
  intro artifact world authority generation values slots keyType valueType layout native output returned accepted
  unfold decodeEntries at accepted
  split at accepted
  · split at accepted
    · cases accepted; exact ⟨[], (List.append_nil _).symm⟩
    · cases accepted
  · split at accepted
    · obtain ⟨⟨key, first⟩, keyAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨⟨value, second⟩, valueAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨⟨rest, third⟩, restAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨a, firstEq⟩ := raw authority generation values slots keyType _ key first keyAt
      obtain ⟨b, secondEq⟩ := raw authority generation values first valueType _ value second valueAt
      obtain ⟨c, thirdEq⟩ := entries authority generation values second keyType valueType layout _ rest third restAt
      have result : third = slots ++ (a ++ b ++ c) := by rw [thirdEq, secondEq, firstEq]; simp only [List.append_assoc]
      cases accepted
      exact ⟨a ++ b ++ c, result⟩
    · cases accepted
  · cases accepted

private theorem decode_slots_append (fuel : Nat) :
    DecodedSlotsAppend fuel ∧ DecodedPayloadSlotsAppend fuel ∧ DecodedEntrySlotsAppend fuel := by
  induction fuel with
  | zero =>
      refine ⟨?_, ?_, ?_⟩
      · intro artifact world authority generation values slots expected native value returned accepted
        cases accepted
      · intro artifact world authority generation values slots types native output returned accepted
        cases types <;> cases native <;> simp only [decodePayloads] at accepted <;> cases accepted
        exact ⟨[], (List.append_nil _).symm⟩
      · intro artifact world authority generation values slots keyType valueType layout native output returned accepted
        cases accepted
  | succ fuel ih =>
      exact ⟨decode_raw_append_succ ih.1 ih.2.1 ih.2.2,
        decode_payloads_append_succ ih.1 ih.2.1, decode_entries_append_succ ih.1 ih.2.2⟩

private theorem execution_resolve_weaken {artifact : Artifact} {world future : Core.StoreTyping}
    {authority : SessionAuthority} {slots : Registry artifact world}
    {expected : Ty} {handle : Handle} {native : Core.Value}
    (accepted : resolve authority slots expected handle = .ok native)
    (extension : Core.WorldExtends world future) :
    resolve authority (slots.weaken extension) expected handle = .ok native := by
  obtain ⟨slot, found, _value⟩ := resolved_slot accepted
  simpa only [resolve, Registry.weaken, List.find?_map, Function.comp_def, found,
    Option.map_some, pure, Except.pure, bind, Except.bind] using accepted

private theorem execution_encode_function_at_registry
    {artifact : Artifact} {world future : Core.StoreTyping}
    {authority authority' : SessionAuthority}
    {slots : Registry artifact world} {returned : Registry artifact future} {fuel : Nat}
    {registry : SourceCoreRawMetadata.Registry} {expected : Ty} {handle : Handle}
    {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : encodeRaw authority slots fuel registry expected (.function handle) = .ok encoded)
    (resolved : resolve authority' returned expected handle = .ok encoded.value)
    (receiving : SourceCoreRawMetadata.Registry) :
    encodeRaw authority' returned fuel receiving expected (.function handle) =
      .ok (.pure receiving encoded.value) := by
  obtain ⟨parameter, result, view⟩ := issuance_encoded_function_view accepted
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      unfold encodeRaw
      rw [view]
      dsimp only
      rw [resolved]
      rfl

private theorem root_start_resolves_weaken
    {artifact : Artifact} {checkpoint : Checkpoint artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {startupFuel : Nat}
    (started : checkpoint.RootStart session key arguments startupFuel)
    {expected : Ty} {handle : Handle} {native : Core.Value}
    (resolved : resolve session.authority session.registry expected handle = .ok native)
    {future : Core.StoreTyping} (extension : Core.WorldExtends checkpoint.world future) :
    resolve checkpoint.origin.authority (checkpoint.registry.weaken extension) expected handle = .ok native := by
  obtain ⟨root, _selected, _key, _arity, encoded, _encoded, origin, _request, world,
    _initial, registry, _values⟩ := started
  cases checkpoint
  rename_i originSession request initialWorld state stored typed extension' initialRegistry values owner
  change originSession = session at origin
  subst originSession
  change initialWorld = session.world at world
  subst initialWorld
  have registryEq : initialRegistry = session.registry := eq_of_heq registry
  subst initialRegistry
  exact execution_resolve_weaken resolved extension

/-- An actual successful execution preserves every previously encoded function
handle and its exact native payload, including captures. The new export may be
arbitrarily nested; its decoder only reuses slots or appends fresh ones. -/
theorem Checkpoint.SucceededResultAt.encodes_function
    {artifact : Artifact} {checkpoint : Checkpoint artifact} {session : Session artifact}
    {key : Key} {arguments : List Value} {startupFuel executionFuel boundaryFuel : Nat}
    {generation : ExportGeneration} {native : Core.Value} {store : Core.Store}
    {completion : Completion artifact}
    (succeeded : checkpoint.SucceededResultAt executionFuel boundaryFuel generation native store completion)
    (started : checkpoint.RootStart session key arguments startupFuel)
    {inputFuel : Nat} {expected : Ty} {handle : Handle} {payload : Core.Value}
    (imported : session.EncodesAt inputFuel expected (.function handle) payload) :
    completion.session.EncodesAt inputFuel expected (.function handle) payload := by
  obtain ⟨oldEncoded, oldAt, oldValue⟩ := imported
  obtain ⟨_completed, result, extension, slots, encoded, _decoded, decode, _encode, _recovered,
    _sourceType, _boundary, _stored, world, authority, _sourcePrefix, values, _owner, registry,
    _origin, _authenticated⟩ := succeeded
  obtain ⟨suffix, slotsEq⟩ := (decode_slots_append boundaryFuel).1
    checkpoint.origin.authority generation checkpoint.values _ _ _ _ slots decode
  have resolved := root_start_resolves_weaken started (encoded_function_resolves oldAt) extension
  have returnedResolved := issuance_resolve_append resolved suffix
  rw [← slotsEq] at returnedResolved
  have returnedEncoded := execution_encode_function_at_registry oldAt returnedResolved completion.session.values.registry
  cases completion
  rename_i value resultType returned outputFuel authenticated origin completionExtension
  cases returned
  rename_i returnedAuthority returnedWorld returnedStore stored environmentTyped returnedRegistry returnedValues owner sourcePrefix
  change returnedWorld = store.map Core.Value.type at world
  subst returnedWorld
  have registryEq : returnedRegistry = slots := eq_of_heq registry
  subst returnedRegistry
  change returnedAuthority = checkpoint.origin.authority at authority
  subst returnedAuthority
  exact ⟨_, returnedEncoded, oldValue⟩

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession

private theorem issuance_global_read {artifact : Artifact} {session : Session artifact}
    {factory : CallableFactory artifact.recipe.compiled} {generation : SourceCorePublicValues.ExportGeneration}
    {fuel : Nat} {completion : Completion artifact}
    (issued : issueCallable session factory generation fuel = .ok completion)
    {location : Nat} {value : Core.Value}
    (member : (location, value) ∈ artifact.recipe.templates.nativeGlobals) :
    session.store[location]? = some value := by
  unfold issueCallable at issued
  obtain ⟨_globals, checked, _issued⟩ := root_factory_bind_ok issued
  unfold checkGlobals SourceCoreCallableNativeSlots.checkPreparedGlobals at checked
  split at checked
  · rename_i exact
    exact of_decide_eq_true (List.all_eq_true.mp exact _ member)
  · split at checked <;> cases checked

/-- Actual named issuance has checked this precise installed slot in the
current physical store. No bootstrap-state equality is assumed. -/
theorem Session.NamedIssuedAt.native_global_read
    {artifact : Artifact} {session : Session artifact}
    {key : Key} {fuel : Nat} {completion : Completion artifact}
    (issued : session.NamedIssuedAt key fuel completion)
    {recipe : Recipe} (atRecipe : artifact.RecipeAt recipe)
    {world : Core.StoreTyping} {store : Core.Store} (atNative : session.NativeAt world store)
    {location : Nat} {value : Core.Value}
    (member : (location, value) ∈ recipe.templates.nativeGlobals) :
    store.read? location = some value := by
  obtain ⟨row, generation, _selected, accepted⟩ := issued
  have actualMember : (location, value) ∈ artifact.recipe.templates.nativeGlobals := by
    rw [atRecipe]
    exact member
  have read := issuance_global_read accepted actualMember
  rw [atNative.2] at read
  exact read

/-- A fixed accepted encoding has one exact native payload. -/
theorem Session.EncodesAt.unique {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {expected : TypeSystem.Ty} {value : SourceCorePublicValues.Value}
    {first second : Core.Value}
    (left : session.EncodesAt fuel expected value first)
    (right : session.EncodesAt fuel expected value second) : first = second := by
  obtain ⟨left, leftAt, firstAt⟩ := left
  obtain ⟨right, rightAt, secondAt⟩ := right
  have same := Except.ok.inj (leftAt.symm.trans rightAt)
  subst right
  exact firstAt.symm.trans secondAt

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

private theorem snapshot_observe_row_append {artifact : Artifact} {world : Core.StoreTyping}
    {store : Core.Store} {values : Values} {authority : SessionAuthority}
    {generation : ExportGeneration} {slots : Registry artifact world}
    {row : HeapRow artifact store} {fuel : Nat}
    {observed : HeapCellExport (world := world) values authority row}
    (accepted : observeRow values authority generation slots row fuel = .ok observed) :
    ∃ suffix, observed.slots = slots ++ suffix := by
  unfold observeRow at accepted
  obtain ⟨selected, _selectedAt, accepted⟩ := root_factory_bind_ok accepted
  split at accepted
  · split at accepted
    · cases accepted
      exact ⟨[], (List.append_nil _).symm⟩
    · split at accepted
      · cases accepted
      · split at accepted
        · obtain ⟨exported, exportedAt, accepted⟩ := root_factory_bind_ok accepted
          cases accepted
          have decoded := (exportValue_success_receipt exportedAt).1
          exact (decode_slots_append fuel).1 _ _ _ _ _ _ _ _ decoded
        · cases accepted
  · obtain ⟨restored, _restoredAt, accepted⟩ := root_factory_bind_ok accepted
    split at accepted
    · cases accepted
      exact ⟨[], (List.append_nil _).symm⟩
    · cases accepted

private theorem snapshot_observe_rows_append {artifact : Artifact} {world : Core.StoreTyping}
    {store : Core.Store} {values : Values} {authority : SessionAuthority}
    {generation : ExportGeneration} {fuel : Nat} {slots : Registry artifact world}
    {rows : List (HeapRow artifact store)}
    {observed : HeapCellsExport (world := world) values authority rows}
    (accepted : observeRows values authority generation fuel slots rows = .ok observed) :
    ∃ suffix, observed.slots = slots ++ suffix := by
  induction rows generalizing slots with
  | nil =>
      cases accepted
      exact ⟨[], (List.append_nil _).symm⟩
  | cons row rows ih =>
      unfold observeRows at accepted
      obtain ⟨head, headAt, accepted⟩ := root_factory_bind_ok accepted
      obtain ⟨tail, tailAt, accepted⟩ := root_factory_bind_ok accepted
      cases accepted
      obtain ⟨headSuffix, headSlots⟩ := snapshot_observe_row_append headAt
      obtain ⟨tailSuffix, tailSlots⟩ := ih tailAt
      exact ⟨headSuffix ++ tailSuffix, by rw [tailSlots, headSlots, List.append_assoc]⟩

private theorem snapshot_observe_heap_append {artifact : Artifact} {session : Session artifact}
    {generation : ExportGeneration} {fuel : Nat} {observed : HeapObservation session}
    (accepted : observeHeap session generation fuel = .ok observed) :
    ∃ suffix, observed.native.slots = session.registry ++ suffix := by
  unfold observeHeap at accepted
  obtain ⟨ledger, _ledgerAt, accepted⟩ := root_factory_bind_ok accepted
  obtain ⟨native, nativeAt, accepted⟩ := root_factory_bind_ok accepted
  cases accepted
  exact snapshot_observe_rows_append nativeAt

/-- Restoration of the exact saved ready session and its successful original
heap observation. This records the captured branch, including its old heap. -/
def Session.RestoredAt {artifact : Artifact} (before after : Session artifact) : Prop :=
  ∃ (snapshot : Snapshot artifact) (fuel : Nat),
    before.SnapshotAt fuel snapshot ∧ snapshot.restore = .ready after

/-- Ready restoration preserves the captured native state, authority and raw
metadata. Heap observation may have appended authenticated handle slots. -/
theorem Session.RestoredAt.same_runtime {artifact : Artifact} {before after : Session artifact}
    (restored : before.RestoredAt after) : before.SameRuntime after := by
  obtain ⟨snapshot, fuel, ⟨generation, observed, _observedAt, snapshotEq⟩, restored⟩ := restored
  subst snapshot
  change RestoredSnapshot.ready {before with registry := observed.native.slots} = .ready after at restored
  cases RestoredSnapshot.ready.inj restored
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Existing exported functions keep their original payload and captured
references through actual same-snapshot ready restoration. -/
theorem Session.RestoredAt.encodes_function {artifact : Artifact} {before after : Session artifact}
    (restored : before.RestoredAt after)
    {fuel : Nat} {expected : Ty} {handle : Handle} {native : Core.Value}
    (imported : before.EncodesAt fuel expected (.function handle) native) :
    after.EncodesAt fuel expected (.function handle) native := by
  obtain ⟨snapshot, boundaryFuel, ⟨generation, observed, observedAt, snapshotEq⟩, restored⟩ := restored
  subst snapshot
  change RestoredSnapshot.ready {before with registry := observed.native.slots} = .ready after at restored
  cases RestoredSnapshot.ready.inj restored
  obtain ⟨suffix, slotsEq⟩ := snapshot_observe_heap_append observedAt
  obtain ⟨encoded, encodedAt, valueEq⟩ := imported
  refine ⟨encoded, ?_, valueEq⟩
  change encodeRaw before.authority observed.native.slots fuel before.values.registry expected (.function handle) = .ok encoded
  rw [slotsEq]
  exact issuance_encode_function_append encodedAt suffix

end Solcore.Frontend.SourceCoreIndexedSession

namespace Solcore.Frontend.SourceCoreIndexedSession
open SourceInference TypeSystem

/-- A function selected inside an actual encoded result can be imported on its
own. The full raw Source type keeps the same checked runtime view. -/
theorem Session.RawEncodedAt.reimports_function
    {artifact : Artifact} {session : Session artifact}
    {fuel : Nat} {registry : SourceCoreRawMetadata.Registry} {expected sourceType : Ty}
    {handle : Handle} {encoded : SourceCoreCompatibleValues.Extended registry Core.Value}
    (accepted : session.RawEncodedAt fuel registry expected (.function handle) encoded)
    (compatible : SourceCoreRawMetadata.runtimeType sourceType =
      SourceCoreRawMetadata.runtimeType expected) :
    session.EncodesAt fuel sourceType (.function handle) encoded.value := by
  have resolved := encoded_function_resolves accepted
  have resolved' : resolve session.authority session.registry sourceType handle = .ok encoded.value := by
    by_cases artifactOwner : handle.belongsToArtifact artifact.authority = true
    · by_cases sessionOwner : handle.belongsToSession session.authority = true
      · obtain ⟨slot, found, _value⟩ := resolved_slot resolved
        by_cases sameType : SourceCoreRawMetadata.runtimeType expected =
            SourceCoreRawMetadata.runtimeType handle.sourceType
        · simpa [resolve, artifactOwner, sessionOwner, found, compatible, sameType,
            bind, Except.bind, pure, Except.pure, throw, throwThe] using resolved
        · simp [resolve, artifactOwner, sessionOwner, found, sameType,
            bind, Except.bind, pure, Except.pure, throw, throwThe] at resolved
      · simp [resolve, artifactOwner, sessionOwner, bind, Except.bind,
          pure, Except.pure, throw, throwThe] at resolved
    · simp [resolve, artifactOwner, bind, Except.bind, pure, Except.pure,
        throw, throwThe] at resolved
  obtain ⟨parameter, result, view⟩ := issuance_encoded_function_view accepted
  refine ⟨.pure session.values.registry encoded.value, ?_, rfl⟩
  cases fuel with
  | zero => cases accepted
  | succ fuel =>
      change encodeRaw session.authority session.registry (fuel + 1) session.values.registry
        sourceType (.function handle) = _
      unfold encodeRaw
      rw [compatible, view]
      dsimp only
      rw [resolved']
      rfl

end Solcore.Frontend.SourceCoreIndexedSession
