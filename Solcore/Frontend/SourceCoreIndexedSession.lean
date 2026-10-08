import Solcore.Frontend.SourceCorePublicValues
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

def Recipe.open (recipe : Recipe) : IO Artifact := return ⟨← SourceCorePublicValues.ArtifactAuthority.mint, recipe⟩
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

def Artifact.bootstrap (artifact : Artifact) (sourcePrefix : InertPrefix artifact) : IO (Bootstrap artifact) :=
  return ⟨← artifact.authority.newSession, .initial artifact.recipe.bootstrap [] [],
    .eval (.nil _) .nil artifact.recipe.bootstrapTyped .nil, sourcePrefix⟩

/-- Fresh source sessions need no legacy heap/carrier argument. The native
frame and global slots are still installed by the resumable bootstrap. -/
def Artifact.bootstrapFresh (artifact : Artifact) : IO (Bootstrap artifact) :=
  artifact.bootstrap ⟨{}, 1, rfl⟩

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

/-- Import a named function from this artifact's exact cached installation.
The specialized key chooses code, identity and descriptor together. -/
def Session.named {artifact : Artifact} (session : Session artifact) (key : Key)
    (boundaryFuel : Nat := 1024) : IO (Except Error (Completion artifact)) := do
  match artifact.recipe.named.find? (fun row => decide (row.1 = key)) with
  | none => pure (.error ⟨[], .missingEntry key⟩)
  | some (_, factory) => pure (issueCallable session factory (← SourceCorePublicValues.ExportGeneration.mint) boundaryFuel)

/-- Import a closed builtin template owned by the artifact's callable table.
No caller-supplied native closure is accepted. -/
def Session.builtin {artifact : Artifact} (session : Session artifact) (function : BuiltinFunctionId)
    (boundaryFuel : Nat := 1024) : IO (Except Error (Completion artifact)) := do
  match artifact.recipe.builtins.find? (fun row => decide (row.1 = function)) with
  | none => pure (.error ⟨[], .missingBuiltin function⟩)
  | some (_, factory) => pure (issueCallable session factory (← SourceCorePublicValues.ExportGeneration.mint) boundaryFuel)

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

def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := do
  match executed : Core.runStateful fuel checkpoint.state with
  | .done value store => pure (complete checkpoint (← SourceCorePublicValues.ExportGeneration.mint) fuel boundaryFuel value store executed)
  | .outOfFuel state => pure (.outOfFuel (suspend checkpoint fuel state executed))
  | .fault _ _ => pure (False.elim (Core.well_typed_runStateful_never_faults checkpoint.typed executed))

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

def Session.snapshot {artifact : Artifact} (session : Session artifact) (boundaryFuel : Nat := 1024) :
    IO (Except Error (Snapshot artifact)) := do
  let generation ← SourceCorePublicValues.ExportGeneration.mint
  pure <| (observeHeap session generation boundaryFuel).map fun observed => ⟨.ready session, observed⟩

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
