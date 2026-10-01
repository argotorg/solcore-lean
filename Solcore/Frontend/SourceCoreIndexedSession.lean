import Solcore.Frontend.SourceCorePublicValues
import Solcore.Frontend.SourceCoreUnifiedCompilation
import Solcore.Frontend.SourceCoreCallableIndexedTemplates

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

end Solcore.Frontend.SourceCoreIndexedSession
