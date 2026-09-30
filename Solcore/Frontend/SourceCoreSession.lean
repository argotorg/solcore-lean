import Solcore.Frontend.SourceCoreDataValues
import Solcore.Frontend.SourceCoreGeneralFunctions
import Solcore.Frontend.SourceCorePlanCatalog
import Std.Sync.Mutex

/-! Owned source values over a typed Core session. The public carrier cannot
contain Core code or references. Function handles are minted only when exporting
a checked native result; they resolve to the original tagged function and its
captured locations in the session heap. This fresh/session-reuse boundary does
not yet import arbitrary pre-existing typed-source closures or heaps. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreSession

open SourceInference TypeSystem
abbrev DataContext := SourceCoreDataValues.Context
abbrev Checked := SourceCoreDataCatalog.Checked
abbrev Key := SourceSpecialization.SpecializationKey

private structure Token where
  index : Nat
  deriving Repr, DecidableEq

private initialize tokenCounter : Std.Mutex Nat ← Std.Mutex.new 0

private def mint : IO Token := tokenCounter.atomically do
  let index ← get
  set (index + 1)
  pure ⟨index⟩

/-- A lookup capability, never serialized Core code. Constructors and ownership
fields stay private. Export generations prevent slot reuse in branched immutable
session snapshots. Tokens are allocated internally, never selected by callers. -/
structure Handle where private mk ::
  private artifact : Token
  private session : Token
  private generation : Token
  private slot : Nat
  private sourceType : Ty
  deriving Repr, DecidableEq

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

abbrev PathStep := SourceCoreDataValues.PathStep

inductive ErrorCode where
  | data (error : SourceCoreDataValues.ErrorCode)
  | foreignArtifact | foreignSession | unknownHandle
  | handleTypeMismatch (expected actual : Ty)
  | invalidNativeValue (expected actual : Core.Ty)
  | missingEntry (key : Key)
  | argumentCountMismatch (expected actual : Nat)
  deriving Repr, DecidableEq

structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr, DecidableEq

private def Error.at (step : PathStep) (error : Error) : Error :=
  { error with path := step :: error.path }
private def fromData (error : SourceCoreDataValues.Error) : Error := ⟨error.path, .data error.code⟩
private def fromCatalog (error : SourceCoreDataCatalog.Error) : Error := ⟨[], .data (.catalog error)⟩

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

private structure Slot (context : DataContext) (world : Core.StoreTyping) where
  handle : Handle
  value : Core.Value
  projection : Core.Ty
  generated : context.checked.catalog.project handle.sourceType = .ok projection
  typed : Core.RuntimeValueHasType world value projection context.checked.catalog.definitions

private abbrev Registry (context : DataContext) (world : Core.StoreTyping) := List (Slot context world)

private def Slot.weaken {context : DataContext} {world future : Core.StoreTyping}
    (extension : Core.WorldExtends world future) (slot : Slot context world) : Slot context future :=
  { slot with typed := slot.typed.weaken extension }
private def Registry.weaken {context : DataContext} {world future : Core.StoreTyping}
    (extension : Core.WorldExtends world future) (registry : Registry context world) : Registry context future :=
  registry.map (Slot.weaken extension)

private def resolve {context : DataContext} {world : Core.StoreTyping}
    (artifact session : Token) (registry : Registry context world) (expected : Ty) (handle : Handle) :
    Except Error Core.Value := do
  unless handle.artifact = artifact do throw ⟨[], .foreignArtifact⟩
  unless handle.session = session do throw ⟨[], .foreignSession⟩
  let slot ← match registry.find? fun slot => decide (slot.handle = handle) with
    | none => throw ⟨[], .unknownHandle⟩
    | some slot => pure slot
  unless handle.sourceType = expected do throw ⟨[], .handleTypeMismatch expected handle.sourceType⟩
  pure slot.value

private def identity (context : DataContext) (type : Ty) : Except Error Core.DataTypeId := do
  match ← (context.checked.catalog.project type).mapError fromCatalog with
  | .namedData id => pure id
  | actual => throw ⟨[], .data (.coreShapeMismatch (.namedData ⟨0⟩) actual)⟩

mutual
  private def encodeRaw {context : DataContext} {world : Core.StoreTyping} :
      Nat → Token → Token → Registry context world → Ty → Value → Except Error Core.Value
    | 0, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, registry, expected, value => do
        match expected, value with
        | .comptime inner, value => encodeRaw fuel artifact session registry inner value
        | .function .., .function handle => resolve artifact session registry expected handle
        | .constructor (.builtin .unit), .unit => pure .unit
        | .constructor (.builtin .bool), .bool value => pure (.bool value)
        | .constructor (.builtin .word), .word value => pure (.word value)
        | .constructor (.builtin .integer), .integer value => pure (.integer value)
        | .product leftType rightType, .product left right => do
            let left ← (encodeRaw fuel artifact session registry leftType left).mapError (Error.at .productLeft)
            let right ← (encodeRaw fuel artifact session registry rightType right).mapError (Error.at .productRight)
            pure (.pair left right)
        | .mapping key value, .mapping actualKey actualValue entries => do
            unless actualKey = key ∧ actualValue = value do
              throw ⟨[], .data (.mappingMetadataMismatch key value actualKey actualValue)⟩
            encodeEntries fuel artifact session registry key value (← identity context expected) entries 0
        | .proxy inner, .proxy actual => do
            unless actual = inner do throw ⟨[], .data (.proxyIdentityMismatch inner actual)⟩
            pure (.constructed ⟨← identity context expected, 0⟩ .unit)
        | expected, .constructed metadata payloads => do
            unless metadata.resultType = expected do throw ⟨[], .data (.sourceTypeMismatch expected metadata.resultType)⟩
            let tag ← (context.checked.catalog.resolveConstructor context.signatures metadata).mapError fromCatalog
            let canonical ← (SourceCoreDataValues.constructorMetadata context expected tag).mapError fromData
            unless metadata = canonical do throw ⟨[], .data .constructorMetadataMismatch⟩
            let payload ← encodePayloads fuel artifact session registry metadata.payloadTypes payloads 0
            pure (.constructed tag payload)
        | expected, value => throw ⟨[], .data (.sourceTypeMismatch expected value.type)⟩

  private def encodePayloads {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
      (artifact session : Token) (registry : Registry context world) (types : List Ty) (values : List Value)
      (index : Nat) : Except Error Core.Value := do
    if types.length ≠ values.length then throw ⟨[], .data (.payloadCountMismatch types.length values.length)⟩
    match fuel, types, values with
    | _, [], [] => pure .unit
    | 0, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, [type], [value] =>
        (encodeRaw fuel artifact session registry type value).mapError (Error.at (.constructorPayload index))
    | fuel + 1, type :: types, value :: values => do
        let value ← (encodeRaw fuel artifact session registry type value).mapError (Error.at (.constructorPayload index))
        pure (.pair value (← encodePayloads fuel artifact session registry types values (index + 1)))
    | _, _, _ => throw ⟨[], .data (.payloadCountMismatch types.length values.length)⟩

  private def encodeEntries {context : DataContext} {world : Core.StoreTyping} :
      Nat → Token → Token → Registry context world → Ty → Ty → Core.DataTypeId → List (Value × Value) →
      Nat → Except Error Core.Value
    | _, _, _, _, _, _, id, [], _ => pure (.constructed ⟨id, 0⟩ .unit)
    | 0, _, _, _, _, _, _, _ :: _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, registry, keyType, valueType, id, (key, value) :: rest, index => do
        let key ← (encodeRaw fuel artifact session registry keyType key).mapError (Error.at (.mappingKey index))
        let value ← (encodeRaw fuel artifact session registry valueType value).mapError (Error.at (.mappingValue index))
        let rest ← encodeEntries fuel artifact session registry keyType valueType id rest (index + 1)
        pure (.constructed ⟨id, 1⟩ (.pair (.pair key value) rest))
end

private def register {context : DataContext} {world : Core.StoreTyping}
    (artifact session generation : Token) (registry : Registry context world)
    (sourceType : Ty) (value : Core.Value) : Except Error (Handle × Registry context world) := do
  match registry.find? fun slot => decide (slot.handle.sourceType = sourceType ∧ slot.value = value) with
  | some slot => pure (slot.handle, registry)
  | none =>
      let projection ← (SourceCoreGeneralEntry.projectType context.checked sourceType).mapError fromCatalog
      let validation ← validateAt context.checked.catalog.definitions world value projection.type
      let handle : Handle := ⟨artifact, session, generation, registry.length, sourceType⟩
      pure (handle, registry ++ [⟨handle, value, projection.type, projection.generated, validation.typed⟩])

mutual
  private def decodeRaw {context : DataContext} {world : Core.StoreTyping} :
      Nat → Token → Token → Token → Registry context world → Ty → Core.Value →
      Except Error (Value × Registry context world)
    | 0, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, expected, value => do
        match expected, value with
        | _, .cellRef .. => throw ⟨[], .data .externalReferenceUnsupported⟩
        | _, .hostFunction .. => throw ⟨[], .data .externalHostUnsupported⟩
        | .comptime inner, value => decodeRaw fuel artifact session generation registry inner value
        | .function .., value =>
            let (handle, registry) ← register artifact session generation registry expected value
            pure (.function handle, registry)
        | _, .closure .. => throw ⟨[], .data .functionHandleRequired⟩
        | .constructor (.builtin .unit), .unit => pure (.unit, registry)
        | .constructor (.builtin .bool), .bool value => pure (.bool value, registry)
        | .constructor (.builtin .word), .word value => pure (.word value, registry)
        | .constructor (.builtin .integer), .integer value => pure (.integer value, registry)
        | .product leftType rightType, .pair left right => do
            let (left, registry) ← (decodeRaw fuel artifact session generation registry leftType left).mapError (Error.at .productLeft)
            let (right, registry) ← (decodeRaw fuel artifact session generation registry rightType right).mapError (Error.at .productRight)
            pure (.product left right, registry)
        | .mapping key value, core => do
            let (entries, registry) ← decodeEntries fuel artifact session generation registry key value
              (← identity context expected) core 0
            pure (.mapping key value entries, registry)
        | .proxy inner, .constructed tag .unit => do
            unless tag = ⟨← identity context expected, 0⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            pure (.proxy inner, registry)
        | expected, .constructed tag payload => do
            let metadata ← (SourceCoreDataValues.constructorMetadata context expected tag).mapError fromData
            let (payloads, registry) ← decodePayloads fuel artifact session generation registry metadata.payloadTypes payload 0
            pure (.constructed metadata payloads, registry)
        | expected, value =>
            let projected ← (context.checked.catalog.project expected).mapError fromCatalog
            throw ⟨[], .data (.coreShapeMismatch projected value.type)⟩

  private def decodePayloads {context : DataContext} {world : Core.StoreTyping} :
      Nat → Token → Token → Token → Registry context world → List Ty → Core.Value → Nat →
      Except Error (List Value × Registry context world)
    | _, _, _, _, registry, [], .unit, _ => pure ([], registry)
    | 0, _, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, [type], value, index => do
        let (value, registry) ← (decodeRaw fuel artifact session generation registry type value).mapError (Error.at (.constructorPayload index))
        pure ([value], registry)
    | fuel + 1, artifact, session, generation, registry, type :: types, .pair value tail, index => do
        let (value, registry) ← (decodeRaw fuel artifact session generation registry type value).mapError (Error.at (.constructorPayload index))
        let (tail, registry) ← decodePayloads fuel artifact session generation registry types tail (index + 1)
        pure (value :: tail, registry)
    | _, _, _, _, _, _, _, _ => throw ⟨[], .data .constructorMetadataMismatch⟩

  private def decodeEntries {context : DataContext} {world : Core.StoreTyping} :
      Nat → Token → Token → Token → Registry context world → Ty → Ty → Core.DataTypeId → Core.Value → Nat →
      Except Error (List (Value × Value) × Registry context world)
    | 0, _, _, _, _, _, _, _, _, _ => throw ⟨[], .data .exhausted⟩
    | fuel + 1, artifact, session, generation, registry, keyType, valueType, id, core, index => do
        match core with
        | .constructed tag .unit =>
            unless tag = ⟨id, 0⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            pure ([], registry)
        | .constructed tag (.pair (.pair key value) tail) => do
            unless tag = ⟨id, 1⟩ do throw ⟨[], .data (.invalidConstructor tag)⟩
            let (key, registry) ← (decodeRaw fuel artifact session generation registry keyType key).mapError (Error.at (.mappingKey index))
            let (value, registry) ← (decodeRaw fuel artifact session generation registry valueType value).mapError (Error.at (.mappingValue index))
            let (tail, registry) ← (decodeEntries fuel artifact session generation registry keyType valueType id tail (index + 1)).mapError (Error.at .mappingTail)
            pure ((key, value) :: tail, registry)
        | _ => throw ⟨[], .data .constructorMetadataMismatch⟩
end

private structure Encoded {context : DataContext} (world : Core.StoreTyping) (sourceType : Ty) where
  value : Core.Value
  type : Core.Ty
  generated : context.checked.catalog.project sourceType = .ok type
  typed : Core.RuntimeValueHasType world value type context.checked.catalog.definitions

private def encode {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
    (artifact session : Token) (registry : Registry context world) (expected : Ty) (value : Value) :
    Except Error (Encoded (context := context) world expected) := do
  let projection ← (SourceCoreGeneralEntry.projectType context.checked expected).mapError fromCatalog
  let core ← encodeRaw fuel artifact session registry expected value
  let validation ← validateAt context.checked.catalog.definitions world core projection.type
  pure ⟨core, projection.type, projection.generated, validation.typed⟩

private structure Exported {context : DataContext} (world : Core.StoreTyping)
    (artifact session : Token) (fuel : Nat) (expected : Ty) (core : Core.Value) where
  value : Value
  registry : Registry context world
  reencoded : encodeRaw fuel artifact session registry expected value = .ok core

/-- The exact re-encoding guard proves that exporting a function handle retains
its complete identity tag, code and captured reference tree inside the owned
registry. Source data substitutions and mapping order are authenticated too. -/
private def exportValue {context : DataContext} {world : Core.StoreTyping} (fuel : Nat)
    (artifact session generation : Token) (registry : Registry context world)
    (expected : Ty) (core : Core.Value) :
    Except Error (Exported (context := context) world artifact session fuel expected core) := do
  let (value, registry) ← decodeRaw fuel artifact session generation registry expected core
  match recovered : encodeRaw fuel artifact session registry expected value with
  | .error error => throw error
  | .ok encoded =>
      if same : encoded = core then
        pure ⟨value, registry, by simpa only [same] using recovered⟩
      else throw ⟨[], .data .nonCanonicalCoreValue⟩

/-- The constructor is sealed. Preparation authenticates the actual plan and
checks each native entry once; cached consumers may inspect those checked
entries without rebuilding them. No owned identity exists until open. -/
structure Recipe where private mk ::
  private context : DataContext
  private prepared : SourceCoreGeneralEntry.PreparedProgram context.checked
  deriving Repr

def Recipe.checked (recipe : Recipe) : Checked := recipe.context.checked
def Recipe.program (recipe : Recipe) : SourceCoreGeneralEntry.PreparedProgram recipe.checked := recipe.prepared

def Recipe.prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (checked : Checked) (compilationFuel : Nat) :
    Except (SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error) Recipe := do
  let prepared ← SourceCoreGeneralFunctions.prepareWithCatalog program plan checked compilationFuel
  pure ⟨⟨checked, program.signatures⟩, prepared⟩

def Recipe.prepareAutomatic (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (compilationFuel : Nat) (callableContracts : Bool := true) : Except SourceCorePlanCatalog.Error Recipe := do
  let prepared ← SourceCorePlanCatalog.prepare program plan compilationFuel callableContracts
  pure ⟨⟨prepared.checked, program.signatures⟩, prepared.program⟩

/-- An owned artifact uses a cached, authenticated recipe. -/
structure Artifact where private mk ::
  private identity : Token
  private context : DataContext
  private program : SourceCoreGeneralEntry.PreparedProgram context.checked

/-- Opening the same recipe again creates a separate owned artifact. This only
mints an identity and copies the cached entries; no compiler is run here. -/
def Recipe.open (recipe : Recipe) : IO Artifact :=
  return ⟨← mint, recipe.context, recipe.prepared⟩

def Artifact.prepare (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (checked : Checked) (compilationFuel : Nat) :
    IO (Except (SourceCoreGeneralEntry.CompileError SourceCoreGeneralFunctions.Error) Artifact) := do
  match Recipe.prepare program plan checked compilationFuel with
  | .error error => pure (.error error)
  | .ok recipe => pure (.ok (← recipe.open))

/-- Discover all closed catalog representations from the authenticated plan. -/
def Artifact.prepareAutomatic (program : CheckedProgram) (plan : SourceSpecializationWorklist.Plan)
    (compilationFuel : Nat) : IO (Except SourceCorePlanCatalog.Error Artifact) := do
  match Recipe.prepareAutomatic program plan compilationFuel with
  | .error error => pure (.error error)
  | .ok recipe => pure (.ok (← recipe.open))

def Artifact.keys (artifact : Artifact) : List Key := artifact.program.entries.map (·.key)

/-- A persistent version of one owned execution session. Heap cells and
registry values are private; copying this value does not mint another identity. -/
structure Session (artifact : Artifact) where private mk ::
  private identity : Token
  private world : Core.StoreTyping
  private store : Core.Store
  private stored : Core.RuntimeStoreHasTypes world store artifact.context.checked.catalog.definitions
  private registry : Registry artifact.context world

def Artifact.newSession (artifact : Artifact) : IO (Session artifact) := do
  pure ⟨← mint, [], [], .nil _, []⟩

def Session.heapSize {artifact : Artifact} (session : Session artifact) : Nat := session.store.length
def Session.functionCount {artifact : Artifact} (session : Session artifact) : Nat := session.registry.length

inductive FunctionIdentity where
  | anonymous
  | named (identity : Core.Word)
  deriving Repr, DecidableEq

/-- Inspect only the source identity tag of an owned function. Equality of the
public carrier compares lookup capabilities; source function equality continues
to use the original anonymous/named tag inside Core. -/
def Session.functionIdentity? {artifact : Artifact} (session : Session artifact) (handle : Handle) :
    Option FunctionIdentity :=
  match resolve artifact.identity session.identity session.registry handle.sourceType handle with
  | .ok (.pair (.pair (.inLeft .word .unit) (.closure ..)) (.word _)) => some .anonymous
  | .ok (.pair (.pair (.inRight .unit (.word identity)) (.closure ..)) (.word _)) => some (.named identity)
  | .ok (.pair (.inLeft .word .unit) (.closure ..)) => some .anonymous
  | .ok (.pair (.inRight .unit (.word identity)) (.closure ..)) => some (.named identity)
  | _ => none

/-- Pure proof boundary for a public value: its private encoding is typed in
the session's current world and comes from resolving owned handles and deeply
authenticating source metadata. -/
def Session.Authenticates {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (sourceType : Ty) (value : Value) : Prop :=
  ∃ core type,
    encodeRaw fuel artifact.identity session.identity session.registry sourceType value = .ok core ∧
    artifact.context.checked.catalog.project sourceType = .ok type ∧
    Core.RuntimeValueHasType session.world core type artifact.context.checked.catalog.definitions

structure Authentication {artifact : Artifact} (session : Session artifact)
    (fuel : Nat) (sourceType : Ty) (value : Value) : Type where private mk ::
  typed : session.Authenticates fuel sourceType value

/-- Deep public validation returns a certificate, never a raw Core closure.
It checks ownership, function type, constructor metadata and every child value. -/
def Session.authenticate {artifact : Artifact} (session : Session artifact) (fuel : Nat)
    (sourceType : Ty) (value : Value) : Except Error (Authentication session fuel sourceType value) := do
  let projection ← (SourceCoreGeneralEntry.projectType artifact.context.checked sourceType).mapError fromCatalog
  match accepted : encodeRaw fuel artifact.identity session.identity session.registry sourceType value with
  | .error error => throw error
  | .ok core =>
      let validation ← validateAt artifact.context.checked.catalog.definitions session.world core projection.type
      pure ⟨⟨core, projection.type, accepted, projection.generated, validation.typed⟩⟩

private structure Frame (definitions : Core.DataEnvironment) (initial : Core.StoreTyping)
    (context : Core.Context) where
  world : Core.StoreTyping
  store : Core.Store
  environment : Core.Environment
  extension : Core.WorldExtends initial world
  stored : Core.RuntimeStoreHasTypes world store definitions
  typed : Core.RuntimeEnvironmentHasTypes world environment context definitions

private def Frame.push {definitions : Core.DataEnvironment} {initial : Core.StoreTyping} {context : Core.Context}
    (frame : Frame definitions initial context) (type : Core.Ty) (value : Core.Value)
    (typed : Core.RuntimeValueHasType frame.world value type definitions) :
    Frame definitions initial (Core.OptionalCell.referenceType type :: context) := by
  let payloadType := Core.OptionalCell.cellType type
  have extension : Core.WorldExtends frame.world (frame.world ++ [payloadType]) := ⟨_, rfl⟩
  exact {
    world := frame.world ++ [payloadType], store := frame.store ++ [.inRight .unit value]
    environment := .cellRef payloadType frame.store.length :: frame.environment
    extension := frame.extension.trans extension
    stored := frame.stored.allocate (.inRight typed)
    typed := .cons (.cellRef (by simp [← frame.stored.length_eq])) (frame.typed.weaken extension)
  }

private def arguments {artifact : Artifact} (session : Session artifact) (fuel : Nat)
    {context : Core.Context} (index : Nat)
    (frame : Frame artifact.context.checked.catalog.definitions session.world context) :
    (inputs : List (SourceCoreGeneralEntry.Input artifact.context.checked)) → List Value →
    Except Error (Frame artifact.context.checked.catalog.definitions session.world
      (SourceCoreGeneralEntry.inputContext inputs ++ context))
  | [], [] => pure (by simpa [SourceCoreGeneralEntry.inputContext] using frame)
  | input :: inputs, value :: values => do
      let encoded ← encode fuel artifact.identity session.identity (session.registry.weaken frame.extension) input.sourceType value
      have same : encoded.type = input.type := Except.ok.inj (encoded.generated.symm.trans input.projection.generated)
      let next ← arguments session fuel (index + 1)
        (frame.push input.type encoded.value (same ▸ encoded.typed)) inputs values
      pure (by simpa [SourceCoreGeneralEntry.inputContext, List.reverse_cons, List.append_assoc] using next)
  | inputs, values => throw ⟨[], .argumentCountMismatch (index + inputs.length) (index + values.length)⟩

structure Checkpoint (artifact : Artifact) where private mk ::
  private origin : Session artifact
  private identity : Token
  private sourceType : Ty
  private type : Core.Ty
  private generated : artifact.context.checked.catalog.project sourceType = .ok type
  private world : Core.StoreTyping
  private state : Core.State
  private stored : Core.RuntimeStoreHasTypes world state.store artifact.context.checked.catalog.definitions
  private typed : Core.StateHasType state (Core.LanguageResult.resultType type) artifact.context.checked.catalog.definitions
  private registry : Registry artifact.context world
  private extension : Core.WorldExtends origin.world world

/-- Append initialized parameter cells to the existing typed heap. Existing
closures keep their actual captures and all previous cell locations. -/
def Session.start {artifact : Artifact} (session : Session artifact) (key : Key)
    (values : List Value) (boundaryFuel : Nat := 1024) : Except Error (Checkpoint artifact) := do
  let entry ← match artifact.program.findEntry? key with
    | none => throw ⟨[], .missingEntry key⟩
    | some entry => pure entry
  if entry.inputs.length ≠ values.length then
    throw ⟨[], .argumentCountMismatch entry.inputs.length values.length⟩
  let initial : Frame artifact.context.checked.catalog.definitions session.world [] :=
    ⟨session.world, session.store, [], .refl _, session.stored, .nil⟩
  let frame ← arguments session boundaryFuel 0 initial entry.inputs values
  have environmentTyped : Core.RuntimeEnvironmentHasTypes frame.world frame.environment
      (SourceCoreGeneralEntry.inputContext entry.inputs) artifact.context.checked.catalog.definitions := by
    simpa using frame.typed
  pure {
    origin := session, identity := session.identity, sourceType := entry.sourceResultType, type := entry.resultType
    generated := entry.result.generated, world := frame.world
    state := .initial entry.body frame.environment frame.store, stored := frame.stored
    typed := .eval frame.stored environmentTyped entry.bodyTyped .nil
    registry := session.registry.weaken frame.extension
    extension := frame.extension
  }

structure Completion (artifact : Artifact) where private mk ::
  value : Value
  sourceType : Ty
  session : Session artifact
  boundaryFuel : Nat
  authenticated : session.Authenticates boundaryFuel sourceType value
  private origin : Session artifact
  private extension : Core.WorldExtends origin.world session.world

inductive Outcome (artifact : Artifact) where
  | succeeded (completion : Completion artifact)
  | failed (reason : Core.Word) (session : Session artifact)
  | outOfFuel (checkpoint : Checkpoint artifact)
  | exportError (error : Error) (session : Session artifact)

private def complete {artifact : Artifact} (checkpoint : Checkpoint artifact) (generation : Token)
    (fuel boundaryFuel : Nat) (value : Core.Value) (store : Core.Store)
    (finished : Core.runStateful fuel checkpoint.state = .done value store) : Outcome artifact := by
  let world := store.map Core.Value.type
  have stored : Core.RuntimeStoreHasTypes world store artifact.context.checked.catalog.definitions := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, _, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using typed
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨_, _, path⟩ := Core.runStateful_sound finished
    obtain ⟨future, extension, typed⟩ := path.preserve_store_world checkpoint.typed checkpoint.stored
    simpa only [typed.world_eq, Core.State.final, Core.State.store] using extension
  have typed : Core.RuntimeValueHasType world value (Core.LanguageResult.resultType checkpoint.type)
      artifact.context.checked.catalog.definitions := by
    obtain ⟨future, typedStore, typedValue⟩ := Core.well_typed_runStateful_preserves_result_type checkpoint.typed finished
    simpa only [typedStore.world_eq] using typedValue
  let registry := checkpoint.registry.weaken extension
  let session : Session artifact := ⟨checkpoint.identity, world, store, stored, registry⟩
  exact match decoded : Core.LanguageResult.decode? value with
  | none => False.elim (by
      obtain ⟨outcome, found, _⟩ := Core.LanguageResult.decode?_runtime_typed typed
      rw [decoded] at found
      cases found)
  | some outcome =>
      have related : outcome.RuntimeHasType world checkpoint.type artifact.context.checked.catalog.definitions := by
        obtain ⟨actual, found, related⟩ := Core.LanguageResult.decode?_runtime_typed typed
        rw [decoded] at found
        cases found
        exact related
      match outcome with
      | .failed reason => .failed reason session
      | .succeeded payload =>
          match exportValue boundaryFuel artifact.identity checkpoint.identity generation registry checkpoint.sourceType payload with
          | .error error => .exportError error session
          | .ok exported =>
              let session : Session artifact := ⟨checkpoint.identity, world, store, stored, exported.registry⟩
              .succeeded ⟨exported.value, checkpoint.sourceType, session, boundaryFuel,
                ⟨payload, checkpoint.type, exported.reencoded, checkpoint.generated, related⟩,
                checkpoint.origin, checkpoint.extension.trans extension⟩

private def suspend {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (state : Core.State) (executed : Core.runStateful fuel checkpoint.state = .outOfFuel state) : Checkpoint artifact := by
  let world := state.store.map Core.Value.type
  have extension : Core.WorldExtends checkpoint.world world := by
    obtain ⟨future, extension, stored⟩ :=
      Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored executed
    simpa only [stored.world_eq] using extension
  have stored : Core.RuntimeStoreHasTypes world state.store artifact.context.checked.catalog.definitions := by
    obtain ⟨future, _, stored⟩ :=
      Core.well_typed_runStateful_preserves_checkpoint_world checkpoint.typed checkpoint.stored executed
    simpa only [stored.world_eq] using stored
  exact {
    origin := checkpoint.origin, identity := checkpoint.identity, sourceType := checkpoint.sourceType, type := checkpoint.type
    generated := checkpoint.generated, world, state, stored
    typed := Core.well_typed_runStateful_preserves_checkpoint_type checkpoint.typed executed
    registry := checkpoint.registry.weaken extension
    extension := checkpoint.extension.trans extension
  }

/-- Obtain a genuine native exhaustion checkpoint, without exporting a result
or minting an identity. Successful and failed completions return none. -/
def Checkpoint.suspend? {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) :
    Option (Checkpoint artifact) :=
  match executed : Core.runStateful fuel checkpoint.state with
  | .outOfFuel state => some (suspend checkpoint fuel state executed)
  | _ => none

/-- Execution and resumption use only the saved native machine state. Every
branch carries either a typed checkpoint or a certified extended session heap.
An export error can reject source metadata; it is not a machine fault. -/
def Checkpoint.resume {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat)
    (boundaryFuel : Nat := 1024) : IO (Outcome artifact) := do
  match executed : Core.runStateful fuel checkpoint.state with
  | .done value store => pure (complete checkpoint (← mint) fuel boundaryFuel value store executed)
  | .fault _error _faultState =>
      pure (False.elim (Core.well_typed_runStateful_never_faults checkpoint.typed executed))
  | .outOfFuel state =>
      pure (.outOfFuel (suspend checkpoint fuel state executed))

def Session.run {artifact : Artifact} (session : Session artifact) (key : Key) (values : List Value)
    (fuel : Nat) (boundaryFuel : Nat := 1024) : IO (Except Error (Outcome artifact)) := do
  match session.start key values boundaryFuel with
  | .error error => pure (.error error)
  | .ok checkpoint => pure (.ok (← checkpoint.resume fuel boundaryFuel))

theorem Completion.typed {artifact : Artifact} (completion : Completion artifact) :
    completion.session.Authenticates completion.boundaryFuel completion.sourceType completion.value :=
  completion.authenticated

/-- Input allocation and every subsequent native step retain the old world's
location types. This certificate includes all resumptions since start. -/
theorem Completion.world_extension {artifact : Artifact} (completion : Completion artifact) :
    Core.WorldExtends completion.origin.world completion.session.world := completion.extension

theorem Checkpoint.world_extension {artifact : Artifact} (checkpoint : Checkpoint artifact) :
    Core.WorldExtends checkpoint.origin.world checkpoint.world := checkpoint.extension

/-- Native result/state typing for each finite amount of fuel. -/
def Checkpoint.NativeSafe {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) : Prop :=
  (Core.runStateful fuel checkpoint.state).HasType (Core.LanguageResult.resultType checkpoint.type)
    artifact.context.checked.catalog.definitions

theorem Checkpoint.native_safe {artifact : Artifact} (checkpoint : Checkpoint artifact) (fuel : Nat) :
    checkpoint.NativeSafe fuel := Core.well_typed_runStateful_has_type checkpoint.typed fuel

def Checkpoint.NativeResumes {artifact : Artifact} (checkpoint next : Checkpoint artifact)
    (spent additional : Nat) : Prop :=
  Core.runStateful additional next.state = Core.runStateful (spent + additional) checkpoint.state

theorem Checkpoint.suspend?_fuel_resume {artifact : Artifact} {checkpoint next : Checkpoint artifact}
    {spent : Nat} (exhausted : checkpoint.suspend? spent = some next) (additional : Nat) :
    checkpoint.NativeResumes next spent additional := by
  unfold Checkpoint.suspend? at exhausted
  split at exhausted
  · cases exhausted
    exact Core.runStateful_resume (by assumption) additional
  · cases exhausted

/-- The heap invariant is a pure Core theorem; fresh token allocation is not
a premise of runtime type safety. -/
theorem Session.heap_typed {artifact : Artifact} (session : Session artifact) :
    Core.RuntimeStoreHasTypes session.world session.store artifact.context.checked.catalog.definitions :=
  session.stored

end Solcore.Frontend.SourceCoreSession
