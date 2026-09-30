import Solcore.Frontend.SourceCoreGeneralEntry

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

private def namedIdentity (context : Context) (type : Ty) : Except Error Core.DataTypeId := do
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
