import Solcore.Frontend.SourceCoreCompatibleCatalog
import Solcore.Frontend.SourceCoreDataValues
import Solcore.Frontend.SourceRuntimeValues

/-! Typed data encoding for the source-compatible native representation.
Raw metadata is authenticated and interned in the owning registry, rather than
canonicalized away. Actual mapping headers determine the transported default.
Every accepted public encoding and decoding checks the complete native tree
and its reverse image. Functions require a later authenticated handle adapter;
closures, references and host capabilities cannot enter this data boundary.

The strict owned codec and its catalog retain their existing interpretation.
This module does not import or evaluate a source runtime expression. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleValues

open TypeSystem SourceInference
abbrev Value := SourceCoreDataValues.Value
abbrev Metadata := SourceCoreRawMetadata.Metadata
abbrev Registry := SourceCoreRawMetadata.Registry
abbrev Checked := SourceCoreCompatibleCatalog.Checked

structure Context where
  checked : Checked
  registry : Registry
  extension : SourceCoreRawMetadata.Extends checked.staticRegistry registry

def Context.initial (checked : Checked) : Context := ⟨checked, checked.staticRegistry, .refl _⟩

theorem Context.registryOwner (context : Context) : context.registry.signatures = context.checked.signatures :=
  context.extension.signatures.trans context.checked.registryOwner

structure Extended (before : Registry) (α : Type) where
  registry : Registry
  preserves : SourceCoreRawMetadata.Extends before registry
  value : α

def Extended.pure (registry : Registry) {α : Type} (value : α) : Extended registry α :=
  ⟨registry, .refl registry, value⟩

def Context.extend (context : Context) (registry : Registry)
    (extension : SourceCoreRawMetadata.Extends context.registry registry) : Context :=
  ⟨context.checked, registry, context.extension.trans extension⟩

abbrev PathStep := SourceCoreDataValues.PathStep

inductive ErrorCode where
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | metadata (error : SourceCoreRawMetadata.Error)
  | rawValue (error : SourceCoreGeneralEntry.ValueError)
  | exhausted
  | sourceTypeMismatch (expected actual : Ty)
  | coreShapeMismatch (expected actual : Core.Ty)
  | metadataKindMismatch (id : Core.Word)
  | unknownMetadata (id : Core.Word)
  | constructorMismatch (constructor : Core.ConstructorId)
  | payloadCountMismatch (expected actual : Nat)
  | malformedPayload
  | transportedDefaultMismatch
  | functionHandleRequired
  | externalReferenceUnsupported
  | externalHostUnsupported
  | nonCanonicalCoreValue
  | nonCanonicalSourceValue
  deriving Repr, DecidableEq

structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr, DecidableEq

def Error.at (step : PathStep) (error : Error) : Error := {error with path := step :: error.path}
private def catalogError (error : SourceCoreCompatibleCatalog.Error) : Error := ⟨[], .catalog error⟩
private def metadataError (error : SourceCoreRawMetadata.Error) : Error := ⟨[], .metadata error⟩
private def rawError (error : SourceCoreGeneralEntry.ValueError) : Error :=
  match error.code with
  | .functionHandleRequired => ⟨error.path.map SourceCoreDataValues.PathStep.rawCore, .functionHandleRequired⟩
  | .externalReferenceUnsupported => ⟨error.path.map SourceCoreDataValues.PathStep.rawCore, .externalReferenceUnsupported⟩
  | .externalHostUnsupported => ⟨error.path.map SourceCoreDataValues.PathStep.rawCore, .externalHostUnsupported⟩
  | _ => ⟨error.path.map SourceCoreDataValues.PathStep.rawCore, .rawValue error⟩

private def identity (checked : Checked) (type : Ty) : Except Error Core.DataTypeId :=
  match checked.catalog.identity? type with
  | some identity => pure identity
  | none => throw (catalogError (.catalog (.missingRepresentation type)))

private def compatible (expected actual : Ty) : Except Error Unit :=
  unless SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual do
    throw ⟨[], .sourceTypeMismatch expected actual⟩

private def lookup (context : Context) (expected : Ty) (id : Core.Word) : Except Error Metadata := do
  let metadata ← match context.registry.lookup id with
    | some metadata => pure metadata
    | none => throw ⟨[], .unknownMetadata id⟩
  discard <| compatible expected metadata.type
  pure metadata

/-- Project the data-only values constructed by the shared pure default
function. This does not authenticate caller values or import source closures. -/
def defaultFromSource? : SourceTypedRuntime.Value → Option Value
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .product left right => do pure (.product (← defaultFromSource? left) (← defaultFromSource? right))
  | .proxy inner => some (.proxy inner)
  | .mapping key value [] => some (.mapping key value [])
  | _ => none

/-- Use the shared pure source default at the actual raw header, then project
its data carrier. Raw proxy identity and nested mapping headers survive. -/
def defaultValue? (fuel : Nat) (type : Ty) : Option Value :=
  (SourceTypedRuntime.defaultValue? fuel type).bind defaultFromSource?

theorem defaultValue?_shared (fuel : Nat) (type : Ty) :
    defaultValue? fuel type = (SourceTypedRuntime.defaultValue? fuel type).bind defaultFromSource? := rfl

/-- Carrier projection cannot turn an existing source default into absence. -/
theorem defaultFromSource?_complete (fuel : Nat) (type : Ty) (source : SourceTypedRuntime.Value)
    (found : SourceTypedRuntime.defaultValue? fuel type = some source) :
    ∃ value, defaultFromSource? source = some value := by
  induction fuel generalizing type source with
  | zero => simp [SourceTypedRuntime.defaultValue?] at found
  | succ fuel inductionHypothesis =>
      cases type with
      | constructor id =>
          cases id with
          | builtin builtin =>
              cases builtin <;> simp [SourceTypedRuntime.defaultValue?] at found <;>
                subst source <;> exact ⟨_, rfl⟩
          | declaration id => simp [SourceTypedRuntime.defaultValue?] at found
      | product left right =>
          cases leftFound : SourceTypedRuntime.defaultValue? fuel left with
          | none => simp [SourceTypedRuntime.defaultValue?, leftFound] at found
          | some leftValue =>
              cases rightFound : SourceTypedRuntime.defaultValue? fuel right with
              | none => simp [SourceTypedRuntime.defaultValue?, leftFound, rightFound] at found
              | some rightValue =>
                  simp [SourceTypedRuntime.defaultValue?, leftFound, rightFound] at found
                  subst source
                  obtain ⟨left, leftProjected⟩ := inductionHypothesis _ _ leftFound
                  obtain ⟨right, rightProjected⟩ := inductionHypothesis _ _ rightFound
                  exact ⟨.product left right, by simp [defaultFromSource?, leftProjected, rightProjected]⟩
      | proxy inner =>
          simp [SourceTypedRuntime.defaultValue?] at found
          subst source
          exact ⟨.proxy inner, rfl⟩
      | mapping key value =>
          simp [SourceTypedRuntime.defaultValue?] at found
          subst source
          exact ⟨.mapping key value [], rfl⟩
      | comptime inner => exact inductionHypothesis _ _ found
      | «variable» _ | parameter _ | application _ _ | function _ _ | error =>
          simp [SourceTypedRuntime.defaultValue?] at found

theorem defaultValue?_absent_iff (fuel : Nat) (type : Ty) :
    defaultValue? fuel type = none ↔ SourceTypedRuntime.defaultValue? fuel type = none := by
  cases found : SourceTypedRuntime.defaultValue? fuel type with
  | none => simp [defaultValue?, found]
  | some source =>
      obtain ⟨value, projected⟩ := defaultFromSource?_complete fuel type source found
      simp [defaultValue?, found, projected]

mutual
  def encodeRaw : (fuel : Nat) → Checked → (registry : Registry) → Ty → Value →
      Except Error (Extended registry Core.Value)
    | 0, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, checked, registry, expected, value => do
      match SourceCoreRawMetadata.runtimeType expected, value with
      | .function .., _ => throw ⟨[], .functionHandleRequired⟩
      | .constructor (.builtin .unit), .unit => pure (Extended.pure registry .unit)
      | .constructor (.builtin .bool), .bool value => pure (Extended.pure registry (.bool value))
      | .constructor (.builtin .word), .word value => pure (Extended.pure registry (.word value))
      | .constructor (.builtin .integer), .integer value => pure (Extended.pure registry (.integer value))
      | .product leftType rightType, .product left right => do
          let left ← (encodeRaw fuel checked registry leftType left).mapError (Error.at .productLeft)
          let right ← (encodeRaw fuel checked left.registry rightType right).mapError (Error.at .productRight)
          pure ⟨right.registry, left.preserves.trans right.preserves, .pair left.value right.value⟩
      | .proxy _, .proxy actual => do
          let registered ← (registry.intern expected (.proxy actual)).mapError metadataError
          let owner ← identity checked expected
          pure ⟨registered.registry, registered.preserves, .constructed ⟨owner, 0⟩ (.word registered.id)⟩
      | .mapping keyType valueType, .mapping actualKey actualValue entries => do
          let registered ← (registry.intern expected (.mapping actualKey actualValue)).mapError metadataError
          let layout ← (checked.catalog.mappingLayout keyType valueType).mapError catalogError
          let entries ← encodeEntriesRaw fuel checked registered.registry actualKey actualValue layout entries 0
          let fallback ← encodeDefaultRaw fuel checked entries.registry actualValue layout.valueType
          pure ⟨fallback.registry, registered.preserves.trans (entries.preserves.trans fallback.preserves),
            .pair (.word registered.id) (.pair fallback.value entries.value)⟩
      | _, .constructed instantiation payloads => do
          let registered ← (registry.intern expected (.constructor instantiation)).mapError metadataError
          let constructor ← (checked.resolveConstructor instantiation).mapError catalogError
          let payloads ← encodePayloadsRaw fuel checked registered.registry instantiation.payloadTypes payloads 0
          pure ⟨payloads.registry, registered.preserves.trans payloads.preserves,
            .constructed constructor (.pair (.word registered.id) payloads.value)⟩
      | _, value => throw ⟨[], .sourceTypeMismatch expected value.type⟩

  def encodePayloadsRaw (fuel : Nat) (checked : Checked) (registry : Registry)
      (types : List Ty) (values : List Value) (index : Nat) : Except Error (Extended registry Core.Value) := do
    unless types.length = values.length do throw ⟨[], .payloadCountMismatch types.length values.length⟩
    match fuel, types, values with
    | _, [], [] => pure (Extended.pure registry .unit)
    | 0, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, [type], [value] => (encodeRaw fuel checked registry type value).mapError (Error.at (.constructorPayload index))
    | fuel + 1, type :: types, value :: values => do
        let value ← (encodeRaw fuel checked registry type value).mapError (Error.at (.constructorPayload index))
        let tail ← encodePayloadsRaw fuel checked value.registry types values (index + 1)
        pure ⟨tail.registry, value.preserves.trans tail.preserves, .pair value.value tail.value⟩
    | _, _, _ => throw ⟨[], .payloadCountMismatch types.length values.length⟩

  def encodeEntriesRaw : (fuel : Nat) → Checked → (registry : Registry) → Ty → Ty →
      Core.OrderedMapping.Layout → List (Value × Value) → Nat → Except Error (Extended registry Core.Value)
    | _, _, registry, _, _, layout, [], _ => pure (Extended.pure registry (Core.OrderedMapping.encode layout []))
    | 0, _, _, _, _, _, _ :: _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, checked, registry, keyType, valueType, layout, (key, value) :: rest, index => do
        let key ← (encodeRaw fuel checked registry keyType key).mapError (Error.at (.mappingKey index))
        let value ← (encodeRaw fuel checked key.registry valueType value).mapError (Error.at (.mappingValue index))
        let tail ← encodeEntriesRaw fuel checked value.registry keyType valueType layout rest (index + 1)
        pure ⟨tail.registry, key.preserves.trans (value.preserves.trans tail.preserves),
          .constructed layout.consConstructor (.pair (.pair key.value value.value) tail.value)⟩

  def encodeDefaultRaw (fuel : Nat) (checked : Checked) (registry : Registry) (rawType : Ty) (nativeType : Core.Ty) :
      Except Error (Extended registry Core.Value) := do
    match defaultValue? (rawType.size + 1) rawType with
    | none => pure (Extended.pure registry (.inLeft nativeType .unit))
    | some value =>
        let encoded ← encodeRaw fuel checked registry rawType value
        pure ⟨encoded.registry, encoded.preserves, .inRight .unit encoded.value⟩
end

mutual
  def decodeRaw : Nat → Context → Ty → Core.Value → Except Error Value
    | 0, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, expected, value => do
      match SourceCoreRawMetadata.runtimeType expected, value with
      | _, .closure .. => throw ⟨[], .functionHandleRequired⟩
      | _, .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
      | _, .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
      | .function .., _ => throw ⟨[], .functionHandleRequired⟩
      | .constructor (.builtin .unit), .unit => pure .unit
      | .constructor (.builtin .bool), .bool value => pure (.bool value)
      | .constructor (.builtin .word), .word value => pure (.word value)
      | .constructor (.builtin .integer), .integer value => pure (.integer value)
      | .product leftType rightType, .pair left right => do
          let left ← (decodeRaw fuel context leftType left).mapError (Error.at .productLeft)
          let right ← (decodeRaw fuel context rightType right).mapError (Error.at .productRight)
          pure (.product left right)
      | .proxy _, .constructed constructor (.word id) => do
          let metadata ← lookup context expected id
          let inner ← match metadata with
            | .proxy inner => pure inner
            | _ => throw ⟨[], .metadataKindMismatch id⟩
          let owner ← identity context.checked expected
          unless constructor = ⟨owner, 0⟩ do throw ⟨[], .constructorMismatch constructor⟩
          pure (.proxy inner)
      | .mapping _ _, .pair (.word id) (.pair fallback stored) => do
          let metadata ← lookup context expected id
          let (key, valueType) ← match metadata with
            | .mapping key value => pure (key, value)
            | _ => throw ⟨[], .metadataKindMismatch id⟩
          let layout ← (context.checked.catalog.mappingLayout key valueType).mapError catalogError
          let entries ← decodeEntriesRaw fuel context key valueType layout stored 0
          let actualDefault ← decodeDefaultRaw fuel context valueType layout.valueType fallback
          unless actualDefault = defaultValue? (valueType.size + 1) valueType do
            throw ⟨[], .transportedDefaultMismatch⟩
          pure (.mapping key valueType entries)
      | _, .constructed constructor (.pair (.word id) payload) => do
          let metadata ← lookup context expected id
          let instantiation ← match metadata with
            | .constructor instantiation => pure instantiation
            | _ => throw ⟨[], .metadataKindMismatch id⟩
          let authentic ← (context.checked.resolveConstructor instantiation).mapError catalogError
          unless constructor = authentic do throw ⟨[], .constructorMismatch constructor⟩
          let payloads ← decodePayloadsRaw fuel context instantiation.payloadTypes payload 0
          pure (.constructed instantiation payloads)
      | _, value =>
          let type ← (context.checked.catalog.project expected).mapError catalogError
          throw ⟨[], .coreShapeMismatch type value.type⟩

  def decodePayloadsRaw : Nat → Context → List Ty → Core.Value → Nat → Except Error (List Value)
    | _, _, [], .unit, _ => pure []
    | 0, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, [type], value, index => do
        pure [← (decodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))]
    | fuel + 1, context, type :: types, .pair value rest, index => do
        let value ← (decodeRaw fuel context type value).mapError (Error.at (.constructorPayload index))
        let rest ← decodePayloadsRaw fuel context types rest (index + 1)
        pure (value :: rest)
    | _, _, _, _, _ => throw ⟨[], .malformedPayload⟩

  def decodeEntriesRaw : Nat → Context → Ty → Ty → Core.OrderedMapping.Layout → Core.Value →
      Nat → Except Error (List (Value × Value))
    | 0, _, _, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, context, keyType, valueType, layout, stored, index => do
        match stored with
        | .constructed constructor .unit =>
            unless constructor = layout.nilConstructor do throw ⟨[], .constructorMismatch constructor⟩
            pure []
        | .constructed constructor (.pair (.pair key value) rest) =>
            unless constructor = layout.consConstructor do throw ⟨[], .constructorMismatch constructor⟩
            let key ← (decodeRaw fuel context keyType key).mapError (Error.at (.mappingKey index))
            let value ← (decodeRaw fuel context valueType value).mapError (Error.at (.mappingValue index))
            let rest ← decodeEntriesRaw fuel context keyType valueType layout rest (index + 1)
            pure ((key, value) :: rest)
        | .closure .. => throw ⟨[], .functionHandleRequired⟩
        | .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
        | .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
        | _ => throw ⟨[], .malformedPayload⟩

  def decodeDefaultRaw (fuel : Nat) (context : Context) (rawType : Ty) (nativeType : Core.Ty)
      (value : Core.Value) : Except Error (Option Value) := do
    match value with
    | .inLeft annotation .unit =>
        unless annotation = nativeType do throw ⟨[], .transportedDefaultMismatch⟩
        pure none
    | .inRight .unit payload => pure (some (← decodeRaw fuel context rawType payload))
    | _ => throw ⟨[], .transportedDefaultMismatch⟩
end

structure Decoded (fuel : Nat) (context : Context) (expected : Ty) (core : Core.Value) where private mk ::
  private sourceValue : Value
  private nativeType : Core.Ty
  private projection : context.checked.catalog.project expected = .ok nativeType
  private typeProof : ∀ world, Core.RuntimeValueHasType world core nativeType context.checked.catalog.definitions
  private reversed : decodeRaw fuel context expected core = .ok sourceValue
  private generated : ∃ encoded : Extended context.registry Core.Value,
    encodeRaw fuel context.checked context.registry expected sourceValue = .ok encoded ∧ encoded.value = core

namespace Decoded
def source {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) : Value := decoded.sourceValue
def type {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) : Core.Ty := decoded.nativeType
theorem projected {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) : context.checked.catalog.project expected = .ok decoded.type := decoded.projection
theorem typed {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world core decoded.type context.checked.catalog.definitions := decoded.typeProof world
theorem decodeRaw_eq {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) : decodeRaw fuel context expected core = .ok decoded.source := decoded.reversed
theorem reencodes {fuel : Nat} {context : Context} {expected : Ty} {core : Core.Value}
    (decoded : Decoded fuel context expected core) :
    ∃ encoded : Extended context.registry Core.Value,
      encodeRaw fuel context.checked context.registry expected decoded.source = .ok encoded ∧ encoded.value = core :=
  decoded.generated
end Decoded

def decodeCertified (fuel : Nat) (context : Context) (expected : Ty) (core : Core.Value) :
    Except Error (Decoded fuel context expected core) := do
  match projected : context.checked.catalog.project expected with
  | .error error => throw (catalogError error)
  | .ok type =>
      let validated ← (SourceCoreGeneralEntry.validateValue context.checked.catalog.definitions core type).mapError rawError
      match reversed : decodeRaw fuel context expected core with
      | .error error => throw error
      | .ok value =>
          match generated : encodeRaw fuel context.checked context.registry expected value with
          | .error error => throw error
          | .ok rebuilt =>
              if canonical : rebuilt.value = core then
                pure (.mk value type projected validated.typed reversed ⟨rebuilt, generated, canonical⟩)
              else throw ⟨[], .nonCanonicalCoreValue⟩

def decode (fuel : Nat) (context : Context) (expected : Ty) (core : Core.Value) : Except Error Value :=
  (decodeCertified fuel context expected core).map (·.source)

structure Encoded (fuel : Nat) (context : Context) (expected : Ty) (source : Value) where private mk ::
  private encoded : Extended context.registry Core.Value
  private certificate : Decoded fuel (context.extend encoded.registry encoded.preserves) expected encoded.value
  private decoded : decodeCertified fuel (context.extend encoded.registry encoded.preserves) expected encoded.value = .ok certificate
  private sameSource : certificate.source = source

namespace Encoded
def value {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : Core.Value := encoded.encoded.value
def context {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : Context :=
  context.extend encoded.encoded.registry encoded.encoded.preserves
def type {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : Core.Ty := encoded.certificate.type
theorem projected {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : context.checked.catalog.project expected = .ok encoded.type :=
  encoded.certificate.projected
theorem typed {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) (world : Core.StoreTyping) :
    Core.RuntimeValueHasType world encoded.value encoded.type context.checked.catalog.definitions :=
  encoded.certificate.typed world
theorem preserves {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : SourceCoreRawMetadata.Extends context.registry encoded.context.registry :=
  encoded.encoded.preserves
theorem decodeRaw_eq {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : decodeRaw fuel encoded.context expected encoded.value = .ok source := by
  have reversed := encoded.certificate.decodeRaw_eq
  rw [encoded.sameSource] at reversed
  exact reversed
theorem decode_encode {fuel : Nat} {context : Context} {expected : Ty} {source : Value}
    (encoded : Encoded fuel context expected source) : decode fuel encoded.context expected encoded.value = .ok source := by
  unfold decode Encoded.context Encoded.value
  rw [encoded.decoded]
  change Except.ok encoded.certificate.source = Except.ok source
  rw [encoded.sameSource]
end Encoded

def encode (fuel : Nat) (context : Context) (expected : Ty) (value : Value) :
    Except Error (Encoded fuel context expected value) := do
  let encoded ← encodeRaw fuel context.checked context.registry expected value
  let updated := context.extend encoded.registry encoded.preserves
  match certified : decodeCertified fuel updated expected encoded.value with
  | .error error => throw error
  | .ok decoded =>
      if same : decoded.source = value then pure (.mk encoded decoded certified same)
      else throw ⟨[], .nonCanonicalSourceValue⟩

end Solcore.Frontend.SourceCoreCompatibleValues
