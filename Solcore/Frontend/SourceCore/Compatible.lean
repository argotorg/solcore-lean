import Solcore.Frontend.SourceCore.CompatibleCatalog
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.Frontend.Internal.RuntimeValues
import Solcore.Frontend.SourceCore.DataPlaces
import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceCore.RawMetadata

/-!
# Compatible lowering

The source-compatible profile: values, data leaves and places. Main declarations:
`SourceCoreCompatibleValues.Context`, `SourceCoreCompatibleDataExpressions`,
`SourceCoreCompatibleDataPlaces`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleValues
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
      | .constructor (.builtin (.fixed type)), .word value =>
          if type.canonical value.val then pure (Extended.pure registry (.word value))
          else throw ⟨[], .nonCanonicalSourceValue⟩
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
      | .constructor (.builtin (.fixed _)), .word value => pure (.word value)
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

namespace Solcore.Frontend.SourceCoreCompatibleValues
open TypeSystem SourceInference

private theorem lookup_of_actual {context : Context} {expected : Ty} {id : Core.Word} {item : Metadata}
    (found : context.registry.lookup id = some item)
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType item.type) :
    lookup context expected id = .ok item := by
  simp only [lookup, found, compatible, same, ↓reduceIte, pure, Except.pure, bind, Except.bind]
  rfl

/-- Proxy conversion uses the authenticated original metadata ID. -/
theorem decode_proxy_at (context : Context) {expected inner : Ty} {owner : Core.DataTypeId} {id : Core.Word}
    (found : context.registry.lookup id = some (.proxy inner))
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.proxy inner))
    (identityAt : context.checked.catalog.identity? expected = some owner) (fuel : Nat) :
    decodeRaw (fuel + 1) context expected (.constructed ⟨owner, 0⟩ (.word id)) = .ok (.proxy inner) := by
  have metadata := lookup_of_actual found same
  unfold decodeRaw
  rw [same]
  simp only [SourceCoreRawMetadata.runtimeType, metadata, identity, identityAt,
    pure, Except.pure, bind, Except.bind, ↓reduceIte]

theorem encode_proxy_at (checked : Checked) {registry : Registry} {expected inner : Ty}
    {owner : Core.DataTypeId} {id : Core.Word}
    (found : registry.lookup id = some (.proxy inner))
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.proxy inner))
    (identityAt : checked.catalog.identity? expected = some owner) (fuel : Nat) :
    encodeRaw (fuel + 1) checked registry expected (.proxy inner) =
      .ok (.pure registry (.constructed ⟨owner, 0⟩ (.word id))) := by
  obtain ⟨inserted, interned, registryEq, idEq⟩ := SourceCoreRawMetadata.Registry.intern_of_lookup found same
  unfold encodeRaw
  rw [same]
  simp only [SourceCoreRawMetadata.runtimeType, interned, Except.mapError,
    identity, identityAt, pure, Except.pure, bind, Except.bind]
  simp only [registryEq, idEq]
  rfl

theorem decode_mapping_at (context : Context) {expected key value : Ty} {id : Core.Word}
    {layout : Core.OrderedMapping.Layout} {stored fallback : Core.Value}
    {entries : List (Value × Value)} {fuel : Nat}
    (found : context.registry.lookup id = some (.mapping key value))
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.mapping key value))
    (layoutAt : context.checked.catalog.mappingLayout key value = .ok layout)
    (rows : decodeEntriesRaw fuel context key value layout stored 0 = .ok entries)
    (defaultAt : decodeDefaultRaw fuel context value layout.valueType fallback =
      .ok (defaultValue? (value.size + 1) value)) :
    decodeRaw (fuel + 1) context expected (.pair (.word id) (.pair fallback stored)) =
      .ok (.mapping key value entries) := by
  have metadata := lookup_of_actual found same
  unfold decodeRaw
  rw [same]
  simp only [SourceCoreRawMetadata.runtimeType, metadata, layoutAt, rows, defaultAt,
    pure, Except.pure, bind, Except.bind, Except.mapError, ↓reduceIte]

theorem encode_mapping_at (checked : Checked) {registry : Registry} {expected key value : Ty}
    {id : Core.Word} {layout : Core.OrderedMapping.Layout} {stored fallback : Core.Value}
    {entries : List (Value × Value)} {fuel : Nat}
    (found : registry.lookup id = some (.mapping key value))
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType (.mapping key value))
    (layoutAt : checked.catalog.mappingLayout (SourceCoreRawMetadata.runtimeType key)
      (SourceCoreRawMetadata.runtimeType value) = .ok layout)
    (rows : encodeEntriesRaw fuel checked registry key value layout entries 0 = .ok (.pure registry stored))
    (defaultAt : encodeDefaultRaw fuel checked registry value layout.valueType = .ok (.pure registry fallback)) :
    encodeRaw (fuel + 1) checked registry expected (.mapping key value entries) =
      .ok (.pure registry (.pair (.word id) (.pair fallback stored))) := by
  obtain ⟨inserted, interned, registryEq, idEq⟩ := SourceCoreRawMetadata.Registry.intern_of_lookup found same
  unfold encodeRaw
  rw [same]
  simp only [SourceCoreRawMetadata.runtimeType, interned, Except.mapError,
    layoutAt, pure, Except.pure, bind, Except.bind]
  have rowsAt : encodeEntriesRaw fuel checked inserted.registry key value layout entries 0 =
      .ok (.pure inserted.registry stored) := by rw [registryEq]; exact rows
  have fallbackAt : encodeDefaultRaw fuel checked inserted.registry value layout.valueType =
      .ok (.pure inserted.registry fallback) := by rw [registryEq]; exact defaultAt
  simp only [rowsAt, Extended.pure, fallbackAt]
  simp only [registryEq, idEq]

end Solcore.Frontend.SourceCoreCompatibleValues
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleDataExpressions
/-! Data leaves and policy factories for the separate source-compatible
profile. Original closed metadata is resolved in the compile-time registry;
input extensions preserve those IDs. Nominal members select the stored fields,
mapping lookups transport the actual header default, and mapping reads create
an empty value only when the source cell's declared type is a bare mapping.

Recursion, calls and control flow belong to the existing caller-owned policy.
No source evaluator or strict-catalog cast is used. Projected assignments and
pattern lowering are separate compatible adapters. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleDataExpressions
open SourceInference
abbrev Context := SourceCoreCompatibleValues.Context
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error
abbrev LoweredExpr := SourceCoreBasic.LoweredExpr
abbrev ExpressionLowerer := SourceCoreFunctions.ExpressionLowerer

def projectType (checked : Checked) (site : SourceCoreElaboration.ErrorSite)
    (type : TypeSystem.Ty) : Except Error Core.Ty :=
  (checked.project type).map (·.type) |>.mapError
    (fun _ => .typeProjection ⟨site, .unsupportedType type⟩)

def readExpression (checked : Checked) (source : TypedSource) (id : ExpressionId) :
    Except Error (ExpressionNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupExpression? id with
    | some node => pure node | none => throw (.missingExpression id)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  pure (node, ← projectType checked (.occurrence id.occurrence) node.type)

def readStatement (checked : Checked) (source : TypedSource) (id : StatementId) :
    Except Error (StatementNode × Core.Ty) := do
  if id.occurrence.owner ≠ source.owner then throw (.ownerMismatch source.owner id.occurrence.owner)
  let node ← match source.lookupStatement? id with
    | some node => pure node | none => throw (.missingStatement id)
  pure (node, ← projectType checked (.occurrence id.occurrence) node.type)

def lowerBinder (checked : Checked) (source : TypedSource) (scope : Scope)
    (binder : TypedBinder) : Except Error Core.Ty := do
  if binder.id.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.id.owner)
  unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding binder.id)
  unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent binder.id)
  if binder.comptime && !checked.catalog.callableContracts then throw (.comptimeBinding binder.id)
  if scope.any (fun entry => decide (entry.1 = binder.id)) then throw (.duplicateBinding binder.id)
  projectType checked (.binder binder.id) binder.scheme.body

def lowerAssignment (checked : Checked) (source : TypedSource) (scope : Scope)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) : Except Error (Nat × Core.Ty) := do
  if operator ≠ .equal then throw (.unsupportedAssignmentOperator operator)
  let binder := assignment.target.root
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent binder)
  unless assignment.target.projections.isEmpty do throw (.projectedAssignment binder)
  let (index, type) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry | none => throw (.missingBinding binder)
  let projected ← projectType checked (.binder binder) assignment.target.type
  SourceCoreBasic.ensureType (.binder binder) type projected
  pure (index, type)

private def unsupported (node : ExpressionNode) : Error := .unsupportedExpression node.id node.form

private def metadataId (context : Context) (node : ExpressionNode)
    (metadata : SourceCoreRawMetadata.Metadata) : Except Error Core.Word :=
  match context.registry.id? metadata with
  | some id => pure id | none => throw (unsupported node)

def quote : Core.Value → Option Core.Expr
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .pair left right => do pure (.pair (← quote left) (← quote right))
  | .inLeft type value => do pure (.inLeft type (← quote value))
  | .inRight type value => do pure (.inRight type (← quote value))
  | .constructed constructor value => do pure (.construct constructor (← quote value))
  | _ => none

/-- Code generation does not extend the frozen static registry. A prepared
inventory must already contain the metadata of every emitted literal. -/
def staticValue (fuel : Nat) (context : Context) (node : ExpressionNode)
    (type : TypeSystem.Ty) (source : SourceCoreCompatibleValues.Value) : Except Error Core.Expr := do
  let encoded ← (SourceCoreCompatibleValues.encode fuel context type source).mapError (fun _ => unsupported node)
  unless encoded.context.registry.entries = context.registry.entries do throw (unsupported node)
  match quote encoded.value with
  | some expression => pure expression | none => throw (unsupported node)

def construct (constructor : Core.ConstructorId) (metadata : Core.Word) (arguments : Core.Expr) : Core.Expr :=
  Core.LanguageResult.bind (.namedData constructor.owner) arguments
    (Core.LanguageResult.success (.construct constructor (.pair (.word metadata) (.var 0))))

/-- The absent path computes its empty literal once before writing it to the
shared optional cell. Existing initialized mappings retain their header. -/
def readMapping (reference empty : Core.Expr) : Core.Expr :=
  .letE reference
    (.caseE (.loadCell (.var 0))
      (.letE (empty.weakenAt 0 |>.weakenAt 0)
        (.letE (.storeCell (.var 2) (.inRight .unit (.var 0)))
          (Core.LanguageResult.success (.var 1))))
      (Core.LanguageResult.success (.var 0)))

def lowerRead (fuel : Nat) (context : Context) (source : TypedSource) (scope : Scope)
    (id : ExpressionId) (reason : Core.Word) : Except Error Core.Expr := do
  let (node, type) ← readExpression context.checked source id
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder | _ => throw (unsupported node)
  if binder.owner ≠ source.owner then throw (.ownerMismatch source.owner binder.owner)
  let (index, payload) ← match SourceCoreLocalCell.lookup? scope binder with
    | some entry => pure entry | none => throw (.missingBinding binder)
  SourceCoreBasic.ensureType (.occurrence id.occurrence) type payload
  let declared ← SourceCoreDataPlaces.rootBinder source binder
  match declared.scheme.body with
  | .mapping key value =>
      let empty ← staticValue fuel context node declared.scheme.body (.mapping key value [])
      pure (readMapping (.var index) empty)
  | _ => pure (Core.OptionalCell.read payload (.var index) reason)

/-- The actual member branch generator, also used to extract static lowering
certificates for the raw constructor metadata and selected payload. -/
def memberBranches (context : Context) (node : ExpressionNode)
    (baseType : TypeSystem.Ty) (result : Core.Ty) (index : Nat) :
    Except Error (Core.DataTypeId × List Core.Expr) := do
  let baseType := SourceCoreRawMetadata.runtimeType baseType
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts baseType with
    | some parts => pure parts | none => throw (unsupported node)
  let signature ← match context.checked.signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | [signature] => pure signature | _ => throw (unsupported node)
  unless signature.parameters.length = arguments.length && !signature.constructors.isEmpty do throw (unsupported node)
  let dataType ← match context.checked.catalog.identity? baseType with
    | some identity => pure identity | none => throw (unsupported node)
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  let branches ← signature.constructors.zipIdx.mapM fun (constructor, position) => do
    let payloadTypes := constructor.payloadTypes.map substitution.apply
    let instantiation : DataConstructorInstantiation := ⟨constructor.id, substitution, payloadTypes, baseType⟩
    let resolved ← (context.checked.resolveConstructor instantiation).mapError (fun _ => unsupported node)
    unless resolved.owner = dataType && resolved.index = position do throw (unsupported node)
    let selected ← match payloadTypes[index]? with
      | some selected => projectType context.checked (.occurrence node.id.occurrence) selected
      | none => throw (unsupported node)
    SourceCoreBasic.ensureType (.occurrence node.id.occurrence) result selected
    let payloads ← payloadTypes.mapM (projectType context.checked (.occurrence node.id.occurrence))
    pure (Core.LanguageResult.success (SourceCoreDataExpressions.projectPacked index payloads (.second (.var 0))))
  pure (dataType, branches)

/-- Base and key effects complete before comparator preparation. Missing
entries select the transported default of the actual evaluated mapping. -/
def index (layout : Core.OrderedMapping.Layout) (comparison base key : Core.Expr)
    (missingBase : Core.Word) : Core.Expr :=
  Core.LanguageResult.bind layout.valueType base
    (Core.LanguageResult.bind layout.valueType (key.weakenAt 0)
      (SourceCoreMappingWithDefault.lookup layout missingBase
        (comparison.weakenAt 0 |>.weakenAt 0) (.var 1) (.var 0)))

theorem index_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {layout : Core.OrderedMapping.Layout} {comparison base key : Core.Expr} (missingBase : Core.Word)
    (registered : layout.Registered definitions)
    (comparisonTyped : Core.HasType environment comparison
      (.function (.product layout.keyType layout.keyType) .bool) definitions)
    (baseTyped : Core.HasType environment base
      (Core.LanguageResult.resultType (SourceCoreMappingWithDefault.type layout)) definitions)
    (keyTyped : Core.HasType environment key (Core.LanguageResult.resultType layout.keyType) definitions) :
    Core.HasType environment (index layout comparison base key missingBase)
      (Core.LanguageResult.resultType layout.valueType) definitions := by
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed baseTyped
  apply Core.LanguageResult.bind_hasType registered.valueWellFormed
    (by simpa [Core.Context.insertAt] using
      keyTyped.weakenAt (inserted := SourceCoreMappingWithDefault.type layout) 0)
  apply SourceCoreMappingWithDefault.lookup_hasType missingBase registered
  · simpa [Core.Context.insertAt, Core.OrderedMapping.Layout.comparisonType] using
      (comparisonTyped.weakenAt (inserted := SourceCoreMappingWithDefault.type layout) 0).weakenAt
        (inserted := layout.keyType) 0
  · exact .var rfl
  · exact .var rfl

theorem index_base_failure {environment : Core.Environment} {before after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {reason : Core.Word} (failed : Core.Evaluates environment before base
      (.inLeft (SourceCoreMappingWithDefault.type layout) (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison base key missingBase)
      (.inLeft layout.valueType (.word reason)) after := Core.LanguageResult.bind_failure _ failed

theorem index_key_failure {environment : Core.Environment} {before middle after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {mapping : Core.Value} {reason : Core.Word}
    (baseEvaluated : Core.Evaluates environment before base (.inRight .word mapping) middle)
    (keyFailed : Core.Evaluates (mapping :: environment) middle (key.weakenAt 0)
      (.inLeft layout.keyType (.word reason)) after) :
    Core.Evaluates environment before (index layout comparison base key missingBase)
      (.inLeft layout.valueType (.word reason)) after :=
  Core.LanguageResult.bind_success _ baseEvaluated (Core.LanguageResult.bind_failure _ keyFailed)

theorem index_completed {environment : Core.Environment} {before middle selected after : Core.Store}
    (layout : Core.OrderedMapping.Layout) (missingBase : Core.Word) {comparison base key : Core.Expr}
    {mapping keyValue result : Core.Value}
    (baseEvaluated : Core.Evaluates environment before base (.inRight .word mapping) middle)
    (keyEvaluated : Core.Evaluates (mapping :: environment) middle (key.weakenAt 0)
      (.inRight .word keyValue) selected)
    (lookedUp : Core.Evaluates (keyValue :: mapping :: environment) selected
      (SourceCoreMappingWithDefault.lookup layout missingBase (comparison.weakenAt 0 |>.weakenAt 0)
        (.var 1) (.var 0)) result after) :
    Core.Evaluates environment before (index layout comparison base key missingBase) result after :=
  Core.LanguageResult.bind_success _ baseEvaluated (Core.LanguageResult.bind_success _ keyEvaluated lookedUp)

def lowerWithReasons (fuel : Nat) (context : Context) (lowerChild : ExpressionLowerer)
    (source : TypedSource) (scope : Scope) (id : ExpressionId) (reasonAt : ExpressionId → Core.Word) :
    Except Error LoweredExpr := do
  match fuel with
  | 0 => throw (.traversalExhausted (.occurrence id.occurrence))
  | fuel + 1 =>
      let (node, type) ← readExpression context.checked source id
      let site := SourceCoreElaboration.ErrorSite.occurrence id.occurrence
      match node.form with
      | .constructor instantiation arguments =>
          unless node.type = instantiation.resultType do throw (unsupported node)
          unless arguments.length = instantiation.payloadTypes.length do throw (unsupported node)
          let constructor ← (context.checked.resolveConstructor instantiation).mapError (fun _ => unsupported node)
          let metadata ← metadataId context node (.constructor instantiation)
          SourceCoreBasic.ensureType site type (.namedData constructor.owner)
          let lowered ← (arguments.zip instantiation.payloadTypes).mapM fun (argument, expected) => do
            let expected ← projectType context.checked site expected
            let argument ← lowerChild fuel source scope argument reasonAt
            SourceCoreBasic.ensureType site expected argument.type
            pure argument
          pure ⟨type, construct constructor metadata (SourceCoreCalls.packArguments lowered).expression⟩
      | .proxy inner =>
          unless node.type = .proxy inner do throw (unsupported node)
          let identity ← match context.checked.catalog.identity? node.type with
            | some identity => pure identity | none => throw (unsupported node)
          let metadata ← metadataId context node (.proxy inner)
          SourceCoreBasic.ensureType site type (.namedData identity)
          unless context.checked.catalog.definitions.lookupConstructorPayloadType? ⟨identity, 0⟩ = some .word do
            throw (unsupported node)
          pure ⟨type, Core.LanguageResult.success (.construct ⟨identity, 0⟩ (.word metadata))⟩
      | .member base _ selected =>
          let (baseNode, baseType) ← readExpression context.checked source base
          let (owner, branches) ← memberBranches context node baseNode.type type selected
          SourceCoreBasic.ensureType site (.namedData owner) baseType
          let base ← lowerChild fuel source scope base reasonAt
          SourceCoreBasic.ensureType site baseType base.type
          pure ⟨type, SourceCoreDataExpressions.member owner type branches base.expression⟩
      | .index base key =>
          let (baseNode, baseType) ← readExpression context.checked source base
          let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
            | .mapping key value => pure (key, value) | _ => throw (unsupported node)
          let layout ← (context.checked.catalog.mappingLayout keyType valueType).mapError (fun _ => unsupported node)
          SourceCoreBasic.ensureType site type layout.valueType
          SourceCoreBasic.ensureType site baseType (SourceCoreMappingWithDefault.type layout)
          let base ← lowerChild fuel source scope base reasonAt
          let key ← lowerChild fuel source scope key reasonAt
          SourceCoreBasic.ensureType site baseType base.type
          SourceCoreBasic.ensureType site layout.keyType key.type
          let comparison ← (SourceCoreCompatibleDataEquality.prepare fuel context.checked keyType).mapError
            (fun _ => unsupported node)
          pure ⟨type, index layout comparison.expression base.expression key.expression (reasonAt id)⟩
      | _ => throw (unsupported node)

def leafLowerer (context : Context) : ExpressionLowerer → ExpressionLowerer :=
  fun child fuel source scope id reasonAt => do
    let (node, type) ← readExpression context.checked source id
    match node.form with
    | .constructor .. | .member .. | .proxy .. | .index .. =>
        lowerWithReasons fuel context child source scope id reasonAt
    | .tuple elements =>
        let children ← elements.mapM fun element => child fuel source scope element reasonAt
        let packed := SourceCoreCalls.packArguments children
        SourceCoreBasic.ensureType (.occurrence id.occurrence) type packed.type
        pure ⟨type, packed.expression⟩
    | _ => SourceCoreBasic.lowerExpression fuel source scope id (reasonAt id)

/- The callable policy must use the representation selected by this catalog.
The owning program supplies its authenticated descriptor hooks. -/
def functionPolicy (fuel : Nat) (context : Context)
    (callables : SourceCoreFunctions.CallablePolicy := {}) : SourceCoreFunctions.Policy := {
  callables
  projectType := projectType context.checked
  readExpression := readExpression context.checked
  lowerBinder := lowerBinder context.checked
  lowerRead := lowerRead fuel context
  leafLowerer := leafLowerer context
}

def loopPolicy (context : Context) (lowerExpression : ExpressionLowerer) : SourceCoreLoops.Policy := {
  lowerExpression
  readStatement := readStatement context.checked
  lowerBinder := lowerBinder context.checked
  lowerAssignment := lowerAssignment context.checked
}

structure Certified (context : Context) (environment : Core.Context) where
  lowered : LoweredExpr
  typed : Core.HasType environment lowered.expression (Core.LanguageResult.resultType lowered.type)
    context.checked.catalog.definitions

def lowerChecked (fuel : Nat) (context : Context) (lowerChild : ExpressionLowerer)
    (source : TypedSource) (scope : Scope) (environment : Core.Context) (id : ExpressionId)
    (reasonAt : ExpressionId → Core.Word) : Except Error (Certified context environment) := do
  let lowered ← lowerWithReasons fuel context lowerChild source scope id reasonAt
  if accepted : Core.infer? environment lowered.expression context.checked.catalog.definitions =
      some (Core.LanguageResult.resultType lowered.type) then
    pure ⟨lowered, Core.infer_sound accepted⟩
  else
    match source.lookupExpression? id with
    | some node => throw (unsupported node) | none => throw (.missingExpression id)

theorem construct_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {constructor : Core.ConstructorId} {payload : Core.Ty} {arguments : Core.Expr} (metadata : Core.Word)
    (registered : definitions.lookupConstructorPayloadType? constructor = some (.product .word payload))
    (argumentsTyped : Core.HasType environment arguments (Core.LanguageResult.resultType payload) definitions) :
    Core.HasType environment (construct constructor metadata arguments)
      (Core.LanguageResult.resultType (.namedData constructor.owner)) definitions := by
  obtain ⟨_, owner⟩ := Core.DataEnvironment.lookupConstructorPayloadType?_owner registered
  exact Core.LanguageResult.bind_hasType (.namedData owner) argumentsTyped
    (.inRight .word (.construct registered (.pair .word (.var rfl))))

theorem construct_evaluates {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) (metadata : Core.Word) {arguments : Core.Expr} {payload : Core.Value}
    (evaluated : Core.Evaluates environment before arguments (.inRight .word payload) after) :
    Core.Evaluates environment before (construct constructor metadata arguments)
      (.inRight .word (.constructed constructor (.pair (.word metadata) payload))) after :=
  Core.LanguageResult.bind_success _ evaluated (.inRight (.construct (.pair .word (.var rfl))))

theorem construct_failure {environment : Core.Environment} {before after : Core.Store}
    (constructor : Core.ConstructorId) (metadata : Core.Word) {payload : Core.Ty} {arguments : Core.Expr}
    {reason : Core.Word} (evaluated : Core.Evaluates environment before arguments (.inLeft payload (.word reason)) after) :
    Core.Evaluates environment before (construct constructor metadata arguments)
      (.inLeft (.namedData constructor.owner) (.word reason)) after :=
  Core.LanguageResult.bind_failure _ evaluated

theorem readMapping_hasType {definitions : Core.DataEnvironment} {environment : Core.Context}
    {payload : Core.Ty} {reference empty : Core.Expr}
    (referenceTyped : Core.HasType environment reference (Core.OptionalCell.referenceType payload) definitions)
    (emptyTyped : Core.HasType environment empty payload definitions) :
    Core.HasType environment (readMapping reference empty) (Core.LanguageResult.resultType payload) definitions := by
  apply Core.HasType.letE referenceTyped
  apply Core.HasType.caseE (.loadCell (.var rfl))
  · apply Core.HasType.letE
      (by simpa [Core.Context.insertAt] using
        (emptyTyped.weakenAt (inserted := Core.OptionalCell.referenceType payload) 0).weakenAt (inserted := .unit) 0)
    exact .letE (.storeCell (.var rfl) (.inRight .unit (.var rfl))) (.inRight .word (.var rfl))
  · exact .inRight .word (.var rfl)

theorem readMapping_present {environment : Core.Environment} {before after : Core.Store}
    {payload : Core.Ty} {reference empty : Core.Expr} {location : Core.Location} {mapping : Core.Value}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType payload) location) after)
    (present : after.read? location = some (.inRight .unit mapping)) :
    Core.Evaluates environment before (readMapping reference empty) (.inRight .word mapping) after :=
  .letE referenceEvaluated (.caseRight (.loadCell (.var rfl) present) (.inRight (.var rfl)))

theorem readMapping_initializes {environment : Core.Environment} {before middle after : Core.Store}
    {payload : Core.Ty} {reference empty : Core.Expr} {location : Core.Location} {mapping : Core.Value}
    (referenceEvaluated : Core.Evaluates environment before reference
      (.cellRef (Core.OptionalCell.cellType payload) location) middle)
    (absent : middle.read? location = some (.inLeft payload .unit))
    (emptyEvaluated : Core.Evaluates
      (.unit :: .cellRef (Core.OptionalCell.cellType payload) location :: environment) middle
      (empty.weakenAt 0 |>.weakenAt 0) mapping after)
    (stillAbsent : after.read? location = some (.inLeft payload .unit)) :
    Core.Evaluates environment before (readMapping reference empty)
      (.inRight .word mapping) (after.set location (.inRight .unit mapping)) := by
  have bound := (List.getElem?_eq_some_iff.mp stillAbsent).1
  exact .letE referenceEvaluated (.caseLeft (.loadCell (.var rfl) absent)
    (.letE emptyEvaluated (.letE (.storeCell (.var rfl) stillAbsent (.inRight (.var rfl))
      (by simp [Core.Store.write?, bound])) (.inRight (.var rfl)))))

end Solcore.Frontend.SourceCoreCompatibleDataExpressions
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleDataPlaces
/-! Source-compatible structural places compile to ordinary Core getter and updater functions.
Raw nominal metadata and mapping headers/defaults survive reconstruction.
Only a declared bare mapping normalizes an absent root without writing it.
All keys are evaluated once before selection. Compound arithmetic uses that
selection; reconstruction reads the latest root after the RHS. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleDataPlaces

open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Context := SourceCoreCompatibleValues.Context
abbrev Error := SourceCoreBasic.Error
abbrev Scope := SourceCoreBasic.Scope
abbrev ExpressionLowerer := SourceCoreControl.ExpressionLowerer

def instructionBinders (instructions : List MatchPatternInstruction) : List TypedBinder :=
  instructions.filterMap fun | .binder binder => some binder | _ => none

def patternBinders (pattern : TypedMatchPattern) : List TypedBinder :=
  match pattern.resolution with
  | .binder binder => [binder]
  | .constructor _ children | .tuple children => instructionBinders children
  | _ => []

def declaredBinders (source : TypedSource) : List TypedBinder :=
  source.inputs ++ source.nodes.flatMap fun
    | .expression node => match node.form with
        | .lambda parameters _ _ => parameters
        | _ => []
    | .statement node => match node.form with
        | .letDecl binder _ => [binder]
        | .forLoop initial _ post _ => (initial ++ post).filterMap fun
            | .letDecl binder _ => some binder
            | _ => none
        | .matchWith resolution => resolution.cases.flatMap (fun arm => patternBinders arm.pattern)
        | _ => []

def rootBinder (source : TypedSource) (id : Resolved.LocalId) : Except Error TypedBinder := do
  if id.owner ≠ source.owner then throw (.ownerMismatch source.owner id.owner)
  match (declaredBinders source).filter (fun binder => decide (binder.id = id)) with
  | [binder] =>
      unless binder.scheme.quantified.isEmpty do throw (.polymorphicBinding id)
      unless binder.schemeRequirements.isEmpty do throw (.bindingRequirementsPresent id)
      pure binder
  | [] => throw (.missingBinding id)
  | _ => throw (.duplicateBinding id)

structure MemberBranch where
  constructor : Core.ConstructorId
  payloadTypes : List Core.Ty
  deriving Repr

inductive Step where
  | index (layout : Core.OrderedMapping.Layout) (key : ExpressionId)
      (valueType : TypeSystem.Ty)
  | member (dataType : Core.DataTypeId) (index : Nat) (branches : List MemberBranch)
      (fieldType : Core.Ty)
  deriving Repr

structure Route where
  rootSourceType : TypeSystem.Ty
  rootType : Core.Ty
  leafType : Core.Ty
  steps : List Step
  rootMapping : Option Core.Expr
  deriving Repr

def Step.resultType : Step → Core.Ty
  | .index layout _ _ => layout.valueType
  | .member _ _ _ type => type

def project (checked : Checked) (site : SourceCoreElaboration.ErrorSite) (type : TypeSystem.Ty) :
    Except Error Core.Ty := SourceCoreCompatibleDataExpressions.projectType checked site type

def memberStep (checked : Checked) (signatures : ProgramSignatures)
    (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId)
    (type : TypeSystem.Ty) (index : Nat) : Except Error (Step × TypeSystem.Ty) := do
  let type := SourceCoreRawMetadata.runtimeType type
  let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts type with
    | some parts => pure parts
    | none => throw (.projectedAssignment root)
  let signature ← match signatures.dataTypes.filter (fun data => decide (data.id = declaration)) with
    | [signature] => pure signature
    | _ => throw (.projectedAssignment root)
  unless signature.parameters.length = arguments.length && !signature.constructors.isEmpty do
    throw (.projectedAssignment root)
  let identity ← match checked.catalog.identity? type with
    | some identity => pure identity
    | none => throw (.projectedAssignment root)
  let substitution : TypeSystem.ParameterSubstitution := signature.parameters.zip arguments
  let mut selected : Option TypeSystem.Ty := none
  let mut branches := []
  for (constructor, position) in signature.constructors.zipIdx do
    let payloadTypes := constructor.payloadTypes.map substitution.apply
    let field ← match payloadTypes[index]? with
      | some field => pure field
      | none => throw (.projectedAssignment root)
    match selected with
    | none => selected := some field
    | some previous => unless SourceCoreRawMetadata.runtimeType previous = SourceCoreRawMetadata.runtimeType field do
        throw (.projectedAssignment root)
    let resolved ← (checked.resolveConstructor {
      constructor := constructor.id, parameterSubstitution := substitution,
      payloadTypes, resultType := type }).mapError (fun _ => SourceCoreBasic.Error.projectedAssignment root)
    unless resolved.owner = identity && resolved.index = position do throw (.projectedAssignment root)
    branches := branches ++ [⟨resolved, ← payloadTypes.mapM (project checked site)⟩]
  let field ← match selected with
    | some field => pure field
    | none => throw (.projectedAssignment root)
  pure (.member identity index branches (← project checked site field), field)

def routeSteps (checked : Checked) (signatures : ProgramSignatures)
    (source : TypedSource) (site : SourceCoreElaboration.ErrorSite) (root : Resolved.LocalId) :
    TypeSystem.Ty → List PlaceProjection → Except Error (List Step × TypeSystem.Ty)
  | type, [] => pure ([], type)
  | type, projection :: rest => do
      let (step, selected) ← match projection with
        | .member _ index => memberStep checked signatures site root type index
        | .index key => do
            let (keySource, valueSource) ← match SourceCoreRawMetadata.runtimeType type with
              | .mapping key value => pure (key, value)
              | _ => throw (.projectedAssignment root)
            if key.occurrence.owner ≠ source.owner then
              throw (.ownerMismatch source.owner key.occurrence.owner)
            let keyNode ← match source.lookupExpression? key with
              | some node => pure node
              | none => throw (.missingExpression key)
            let keyType ← project checked (.occurrence key.occurrence) keyNode.type
            let projectedKey ← project checked site keySource
            SourceCoreBasic.ensureType site projectedKey keyType
            let projectedValue ← project checked site valueSource
            let identity ← match checked.catalog.identity? type with
              | some identity => pure identity
              | none => throw (.projectedAssignment root)
            let layout : Core.OrderedMapping.Layout := ⟨projectedKey, projectedValue, identity⟩
            unless checked.catalog.definitions[identity.index]? = some layout.definition do
              throw (.projectedAssignment root)
            pure (.index layout key valueSource, valueSource)
      let (steps, final) ← routeSteps checked signatures source site root selected rest
      pure (step :: steps, final)

/-- Authenticate the retained path against the root declaration and every
constructor's payload, independently of the ambient de Bruijn positions. -/
def describe (context : Context) (signatures : ProgramSignatures) (source : TypedSource)
    (site : SourceCoreElaboration.ErrorSite) (assignment : AssignmentResolution) : Except Error Route := do
  let checked := context.checked
  let root := assignment.target.root
  unless assignment.requirements.isEmpty do throw (.assignmentRequirementsPresent root)
  let binder ← rootBinder source root
  let rootType ← project checked (.binder root) binder.scheme.body
  let (steps, selected) ← routeSteps checked signatures source site root binder.scheme.body assignment.target.projections
  unless SourceCoreRawMetadata.runtimeType selected = SourceCoreRawMetadata.runtimeType assignment.target.type do
    throw (.projectedAssignment root)
  let rootMapping ← match binder.scheme.body with
    | .mapping key value => do
        let identity ← match checked.catalog.identity? binder.scheme.body with
          | some identity => pure identity
          | none => throw (.projectedAssignment root)
        let layout : Core.OrderedMapping.Layout :=
          ⟨← project checked site key, ← project checked site value, identity⟩
        unless checked.catalog.definitions[identity.index]? = some layout.definition do
          throw (.projectedAssignment root)
        let carrier ← (SourceCoreCompatibleValues.encode (binder.scheme.body.size + 20) context
          binder.scheme.body (.mapping key value [])).mapError (fun _ => .projectedAssignment root)
        unless carrier.context.registry.entries = context.registry.entries do throw (.projectedAssignment root)
        let empty ← match SourceCoreCompatibleDataExpressions.quote carrier.value with
          | some expression => pure expression | none => throw (.projectedAssignment root)
        pure (some empty)
    | _ => pure none
  pure ⟨binder.scheme.body, rootType, ← project checked site assignment.target.type, steps, rootMapping⟩

structure PreparedIndex where
  layout : Core.OrderedMapping.Layout
  key : ExpressionId
  keyPosition : Nat
  comparison : Core.Expr
  missing : Core.Word
  deriving Repr

inductive PreparedStep where
  | index (prepared : PreparedIndex)
  | member (dataType : Core.DataTypeId) (index : Nat) (branches : List MemberBranch) (fieldType : Core.Ty)
  deriving Repr

structure Prepared where
  route : Route
  steps : List PreparedStep
  keys : List (ExpressionId × Core.Ty)
  invalidProjection : Core.Word
  deriving Repr

def prepare (context : Context) (fuel : Nat) (route : Route)
    (invalid : Core.Word) (missing : TypeSystem.Ty → Core.Word) : Except Error Prepared := do
  let checked := context.checked
  let mut steps := []
  let mut keys := []
  for step in route.steps do
    match step with
    | .member dataType index branches fieldType => steps := steps ++ [.member dataType index branches fieldType]
    | .index layout key valueType =>
        let keySource ← match checked.catalog.entries[layout.dataType.index]? with
          | some entry => match entry.sourceType with
            | .mapping key _ => pure key
            | _ => throw (.missingExpression key)
          | none => throw (.missingExpression key)
        let comparison ← (SourceCoreCompatibleDataEquality.prepare fuel checked keySource).mapError
          (fun _ => SourceCoreBasic.Error.missingExpression key)
        steps := steps ++ [.index ⟨layout, key, keys.length, comparison.expression, missing valueType⟩]
        keys := keys ++ [(key, layout.keyType)]
  pure ⟨route, steps, keys, invalid⟩

def shift (count : Nat) (expression : Core.Expr) : Core.Expr :=
  (List.range count).foldl (fun expression _ => expression.weakenAt 0) expression

def pack : List Core.Expr → Core.Expr
  | [] => .unit
  | [one] => one
  | one :: rest => .pair one (pack rest)

def replacePacked (index : Nat) (types : List Core.Ty) (payload value : Core.Expr) : Core.Expr :=
  pack (types.zipIdx.map fun (_, position) => if position = index then value
    else SourceCoreDataExpressions.projectPacked position types payload)

def normalizeRoot (prepared : Prepared) (optional : Core.Expr) : Core.Expr :=
  match prepared.route.rootMapping with
  | some empty => .caseE optional
      (.inRight .unit (empty.weakenAt 0)) (.inRight .unit (.var 0))
  | none => optional

def Prepared.keyTypes (prepared : Prepared) : List Core.Ty := prepared.keys.map (·.2)
def Prepared.optionalLeaf (prepared : Prepared) : Core.Ty := Core.OptionalCell.cellType prepared.route.leafType

def selectedIndex (prepared : Prepared) (index : PreparedIndex) (current keys : Core.Expr) : Core.Expr :=
  let key := SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes keys
  SourceCoreMappingWithDefault.lookup index.layout index.missing index.comparison current key

def select (prepared : Prepared) : List PreparedStep → Core.Expr → Core.Expr → Core.Expr
  | [], current, _ => Core.LanguageResult.success (.inRight .unit current)
  | .index index :: rest, current, keys =>
      Core.LanguageResult.bind prepared.optionalLeaf (selectedIndex prepared index current keys)
        (select prepared rest (.var 0) (shift 1 keys))
  | .member dataType index branches _ :: rest, current, keys =>
      .matchData dataType (Core.LanguageResult.resultType prepared.optionalLeaf) current
        (branches.map fun branch => select prepared rest
          (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.second (.var 0))) (shift 1 keys))

/-- Updater follows the latest structure, including defaults, before replacing
the leaf. A path failure therefore precedes even a constant leaf modifier. -/
def update (prepared : Prepared) : List PreparedStep → Core.Ty → Core.Expr → Core.Expr → Core.Expr → Core.Expr
  | [], _, _, _, replacement => Core.LanguageResult.success replacement
  | .index index :: rest, _, current, keys, replacement =>
      Core.LanguageResult.bind (SourceCoreMappingWithDefault.type index.layout) (selectedIndex prepared index current keys)
        (Core.LanguageResult.bind (SourceCoreMappingWithDefault.type index.layout)
          (update prepared rest index.layout.valueType (.var 0) (shift 1 keys) (shift 1 replacement))
          (SourceCoreMappingWithDefault.insert index.layout index.comparison (shift 2 current)
            (SourceCoreDataExpressions.projectPacked index.keyPosition prepared.keyTypes (shift 2 keys)) (.var 0)))
  | .member dataType index branches fieldType :: rest, _, current, keys, replacement =>
      .matchData dataType (Core.LanguageResult.resultType (.namedData dataType)) current
        (branches.map fun branch =>
          Core.LanguageResult.bind (.namedData dataType)
            (update prepared rest fieldType
              (SourceCoreDataExpressions.projectPacked index branch.payloadTypes (.second (.var 0)))
              (shift 1 keys) (shift 1 replacement))
            (Core.LanguageResult.success (.construct branch.constructor
              (.pair (.first (.var 1)) (replacePacked index branch.payloadTypes (.second (.var 1)) (.var 0))))))

def getter (prepared : Prepared) (keyType : Core.Ty) : Core.Expr :=
  .lambda (.product (Core.OptionalCell.cellType prepared.route.rootType) keyType)
    (Core.LanguageResult.resultType prepared.optionalLeaf)
    (match prepared.steps with
      | [] => Core.LanguageResult.success (normalizeRoot prepared (.first (.var 0)))
      | steps => .caseE (normalizeRoot prepared (.first (.var 0)))
          (Core.LanguageResult.failure prepared.optionalLeaf (.word prepared.invalidProjection))
          (select prepared steps (.var 0) (.second (.var 1))))

def setter (prepared : Prepared) (keyType : Core.Ty) : Core.Expr :=
  .lambda (.product (Core.OptionalCell.cellType prepared.route.rootType)
    (.product keyType prepared.route.leafType)) (Core.LanguageResult.resultType prepared.route.rootType)
    (match prepared.steps with
      | [] => Core.LanguageResult.success (.second (.second (.var 0)))
      | steps => .caseE (normalizeRoot prepared (.first (.var 0)))
          (Core.LanguageResult.failure prepared.route.rootType (.word prepared.invalidProjection))
          (update prepared steps prepared.route.rootType (.var 0)
            (.first (.second (.var 1))) (.second (.second (.var 1)))))

def binaryOperator (integer : Bool) : Syntax.ValueAssignOp → Option SourceCoreDataPlaces.Modifier
  | .equal => none
  | .add => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerAdd else .wordAdd))
  | .subtract => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerSub else .wordSub))
  | .multiply => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerMul else .wordMul))
  | .divide => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerDiv else .wordDiv))
  | .modulo => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerMod else .wordMod))
  | .bitAnd => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerAnd else .wordAnd))
  | .bitOr => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerOr else .wordOr))
  | .bitXor => some (SourceCoreDataPlaces.Modifier.total (if integer then .integerXor else .wordXor))
  -- Shifts and unchecked arithmetic take Words only; `lower` rejects them at
  -- Integer leaves.
  | .shiftLeft => some (SourceCoreDataPlaces.Modifier.total .wordShl)
  | .shiftRight => some (SourceCoreDataPlaces.Modifier.total .wordShr)
  | .uncheckedAdd => some (SourceCoreDataPlaces.Modifier.total .wordAdd)
  | .uncheckedSubtract => some (SourceCoreDataPlaces.Modifier.total .wordSub)
  | .uncheckedMultiply => some (SourceCoreDataPlaces.Modifier.total .wordMul)
  | .uncheckedDivide => some ⟨.wordDiv, true⟩
  | .uncheckedModulo => some ⟨.wordMod, true⟩

def modified (type : Core.Ty) (operator : Option SourceCoreDataPlaces.Modifier) (bitNot : Bool)
    (snapshot rhs : Core.Expr) (invalid : Core.Word) : Core.Expr :=
  if bitNot then .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
    (Core.LanguageResult.success (.unary (if type = .integer then .integerNot else .wordNot) (.var 0)))
  else match operator with
    | none => Core.LanguageResult.success rhs
    | some modifier => .caseE snapshot (Core.LanguageResult.failure type (.word invalid))
        (Core.LanguageResult.success (.binary modifier.operation (.var 0) (shift 1 rhs)))

/-- Internal binders: reference, keys, snapshot, RHS, modified leaf, updated
root, store result. Source expressions are shifted only at their insertion. -/
def execute (prepared : Prepared) (reference : Core.Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Core.Expr) (outputType : Core.Ty) (operator : Option SourceCoreDataPlaces.Modifier)
    (bitNot : Bool) (invalidOperand : Core.Word) : Core.Expr :=
  .letE reference
    (Core.LanguageResult.bind outputType (shift 1 keys.expression)
      (Core.LanguageResult.bind outputType
        (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
        (Core.LanguageResult.bind outputType (shift 3 rhs)
          (Core.LanguageResult.bind outputType
            (modified prepared.route.leafType operator bitNot (.var 1) (.var 0) invalidOperand)
            (Core.LanguageResult.bind outputType
              (.apply (setter prepared keys.type)
                (.pair (.loadCell (.var 4)) (.pair (.var 3) (.var 0))))
              (SourceCoreDataPlaces.guard outputType operator
                (.letE (.storeCell (.var 5) (.inRight .unit (.var 0))) (shift 7 next))))))))

def lower (context : Context) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Core.Ty) (next : Core.Expr) (reasonAt : ExpressionId → Core.Word)
    (invalidProjection invalidOperand : Core.Word) (missing : TypeSystem.Ty → Core.Word) : Except Error Core.Expr := do
  let route ← describe context signatures source site assignment
  let (index, storedType) ← match SourceCoreLocalCell.lookup? scope assignment.target.root with
    | some found => pure found
    | none => throw (.missingBinding assignment.target.root)
  SourceCoreBasic.ensureType site route.rootType storedType
  let prepared ← prepare context fuel route invalidProjection missing
  let keys ← prepared.keys.mapM fun (id, expected) => do
    let key ← expression fuel source scope id reasonAt
    SourceCoreBasic.ensureType (.occurrence id.occurrence) expected key.type
    pure key
  let bitNot := rhs.isNone
  if operator ≠ .equal || bitNot then
    unless route.leafType = .word || (route.leafType = .integer && !operator.wordOnly) do
      throw (.unsupportedAssignmentOperator operator)
  let rhs ← match rhs with
    | none => pure (Core.LanguageResult.success .unit)
    | some id => do
        let value ← expression fuel source scope id reasonAt
        SourceCoreBasic.ensureType site route.leafType value.type
        pure value.expression
  pure (execute prepared (.var index) (SourceCoreCalls.packArguments keys) rhs next outputType
    (binaryOperator (route.leafType = .integer) operator) bitNot invalidOperand)

/-- A key failure stops before snapshot selection, RHS and structural write.
The premise uses the actual inserted reference environment. -/
theorem execute_key_failure {environment : Core.Environment} {before middle after : Core.Store}
    (prepared : Prepared) (reference : Core.Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Core.Expr) (outputType : Core.Ty) (operator : Option SourceCoreDataPlaces.Modifier)
    (bitNot : Bool) (invalidOperand reason : Core.Word) (ref : Core.Value)
    (referenceEvaluated : Core.Evaluates environment before reference ref middle)
    (failed : Core.Evaluates (ref :: environment) middle (shift 1 keys.expression)
      (.inLeft keys.type (.word reason)) after) :
    Core.Evaluates environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE referenceEvaluated (Core.LanguageResult.bind_failure _ failed)

/-- RHS failure retains key and selection effects, and performs no modifier,
latest-root reconstruction or write. No weakening of an exact store is assumed. -/
theorem execute_rhs_failure {environment : Core.Environment}
    {before referenced keyed selected after : Core.Store}
    (prepared : Prepared) (reference : Core.Expr) (keys : SourceCoreBasic.LoweredExpr)
    (rhs next : Core.Expr) (outputType : Core.Ty) (operator : Option SourceCoreDataPlaces.Modifier)
    (bitNot : Bool) (invalidOperand reason : Core.Word) (ref key snapshot : Core.Value)
    (referenceEvaluated : Core.Evaluates environment before reference ref referenced)
    (keysEvaluated : Core.Evaluates (ref :: environment) referenced (shift 1 keys.expression)
      (.inRight .word key) keyed)
    (selectionEvaluated : Core.Evaluates (key :: ref :: environment) keyed
      (.apply (getter prepared keys.type) (.pair (.loadCell (.var 1)) (.var 0)))
      (.inRight .word snapshot) selected)
    (failed : Core.Evaluates (snapshot :: key :: ref :: environment) selected (shift 3 rhs)
      (.inLeft prepared.route.leafType (.word reason)) after) :
    Core.Evaluates environment before
      (execute prepared reference keys rhs next outputType operator bitNot invalidOperand)
      (.inLeft outputType (.word reason)) after :=
  .letE referenceEvaluated (Core.LanguageResult.bind_success _ keysEvaluated
    (Core.LanguageResult.bind_success _ selectionEvaluated (Core.LanguageResult.bind_failure _ failed)))

structure Certified (definitions : Core.DataEnvironment) (environment : Core.Context) (outputType : Core.Ty) where
  expression : Core.Expr
  typed : Core.HasType environment expression (Core.LanguageResult.resultType outputType) definitions

/-- The checker uses the actual ambient definitions, including a marker
suffix when the supplied continuation contains source-visible allocations. -/
def lowerChecked (context : Context) (signatures : ProgramSignatures) (expression : ExpressionLowerer)
    (fuel : Nat) (source : TypedSource) (scope : Scope) (site : SourceCoreElaboration.ErrorSite)
    (assignment : AssignmentResolution) (operator : Syntax.ValueAssignOp) (rhs : Option ExpressionId)
    (outputType : Core.Ty) (next : Core.Expr) (reasonAt : ExpressionId → Core.Word)
    (invalidProjection invalidOperand : Core.Word) (missing : TypeSystem.Ty → Core.Word)
    (definitions : Core.DataEnvironment) (environment : Core.Context) :
    Except Error (Certified definitions environment outputType) := do
  let expression ← lower context signatures expression fuel source scope site assignment operator rhs outputType next
    reasonAt invalidProjection invalidOperand missing
  if accepted : Core.infer? environment expression definitions = some (Core.LanguageResult.resultType outputType) then
    pure ⟨expression, Core.infer_sound accepted⟩
  else throw (.projectedAssignment assignment.target.root)

end Solcore.Frontend.SourceCoreCompatibleDataPlaces
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
/-! Missing defaults reserve disjoint program-wide word ranges. Within one
range the actual raw mapping-header ID selects `typeMismatch rawValueType none`.
Input registry extensions use the same static range inventory; rebuilding the
diagnostic table performs metadata lookup only. It does not evaluate source.

The emitted code adds a header ID to the site's base. Preparation checks the
end of each reserved range without wrapping. Tables reject IDs outside the
reserved registry budget and headers of an unrelated runtime value type. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
open SourceInference
abbrev Context := SourceCoreCompatibleValues.Context
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Site := SourceCoreElaboration.ErrorSite
abbrev Diagnostic := SourceCoreFaultSites.Diagnostic

structure MissingSite where
  owner : Key
  site : Site
  binder : Option Resolved.LocalId
  keyType : TypeSystem.Ty
  valueType : TypeSystem.Ty
  span : Syntax.SourceSpan
  base : Core.Word
  deriving Repr

structure Program (context : Context) where
  program : SourceCoreDataPlaceFaultSites.Program
  missing : List MissingSite
  /-- The preexisting read/assignment/function boundary and place faults. -/
  fixed : List (Core.Word × Diagnostic)
  /-- Later diagnostic inventories start here, even before dynamic headers
  occupy the remaining slots in the reserved ranges. -/
  nextReason : Nat

def Program.context {context : Context} (_program : Program context) : Context := context

inductive Error where
  | base (error : SourceCoreProgramFaultSites.Error)
  | lowering (error : SourceCoreBasic.Error)
  | duplicateOccurrence (expression : ExpressionId)
  | ownerMismatch (expression : ExpressionId)
  | sourceOwnerMismatch (expected actual : Resolved.DeclarationId)
  | reasonSpaceExhausted
  | registryBudgetExceeded
  | registryOwnerMismatch
  deriving Repr

private def word (number : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? number with
  | some value => pure value | none => throw .reasonSpaceExhausted

/-- The native addition has the same number as the metadata decoder when
the reserved endpoint and authenticated header remain within their budget. -/
theorem token_nonWrapping (base header : Core.Word) (capacity : Nat)
    (reserved : base.val + capacity < Core.wordModulus) (bounded : header.val ≤ capacity) :
    (base.add header).val = base.val + header.val := by
  change (base.val + header.val) % Core.wordModulus = base.val + header.val
  apply Nat.mod_eq_of_lt
  omega

theorem token_ranges_disjoint (left right leftHeader rightHeader : Core.Word) (leftCapacity rightCapacity : Nat)
    (leftReserved : left.val + leftCapacity < Core.wordModulus)
    (rightReserved : right.val + rightCapacity < Core.wordModulus)
    (leftBounded : leftHeader.val ≤ leftCapacity) (rightBounded : rightHeader.val ≤ rightCapacity)
    (separate : left.val + leftCapacity < right.val) :
    left.add leftHeader ≠ right.add rightHeader := by
  intro same
  have equal := congrArg Fin.val same
  rw [token_nonWrapping left leftHeader leftCapacity leftReserved leftBounded,
    token_nonWrapping right rightHeader rightCapacity rightReserved rightBounded] at equal
  omega

private def targets (node : StatementNode) : List AssignmentResolution :=
  match node.form with
  | .assignValue assignment _ _ | .assignBitNot assignment => [assignment]
  | .forLoop initial _ post _ => (initial ++ post).filterMap fun
      | .assignValue assignment _ _ | .assignBitNot assignment => some assignment
      | _ => none
  | _ => []

/-- Raw headers are interpreted within the exact owning registry. The list
contains only headers compatible with this site's projected value type. -/
def missingDiagnostics (registry : SourceCoreRawMetadata.Registry)
    (sites : List MissingSite) : Except Error (List (Core.Word × Diagnostic)) := do
  unless registry.length ≤ registry.limits.maxEntries do throw .registryBudgetExceeded
  let mut diagnostics := []
  for site in sites do
    for (metadata, index) in registry.entries.zipIdx do
      match metadata with
      | .mapping keyType valueType =>
          if SourceCoreRawMetadata.runtimeType keyType = SourceCoreRawMetadata.runtimeType site.keyType &&
              SourceCoreRawMetadata.runtimeType valueType = SourceCoreRawMetadata.runtimeType site.valueType then
            let reason ← word (site.base.val + index + 1)
            unless diagnostics.any (fun previous => decide (previous.1 = reason)) do
              diagnostics := diagnostics ++ [(reason, {
                error := .typeMismatch valueType none, site := site.site, span := some site.span })]
      | _ => pure ()
  pure diagnostics

/-- Rebuild exact raw-type diagnostics after authenticated input extension.
The old static registry must remain a prefix; no slot is silently rebound. -/
def Program.tableForRegistry {context : Context} (program : Program context) (registry : SourceCoreRawMetadata.Registry)
    (_extension : SourceCoreRawMetadata.Extends program.context.registry registry) :
    Except Error SourceCoreFaultSites.Table := do
  let extra ← missingDiagnostics registry program.missing
  pure { program.program.rootTable with additional := program.fixed ++ extra }

def Program.diagnostic? {context : Context} (program : Program context) (registry : SourceCoreRawMetadata.Registry)
    (extension : SourceCoreRawMetadata.Extends program.context.registry registry)
    (reason : Core.Word) : Except Error (Option Diagnostic) := do
  let table ← program.tableForRegistry registry extension
  pure (table.diagnostic? reason)

/-- The base inventory has the same provider interface as the strict
DataPlaceFaultSites.Program. Only missing-default reasons represent ranges. -/
def prepare (context : Context) (plan : Plan) (root : Key)
    (extraSources : List (Key × TypedSource) := []) : Except Error (Program context) := do
  let base ← (SourceCoreProgramFaultSites.prepare plan root).mapError Error.base
  let used := base.rootTable.reads.map (·.reason.val) ++
    base.rootTable.additional.map (·.1.val) ++ [base.rootTable.escapedReason.val]
  let mut next := used.foldl max 0 + 1
  let width := context.registry.limits.maxEntries + 1
  let mut indices : List SourceCoreDataFaultSites.IndexSite := []
  let mut places : List SourceCoreDataPlaceFaultSites.Site := []
  let mut missing : List MissingSite := []
  let mut fixed := base.rootTable.additional
  let sources := plan.specializations.map (fun specialized => (specialized.key, specialized.function.typedBody)) ++ extraSources
  for (owner, source) in sources do
    if source.owner ≠ owner.declaration then throw (.sourceOwnerMismatch owner.declaration source.owner)
    let mut seenIndices : List ExpressionId := []
    for retained in source.nodes do
      match retained with
      | .expression node =>
          match node.form with
          | .index mapping key =>
              if node.id.occurrence.owner ≠ source.owner then throw (.ownerMismatch node.id)
              if mapping.occurrence.owner ≠ source.owner then throw (.ownerMismatch mapping)
              if key.occurrence.owner ≠ source.owner then throw (.ownerMismatch key)
              if seenIndices.contains node.id then throw (.duplicateOccurrence node.id)
              seenIndices := node.id :: seenIndices
              let reason ← match indices.find? (fun previous => decide (previous.owner = owner ∧ previous.expression = node.id)) with
                | some previous => pure previous.reason
                | none => do
                    let reason ← word next
                    discard <| word (next + width - 1)
                    next := next + width
                    let diagnostic : Diagnostic := {
                      error := .typeMismatch node.type none, site := .occurrence node.id.occurrence, span := some node.span }
                    indices := indices ++ [⟨owner, node.id, reason, diagnostic⟩]
                    pure reason
              let baseNode ← match source.lookupExpression? mapping with
                | some base => pure base | none => throw (.lowering (.missingExpression mapping))
              let (keyType, valueType) ← match SourceCoreRawMetadata.runtimeType baseNode.type with
                | .mapping keyType valueType => pure (keyType, valueType)
                | _ => throw (.lowering (.missingExpression key))
              unless SourceCoreRawMetadata.runtimeType node.type = valueType do
                throw (.lowering (.missingExpression node.id))
              missing := missing ++ [⟨owner, .occurrence node.id.occurrence, none, keyType, node.type, node.span, reason⟩]
          | _ => pure ()
      | .statement node =>
          let site := SourceCoreElaboration.ErrorSite.occurrence node.id.occurrence
          for assignment in targets node do
            -- Principal local bodies are visited again through their actual
            -- contextual instances. Only concrete routes generate code.
            let declared := (SourceCoreDataPlaces.declaredBinders source).filter (fun binder =>
              decide (binder.id = assignment.target.root))
            let concrete := SourceCoreDataCatalog.closed assignment.target.type &&
              declared.any (fun binder => SourceCoreDataCatalog.closed binder.scheme.body)
            if concrete then
              let route ← (SourceCoreCompatibleDataPlaces.describe context context.checked.signatures source site assignment)
                |>.mapError Error.lowering
              unless route.steps.isEmpty || places.any (fun previous => decide
                  (previous.owner = owner ∧ previous.location = site ∧
                   previous.binder = assignment.target.root ∧ previous.missingType = none)) do
                let reason ← word next
                next := next + 1
                let diagnostic : Diagnostic := {error := .invalidPlaceProjection, site, span := some node.span}
                places := places ++ [⟨owner, site, assignment.target.root, none, reason, diagnostic⟩]
                fixed := fixed ++ [(reason, diagnostic)]
              for step in route.steps do
                match step with
                | .index _ key valueType =>
                    let reason ← match places.find? (fun previous => decide
                        (previous.owner = owner ∧ previous.location = site ∧
                         previous.binder = assignment.target.root ∧ previous.missingType = some valueType)) with
                      | some previous => pure previous.reason
                      | none => do
                          let reason ← word next
                          discard <| word (next + width - 1)
                          next := next + width
                          let diagnostic : Diagnostic := {error := .typeMismatch valueType none, site, span := some node.span}
                          places := places ++ [⟨owner, site, assignment.target.root, some valueType, reason, diagnostic⟩]
                          pure reason
                    let keyNode ← match source.lookupExpression? key with
                      | some keyNode => pure keyNode | none => throw (.lowering (.missingExpression key))
                    missing := missing ++ [⟨owner, site, some assignment.target.root, keyNode.type, valueType, node.span, reason⟩]
                | _ => pure ()
  let extra ← missingDiagnostics context.registry missing
  let rootTable := {base.rootTable with additional := fixed ++ extra}
  let expressions : SourceCoreDataFaultSites.Program := {base, indices, rootTable}
  let program : SourceCoreDataPlaceFaultSites.Program := {base, expressions, places, rootTable}
  pure {program, missing, fixed, nextReason := next}

end Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites

namespace Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
open SourceInference

private def diagnosticStepResult {β : Type} : ForInStep β → β
  | .done value | .yield value => value

private theorem diagnosticLoopInvariant {α β ε : Type} {items : List α}
    {before after : β} {step : α → β → Except ε (ForInStep β)} {invariant : β → Prop}
    (initial : invariant before)
    (keep : ∀ item ∈ items, ∀ previous next, invariant previous →
      step item previous = .ok next → invariant (diagnosticStepResult next))
    (accepted : forIn items before step = .ok after) : invariant after := by
  induction items generalizing before with
  | nil =>
    simp only [List.forIn_nil, pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact initial
  | cons item rest ih =>
    rw [List.forIn_cons] at accepted
    cases produced : step item before with
    | error error => simp [produced, bind, Except.bind] at accepted
    | ok next =>
      have kept := keep item (by simp) before next initial produced
      cases next with
      | done value =>
        simp [produced, bind, Except.bind] at accepted
        cases accepted
        exact kept
      | yield value =>
        simp only [produced, bind, Except.bind] at accepted
        exact ih kept (fun other member => keep other (by simp [member])) accepted

/-- A returned missing-default diagnostic comes from an actual site and
an actual raw mapping header in this receiver registry. The token conversion
is the checked, non-wrapping conversion used by the original producer. -/
def MissingDiagnosticOrigin (registry : SourceCoreRawMetadata.Registry)
    (sites : List MissingSite) (entry : Core.Word × Diagnostic) : Prop :=
  ∃ site ∈ sites, ∃ keyType valueType index,
    (SourceCoreRawMetadata.Metadata.mapping keyType valueType, index) ∈ registry.entries.zipIdx ∧
    SourceCoreRawMetadata.runtimeType keyType = SourceCoreRawMetadata.runtimeType site.keyType ∧
    SourceCoreRawMetadata.runtimeType valueType = SourceCoreRawMetadata.runtimeType site.valueType ∧
    Core.Word.ofNat? (site.base.val + index + 1) = some entry.1 ∧
    entry.2 = {error := .typeMismatch valueType none, site := site.site, span := some site.span}

private theorem diagnostic_word_issued {number : Nat} {reason : Core.Word}
    (issued : word number = .ok reason) : Core.Word.ofNat? number = some reason := by
  unfold word at issued
  cases converted : Core.Word.ofNat? number with
  | none => simp [converted, throw, throwThe, MonadExceptOf.throw] at issued
  | some value =>
    simp [converted] at issued
    cases issued
    rfl

/-- Finite inventory traversal of the original table producer. It does not
evaluate a Source expression or infer an origin from a runtime error. -/
theorem missingDiagnostics_origins {registry : SourceCoreRawMetadata.Registry}
    {sites : List MissingSite} {entries : List (Core.Word × Diagnostic)}
    (accepted : missingDiagnostics registry sites = .ok entries) :
    ∀ entry ∈ entries, MissingDiagnosticOrigin registry sites entry := by
  unfold missingDiagnostics at accepted
  split at accepted
  next bounded =>
    simp only [bind, Except.bind, pure, Except.pure] at accepted
    generalize outer : forIn (m := Except Error) sites ([] : List (Core.Word × Diagnostic)) _ = result at accepted
    cases result with
    | error error => cases accepted
    | ok result =>
      cases accepted
      apply diagnosticLoopInvariant (invariant := fun rows => ∀ entry ∈ rows,
        MissingDiagnosticOrigin registry sites entry) (items := sites) (before := []) ?_ ?_ outer
      · simp
      · intro site siteMember previous next known step
        generalize produced : forIn (m := Except Error) registry.entries.zipIdx previous _ = inner at step
        cases inner with
        | error error => cases step
        | ok rows =>
          cases step
          change ∀ entry ∈ rows, MissingDiagnosticOrigin registry sites entry
          apply diagnosticLoopInvariant known ?_ produced
          intro metadata member current yielded currentKnown emitted
          rcases metadata with ⟨metadata, index⟩
          cases metadata <;> simp only at emitted
          all_goals try { cases emitted; exact currentKnown }
          next keyType valueType =>
            split at emitted
            next views =>
              cases issued : word (site.base.val + index + 1) with
              | error error => simp [issued] at emitted
              | ok reason =>
                simp only [issued] at emitted
                split at emitted
                next duplicate =>
                  cases emitted
                  exact currentKnown
                next fresh =>
                  cases emitted
                  intro entry included
                  rcases List.mem_append.mp included with earlier | added
                  · exact currentKnown entry earlier
                  · simp only [List.mem_singleton] at added
                    cases added
                    have viewsPair :
                        SourceCoreRawMetadata.runtimeType keyType = SourceCoreRawMetadata.runtimeType site.keyType ∧
                        SourceCoreRawMetadata.runtimeType valueType = SourceCoreRawMetadata.runtimeType site.valueType := by
                      simpa using views
                    exact ⟨site, siteMember, keyType, valueType, index, member,
                      viewsPair.1, viewsPair.2,
                      diagnostic_word_issued issued, rfl⟩
            next unrelated =>
              cases emitted
              exact currentKnown
  next overBudget =>
    simp [throw, throwThe, MonadExceptOf.throw, bind, Except.bind] at accepted

/-- The issued zip index identifies a genuine one-based header in this exact
registry, and native addition produces the same checked diagnostic token. -/
theorem MissingDiagnosticOrigin.mapping_header
    {registry : SourceCoreRawMetadata.Registry} {sites : List MissingSite}
    {entry : Core.Word × Diagnostic} (origin : MissingDiagnosticOrigin registry sites entry) :
    ∃ site ∈ sites, ∃ keyType valueType, ∃ header : Core.Word,
      registry.lookup header = some (.mapping keyType valueType) ∧
      SourceCoreRawMetadata.runtimeType keyType = SourceCoreRawMetadata.runtimeType site.keyType ∧
      SourceCoreRawMetadata.runtimeType valueType = SourceCoreRawMetadata.runtimeType site.valueType ∧
      site.base.val + header.val < Core.wordModulus ∧
      site.base.add header = entry.1 ∧
      entry.2 = {error := .typeMismatch valueType none, site := site.site, span := some site.span} := by
  obtain ⟨site, siteMember, keyType, valueType, index, member, keys, values, issued, diagnostic⟩ := origin
  have tokenValue : entry.1.val = site.base.val + index + 1 := by
    unfold Core.Word.ofNat? at issued
    split at issued
    · exact congrArg Fin.val (Option.some.inj issued).symm
    · contradiction
  have bounded : site.base.val + index + 1 < Core.wordModulus := by
    rw [← tokenValue]
    exact entry.1.isLt
  let header : Core.Word := ⟨index + 1, by omega⟩
  have indexed := List.mem_zipIdx member
  have found : registry.entries[index]? = some (.mapping keyType valueType) := by
    rw [List.getElem?_eq_getElem (by simpa using indexed.2.1)]
    simpa only [Nat.sub_zero] using congrArg some indexed.2.2.symm
  have lookup : registry.lookup header = some (.mapping keyType valueType) := by
    simp [SourceCoreRawMetadata.Registry.lookup, header, found]
  have reserved : site.base.val + header.val < Core.wordModulus := by
    simpa only [header, Nat.add_assoc] using bounded
  have added : site.base.add header = entry.1 := by
    apply Fin.ext
    change (site.base.val + (index + 1)) % Core.wordModulus = entry.1.val
    rw [tokenValue]
    simpa only [Nat.add_assoc] using
      (Nat.mod_eq_of_lt (by simpa only [header, Nat.add_assoc] using bounded))
  exact ⟨site, siteMember, keyType, valueType, header, lookup, keys, values, reserved, added, diagnostic⟩

/-- The same successful rebuild keeps the original table fields, fixed
diagnostics and exactly the newly issued raw-header diagnostics. -/
theorem Program.tableForRegistry_receipt {context : Context} {program : Program context}
    {registry : SourceCoreRawMetadata.Registry}
    {extension : SourceCoreRawMetadata.Extends program.context.registry registry}
    {table : SourceCoreFaultSites.Table}
    (accepted : program.tableForRegistry registry extension = .ok table) :
    ∃ extra,
      missingDiagnostics registry program.missing = .ok extra ∧
      table = {program.program.rootTable with additional := program.fixed ++ extra} ∧
      ∀ entry ∈ extra, MissingDiagnosticOrigin registry program.missing entry := by
  unfold Program.tableForRegistry at accepted
  cases issued : missingDiagnostics registry program.missing with
  | error error => simp [issued, bind, Except.bind] at accepted
  | ok extra =>
    simp only [issued, bind, Except.bind, pure, Except.pure, Except.ok.injEq] at accepted
    cases accepted
    exact ⟨extra, rfl, rfl, missingDiagnostics_origins issued⟩

end Solcore.Frontend.SourceCoreCompatibleDataPlaceFaultSites
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreRawMetadataRuntime
/-! The metadata registry and the shared source-value carrier use the same
runtime type compatibility relation. This bridge imports the carrier only;
there is no source expression or statement evaluator dependency. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreRawMetadata

/-- The source runtime's normalization is the metadata view followed by its
own normalization, which also gives the fixed-width integer types the runtime
type `word`. -/
theorem runtimeType_sourceValues (type : TypeSystem.Ty) :
    SourceTypedRuntime.runtimeType (runtimeType type) = SourceTypedRuntime.runtimeType type := by
  induction type
  case constructor id => rfl
  all_goals simp_all [runtimeType]

theorem Inserted.source_runtime_compatible {before : Registry} {expected : TypeSystem.Ty} {metadata : Metadata}
    (inserted : Inserted before expected metadata) :
    SourceTypedRuntime.runtimeType expected = SourceTypedRuntime.runtimeType metadata.type := by
  rw [← runtimeType_sourceValues expected, ← runtimeType_sourceValues metadata.type,
    inserted.runtime_compatible]

end Solcore.Frontend.SourceCoreRawMetadata
end
