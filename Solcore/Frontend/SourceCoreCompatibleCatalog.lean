import Solcore.Frontend.SourceCoreRawMetadata
import Solcore.Frontend.SourceCoreDataCatalog
import Solcore.Frontend.SourceCoreMappingWithDefault

/-! A separate native representation for the historical source-value boundary.
Runtime-compatible nominal instantiations share one native data identity, while
raw metadata words remain in values. The strict catalog and its interpretation
are unchanged. Mapping entries use the ordinary ordered-list library; their
outer carrier additionally transports the raw header and its actual default.

Recursive definitions reserve their native identity before visiting payloads.
The final ordinary Core checker certifies this module's own definitions and
projections. No strict catalog projection is reinterpreted as a compatible one. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreCompatibleCatalog

open TypeSystem SourceInference
abbrev Metadata := SourceCoreRawMetadata.Metadata
abbrev Registry := SourceCoreRawMetadata.Registry
abbrev Limits := SourceCoreRawMetadata.Limits
abbrev Entry := SourceCoreDataCatalog.Entry

inductive Error where
  | catalog (error : SourceCoreDataCatalog.Error)
  | metadata (error : SourceCoreRawMetadata.Error)
  deriving Repr, DecidableEq

structure Catalog where
  entries : List Entry := []
  callableContracts : Bool := true
  deriving Repr

def Catalog.definitions (catalog : Catalog) : Core.DataEnvironment :=
  catalog.entries.map (fun entry => entry.definition.getD ⟨[]⟩)

def Catalog.functionType (catalog : Catalog) (parameter result : Core.Ty) : Core.Ty :=
  if catalog.callableContracts then Core.CallableContract.functionType parameter result
  else Core.TaggedFunction.functionType parameter result

def Catalog.identity? (catalog : Catalog) (type : Ty) : Option Core.DataTypeId :=
  (catalog.entries.zipIdx.find? (fun item => decide (item.1.sourceType = SourceCoreRawMetadata.runtimeType type))).map
    (fun item => ⟨item.2⟩)

def Catalog.project (catalog : Catalog) : Ty → Except Error Core.Ty
  | .constructor (.builtin .unit) => pure .unit
  | .constructor (.builtin .bool) => pure .bool
  | .constructor (.builtin .word) => pure .word
  | .constructor (.builtin .integer) => pure .integer
  | .product left right => do pure (.product (← catalog.project left) (← catalog.project right))
  | .function parameter result => do
      pure (catalog.functionType (← catalog.project parameter) (← catalog.project result))
  | .comptime inner => catalog.project inner
  | .mapping key value => do
      let identity ← match catalog.identity? (.mapping key value) with
        | some identity => pure identity
        | none => throw (.catalog (.missingRepresentation (SourceCoreRawMetadata.runtimeType (.mapping key value))))
      let layout : Core.OrderedMapping.Layout := ⟨← catalog.project key, ← catalog.project value, identity⟩
      pure (SourceCoreMappingWithDefault.type layout)
  | type => match catalog.identity? type with
      | some identity => pure (.namedData identity)
      | none => throw (.catalog (.missingRepresentation (SourceCoreRawMetadata.runtimeType type)))

theorem Catalog.project_runtimeType (catalog : Catalog) (type : Ty) :
    catalog.project (SourceCoreRawMetadata.runtimeType type) = catalog.project type := by
  induction type <;> simp_all [Catalog.project, Catalog.identity?, SourceCoreRawMetadata.runtimeType,
    SourceCoreRawMetadata.runtimeType_idempotent] <;> rfl

private def reserve (catalog : Catalog) (type : Ty) (constructors : List ProgramDataConstructorId := []) :
    Core.DataTypeId × Catalog :=
  (⟨catalog.entries.length⟩, {catalog with entries := catalog.entries ++ [{sourceType := type, definition := none, constructors}]})

private def install (catalog : Catalog) (identity : Core.DataTypeId) (payloads : List Core.Ty) : Catalog :=
  {catalog with entries := catalog.entries.modify identity.index (fun entry => {entry with definition := some ⟨payloads⟩})}

def packTypes : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: types => .product type (packTypes types)

private def exactData (signatures : ProgramSignatures) (id : Resolved.DeclarationId) : Except Error ProgramDataSignature :=
  match signatures.dataTypes.filter (fun signature => decide (signature.id = id)) with
  | [] => throw (.catalog (.missingData id))
  | [signature] => pure signature
  | _ => throw (.catalog (.ambiguousData id))

mutual
  def registerType (signatures : ProgramSignatures) (fuel : Nat) (catalog : Catalog) (original : Ty) :
      Except Error (Catalog × Core.Ty) := do
    let type := SourceCoreRawMetadata.runtimeType original
    unless SourceCoreDataCatalog.closed type do throw (.catalog (.openType original))
    if (catalog.identity? type).isSome then return (catalog, ← catalog.project type)
    match fuel with
    | 0 => throw (.catalog .exhausted)
    | fuel + 1 => match type with
      | .constructor (.builtin _) => pure (catalog, ← catalog.project type)
      | .product left right => do
          let (catalog, left) ← registerType signatures fuel catalog left
          let (catalog, right) ← registerType signatures fuel catalog right
          pure (catalog, .product left right)
      | .function parameter result => do
          let (catalog, parameter) ← registerType signatures fuel catalog parameter
          let (catalog, result) ← registerType signatures fuel catalog result
          pure (catalog, catalog.functionType parameter result)
      | .proxy inner => do
          let (identity, catalog) := reserve catalog type
          let (catalog, _) ← registerType signatures fuel catalog inner
          pure (install catalog identity [.word], .namedData identity)
      | .mapping key value => do
          let (identity, catalog) := reserve catalog type
          let (catalog, key) ← registerType signatures fuel catalog key
          let (catalog, value) ← registerType signatures fuel catalog value
          let layout : Core.OrderedMapping.Layout := ⟨key, value, identity⟩
          pure (install catalog identity layout.definition.constructorPayloadTypes, SourceCoreMappingWithDefault.type layout)
      | _ => do
          let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts type with
            | some parts => pure parts
            | none => throw (.catalog (.unsupportedType original))
          let signature ← exactData signatures declaration
          unless signature.parameters.length = arguments.length do
            throw (.catalog (.parameterCount declaration signature.parameters.length arguments.length))
          unless signature.parameters.Nodup && (signature.constructors.map (·.id)).Nodup do
            throw (.catalog (.unsupportedType original))
          for constructor in signature.constructors do
            unless constructor.id.dataType = declaration do throw (.catalog (.malformedConstructor constructor.id))
          let substitution : ParameterSubstitution := signature.parameters.zip arguments
          let (identity, catalog) := reserve catalog type (signature.constructors.map (·.id))
          let (catalog, payloads) ← registerTypes signatures fuel catalog
            (signature.constructors.map (fun constructor => Ty.productMany (constructor.payloadTypes.map substitution.apply)))
          pure (install catalog identity (payloads.map (Core.Ty.product .word)), .namedData identity)

  def registerTypes (signatures : ProgramSignatures) (fuel : Nat) (catalog : Catalog) :
      List Ty → Except Error (Catalog × List Core.Ty)
    | [] => pure (catalog, [])
    | type :: types => match fuel with
      | 0 => throw (.catalog .exhausted)
      | fuel + 1 => do
          let (catalog, type) ← registerType signatures fuel catalog type
          let (catalog, types) ← registerTypes signatures fuel catalog types
          pure (catalog, type :: types)
end

mutual
  /-- Traverse original closed types, retaining every raw constructor
  instantiation and header. Seen raw types stop nominal recursion. -/
  def discoverMetadata (signatures : ProgramSignatures) (fuel : Nat) (seen : List Ty) (type : Ty) :
      Except Error (List Ty × List Metadata) := do
    unless SourceCoreDataCatalog.closed type do throw (.catalog (.openType type))
    if type ∈ seen then return (seen, [])
    match fuel with
    | 0 => throw (.catalog .exhausted)
    | fuel + 1 =>
      let seen := seen ++ [type]
      match type with
      | .constructor (.builtin _) => pure (seen, [])
      | .comptime inner => discoverMetadata signatures fuel seen inner
      | .product left right | .function left right => discoverMetadataList signatures fuel seen [left, right]
      | .proxy inner => do
          let (seen, metadata) ← discoverMetadata signatures fuel seen inner
          pure (seen, .proxy inner :: metadata)
      | .mapping key value => do
          let (seen, metadata) ← discoverMetadataList signatures fuel seen [key, value]
          pure (seen, .mapping key value :: metadata)
      | _ => do
          let (declaration, arguments) ← match SourceCoreDataCatalog.nominalParts type with
            | some parts => pure parts
            | none => throw (.catalog (.unsupportedType type))
          let signature ← exactData signatures declaration
          unless signature.parameters.length = arguments.length do
            throw (.catalog (.parameterCount declaration signature.parameters.length arguments.length))
          let substitution : ParameterSubstitution := signature.parameters.zip arguments
          let instantiations := signature.constructors.map (fun constructor => {
            constructor := constructor.id, parameterSubstitution := substitution,
            payloadTypes := constructor.payloadTypes.map substitution.apply, resultType := type : DataConstructorInstantiation })
          let (seen, metadata) ← discoverMetadataList signatures fuel seen (instantiations.flatMap (·.payloadTypes))
          pure (seen, instantiations.map SourceCoreRawMetadata.Metadata.constructor ++ metadata)

  def discoverMetadataList (signatures : ProgramSignatures) (fuel : Nat) (seen : List Ty) :
      List Ty → Except Error (List Ty × List Metadata)
    | [] => pure (seen, [])
    | type :: types => match fuel with
      | 0 => throw (.catalog .exhausted)
      | fuel + 1 => do
          let (seen, metadata) ← discoverMetadata signatures fuel seen type
          let (seen, rest) ← discoverMetadataList signatures fuel seen types
          pure (seen, metadata ++ rest)
end

structure Checked where
  catalog : Catalog
  definitionsTyped : catalog.definitions.WellFormed
  signatures : ProgramSignatures
  staticRegistry : Registry
  registryOwner : staticRegistry.signatures = signatures

/-- Signature ownership is retained beside the separately checked compatible
definitions. The static registry derives from original source metadata, never
from the canonical native type alone. -/
def prepare (signatures : ProgramSignatures) (fuel : Nat) (types : List Ty)
    (extraStaticMetadata : List Metadata := []) (limits : Limits := {})
    (callableContracts : Bool := true) : Except Error Checked := do
  let (catalog, _) ← registerTypes signatures fuel {callableContracts} types
  for (entry, index) in catalog.entries.zipIdx do
    if entry.definition.isNone then throw (.catalog (.unfinishedDefinition index))
  let (_, metadata) ← discoverMetadataList signatures fuel [] types
  match registered : SourceCoreRawMetadata.prepare signatures (metadata ++ extraStaticMetadata) limits with
  | .error error => throw (.metadata error)
  | .ok registry =>
      if accepted : catalog.definitions.isWellFormed = true then
        pure ⟨catalog, Core.DataEnvironment.isWellFormed_sound accepted, signatures, registry,
          SourceCoreRawMetadata.prepare_signatures registered⟩
      else throw (.catalog .invalidDefinitions)

private theorem bind_ok {α β ε : Type} {action : Except ε α} {next : α → Except ε β} {output : β}
    (accepted : action >>= next = .ok output) : ∃ value, action = .ok value ∧ next value = .ok output := by
  cases action with
  | error error => cases accepted
  | ok value => exact ⟨value, rfl, accepted⟩

/-- The catalog factory retains the supplied source signature owner. -/
theorem prepare_signatures {signatures : ProgramSignatures} {fuel : Nat} {types : List Ty}
    {metadata : List Metadata} {limits : Limits} {callableContracts : Bool} {checked : Checked}
    (accepted : prepare signatures fuel types metadata limits callableContracts = .ok checked) :
    checked.signatures = signatures := by
  unfold prepare at accepted
  obtain ⟨registered, _, accepted⟩ := bind_ok accepted
  rcases registered with ⟨catalog, nativeTypes⟩
  obtain ⟨_, _, accepted⟩ := bind_ok accepted
  obtain ⟨discovered, _, accepted⟩ := bind_ok accepted
  rcases discovered with ⟨seen, original⟩
  dsimp only at accepted
  split at accepted
  · cases accepted
  · split at accepted
    · cases accepted; rfl
    · cases accepted

structure Projection (definitions : Core.DataEnvironment) where
  type : Core.Ty
  typed : type.WellFormed definitions
  deriving Repr

def Checked.project (checked : Checked) (type : Ty) : Except Error (Projection checked.catalog.definitions) := do
  let native ← checked.catalog.project type
  if accepted : native.isWellFormed checked.catalog.definitions = true then
    pure ⟨native, Core.Ty.isWellFormed_sound accepted⟩
  else throw (.catalog (.invalidProjection type native))

def Catalog.mappingLayout (catalog : Catalog) (key value : Ty) : Except Error Core.OrderedMapping.Layout := do
  let identity ← match catalog.identity? (.mapping key value) with
    | some identity => pure identity
    | none => throw (.catalog (.missingRepresentation (.mapping key value)))
  let layout : Core.OrderedMapping.Layout := ⟨← catalog.project key, ← catalog.project value, identity⟩
  unless catalog.definitions[identity.index]? = some layout.definition do
    throw (.catalog (.invalidProjection (.mapping key value) (SourceCoreMappingWithDefault.type layout)))
  pure layout

def Catalog.constructor? (catalog : Catalog) (instantiation : DataConstructorInstantiation) : Option Core.ConstructorId := do
  let identity ← catalog.identity? instantiation.resultType
  let entry ← catalog.entries[identity.index]?
  let (_, index) ← entry.constructors.zipIdx.find? (fun item => decide (item.1 = instantiation.constructor))
  pure ⟨identity, index⟩

def Checked.resolveConstructor (checked : Checked) (instantiation : DataConstructorInstantiation) : Except Error Core.ConstructorId := do
  unless SourceCoreRawMetadata.constructorAuthentic checked.signatures instantiation do
    throw (.metadata (.invalidConstructor instantiation))
  let constructor ← match checked.catalog.constructor? instantiation with
    | some constructor => pure constructor
    | none => throw (.catalog (.missingRepresentation instantiation.resultType))
  let payloads ← instantiation.payloadTypes.mapM checked.catalog.project
  unless checked.catalog.definitions.lookupConstructorPayloadType? constructor = some (.product .word (packTypes payloads)) do
    throw (.catalog (.malformedConstructor instantiation.constructor))
  pure constructor

end Solcore.Frontend.SourceCoreCompatibleCatalog
