import Solcore.Frontend.SourceCompilationPlan
import Solcore.Core.TaggedFunction
import Solcore.Core.Data

/-! Closed source data identities and their ordinary Core definitions.
The builder reserves an identity before visiting its payloads, so recursive
nominal definitions share one identity. Mapping and proxy add data definitions,
not Core syntax. Integer uses the kernel scalar carrier. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataCatalog

open TypeSystem SourceInference

inductive Error where
  | exhausted
  | openType (type : Ty)
  | unsupportedType (type : Ty)
  | missingData (id : Resolved.DeclarationId)
  | ambiguousData (id : Resolved.DeclarationId)
  | parameterCount (id : Resolved.DeclarationId) (expected actual : Nat)
  | malformedConstructor (id : ProgramDataConstructorId)
  | missingRepresentation (type : Ty)
  | unfinishedDefinition (index : Nat)
  | invalidDefinitions
  | invalidProjection (type : Ty) (projected : Core.Ty)
  deriving Repr, DecidableEq

/-- Representation keys erase outer staging wrappers while retaining observable
nominal arguments and proxy identities. Their payloads are projected separately. -/
def erase : Ty → Ty
  | .application function argument => .application function argument
  | .function parameter result => .function (erase parameter) (erase result)
  | .product left right => .product (erase left) (erase right)
  | .mapping key value => .mapping (erase key) (erase value)
  | .proxy inner => .proxy inner
  | .comptime inner => erase inner
  | type => type

def closed : Ty → Bool
  | .variable _ | .parameter _ | .error => false
  | .application left right | .function left right | .product left right
  | .mapping left right => closed left && closed right
  | .proxy inner | .comptime inner => closed inner
  | .constructor _ => true

def nominalParts : Ty → Option (Resolved.DeclarationId × List Ty)
  | .constructor (.declaration id) => some (id, [])
  | .application function argument => do
      let (id, arguments) ← nominalParts function
      pure (id, arguments ++ [argument])
  | _ => none

structure Entry where
  sourceType : Ty
  definition : Option Core.DataDefinition
  constructors : List ProgramDataConstructorId := []
  deriving Repr

structure Catalog where
  entries : List Entry := []
  deriving Repr

def Catalog.definitions (catalog : Catalog) : Core.DataEnvironment :=
  catalog.entries.map fun entry => entry.definition.getD ⟨[]⟩

def Catalog.identity? (catalog : Catalog) (type : Ty) : Option Core.DataTypeId :=
  (catalog.entries.zipIdx.find? fun item => decide (item.1.sourceType = erase type)).map
    fun item => ⟨item.2⟩

def Catalog.project (catalog : Catalog) : Ty → Except Error Core.Ty
  | .constructor (.builtin .unit) => pure .unit
  | .constructor (.builtin .bool) => pure .bool
  | .constructor (.builtin .word) => pure .word
  | .constructor (.builtin .integer) => pure .integer
  | .product left right => do pure (.product (← catalog.project left) (← catalog.project right))
  | .function parameter result => do
      pure (Core.TaggedFunction.functionType (← catalog.project parameter) (← catalog.project result))
  | .comptime inner => catalog.project inner
  | type => match catalog.identity? type with
      | some identity => pure (.namedData identity)
      | none => throw (.missingRepresentation type)

private def Catalog.reserve (catalog : Catalog) (type : Ty)
    (constructors : List ProgramDataConstructorId := []) : Core.DataTypeId × Catalog :=
  (⟨catalog.entries.length⟩,
    { catalog with entries := catalog.entries ++ [{ sourceType := type, definition := none, constructors }] })

private def Catalog.install (catalog : Catalog) (id : Core.DataTypeId)
    (payloads : List Core.Ty) : Catalog :=
  { catalog with entries := catalog.entries.modify id.index fun entry =>
      { entry with definition := some ⟨payloads⟩ } }

private def productMany : List Core.Ty → Core.Ty
  | [] => .unit
  | [type] => type
  | type :: types => .product type (productMany types)

private def exactData (signatures : ProgramSignatures) (id : Resolved.DeclarationId) :
    Except Error ProgramDataSignature :=
  match signatures.dataTypes.filter fun item => decide (item.id = id) with
  | [] => throw (.missingData id)
  | [item] => pure item
  | _ => throw (.ambiguousData id)

mutual
  /-- The budget bounds both discovery depth and payload/list traversal. A
  previously reserved type may be referenced even at depth zero. -/
  def registerType (signatures : ProgramSignatures) (fuel : Nat)
      (catalog : Catalog) (sourceType : Ty) : Except Error (Catalog × Core.Ty) := do
    let type := erase sourceType
    unless closed type do throw (.openType type)
    if let some identity := catalog.identity? type then
      return (catalog, .namedData identity)
    match fuel with
    | 0 => throw .exhausted
    | fuel + 1 =>
      match type with
      | .constructor (.builtin _) => pure (catalog, ← catalog.project type)
      | .product left right => do
          let (catalog, left) ← registerType signatures fuel catalog left
          let (catalog, right) ← registerType signatures fuel catalog right
          pure (catalog, .product left right)
      | .function parameter result => do
          let (catalog, parameter) ← registerType signatures fuel catalog parameter
          let (catalog, result) ← registerType signatures fuel catalog result
          pure (catalog, Core.TaggedFunction.functionType parameter result)
      | .proxy inner => do
          let (catalog, _) ← registerType signatures fuel catalog inner
          let (identity, catalog) := catalog.reserve type
          pure (catalog.install identity [.unit], .namedData identity)
      | .mapping key value => do
          let (identity, catalog) := catalog.reserve type
          let (catalog, key) ← registerType signatures fuel catalog key
          let (catalog, value) ← registerType signatures fuel catalog value
          pure (catalog.install identity
            [.unit, .product (.product key value) (.namedData identity)], .namedData identity)
      | _ => do
          let (id, arguments) ← match nominalParts type with
            | some parts => pure parts
            | none => throw (.unsupportedType type)
          let signature ← exactData signatures id
          if signature.parameters.length ≠ arguments.length then
            throw (.parameterCount id signature.parameters.length arguments.length)
          unless signature.parameters.Nodup do throw (.unsupportedType type)
          unless (signature.constructors.map (·.id)).Nodup do throw (.unsupportedType type)
          for constructor in signature.constructors do
            unless constructor.id.dataType = id do throw (.malformedConstructor constructor.id)
          let substitution : ParameterSubstitution := signature.parameters.zip arguments
          let payloads := signature.constructors.map fun constructor =>
            Ty.productMany (constructor.payloadTypes.map substitution.apply)
          let (identity, catalog) := catalog.reserve type (signature.constructors.map (·.id))
          let (catalog, payloads) ← registerTypes signatures fuel catalog payloads
          pure (catalog.install identity payloads, .namedData identity)

  def registerTypes (signatures : ProgramSignatures) (fuel : Nat)
      (catalog : Catalog) (types : List Ty) : Except Error (Catalog × List Core.Ty) :=
    match types with
    | [] => pure (catalog, [])
    | type :: types => match fuel with
      | 0 => throw .exhausted
      | fuel + 1 => do
          let (catalog, type) ← registerType signatures fuel catalog type
          let (catalog, types) ← registerTypes signatures fuel catalog types
          pure (catalog, type :: types)
end

structure Checked where
  catalog : Catalog
  definitionsTyped : catalog.definitions.WellFormed
  deriving Repr

/-- Finalize once before executable lowering. Placeholder definitions cannot
escape this API, and the ordinary Core definition checker authenticates every
recursive payload reference. -/
def prepare (signatures : ProgramSignatures)
    (fuel : Nat) (types : List Ty) : Except Error Checked := do
  let (catalog, _) ← registerTypes signatures fuel {} types
  for (entry, index) in catalog.entries.zipIdx do
    if entry.definition.isNone then throw (.unfinishedDefinition index)
  if accepted : catalog.definitions.isWellFormed = true then
    pure { catalog, definitionsTyped := Core.DataEnvironment.isWellFormed_sound accepted }
  else throw .invalidDefinitions

structure Projection (definitions : Core.DataEnvironment) where
  type : Core.Ty
  typed : type.WellFormed definitions
  deriving Repr

/-- Public consumers obtain a well-formed projected type, including structural
function types which are not themselves stored as catalog entries. -/
def Checked.project (checked : Checked) (sourceType : Ty) :
    Except Error (Projection checked.catalog.definitions) := do
  let type ← checked.catalog.project sourceType
  if accepted : type.isWellFormed checked.catalog.definitions = true then
    pure { type, typed := Core.Ty.isWellFormed_sound accepted }
  else throw (.invalidProjection sourceType type)

def Catalog.constructor? (catalog : Catalog) (instantiation : DataConstructorInstantiation) :
    Option Core.ConstructorId := do
  let identity ← catalog.identity? instantiation.resultType
  let entry ← catalog.entries[identity.index]?
  let (_, index) ← entry.constructors.zipIdx.find? fun item => decide (item.1 = instantiation.constructor)
  pure ⟨identity, index⟩

/-- Authenticate source constructor metadata against the exact signature
catalog before selecting its Core constructor. The low-level lookup alone does
not establish that its payload metadata is genuine. -/
def Catalog.resolveConstructor (catalog : Catalog) (signatures : ProgramSignatures)
    (instantiation : DataConstructorInstantiation) : Except Error Core.ConstructorId := do
  let signature ← exactData signatures instantiation.constructor.dataType
  let constructor ← match signature.constructors.filter fun item =>
      decide (item.id = instantiation.constructor) with
    | [constructor] => pure constructor
    | _ => throw (.malformedConstructor instantiation.constructor)
  unless instantiation.parameterSubstitution.map Prod.fst = signature.parameters do
    throw (.malformedConstructor instantiation.constructor)
  let arguments := instantiation.parameterSubstitution.map Prod.snd
  unless arguments.all closed do throw (.openType instantiation.resultType)
  unless instantiation.resultType = Ty.nominal signature.id arguments do
    throw (.malformedConstructor instantiation.constructor)
  unless instantiation.payloadTypes = constructor.payloadTypes.map instantiation.parameterSubstitution.apply do
    throw (.malformedConstructor instantiation.constructor)
  let identity ← match catalog.constructor? instantiation with
    | some identity => pure identity
    | none => throw (.missingRepresentation instantiation.resultType)
  let payloadTypes ← instantiation.payloadTypes.mapM catalog.project
  unless catalog.definitions.lookupConstructorPayloadType? identity = some (productMany payloadTypes) do
    throw (.malformedConstructor instantiation.constructor)
  pure identity

def Catalog.proxyValue? (catalog : Catalog) (inner : Ty) : Option Core.Value := do
  let identity ← catalog.identity? (.proxy inner)
  pure (.constructed ⟨identity, 0⟩ .unit)

def Catalog.emptyMapping? (catalog : Catalog) (key value : Ty) : Option Core.Value := do
  let identity ← catalog.identity? (.mapping key value)
  pure (.constructed ⟨identity, 0⟩ .unit)

end Solcore.Frontend.SourceCoreDataCatalog
