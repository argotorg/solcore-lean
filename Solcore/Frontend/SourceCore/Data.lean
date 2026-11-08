import Solcore.Frontend.SourceCompilationPlan
import Solcore.Core.Internal.ConventionLaws
import Solcore.Core.Data
import Solcore.Core.Internal.MappingLaws

/-!
# Data catalog

Closed data identities, their Core definitions, equality and defaults. This file stays below
lowering, because CoreLowering imports it and a wider closure changes its `simp` calls. Main
declarations: `SourceCoreDataCatalog.Catalog`, `SourceCoreDataCatalog.Error`.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataCatalog
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
  callableContracts : Bool := false
  deriving Repr

/-- Function representation is fixed for the entire catalog, including nominal
and mapping payloads. Existing callers retain their tagged carrier by default. -/
def Catalog.functionType (catalog : Catalog) (parameter result : Core.Ty) : Core.Ty :=
  if catalog.callableContracts then Core.CallableContract.functionType parameter result
  else Core.TaggedFunction.functionType parameter result

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
      pure (catalog.functionType (← catalog.project parameter) (← catalog.project result))
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
          pure (catalog, catalog.functionType parameter result)
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
    (fuel : Nat) (types : List Ty) (callableContracts : Bool := false) : Except Error Checked := do
  let (catalog, _) ← registerTypes signatures fuel { callableContracts } types
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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDataEquality
/-! Equality is ordinary Core code. A preparation expression allocates all
catalog comparator cells once, installs mutually recursive closures, then
returns the requested comparator. Its invocation bodies contain no allocation
or write. Source metadata authenticity is a separate representation premise. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDataEquality

open Core

inductive Error where
  | catalog (error : SourceCoreDataCatalog.Error)
  | exhausted
  | unsupportedCarrier (type : Core.Ty)
  | missingEntry (id : DataTypeId)
  | missingDefinition (id : DataTypeId)
  | checkFailed (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

abbrev Catalog := SourceCoreDataCatalog.Catalog

def comparatorType (type : Core.Ty) : Core.Ty := .function (.product type type) .bool

def referenceIndex (catalog : Catalog) (depth : Nat) (id : DataTypeId) : Nat :=
  depth + (catalog.entries.length - 1 - id.index)

/-- The absent branch is unreachable after installation. It remains a total
ordinary sum elimination and introduces no language or machine failure. -/
def invoke (reference left right : Expr) : Expr :=
  .caseE (.loadCell reference) (.bool false)
    (.apply (.var 0) (.pair (left.weakenAt 0) (right.weakenAt 0)))

/-- Raw tagged-function equality; only the identity tags are observed. -/
def functionEqual (left right : Expr) : Expr :=
  .letE left (.letE (right.weakenAt 0) TaggedFunction.equalBody)

/-- The descriptor is a call contract, while source equality observes only
the tagged function's identity. This shape is special only in that profile. -/
def isCallableContractType : Core.Ty → Bool
  | .product (.product (.sum .unit .word) (.function _ (.sum .word _))) .word => true
  | _ => false

/-- Function patterns are selected according to the catalog profile. A source
product containing a function therefore retains its ordinary product fields. -/
def compareType (fuel : Nat) (catalog : Catalog) (depth : Nat)
    (type : Core.Ty) (left right : Expr) : Except Error Expr :=
  match fuel with
  | 0 => throw .exhausted
  | fuel + 1 => match type with
    | .unit => pure (.bool true)
    | .bool => pure (.ifE left right (.unary .boolNot right))
    | .word => pure (.binary .wordEq left right)
    | .integer => pure (.binary .integerEq left right)
    | .product (.sum .unit .word) (.function _ (.sum .word _)) =>
        pure (functionEqual left right)
    | .product first second => do
        if catalog.callableContracts && isCallableContractType type then
          pure (functionEqual (.first left) (.first right))
        else
          pure (.ifE
            (← compareType fuel catalog depth first (.first left) (.first right))
            (← compareType fuel catalog depth second (.second left) (.second right))
            (.bool false))
    | .namedData id => do
        let entry ← match catalog.entries[id.index]? with
          | some entry => pure entry
          | none => throw (.missingEntry id)
        match entry.sourceType with
        | .mapping _ _ => pure (.bool false)
        | .proxy _ => pure (.bool true)
        | _ => pure (invoke (.var (referenceIndex catalog depth id)) left right)
    | _ => throw (.unsupportedCarrier type)

def nominalBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId)
    (payloads : List Core.Ty) : Except Error Expr := do
  let branches ← payloads.zipIdx.mapM fun (payload, leftIndex) => do
    let inner ← payloads.zipIdx.mapM fun (_, rightIndex) => do
      if leftIndex = rightIndex then
        compareType fuel catalog 3 payload (.var 1) (.var 0)
      else pure (.bool false)
    pure (.matchData id .bool (.second (.var 1)) inner)
  pure (.matchData id .bool (.first (.var 0)) branches)

def helperBody (fuel : Nat) (catalog : Catalog) (id : DataTypeId) : Except Error Expr := do
  let entry ← match catalog.entries[id.index]? with
    | some entry => pure entry
    | none => throw (.missingEntry id)
  match entry.sourceType with
  | .mapping _ _ => pure (.bool false)
  | .proxy _ => pure (.bool true)
  | _ =>
    let definition ← match entry.definition with
      | some definition => pure definition
      | none => throw (.missingDefinition id)
    nominalBody fuel catalog id definition.constructorPayloadTypes

/-- Bodies are prepared in catalog order, while the captured cell environment
is newest first. A write's temporary Unit binder is removed by weakening the
remaining installation code. -/
def install (catalog : Catalog) (bodies : List Expr) (next : Expr) : Expr :=
  (bodies.zipIdx).foldr (fun (body, index) next =>
    .letE (.storeCell (.var (referenceIndex catalog 0 ⟨index⟩))
      (.inRight .unit (.lambda (.product (.namedData ⟨index⟩) (.namedData ⟨index⟩)) .bool body)))
      (next.weakenAt 0)) next

def allocate (catalog : Catalog) (next : Expr) : Expr :=
  (catalog.entries.zipIdx).foldr (fun (_, index) next =>
    .letE (OptionalCell.allocate (comparatorType (.namedData ⟨index⟩))) next) next

def helperBodies (fuel : Nat) (catalog : Catalog) : Except Error (List Expr) :=
  catalog.entries.zipIdx.mapM fun (_, index) => helperBody fuel catalog ⟨index⟩

structure Prepared (checked : SourceCoreDataCatalog.Checked) where
  sourceType : TypeSystem.Ty
  type : Core.Ty
  projection : checked.catalog.project sourceType = .ok type
  compilationFuel : Nat
  bodies : List Expr
  bodiesGenerated : helperBodies compilationFuel checked.catalog = .ok bodies
  body : Expr
  bodyGenerated : compareType compilationFuel checked.catalog 1 type (.first (.var 0)) (.second (.var 0)) = .ok body
  expression : Expr
  expression_eq : expression = allocate checked.catalog
    (install checked.catalog bodies (.lambda (.product type type) .bool body))
  typed : HasType [] expression (comparatorType type) checked.catalog.definitions
  deriving Repr

/-- All preparation effects precede every comparison, including comparisons
performed later by OrderedMapping in an extended store. -/
def prepare (fuel : Nat) (checked : SourceCoreDataCatalog.Checked)
    (sourceType : TypeSystem.Ty) : Except Error (Prepared checked) := do
  match projected : checked.catalog.project sourceType with
  | .error error => throw (.catalog error)
  | .ok type =>
    match bodiesGenerated : helperBodies fuel checked.catalog with
    | .error error => throw error
    | .ok bodies =>
      match bodyGenerated : compareType fuel checked.catalog 1 type (.first (.var 0)) (.second (.var 0)) with
      | .error error => throw error
      | .ok body =>
        let expression := allocate checked.catalog
          (install checked.catalog bodies (.lambda (.product type type) .bool body))
        if accepted : infer? [] expression checked.catalog.definitions = some (comparatorType type) then
          pure {
            sourceType, type, projection := projected, compilationFuel := fuel, bodies,
            bodiesGenerated, body, bodyGenerated, expression, expression_eq := rfl, typed := infer_sound accepted
          }
        else throw (.checkFailed (comparatorType type) (infer? [] expression checked.catalog.definitions))

/- Syntactic read-only audit. This does not imply termination: the finite
comparison theorem additionally follows the related values' constructor tree. -/
mutual
  def ReadOnly : Expr → Prop
    | .newCell _ _ | .storeCell _ _ => False
    | .pair a b | .apply a b | .binary _ a b | .letE a b => ReadOnly a ∧ ReadOnly b
    | .first a | .second a | .lambda _ _ a | .inLeft _ a | .inRight _ a
    | .loadCell a | .construct _ a | .unary _ a => ReadOnly a
    | .caseE a b c | .ternary _ a b c | .ifE a b c => ReadOnly a ∧ ReadOnly b ∧ ReadOnly c
    | .matchData _ _ a branches => ReadOnly a ∧ ReadOnlyList branches
    | _ => True
  def ReadOnlyList : List Expr → Prop
    | [] => True
    | x :: xs => ReadOnly x ∧ ReadOnlyList xs
end

end Solcore.Frontend.SourceCoreDataEquality
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreDefaultValue
/-! Optional source defaults, generated as ordinary Core values. Absence is
returned to the caller so its own language-failure policy remains explicit. -/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreDefaultValue

open Core
abbrev Error := SourceCoreDataEquality.Error
abbrev Catalog := SourceCoreDataCatalog.Catalog

def defaultExpression (fuel : Nat) (catalog : Catalog) (type : TypeSystem.Ty) :
    Except Error (Option Expr) :=
  match fuel with
  | 0 => throw .exhausted
  | fuel + 1 => match type with
    | .constructor (.builtin .unit) => pure (some .unit)
    | .constructor (.builtin .bool) => pure (some (.bool false))
    | .constructor (.builtin .word) => pure (some (.word Word.zero))
    | .constructor (.builtin .integer) => pure (some (.integer 0))
    | .product left right => do
        let left ← defaultExpression fuel catalog left
        let right ← defaultExpression fuel catalog right
        pure (do pure (.pair (← left) (← right)))
    | .proxy _ | .mapping _ _ =>
        match catalog.identity? type with
        | some id => pure (some (.construct ⟨id, 0⟩ .unit))
        | none => throw (.catalog (.missingRepresentation type))
    | .comptime inner => defaultExpression fuel catalog inner
    | _ => pure none

def wrap (type : Core.Ty) : Option Expr → Expr
  | none => .inLeft type .unit
  | some value => .inRight .unit value

structure Prepared (checked : SourceCoreDataCatalog.Checked) where
  sourceType : TypeSystem.Ty
  type : Core.Ty
  projection : checked.catalog.project sourceType = .ok type
  compilationFuel : Nat
  default : Option Expr
  generated : defaultExpression compilationFuel checked.catalog sourceType = .ok default
  expression : Expr
  expression_eq : expression = wrap type default
  typed : HasType [] expression (.sum .unit type) checked.catalog.definitions
  deriving Repr

def prepare (fuel : Nat) (checked : SourceCoreDataCatalog.Checked)
    (sourceType : TypeSystem.Ty) : Except Error (Prepared checked) := do
  match projected : checked.catalog.project sourceType with
  | .error error => throw (.catalog error)
  | .ok type =>
    match generated : defaultExpression fuel checked.catalog sourceType with
    | .error error => throw error
    | .ok default =>
      let expression := wrap type default
      if accepted : infer? [] expression checked.catalog.definitions = some (.sum .unit type) then
        pure {
          sourceType, type, projection := projected, compilationFuel := fuel,
          default, generated, expression, expression_eq := rfl, typed := infer_sound accepted
        }
      else throw (.checkFailed (.sum .unit type) (infer? [] expression checked.catalog.definitions))

end Solcore.Frontend.SourceCoreDefaultValue
end
