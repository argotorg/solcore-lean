import Solcore.Frontend.SourceCoreCompatibleFunctions
import Solcore.Frontend.SourceCoreCompatibleInputs
import Solcore.Frontend.SourceCoreCompatibleMarkedFunctions
import Solcore.Frontend.SourceCoreCallableAncestryPrograms
import Solcore.Frontend.SourceCoreCallablePairedPrograms

/-! Reverse source values from a cached compatible artifact. Named outputs
must match both the installed global slot and its prepared code/capture
snapshot. Builtins match the closed native template and the actual typed
world. Descriptor words alone never authenticate arbitrary closure payloads.

Preparation retains source evidence once. Decoding reads no source graph and
resolves no evidence. This initial boundary covers fresh source invocations
whose globals begin at Core location zero. Lambda/source heap reconstruction
requires the later allocation/capture ledger and is explicitly rejected here. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleOutputs
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Prepared := SourceCoreCompatibleFunctions.Prepared
abbrev Values := SourceCoreCompatibleValues.Context
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Origin := SourceCoreStageCodebook.Origin
abbrev PathStep := SourceCoreDataValues.PathStep

inductive ErrorCode where
  | sourceInputsUnavailable
  | source (error : SourceCompilationPlan.Error)
  | codec (error : SourceCoreCompatibleValues.ErrorCode)
  | catalog (error : SourceCoreCompatibleCatalog.Error)
  | missingCodebook
  | missingOrigin (origin : Origin)
  | malformedTemplate (index : Nat)
  | templateTypeMismatch (index : Nat)
  | missingGlobalSlot (index : Nat)
  | globalSlotMismatch (index : Nat)
  | unknownDescriptor (id : Core.Word)
  | callableIdentityMismatch
  | callablePayloadMismatch
  | lambdaExportRequiresLedger (origin : Origin)
  | unsupportedCallableProfile
  | externalReferenceUnsupported
  | externalHostUnsupported
  | exhausted
  | notSucceeded
  deriving Repr

structure Error where
  path : List PathStep := []
  code : ErrorCode
  deriving Repr
private def Error.at (step : PathStep) (error : Error) : Error := {error with path := step :: error.path}
private def fromCodec (error : SourceCoreCompatibleValues.Error) : Error := ⟨error.path, .codec error.code⟩

private structure Named where
  key : Key
  sourceType : Ty
  evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment
  identity : Core.Word
  descriptor : Core.Word
  location : Nat
  closure : Core.Value

private structure Builtin where
  function : BuiltinFunctionId
  identity : Core.Word
  descriptor : Core.Word
  input : Core.Ty
  output : Core.Ty
  body : Core.Expr

inductive ArtifactOrigin (checked : Checked) where
  | ordinary (prepared : Prepared checked)
  | marked (prepared : SourceCoreCompatibleMarkedFunctions.Prepared checked)
  | ancestry (prepared : SourceCoreCallableAncestryPrograms.Prepared checked)
  | paired (prepared : SourceCoreCallablePairedPrograms.Prepared checked)

def ArtifactOrigin.base {checked : Checked} : ArtifactOrigin checked → Prepared checked
  | .ordinary prepared => prepared
  | .marked prepared => prepared.base
  | .ancestry prepared => prepared.base
  | .paired prepared => prepared.base

def ArtifactOrigin.definitions {checked : Checked} : ArtifactOrigin checked → Core.DataEnvironment
  | .ordinary _ => checked.catalog.definitions
  | .marked prepared => prepared.layouts.definitions
  | .ancestry prepared => prepared.layouts.definitions
  | .paired prepared => prepared.layouts.definitions

def ArtifactOrigin.closures {checked : Checked} : ArtifactOrigin checked → List Core.Expr
  | .ordinary prepared => prepared.closures
  | .marked prepared => prepared.secondPass.closures
  | .ancestry prepared => prepared.secondPass.closures
  | .paired prepared => prepared.secondPass.closures

def ArtifactOrigin.inputContext? {checked : Checked} : ArtifactOrigin checked → Option SourceCoreCompatibleInputs.Context
  | .ordinary prepared => prepared.sourceInputs.map (·.context)
  | .marked prepared => some prepared.sourceInputs.context
  | .ancestry prepared => some prepared.sourceInputs.context
  | .paired prepared => some prepared.sourceInputs.context

/-- The administrative reference follows every source-global reference. -/
def ArtifactOrigin.contextSuffix {checked : Checked} : ArtifactOrigin checked → Core.Context
  | .ordinary _ | .marked _ => []
  | .ancestry prepared => [prepared.ancestry.layout.referenceType]
  | .paired prepared => [prepared.ancestry.layout.referenceType]

def ArtifactOrigin.environmentSuffix {checked : Checked} : ArtifactOrigin checked → Core.Environment
  | .ordinary _ | .marked _ => []
  | .ancestry prepared => [.cellRef prepared.ancestry.layout.frame.type 0]
  | .paired prepared => [.cellRef prepared.ancestry.layout.frame.type 0]

def ArtifactOrigin.globalBase {checked : Checked} : ArtifactOrigin checked → Nat
  | .ordinary _ | .marked _ => 0
  | .ancestry _ => 1
  | .paired _ => 1

structure Recipe (checked : Checked) (definitions : Core.DataEnvironment := checked.catalog.definitions) where private mk ::
  private origin : ArtifactOrigin checked
  private definitionsExact : origin.definitions = definitions
  private named : List Named
  private builtins : List Builtin

private def identified (index : Nat) : Except Error Core.Word :=
  match Core.Word.ofNat? (index + 1) with
  | some word => pure word
  | none => throw ⟨[], .malformedTemplate index⟩

private def descriptor (table : SourceCoreStageCodebook.Table) (origin : Origin) : Except Error Core.Word :=
  match table.idAt? origin with
  | some word => pure word
  | none => throw ⟨[], .missingOrigin origin⟩

/-- Match the exact administrative weakening performed by installFunctions.
This Core-only traversal runs once at artifact preparation. -/
def installedTemplate (index : Nat) (expression : Core.Expr) : Core.Expr :=
  (List.range index).foldl (fun expression _ => expression.weakenAt 0) expression

/-- Fresh source invocation globals are allocated in plan order, then appear
newest first in the lexical environment. No source prefix is imported here. -/
def freshGlobals (globals : List SourceCoreCalls.Signature) : Core.Environment :=
  globals.zipIdx.map fun (signature, index) =>
    .cellRef (Core.OptionalCell.cellType signature.functionType) (globals.length - 1 - index)

/-- Consume the compiler-owned cache, never caller-selected closure templates.
Evidence selection and source signature checks happen only during preparation. -/
private def prepareOrigin {checked : Checked} (origin : ArtifactOrigin checked) :
    Except Error (Recipe checked origin.definitions) := do
  let prepared := origin.base
  let closures := origin.closures
  let program := prepared.sourceProgram
  let inputContext ← match origin.inputContext? with
    | some ready => pure ready
    | none => throw ⟨[], .sourceInputsUnavailable⟩
  unless checked.catalog.callableContracts do throw ⟨[], .unsupportedCallableProfile⟩
  let table ← match prepared.callableContext with
    | some native => pure native.table | none => throw ⟨[], .missingCodebook⟩
  unless prepared.globals.length = closures.length do throw ⟨[], .malformedTemplate 0⟩
  let mut named := []
  for ((signature, expression), index) in (prepared.globals.zip closures).zipIdx do
    let specialized ← (SourceCompilationPlan.exactSpecialization prepared.plan signature.key).mapError (fun error => ⟨[], .source error⟩)
    let evidence ← (SourceCompilationPlan.resolveRuntimeEvidenceEnvironment program signature.key specialized.assumptions)
      |>.mapError (fun error => ⟨[], .source error⟩)
    discard <| (SourceCompilationPlan.validateAuthenticatedRuntimeEvidence program.signatures signature.key specialized.assumptions evidence)
      |>.mapError (fun error => ⟨[], .source error⟩)
    let template := installedTemplate index expression
    let (input, output, body) ← match template with
      | .lambda input output body => pure (input, output, body)
      | _ => throw ⟨[], .malformedTemplate index⟩
    unless input = signature.parameterType && output = Core.LanguageResult.resultType signature.resultType do
      throw ⟨[], .templateTypeMismatch index⟩
    unless Core.infer? ((List.replicate index .unit) ++ inputContext.coreContext ++ origin.contextSuffix) template origin.definitions =
        some signature.functionType do throw ⟨[], .templateTypeMismatch index⟩
    named := named ++ [⟨signature.key, specialized.function.type, evidence, ← identified index,
      ← descriptor table (.named signature.key), origin.globalBase + (prepared.globals.length - 1 - index),
      .closure input output body ((List.replicate index .unit) ++
        (freshGlobals prepared.globals).map (fun value => match value with
          | .cellRef type location => .cellRef type (origin.globalBase + location)
          | value => value) ++ origin.environmentSuffix)⟩]
  let builtins ← BuiltinFunctionId.all.zipIdx.mapM fun (function, index) => do
    let (input, output, body) ← match SourceCoreInteger.builtinClosure function with
      | .lambda input output body => pure (input, output, body)
      | _ => throw ⟨[], .malformedTemplate index⟩
    pure (⟨function, ← identified (prepared.globals.length + index),
      ← descriptor table (.builtin function), input, output, body⟩ : Builtin)
  pure (.mk origin rfl named builtins)

def prepare {checked : Checked} (prepared : Prepared checked) : Except Error (Recipe checked) :=
  prepareOrigin (.ordinary prepared)

def prepareMarked {checked : Checked} (prepared : SourceCoreCompatibleMarkedFunctions.Prepared checked) :
    Except Error (Recipe checked prepared.layouts.definitions) := prepareOrigin (.marked prepared)

def prepareAncestry {checked : Checked} (prepared : SourceCoreCallableAncestryPrograms.Prepared checked) :
    Except Error (Recipe checked prepared.layouts.definitions) := prepareOrigin (.ancestry prepared)

def preparePaired {checked : Checked} (prepared : SourceCoreCallablePairedPrograms.Prepared checked) :
    Except Error (Recipe checked prepared.layouts.definitions) := prepareOrigin (.paired prepared)

structure Snapshot {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) where private mk ::
  store : Core.Store
  stored : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store definitions
  private slots : ∀ row ∈ recipe.named, store[row.location]? = some (.inRight .unit row.closure)

private def slotError {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (store : Core.Store) : Error :=
  match recipe.named.find? (fun row => store[row.location]? != some (.inRight .unit row.closure)) with
  | some row => match store[row.location]? with
    | none => ⟨[], .missingGlobalSlot row.location⟩
    | some _ => ⟨[], .globalSlotMismatch row.location⟩
  | none => ⟨[], .globalSlotMismatch 0⟩

/-- A typed native completion supplies the store proof. Every named slot must
still equal the cache's exact fresh installation, including administrative
captures. This rejects foreign, missing and edited callable stores. -/
def snapshot {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (store : Core.Store)
    (stored : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store definitions) :
    Except Error (Snapshot recipe) := do
  if slots : ∀ row ∈ recipe.named, store[row.location]? = some (.inRight .unit row.closure) then
    pure (.mk store stored slots)
  else throw (slotError recipe store)

theorem snapshot_store {checked : Checked} {definitions : Core.DataEnvironment} {recipe : Recipe checked definitions} {store : Core.Store}
    {stored : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store definitions}
    {result : Snapshot recipe} (accepted : snapshot recipe store stored = .ok result) : result.store = store := by
  unfold snapshot at accepted
  split at accepted
  · cases accepted; rfl
  · cases accepted

private def sourceFromData : SourceCoreCompatibleValues.Value → Option SourceValue
  | .unit => some .unit
  | .bool value => some (.bool value)
  | .word value => some (.word value)
  | .integer value => some (.integer value)
  | .product left right => do pure (.product (← sourceFromData left) (← sourceFromData right))
  | .proxy inner => some (.proxy inner)
  | .constructed instantiation payloads => do pure (.constructed instantiation (← payloads.mapM sourceFromData))
  | .mapping key value entries => do pure (.mapping key value (← entries.mapM fun entry => do
      pure (← sourceFromData entry.1, ← sourceFromData entry.2)))
  decreasing_by
    all_goals first
      | decreasing_trivial
      | have smaller := List.sizeOf_lt_of_mem (by assumption)
        cases entry
        simp_all only [SourceCoreDataValues.Value.mapping.sizeOf_spec, Prod.mk.sizeOf_spec]
        omega

private def dataOnly : Core.Value → Bool
  | .closure .. | .cellRef .. | .hostFunction .. => false
  | .pair left right => dataOnly left && dataOnly right
  | .inLeft _ payload | .inRight _ payload | .constructed _ payload => dataOnly payload
  | _ => true

private def compatible (expected actual : Ty) : Except Error Unit :=
  unless SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual do
    throw ⟨[], .codec (.sourceTypeMismatch expected actual)⟩

private def metadata (context : Values) (expected : Ty) (id : Core.Word) : Except Error SourceCoreRawMetadata.Metadata := do
  let value ← match context.registry.lookup id with
    | some value => pure value | none => throw ⟨[], .codec (.unknownMetadata id)⟩
  discard <| compatible expected value.type
  pure value

private def callable {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (expected : Ty) (value : Core.Value) : Except Error SourceValue := do
  let (identity, closure, id) ← match value with
    | .pair (.pair (.inRight .unit (.word identity)) closure) (.word id) => pure (identity, closure, id)
    | .pair (.pair (.inLeft .word .unit) _) (.word id) =>
        let table ← match recipe.origin.base.callableContext with
          | some native => pure native.table | none => throw ⟨[], .missingCodebook⟩
        let row ← match table.entryAt? id with
          | some row => pure row | none => throw ⟨[], .unknownDescriptor id⟩
        match row.origin with
        | .lambda .. => throw ⟨[], .lambdaExportRequiresLedger row.origin⟩
        | _ => throw ⟨[], .callableIdentityMismatch⟩
    | .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
    | .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
    | _ => throw ⟨[], .callablePayloadMismatch⟩
  let table ← match recipe.origin.base.callableContext with
    | some native => pure native.table | none => throw ⟨[], .missingCodebook⟩
  let entry ← match table.entryAt? id with
    | some entry => pure entry | none => throw ⟨[], .unknownDescriptor id⟩
  match entry.origin with
  | .named key =>
      let row ← match recipe.named.find? (fun row => decide (row.key = key)) with
        | some row => pure row | none => throw ⟨[], .missingOrigin entry.origin⟩
      discard <| compatible expected row.sourceType
      unless identity = row.identity && id = row.descriptor do throw ⟨[], .callableIdentityMismatch⟩
      unless closure = row.closure do throw ⟨[], .callablePayloadMismatch⟩
      pure (.global row.key row.evidence)
  | .builtin function =>
      let row ← match recipe.builtins.find? (fun row => decide (row.function = function)) with
        | some row => pure row | none => throw ⟨[], .missingOrigin entry.origin⟩
      discard <| compatible expected function.type
      unless identity = row.identity && id = row.descriptor do throw ⟨[], .callableIdentityMismatch⟩
      match closure with
      | .closure input output body _ =>
          unless input = row.input && output = row.output && body = row.body do throw ⟨[], .callablePayloadMismatch⟩
          pure (.builtin row.function)
      | .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
      | .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
      | _ => throw ⟨[], .callablePayloadMismatch⟩
  | .lambda .. => throw ⟨[], .lambdaExportRequiresLedger entry.origin⟩

/-- A function leaf decoder owns its separate code, metadata and capture
receipts. Structural traversal does not certify those leaves by itself. -/
abbrev LeafDecoder := Ty → Core.Value → Except Error SourceValue

/-- The existing exact named/builtin decoder, for delegation from a richer
lambda decoder. Its recipe still authenticates the installed global slots. -/
def decodeCallable {checked : Checked} {definitions : Core.DataEnvironment}
    (recipe : Recipe checked definitions) : LeafDecoder := callable recipe

mutual
  private def decodeWithRaw {checked : Checked} {definitions : Core.DataEnvironment} : Nat → LeafDecoder → Recipe checked definitions → Values → Ty → Core.Value → Except Error SourceValue
    | 0, _, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, leaf, recipe, context, expected, value => do
        if dataOnly value then
          let data ← (SourceCoreCompatibleValues.decode (fuel + 1) context expected value).mapError fromCodec
          match sourceFromData data with
          | some value => pure value
          | none => throw ⟨[], .callablePayloadMismatch⟩
        else
          match SourceCoreRawMetadata.runtimeType expected, value with
          | .function .., value => leaf expected value
          | .product leftType rightType, .pair left right =>
              let left ← (decodeWithRaw fuel leaf recipe context leftType left).mapError (Error.at .productLeft)
              let right ← (decodeWithRaw fuel leaf recipe context rightType right).mapError (Error.at .productRight)
              pure (.product left right)
          | .mapping _ _, .pair (.word id) (.pair fallback stored) =>
              let (keyType, valueType) ← match ← metadata context expected id with
                | .mapping key value => pure (key, value)
                | _ => throw ⟨[], .codec (.metadataKindMismatch id)⟩
              let layout ← (context.checked.catalog.mappingLayout keyType valueType).mapError (fun error => ⟨[], .catalog error⟩)
              let entries ← decodeWithEntries fuel leaf recipe context keyType valueType layout stored 0
              let actual ← (SourceCoreCompatibleValues.decodeDefaultRaw fuel context valueType layout.valueType fallback).mapError fromCodec
              unless actual = SourceCoreCompatibleValues.defaultValue? (valueType.size + 1) valueType do
                throw ⟨[], .codec .transportedDefaultMismatch⟩
              pure (.mapping keyType valueType entries)
          | _, .constructed constructor (.pair (.word id) payload) =>
              let instantiation ← match ← metadata context expected id with
                | .constructor instantiation => pure instantiation
                | _ => throw ⟨[], .codec (.metadataKindMismatch id)⟩
              let authentic ← (context.checked.resolveConstructor instantiation).mapError (fun error => ⟨[], .catalog error⟩)
              unless constructor = authentic do throw ⟨[], .codec (.constructorMismatch constructor)⟩
              let payloads ← decodeWithPayloads fuel leaf recipe context instantiation.payloadTypes payload 0
              pure (.constructed instantiation payloads)
          | _, .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
          | _, .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
          | _, _ => throw ⟨[], .callablePayloadMismatch⟩

  private def decodeWithPayloads {checked : Checked} {definitions : Core.DataEnvironment} : Nat → LeafDecoder → Recipe checked definitions → Values → List Ty → Core.Value → Nat → Except Error (List SourceValue)
    | _, _, _, _, [], .unit, _ => pure []
    | 0, _, _, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, leaf, recipe, context, [type], value, index =>
        return [← (decodeWithRaw fuel leaf recipe context type value).mapError (Error.at (.constructorPayload index))]
    | fuel + 1, leaf, recipe, context, type :: types, .pair value rest, index => do
        let value ← (decodeWithRaw fuel leaf recipe context type value).mapError (Error.at (.constructorPayload index))
        let rest ← decodeWithPayloads fuel leaf recipe context types rest (index + 1)
        pure (value :: rest)
    | _, _, _, _, _, _, _ => throw ⟨[], .codec .malformedPayload⟩

  private def decodeWithEntries {checked : Checked} {definitions : Core.DataEnvironment} : Nat → LeafDecoder → Recipe checked definitions → Values → Ty → Ty →
      Core.OrderedMapping.Layout → Core.Value → Nat → Except Error (List (SourceValue × SourceValue))
    | 0, _, _, _, _, _, _, _, _ => throw ⟨[], .exhausted⟩
    | fuel + 1, leaf, recipe, context, keyType, valueType, layout, stored, index => do
        match stored with
        | .constructed constructor .unit =>
            unless constructor = layout.nilConstructor do throw ⟨[], .codec (.constructorMismatch constructor)⟩
            pure []
        | .constructed constructor (.pair (.pair key value) rest) =>
            unless constructor = layout.consConstructor do throw ⟨[], .codec (.constructorMismatch constructor)⟩
            let key ← (decodeWithRaw fuel leaf recipe context keyType key).mapError (Error.at (.mappingKey index))
            let value ← (decodeWithRaw fuel leaf recipe context valueType value).mapError (Error.at (.mappingValue index))
            let rest ← decodeWithEntries fuel leaf recipe context keyType valueType layout rest (index + 1)
            pure ((key, value) :: rest)
        | .cellRef .. => throw ⟨[], .externalReferenceUnsupported⟩
        | .hostFunction .. => throw ⟨[], .externalHostUnsupported⟩
        | _ => throw ⟨[], .codec .malformedPayload⟩
end

private def decodeRaw {checked : Checked} {definitions : Core.DataEnvironment}
    (fuel : Nat) (recipe : Recipe checked definitions) (context : Values)
    (expected : Ty) (value : Core.Value) : Except Error SourceValue :=
  decodeWithRaw fuel (decodeCallable recipe) recipe context expected value

structure Decoded {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (snapshot : Snapshot recipe)
    (context : Values) (expected : Ty) (core : Core.Value) where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) core type definitions
  private reversed : ∃ fuel, decodeRaw fuel recipe context expected core = .ok source

/-- Typed Core success supplies the world proof, while the sealed recipe and
snapshot authenticate executable leaves. Raw external capabilities never
become source data. The context ownership proof retains the native profile. -/
def decode {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (snapshot : Snapshot recipe)
    (context : Values) (owner : context.checked = checked) (expected : Ty) (core : Core.Value)
    (type : Core.Ty) (projected : checked.catalog.project expected = .ok type)
    (typed : Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) core type definitions)
    (fuel : Nat := 1024) : Except Error (Decoded recipe snapshot context expected core) := do
  let _ := owner
  match reversed : decodeRaw fuel recipe context expected core with
  | .error error => throw error
  | .ok source => pure (.mk source type projected typed ⟨fuel, reversed⟩)

/-- Actual structural decoding with an explicit function-leaf policy. The
policy's code and capture receipts must be retained by its caller. Native
typing and this receipt alone do not establish source execution meaning. -/
structure LeafDecoded {checked : Checked} {definitions : Core.DataEnvironment}
    (leaf : LeafDecoder) (recipe : Recipe checked definitions) (snapshot : Snapshot recipe)
    (context : Values) (expected : Ty) (core : Core.Value) where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) core type definitions
  private reversed : ∃ fuel, decodeWithRaw fuel leaf recipe context expected core = .ok source

def decodeWithLeaves {checked : Checked} {definitions : Core.DataEnvironment}
    (leaf : LeafDecoder) (recipe : Recipe checked definitions) (snapshot : Snapshot recipe)
    (context : Values) (owner : context.checked = checked) (expected : Ty) (core : Core.Value)
    (type : Core.Ty) (projected : checked.catalog.project expected = .ok type)
    (typed : Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) core type definitions)
    (fuel : Nat := 1024) : Except Error (LeafDecoded leaf recipe snapshot context expected core) := do
  let _ := owner
  match reversed : decodeWithRaw fuel leaf recipe context expected core with
  | .error error => throw error
  | .ok source => pure ⟨source, type, projected, typed, ⟨fuel, reversed⟩⟩

/-- Delegating all callable leaves to the original policy retains exactly the
existing decoder's certificate. No new function origin is admitted. -/
def LeafDecoded.default {checked : Checked} {definitions : Core.DataEnvironment}
    {recipe : Recipe checked definitions} {snapshot : Snapshot recipe} {context : Values}
    {expected : Ty} {core : Core.Value}
    (decoded : LeafDecoded (decodeCallable recipe) recipe snapshot context expected core) :
    Decoded recipe snapshot context expected core :=
  ⟨decoded.source, decoded.type, decoded.projected, decoded.typed, decoded.reversed⟩

structure Completion {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (context : Values) (expected : Ty) where private mk ::
  snapshot : Snapshot recipe
  core : Core.Value
  decoded : Decoded recipe snapshot context expected core

/-- Extract the actual finite world from the typed native observation; this
uses store annotations and the proved uniqueness of a store's typing world.
It does not run or inspect any source evaluator. -/
def decodeSuccess {checked : Checked} {definitions : Core.DataEnvironment} (recipe : Recipe checked definitions) (context : Values)
    (owner : context.checked = checked) (expected : Ty) {type : Core.Ty}
    (projected : checked.catalog.project expected = .ok type)
    (result : SourceCoreGeneralEntry.Result definitions type)
    (fuel : Nat := 1024) : Except Error (Completion recipe context expected) := do
  match observed : result.observation with
  | .succeeded value store =>
      let stored : Core.RuntimeStoreHasTypes (store.map Core.Value.type) store definitions := by
        obtain ⟨_, stored, _⟩ := result.success_typed observed
        simpa only [stored.world_eq] using stored
      let typed : Core.RuntimeValueHasType (store.map Core.Value.type) value type definitions := by
        obtain ⟨_, stored, typed⟩ := result.success_typed observed
        simpa only [stored.world_eq] using typed
      match accepted : snapshot recipe store stored with
      | .error error => throw error
      | .ok snapshot =>
          have typed : Core.RuntimeValueHasType (snapshot.store.map Core.Value.type) value type definitions := by
            rw [snapshot_store accepted]
            exact typed
          let decoded ← decode recipe snapshot context owner expected value type projected typed fuel
          pure (.mk snapshot value decoded)
  | _ => throw ⟨[], .notSucceeded⟩

end Solcore.Frontend.SourceCoreCompatibleOutputs
