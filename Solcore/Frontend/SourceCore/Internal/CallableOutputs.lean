import Solcore.Frontend.SourceCore.Internal.CallablePaired
import Solcore.Frontend.SourceCore.Internal.CallableIndexed
import Solcore.Frontend.SourceCore.CompatibleFunctions
import Solcore.Frontend.SourceCore.Internal.CallableViews
import Solcore.Frontend.SourceCore.Internal.CallableAncestry
import Solcore.Frontend.SourceCore.Internal.Carriers
import Solcore.Frontend.SourceCore.Internal.Entries
import Solcore.Frontend.Internal.RuntimeValidation
import Solcore.Frontend.SourceCore.Compatible
import Solcore.Core.Safety

/-!
# Callable outputs

Reverse source values and heap exports of the compatible, paired and indexed programs, and the
public output codec.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableNativeCellHeaders
/-! Raw source declarations cached for the finite prepared metadata graph.
Compiler and source substitution contexts remain distinct. Each raw binder
is joined to its actual compiler inventory by stable identity before execution.
Snapshot decoding and execution history are supplied by runner adapters. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableNativeCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Inventory {checked : Checked} (base : Base checked) := SourceCoreAllocationContexts.Inventory base.plan base.contexts
abbrev Context {checked : Checked} (base : Base checked) := SourceCoreAllocationContexts.Certified base.plan base.contexts
abbrev Binding := SourceCoreAllocationContexts.BinderReceipt

inductive Error where
  | metadata (error : SourceCoreAllocationContexts.Error)
  | missingContext (position : Nat)
  | missingBinder (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

structure Header {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) where private mk ::
  position : Fin graph.table.states.length
  context : Context base
  owned : context ∈ inventory.rows
  selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
    context.context.active = (graph.table.states[position]).nativeActive
  bindings : List (Binding (graph.table.states[position]).metadata.source)
  collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings
  nativeBinder : TypedBinder
  nativeOwned : nativeBinder ∈ context.context.binders
  raw : Binding (graph.table.states[position]).metadata.source
  rawOwned : raw ∈ bindings
  identity : raw.binder.id = nativeBinder.id

private def headerForBinding {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base)
    (position : Fin graph.table.states.length) (context : Context base) (owned : context ∈ inventory.rows)
    (selected : context.context.owner = (graph.table.states[position]).metadata.owner ∧
      context.context.active = (graph.table.states[position]).nativeActive)
    (bindings : List (Binding (graph.table.states[position]).metadata.source))
    (collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source = .ok bindings)
    (native : TypedBinder) (nativeOwned : native ∈ context.context.binders) :
    Except Error (Header graph inventory) := by
  cases rawFound : bindings.find? (fun (raw : Binding (graph.table.states[position]).metadata.source) => decide (raw.binder.id = native.id)) with
  | none => exact .error (.missingBinder position.val native.id)
  | some raw =>
    have identity : raw.binder.id = native.id := of_decide_eq_true (List.find?_some (p := fun (candidate : Binding (graph.table.states[position]).metadata.source) => decide (candidate.binder.id = native.id)) rawFound)
    exact .ok ⟨position, context, owned, selected, bindings, collected, native, nativeOwned, raw,
      List.mem_of_find?_eq_some rawFound, identity⟩

private def headersAt {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base)
    (position : Fin graph.table.states.length) : Except Error (List (Header graph inventory)) := by
  cases found : inventory.rows.attach.find? (fun (context : {context : Context base // context ∈ inventory.rows}) => decide
      (context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive)) with
  | none => exact .error (.missingContext position.val)
  | some context =>
    have selected : context.val.context.owner = (graph.table.states[position]).metadata.owner ∧
        context.val.context.active = (graph.table.states[position]).nativeActive :=
      of_decide_eq_true (List.find?_some (p := fun (candidate : {candidate : Context base // candidate ∈ inventory.rows}) => decide
        (candidate.val.context.owner = (graph.table.states[position]).metadata.owner ∧
          candidate.val.context.active = (graph.table.states[position]).nativeActive)) found)
    cases collected : SourceCoreAllocationContexts.binders (graph.table.states[position]).metadata.source with
    | error error => exact .error (Error.metadata error)
    | ok bindings =>
      exact context.val.context.binders.attach.mapM fun (native : {native : TypedBinder // native ∈ context.val.context.binders}) =>
        headerForBinding graph inventory position context.val context.property selected bindings collected native.val native.property

structure Prepared {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) where private mk ::
  headers : List (Header graph inventory)
  groups : List (List (Header graph inventory))
  collected : (List.finRange graph.table.states.length).mapM (headersAt graph inventory) = .ok groups
  flattened : headers = groups.flatten

def prepare {checked : Checked} {base : Base checked} (graph : Graph base) (inventory : Inventory base) : Except Error (Prepared graph inventory) :=
  match collected : (List.finRange graph.table.states.length).mapM (headersAt graph inventory) with
  | .error error => .error error
  | .ok groups => .ok ⟨groups.flatten, groups, collected, rfl⟩

def Prepared.at? {checked : Checked} {base : Base checked} {graph : Graph base} {inventory : Inventory base}
    (prepared : Prepared graph inventory) (position : Nat) (key : SourceCoreAllocationLayouts.Key) : Option (Header graph inventory) :=
  prepared.headers.find? fun header => decide (header.position.val = position ∧
    header.context.context.owner = key.owner ∧ header.context.context.active = key.active ∧ header.nativeBinder = key.binder)

theorem Prepared.binder_identity {checked : Checked} {base : Base checked}
    {graph : Graph base} {inventory : Inventory base} (prepared : Prepared graph inventory)
    {position : Nat} {key : SourceCoreAllocationLayouts.Key} {header : Header graph inventory}
    (selected : prepared.at? position key = some header) : header.raw.binder.id = key.binder.id := by
  have tested := List.find?_some selected
  have native : header.nativeBinder = key.binder := (of_decide_eq_true tested).2.2.2
  exact header.identity.trans (congrArg TypedBinder.id native)

end Solcore.Frontend.SourceCoreCallableNativeCellHeaders
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
/-! The paired runner joins an actual allocation snapshot to the shared raw
source declaration cache. Metadata is prepared once; runtime selection checks
only the snapshot's table index and the recorded compiler allocation key.
The selector keeps store adjacency without inferring execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Header {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Header graph program.contexts
abbrev Prepared {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Prepared graph program.contexts

inductive Error where
  | metadata (error : SourceCoreCallableNativeCellHeaders.Error)
  | snapshot (error : SourceCoreCallableIndexedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

def prepare {checked : Checked} {program : Program checked} (graph : Graph program.base) :
    Except Error (Prepared (program := program) graph) :=
  (SourceCoreCallableNativeCellHeaders.prepare graph program.contexts).mapError Error.metadata

structure Selected {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  snapshot : SourceCoreCallableIndexedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : snapshot.frame.index? = some position
  header : Header (program := program) graph
  selected : prepared.at? position row.entry.key = some header

def select {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Selected prepared row) := do
  let snapshot ← (SourceCoreCallableIndexedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
  match lookup : snapshot.frame.index? with
  | some position =>
    match selected : prepared.at? position row.entry.key with
    | none => throw (.headerUnavailable position row.entry.key.binder.id)
    | some header => pure ⟨snapshot, position, lookup, header, selected⟩
  | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Selected.binder_identity {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {prepared : Prepared (program := program) graph} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (selected : Selected prepared row) :
    selected.header.raw.binder.id = row.entry.key.binder.id :=
  SourceCoreCallableNativeCellHeaders.Prepared.binder_identity prepared selected.selected

end Solcore.Frontend.SourceCoreCallableIndexedCellHeaders
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleOutputs
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
  | indexed (prepared : SourceCoreCallableIndexedPrograms.Prepared checked)

def ArtifactOrigin.base {checked : Checked} : ArtifactOrigin checked → Prepared checked
  | .ordinary prepared => prepared
  | .marked prepared => prepared.base
  | .ancestry prepared => prepared.base
  | .paired prepared => prepared.base
  | .indexed prepared => prepared.base

def ArtifactOrigin.definitions {checked : Checked} : ArtifactOrigin checked → Core.DataEnvironment
  | .ordinary _ => checked.catalog.definitions
  | .marked prepared => prepared.layouts.definitions
  | .ancestry prepared => prepared.layouts.definitions
  | .paired prepared => prepared.layouts.definitions
  | .indexed prepared => prepared.layouts.definitions

def ArtifactOrigin.closures {checked : Checked} : ArtifactOrigin checked → List Core.Expr
  | .ordinary prepared => prepared.closures
  | .marked prepared => prepared.secondPass.closures
  | .ancestry prepared => prepared.secondPass.closures
  | .paired prepared => prepared.secondPass.closures
  | .indexed prepared => prepared.secondPass.closures

def ArtifactOrigin.inputContext? {checked : Checked} : ArtifactOrigin checked → Option SourceCoreCompatibleInputs.Context
  | .ordinary prepared => prepared.sourceInputs.map (·.context)
  | .marked prepared => some prepared.sourceInputs.context
  | .ancestry prepared => some prepared.sourceInputs.context
  | .paired prepared => some prepared.sourceInputs.context
  | .indexed prepared => some prepared.sourceInputs.context

/-- The administrative reference follows every source-global reference. -/
def ArtifactOrigin.contextSuffix {checked : Checked} : ArtifactOrigin checked → Core.Context
  | .ordinary _ | .marked _ => []
  | .ancestry prepared => [prepared.ancestry.layout.referenceType]
  | .paired prepared => [prepared.ancestry.layout.referenceType]
  | .indexed prepared => [prepared.ancestry.layout.referenceType]

def ArtifactOrigin.environmentSuffix {checked : Checked} : ArtifactOrigin checked → Core.Environment
  | .ordinary _ | .marked _ => []
  | .ancestry prepared => [.cellRef prepared.ancestry.layout.frame.type 0]
  | .paired prepared => [.cellRef prepared.ancestry.layout.frame.type 0]
  | .indexed prepared => [.cellRef prepared.ancestry.layout.frame.type 0]

def ArtifactOrigin.globalBase {checked : Checked} : ArtifactOrigin checked → Nat
  | .ordinary _ | .marked _ => 0
  | .ancestry _ => 1
  | .paired _ => 1
  | .indexed _ => 1

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

/-- Exact named/builtin code and global slots for the finite indexed runner. -/
def prepareIndexed {checked : Checked} (prepared : SourceCoreCallableIndexedPrograms.Prepared checked) :
    Except Error (Recipe checked prepared.layouts.definitions) := prepareOrigin (.indexed prepared)

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
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedOutputs
/-! Prepared output policy for the owning indexed Core runner. Function leaves
must occur in its completed result or a recorded source-cell payload; closure
saved environments are excluded. The actual finite-world typing follows that
path. Lambda code/captures and raw source metadata then use the cached finite
receipts. Named/builtin leaves use the exact installed output recipe.

All source graphs, substitutions, evidence and code templates are prepared
before execution. Runtime decoding locates native data, joins physical source
allocations and selects cached headers/recipes. This boundary does not claim
whole source/Core execution correspondence or import a source evaluator.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedOutputs
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Completion {checked : Checked} (program : Program checked) := SourceCoreCallableIndexedPrograms.Completion program
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Ledger {checked : Checked} {program : Program checked} (completion : Completion program) (initial : SourceHeap) :=
  SourceCoreCallableIndexedLedger.Receipt completion initial
abbrev StoreOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallableIndexedLedger.store completion
abbrev WorldOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallableIndexedLedger.world completion

inductive Error where
  | graph (error : SourceCoreCallableAncestryPairedPreparation.Error)
  | headers (error : SourceCoreCallablePairedHeaders.Error)
  | templates (error : SourceCoreCallableIndexedTemplates.Error)
  | views (error : SourceCoreCallableIndexedReadViews.Error)
  | output (error : SourceCoreCompatibleOutputs.Error)
  | ledger (error : SourceCoreAllocationLedger.Error)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | restore (error : SourceCoreCallableIndexedRestoration.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | unavailableValue
  | notCallable
  | callableTypeMismatch
  | notSucceeded
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base
  graphPrepared : SourceCoreCallableAncestryPairedPreparation.prepare program.base = .ok graph
  headers : SourceCoreCallablePairedHeaders.Prepared graph
  headersPrepared : SourceCoreCallablePairedHeaders.prepare graph = .ok headers
  templates : SourceCoreCallableIndexedTemplates.Cache program
  templatesPrepared : SourceCoreCallableIndexedTemplates.prepare program = .ok templates
  views : SourceCoreCallableIndexedReadViews.Cache templates
  viewsPrepared : SourceCoreCallableIndexedReadViews.prepare templates = .ok views
  recipe : SourceCoreCompatibleOutputs.Recipe checked program.layouts.definitions
  recipePrepared : SourceCoreCompatibleOutputs.prepareIndexed program = .ok recipe

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  let graph := program.ancestry.graph
  let graphPrepared := program.ancestry.graphPrepared
  match headersPrepared : SourceCoreCallablePairedHeaders.prepare graph with
  | .error error => throw (.headers error)
  | .ok headers =>
    match templatesPrepared : SourceCoreCallableIndexedTemplates.prepare program with
    | .error error => throw (.templates error)
    | .ok templates =>
      match viewsPrepared : SourceCoreCallableIndexedReadViews.prepare templates with
      | .error error => throw (.views error)
      | .ok views =>
        match recipePrepared : SourceCoreCompatibleOutputs.prepareIndexed program with
        | .error error => throw (.output error)
        | .ok recipe => pure ⟨graph, graphPrepared, headers, headersPrepared, templates, templatesPrepared,
            views, viewsPrepared, recipe, recipePrepared⟩


/-- A native function leaf comes from public result data or an actual source
allocation payload, never arbitrary supplied code or saved environment data. -/
inductive Origin {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Prop where
  | result {root : Core.Value}
      (observation : completion.result.native.observation = .succeeded root (StoreOf completion))
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value
  | payload (ordinal : Fin ledger.ledger.rows.length) {root : Core.Value}
      (present : (ledger.ledger.rows[ordinal]).payload = some root)
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value

structure Located {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Type where private mk ::
  origin : Origin completion ledger value
  typed : RuntimeValueHasType (WorldOf completion) value value.type program.layouts.definitions

private def locatePayload {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Option (Located ledger value) :=
  (List.finRange ledger.ledger.rows.length).findSome? fun ordinal =>
    match present : (ledger.ledger.rows[ordinal]).payload with
    | none => none
    | some root => match SourceCoreCallableNativeSubvalues.find value root with
      | none => none
      | some inside => some ⟨.payload ordinal present inside.related,
          SourceCoreCallableNativeSubvalues.runtime_typed inside.related
            ((ledger.ledger.rows[ordinal]).payload_typed ledger.typed present)⟩

def locate {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Except Error (Located ledger value) :=
  match observed : completion.result.native.observation with
  | .succeeded root store =>
    match SourceCoreCallableNativeSubvalues.find value root with
    | some inside =>
      have storeExact : StoreOf completion = store := by
        simp only [StoreOf, SourceCoreCallableIndexedLedger.store,
          SourceCoreCompatibleMarkedLedger.observedStore, observed]
      have rootTyped : RuntimeValueHasType (WorldOf completion) root completion.entry.native.resultType program.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
        have equal := stored.world_eq
        subst world
        simpa only [WorldOf, SourceCoreCallableIndexedLedger.world, ← storeExact] using typed
      .ok ⟨.result (by simpa only [storeExact] using observed) inside.related,
        SourceCoreCallableNativeSubvalues.runtime_typed inside.related rootTyped⟩
    | none => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue
  | _ => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue

structure SnapshotAt {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) where private mk ::
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.recipe
  exact : snapshot.store = StoreOf completion

def snapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) : Except Error (SnapshotAt prepared completion) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.recipe (StoreOf completion)
      (SourceCoreCallableIndexedLedger.store_typed completion) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

/-- Sealed source reconstructions retain the distinct native origin, code,
physical capture join and cached metadata selection of their function leaves. -/
inductive LeafRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (expected : TypeSystem.Ty) (value : Core.Value) : SourceValue → Prop where
  | ordinary (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedTemplates.Authenticated prepared.templates (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallableIndexedRestoration.Ordinary prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | read (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedReadViews.Authenticated prepared.views (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallableIndexedRestoration.Read prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | known (located : Located ledger value) (snapshot : SnapshotAt prepared completion)
      {source : SourceValue} (decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value = .ok source) :
      LeafRelated prepared completion ledger expected value source

structure Leaf {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    (expected : TypeSystem.Ty) (value : Core.Value) : Type where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions
  related : LeafRelated prepared completion ledger expected value source

def decodeLeaf {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :
    Except Error (Leaf (prepared := prepared) (completion := completion) (ledger := ledger) expected value) := do
  let located ← locate completion ledger value
  let .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word := value.type
    | throw .notCallable
  match projected : checked.catalog.project expected with
  | .error error => throw (.projection error)
  | .ok type =>
    if same : type = CallableContract.functionType parameter result then
      if valueType : value.type = CallableContract.functionType parameter result then
        have typed : RuntimeValueHasType (WorldOf completion) value (CallableContract.functionType parameter result) program.layouts.definitions :=
          valueType ▸ located.typed
        have expectedTyped : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions := same.symm ▸ typed
        let stored := SourceCoreCallableIndexedLedger.store_typed completion
        match SourceCoreCallableIndexedReadViews.authenticate prepared.views stored value parameter result typed with
        | .ok authenticated =>
          let restored ← (SourceCoreCallableIndexedRestoration.restoreRead prepared.headers authenticated ledger).mapError Error.restore
          pure ⟨restored.source, type, projected, expectedTyped, .read located authenticated restored⟩
        | .error _ =>
          match SourceCoreCallableIndexedTemplates.authenticate prepared.templates stored value parameter result typed with
          | .ok authenticated =>
            let restored ← (SourceCoreCallableIndexedRestoration.restoreOrdinary prepared.headers authenticated ledger).mapError Error.restore
            pure ⟨restored.source, type, projected, expectedTyped, .ordinary located authenticated restored⟩
          | .error _ =>
            match decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value with
            | .error error => throw (.output error)
            | .ok source => pure ⟨source, type, projected, expectedTyped, .known located snapshot decoded⟩
      else throw .callableTypeMismatch
    else throw .callableTypeMismatch

/-- Structural decoding delegates each actual function leaf to this owned
policy. Its checked `Leaf` factory can be inspected separately by consumers. -/
def leafPolicy {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) : SourceCoreCompatibleOutputs.LeafDecoder := fun expected value =>
  (decodeLeaf prepared completion ledger snapshot expected value).map (·.source)
    |>.mapError (fun _ => ⟨[], .callablePayloadMismatch⟩)

abbrev Data {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :=
  SourceCoreCompatibleOutputs.LeafDecoded (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context expected value

def decodeData {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value)
    (type : Core.Ty) (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions)
    (fuel : Nat := 1024) : Except Error (Data ledger snapshot expected value) := do
  have actual : RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type) value type program.layouts.definitions := by
    rw [snapshot.exact]
    exact typed
  (SourceCoreCompatibleOutputs.decodeWithLeaves (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context completion.result.contextOwner expected value type projected actual fuel)
      |>.mapError Error.output

structure Success {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) (expected : TypeSystem.Ty) where private mk ::
  ledger : Ledger completion initial
  snapshot : SnapshotAt prepared completion
  core : Core.Value
  observation : completion.result.native.observation = .succeeded core (StoreOf completion)
  decoded : Data ledger snapshot expected core

/-- Consume a native successful observation without running or resuming source
code. Deep function leaves keep the same owning completion and typed ledger. -/
def decodeSuccess {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (expected : TypeSystem.Ty)
    (projected : checked.catalog.project expected = .ok completion.entry.native.resultType)
    (initial : SourceHeap := []) (fuel : Nat := 1024) : Except Error (Success prepared completion initial expected) := do
  let ledger ← (SourceCoreCallableIndexedLedger.scan completion initial).mapError Error.ledger
  let snapshot ← snapshot prepared completion
  match observed : completion.result.native.observation with
  | .succeeded value store =>
    have storeExact : StoreOf completion = store := by
      simp only [StoreOf, SourceCoreCallableIndexedLedger.store,
        SourceCoreCompatibleMarkedLedger.observedStore, observed]
    have typed : RuntimeValueHasType (WorldOf completion) value completion.entry.native.resultType program.layouts.definitions := by
      obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
      have equal := stored.world_eq
      subst world
      simpa only [WorldOf, SourceCoreCallableIndexedLedger.world, ← storeExact] using typed
    let decoded ← decodeData prepared completion ledger snapshot expected value completion.entry.native.resultType projected typed fuel
    pure ⟨ledger, snapshot, value, by simpa only [storeExact] using observed, decoded⟩
  | _ => throw .notSucceeded

end Solcore.Frontend.SourceCoreCallableIndexedOutputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs
/-! Export actual recorded source cells, including generic principals and
deep callable data. Raw declarations come from the reached source-state
cache rather than the compiler's complete native substitution context.
The opaque source prefix and ordered physical allocation receipts survive.
This decoder does not evaluate source code or establish execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs
open SourceInference
open SourceCoreCallableIndexedOutputs
abbrev Cell := SourceTypedRuntime.Cell
abbrev Row {checked : Checked} {program : Program checked} (completion : Completion program) :=
  SourceCoreAllocationLedger.Row program.layouts (StoreOf completion)

inductive Error where
  | output (error : SourceCoreCallableIndexedOutputs.Error)
  | headers (error : SourceCoreCallableIndexedCellHeaders.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | projection (location : SourceTypedRuntime.Location) (error : SourceCoreCompatibleCatalog.Error)
  | payloadTypeMismatch (location : SourceTypedRuntime.Location) (expected actual : Core.Ty)
  | principalTypeMismatch (location : SourceTypedRuntime.Location)
  | snapshotUnavailable
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  output : SourceCoreCallableIndexedOutputs.Prepared program
  outputPrepared : SourceCoreCallableIndexedOutputs.prepare program = .ok output
  headers : SourceCoreCallableIndexedCellHeaders.Prepared (program := program) output.graph
  headersPrepared : SourceCoreCallableIndexedCellHeaders.prepare (program := program) output.graph = .ok headers

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  match outputPrepared : SourceCoreCallableIndexedOutputs.prepare program with
  | .error error => throw (.output error)
  | .ok output =>
    match headersPrepared : SourceCoreCallableIndexedCellHeaders.prepare (program := program) output.graph with
    | .error error => throw (.headers error)
    | .ok headers => pure ⟨output, outputPrepared, headers, headersPrepared⟩

abbrev Selection {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {completion : Completion program} (row : Row completion) :=
  SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row

def rawType {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {row : Row completion} (selected : Selection prepared row) : TypeSystem.Ty :=
  selected.header.raw.binder.scheme.body

inductive CellDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (row : Row completion) : Cell → Prop where
  | absent (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      (missing : row.payload = none) :
      CellDecoded prepared completion ledger row ⟨rawType selected, none⟩
  | present (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      {value : Core.Value} (present : row.payload = some value)
      (snapshot : SnapshotAt prepared.output completion)
      (decoded : Data ledger snapshot (rawType selected) value) :
      CellDecoded prepared completion ledger row ⟨rawType selected, some decoded.source⟩
  | principal (selected : Selection prepared row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored prepared.output.headers row)
      (same : restored.cell.type = rawType selected) :
      CellDecoded prepared completion ledger row restored.cell

theorem CellDecoded.raw_header {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {row : Row completion} {cell : Cell} (decoded : CellDecoded prepared completion ledger row cell) :
    ∃ selected : Selection prepared row, cell.type = rawType selected ∧
      selected.header.raw.binder.id = row.entry.key.binder.id := by
  cases decoded with
  | absent selected _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | present selected _ _ _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | principal selected _ _ same => exact ⟨selected, same, selected.binder_identity⟩

private def decodeCell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) :
    Except Error {cell : Cell // CellDecoded prepared completion ledger row cell} := do
  let selected ← (SourceCoreCallableIndexedCellHeaders.select prepared.headers row).mapError Error.headers
  if monomorphic : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨rawType selected, none⟩, .absent selected monomorphic present⟩
    | some value =>
      match projected : checked.catalog.project (rawType selected) with
      | .error error => throw (.projection row.sourceLocation error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let snapshot ← match available with
            | none => throw .snapshotUnavailable
            | some snapshot => pure snapshot
          let typed := row.payload_typed ledger.typed present
          let decoded ← (decodeData prepared.output completion ledger snapshot (rawType selected) value
            row.entry.key.payloadType (by simpa only [same] using projected) typed fuel).mapError Error.output
          pure ⟨⟨rawType selected, some decoded.source⟩, .present selected monomorphic present snapshot decoded⟩
        else throw (.payloadTypeMismatch row.sourceLocation type row.entry.key.payloadType)
  else
    let restored ← (SourceCoreCallableIndexedPrincipalAllocations.restore prepared.output.headers row).mapError Error.principal
    if same : restored.cell.type = rawType selected then
      pure ⟨restored.cell, .principal selected monomorphic restored same⟩
    else throw (.principalTypeMismatch row.sourceLocation)

private def cell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) : Except Error Cell :=
  (decodeCell prepared completion ledger available fuel row).map Subtype.val

inductive CellsDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial) :
    List (Row completion) → List Cell → Prop where
  | nil : CellsDecoded prepared completion ledger [] []
  | cons {row rows cell cells} (head : CellDecoded prepared completion ledger row cell)
      (tail : CellsDecoded prepared completion ledger rows cells) :
      CellsDecoded prepared completion ledger (row :: rows) (cell :: cells)

private theorem cells_sound {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) {rows : List (Row completion)} {cells : List Cell}
    (accepted : rows.mapM (cell prepared completion ledger available fuel) = .ok cells) :
    CellsDecoded prepared completion ledger rows cells := by
  induction rows generalizing cells with
  | nil => simp at accepted; subst cells; exact .nil
  | cons row rows ih =>
    cases head : decodeCell prepared completion ledger available fuel row with
    | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind] at accepted
    | ok decoded =>
      cases tail : rows.mapM (cell prepared completion ledger available fuel) with
      | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail] at accepted
      | ok rest =>
        simp only [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst cells
        exact .cons decoded.property (ih tail)

theorem CellsDecoded.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) : cells.length = rows.length := by
  induction decoded <;> simp_all

theorem CellsDecoded.lookup {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) {index : Nat} {row : Row completion}
    (found : rows[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ CellDecoded prepared completion ledger row cell := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst row; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

structure Export {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) where private mk ::
  ledger : Ledger completion initial
  snapshot : Option (SnapshotAt prepared.output completion)
  cells : List Cell
  decoded : CellsDecoded prepared completion ledger ledger.ledger.rows cells
  private fuel : Nat
  private exported : ledger.ledger.exportHeap (cell prepared completion ledger snapshot fuel) = .ok (initial ++ cells)

def Export.heap {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) : SourceHeap :=
  initial ++ exported.cells

def exportHeap {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap := []) (fuel : Nat := 1024) :
    Except Error (Export prepared completion initial) := do
  let ledger ← (SourceCoreCallableIndexedLedger.scan completion initial).mapError (Error.output ∘ SourceCoreCallableIndexedOutputs.Error.ledger)
  let available ← if ledger.ledger.rows.any (fun row => row.payload.isSome) then
      some <$> ((SourceCoreCallableIndexedOutputs.snapshot prepared.output completion).mapError Error.output)
    else pure none
  match accepted : ledger.ledger.rows.mapM (cell prepared completion ledger available fuel) with
  | .error error => throw error
  | .ok cells => pure ⟨ledger, available, cells, cells_sound prepared completion ledger available fuel accepted, fuel, by
      simp [SourceCoreAllocationLedger.Ledger.exportHeap, accepted, Functor.map, Except.map]⟩

theorem Export.prefix_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.take initial.length = initial :=
  exported.ledger.ledger.exportHeap_prefix _ exported.exported

theorem Export.length_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.length = initial.length + exported.ledger.ledger.rows.length := by
  simp only [heap, List.length_append, exported.decoded.length]

theorem Export.cell_at_sourceLocation {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial)
    (index : Fin exported.ledger.ledger.rows.length) :
    ∃ cell, exported.heap[(exported.ledger.ledger.rows[index]).sourceLocation.index]? = some cell ∧
      CellDecoded prepared completion exported.ledger (exported.ledger.ledger.rows[index]) cell := by
  obtain ⟨cell, found, decoded⟩ := exported.decoded.lookup (List.getElem?_eq_getElem index.isLt)
  refine ⟨cell, ?_, decoded⟩
  rw [exported.ledger.ledger.sourceLocation_exact]
  simpa [Export.heap, List.getElem?_append_right] using found

end Solcore.Frontend.SourceCoreCallableIndexedHeapOutputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedCellHeaders
/-! The paired runner joins an actual allocation snapshot to the shared raw
source declaration cache. Metadata is prepared once; runtime selection checks
only the snapshot's table index and the recorded compiler allocation key.
The selector keeps store adjacency without inferring execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedCellHeaders
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Graph := @SourceCoreCallableAncestryPairedPreparation.Prepared
abbrev Header {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Header graph program.contexts
abbrev Prepared {checked : Checked} {program : Program checked} (graph : Graph program.base) :=
  SourceCoreCallableNativeCellHeaders.Prepared graph program.contexts

inductive Error where
  | metadata (error : SourceCoreCallableNativeCellHeaders.Error)
  | snapshot (error : SourceCoreCallablePairedAllocationFrames.Error)
  | frameUnavailable (binder : Resolved.LocalId)
  | headerUnavailable (position : Nat) (binder : Resolved.LocalId)
  deriving Repr

def prepare {checked : Checked} {program : Program checked} (graph : Graph program.base) :
    Except Error (Prepared (program := program) graph) :=
  (SourceCoreCallableNativeCellHeaders.prepare graph program.contexts).mapError Error.metadata

structure Selected {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  snapshot : SourceCoreCallablePairedAllocationFrames.Snapshot program.ancestry.layout.frame row
  position : Nat
  lookup : graph.table.lookupIndex? snapshot.frame = some (some position)
  header : Header (program := program) graph
  selected : prepared.at? position row.entry.key = some header

def select {checked : Checked} {program : Program checked} {graph : Graph program.base}
    (prepared : Prepared (program := program) graph) {store : Core.Store}
    (row : SourceCoreAllocationLedger.Row program.layouts store) : Except Error (Selected prepared row) := do
  let snapshot ← (SourceCoreCallablePairedAllocationFrames.snapshot program.ancestry.layout.frame row).mapError Error.snapshot
  match lookup : graph.table.lookupIndex? snapshot.frame with
  | some (some position) =>
    match selected : prepared.at? position row.entry.key with
    | none => throw (.headerUnavailable position row.entry.key.binder.id)
    | some header => pure ⟨snapshot, position, lookup, header, selected⟩
  | _ => throw (.frameUnavailable row.entry.key.binder.id)

theorem Selected.binder_identity {checked : Checked} {program : Program checked} {graph : Graph program.base}
    {prepared : Prepared (program := program) graph} {store : Core.Store}
    {row : SourceCoreAllocationLedger.Row program.layouts store} (selected : Selected prepared row) :
    selected.header.raw.binder.id = row.entry.key.binder.id :=
  SourceCoreCallableNativeCellHeaders.Prepared.binder_identity prepared selected.selected

end Solcore.Frontend.SourceCoreCallablePairedCellHeaders
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedOutputs
/-! Prepared output policy for the owning paired Core runner. Function leaves
must occur in its completed result or a recorded source-cell payload; closure
saved environments are excluded. The actual finite-world typing follows that
path. Lambda code/captures and raw source metadata then use the paired cached
receipts. Named/builtin leaves use the exact installed output recipe.

All source graphs, substitutions, evidence and code templates are prepared
before execution. Runtime decoding locates native data, joins physical source
allocations and selects cached headers/recipes. This boundary does not claim
whole source/Core execution correspondence or import a source evaluator.
-/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedOutputs
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallablePairedPrograms.Prepared
abbrev Completion {checked : Checked} (program : Program checked) := SourceCoreCallablePairedPrograms.Completion program
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Ledger {checked : Checked} {program : Program checked} (completion : Completion program) (initial : SourceHeap) :=
  SourceCoreCallablePairedLedger.Receipt completion initial
abbrev StoreOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallablePairedLedger.store completion
abbrev WorldOf {checked : Checked} {program : Program checked} (completion : Completion program) := SourceCoreCallablePairedLedger.world completion

inductive Error where
  | graph (error : SourceCoreCallableAncestryPairedPreparation.Error)
  | headers (error : SourceCoreCallablePairedHeaders.Error)
  | templates (error : SourceCoreCallablePairedTemplates.Error)
  | views (error : SourceCoreCallablePairedReadViews.Error)
  | output (error : SourceCoreCompatibleOutputs.Error)
  | ledger (error : SourceCoreAllocationLedger.Error)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | restore (error : SourceCoreCallablePairedRestoration.Error)
  | principal (error : SourceCoreCallablePairedPrincipalAllocations.Error)
  | unavailableValue
  | notCallable
  | callableTypeMismatch
  | notSucceeded
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base
  graphPrepared : SourceCoreCallableAncestryPairedPreparation.prepare program.base = .ok graph
  headers : SourceCoreCallablePairedHeaders.Prepared graph
  headersPrepared : SourceCoreCallablePairedHeaders.prepare graph = .ok headers
  templates : SourceCoreCallablePairedTemplates.Cache program
  templatesPrepared : SourceCoreCallablePairedTemplates.prepare program = .ok templates
  views : SourceCoreCallablePairedReadViews.Cache templates
  viewsPrepared : SourceCoreCallablePairedReadViews.prepare templates = .ok views
  recipe : SourceCoreCompatibleOutputs.Recipe checked program.layouts.definitions
  recipePrepared : SourceCoreCompatibleOutputs.preparePaired program = .ok recipe

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  match graphPrepared : SourceCoreCallableAncestryPairedPreparation.prepare program.base with
  | .error error => throw (.graph error)
  | .ok graph =>
    match headersPrepared : SourceCoreCallablePairedHeaders.prepare graph with
    | .error error => throw (.headers error)
    | .ok headers =>
      match templatesPrepared : SourceCoreCallablePairedTemplates.prepare program with
      | .error error => throw (.templates error)
      | .ok templates =>
        match viewsPrepared : SourceCoreCallablePairedReadViews.prepare templates with
        | .error error => throw (.views error)
        | .ok views =>
          match recipePrepared : SourceCoreCompatibleOutputs.preparePaired program with
          | .error error => throw (.output error)
          | .ok recipe => pure ⟨graph, graphPrepared, headers, headersPrepared, templates, templatesPrepared,
              views, viewsPrepared, recipe, recipePrepared⟩

/-- A native function leaf comes from public result data or an actual source
allocation payload, never arbitrary supplied code or saved environment data. -/
inductive Origin {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Prop where
  | result {root : Core.Value}
      (observation : completion.result.native.observation = .succeeded root (StoreOf completion))
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value
  | payload (ordinal : Fin ledger.ledger.rows.length) {root : Core.Value}
      (present : (ledger.ledger.rows[ordinal]).payload = some root)
      (inside : SourceCoreCallableNativeSlots.Subvalue value root) : Origin completion ledger value

structure Located {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Type where private mk ::
  origin : Origin completion ledger value
  typed : RuntimeValueHasType (WorldOf completion) value value.type program.layouts.definitions

private def locatePayload {checked : Checked} {program : Program checked} {completion : Completion program}
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Option (Located ledger value) :=
  (List.finRange ledger.ledger.rows.length).findSome? fun ordinal =>
    match present : (ledger.ledger.rows[ordinal]).payload with
    | none => none
    | some root => match SourceCoreCallableNativeSubvalues.find value root with
      | none => none
      | some inside => some ⟨.payload ordinal present inside.related,
          SourceCoreCallableNativeSubvalues.runtime_typed inside.related
            ((ledger.ledger.rows[ordinal]).payload_typed ledger.typed present)⟩

def locate {checked : Checked} {program : Program checked} (completion : Completion program)
    {initial : SourceHeap} (ledger : Ledger completion initial) (value : Core.Value) : Except Error (Located ledger value) :=
  match observed : completion.result.native.observation with
  | .succeeded root store =>
    match SourceCoreCallableNativeSubvalues.find value root with
    | some inside =>
      have storeExact : StoreOf completion = store := by
        simp only [StoreOf, SourceCoreCallablePairedLedger.store,
          SourceCoreCompatibleMarkedLedger.observedStore, observed]
      have rootTyped : RuntimeValueHasType (WorldOf completion) root completion.entry.native.resultType program.layouts.definitions := by
        obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
        have equal := stored.world_eq
        subst world
        simpa only [WorldOf, SourceCoreCallablePairedLedger.world, ← storeExact] using typed
      .ok ⟨.result (by simpa only [storeExact] using observed) inside.related,
        SourceCoreCallableNativeSubvalues.runtime_typed inside.related rootTyped⟩
    | none => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue
  | _ => match locatePayload ledger value with | some found => .ok found | none => .error .unavailableValue

structure SnapshotAt {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) where private mk ::
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.recipe
  exact : snapshot.store = StoreOf completion

def snapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) : Except Error (SnapshotAt prepared completion) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.recipe (StoreOf completion)
      (SourceCoreCallablePairedLedger.store_typed completion) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

/-- Sealed source reconstructions retain the distinct native origin, code,
physical capture join and cached metadata selection of their function leaves. -/
inductive LeafRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (expected : TypeSystem.Ty) (value : Core.Value) : SourceValue → Prop where
  | ordinary (located : Located ledger value)
      (authenticated : SourceCoreCallablePairedTemplates.Authenticated prepared.templates (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallablePairedRestoration.Ordinary prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | read (located : Located ledger value)
      (authenticated : SourceCoreCallablePairedReadViews.Authenticated prepared.views (WorldOf completion) (StoreOf completion) value)
      (restored : SourceCoreCallablePairedRestoration.Read prepared.headers authenticated ledger) :
      LeafRelated prepared completion ledger expected value restored.source
  | known (located : Located ledger value) (snapshot : SnapshotAt prepared completion)
      {source : SourceValue} (decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value = .ok source) :
      LeafRelated prepared completion ledger expected value source

structure Leaf {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    (expected : TypeSystem.Ty) (value : Core.Value) : Type where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions
  related : LeafRelated prepared completion ledger expected value source

def decodeLeaf {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :
    Except Error (Leaf (prepared := prepared) (completion := completion) (ledger := ledger) expected value) := do
  let located ← locate completion ledger value
  let .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word := value.type
    | throw .notCallable
  match projected : checked.catalog.project expected with
  | .error error => throw (.projection error)
  | .ok type =>
    if same : type = CallableContract.functionType parameter result then
      if valueType : value.type = CallableContract.functionType parameter result then
        have typed : RuntimeValueHasType (WorldOf completion) value (CallableContract.functionType parameter result) program.layouts.definitions :=
          valueType ▸ located.typed
        have expectedTyped : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions := same.symm ▸ typed
        let stored := SourceCoreCallablePairedLedger.store_typed completion
        match SourceCoreCallablePairedReadViews.authenticate prepared.views stored value parameter result typed with
        | .ok authenticated =>
          let restored ← (SourceCoreCallablePairedRestoration.restoreRead prepared.headers authenticated ledger).mapError Error.restore
          pure ⟨restored.source, type, projected, expectedTyped, .read located authenticated restored⟩
        | .error _ =>
          match SourceCoreCallablePairedTemplates.authenticate prepared.templates stored value parameter result typed with
          | .ok authenticated =>
            let restored ← (SourceCoreCallablePairedRestoration.restoreOrdinary prepared.headers authenticated ledger).mapError Error.restore
            pure ⟨restored.source, type, projected, expectedTyped, .ordinary located authenticated restored⟩
          | .error _ =>
            match decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.recipe expected value with
            | .error error => throw (.output error)
            | .ok source => pure ⟨source, type, projected, expectedTyped, .known located snapshot decoded⟩
      else throw .callableTypeMismatch
    else throw .callableTypeMismatch

/-- Structural decoding delegates each actual function leaf to this owned
policy. Its checked `Leaf` factory can be inspected separately by consumers. -/
def leafPolicy {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) : SourceCoreCompatibleOutputs.LeafDecoder := fun expected value =>
  (decodeLeaf prepared completion ledger snapshot expected value).map (·.source)
    |>.mapError (fun _ => ⟨[], .callablePayloadMismatch⟩)

abbrev Data {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value) :=
  SourceCoreCompatibleOutputs.LeafDecoded (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context expected value

def decodeData {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (snapshot : SnapshotAt prepared completion) (expected : TypeSystem.Ty) (value : Core.Value)
    (type : Core.Ty) (projected : checked.catalog.project expected = .ok type)
    (typed : RuntimeValueHasType (WorldOf completion) value type program.layouts.definitions)
    (fuel : Nat := 1024) : Except Error (Data ledger snapshot expected value) := do
  have actual : RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type) value type program.layouts.definitions := by
    rw [snapshot.exact]
    exact typed
  (SourceCoreCompatibleOutputs.decodeWithLeaves (leafPolicy prepared completion ledger snapshot)
    prepared.recipe snapshot.snapshot completion.result.context completion.result.contextOwner expected value type projected actual fuel)
      |>.mapError Error.output

structure Success {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) (expected : TypeSystem.Ty) where private mk ::
  ledger : Ledger completion initial
  snapshot : SnapshotAt prepared completion
  core : Core.Value
  observation : completion.result.native.observation = .succeeded core (StoreOf completion)
  decoded : Data ledger snapshot expected core

/-- Consume a native successful observation without running or resuming source
code. Deep function leaves keep the same owning completion and typed ledger. -/
def decodeSuccess {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (expected : TypeSystem.Ty)
    (projected : checked.catalog.project expected = .ok completion.entry.native.resultType)
    (initial : SourceHeap := []) (fuel : Nat := 1024) : Except Error (Success prepared completion initial expected) := do
  let ledger ← (SourceCoreCallablePairedLedger.scan completion initial).mapError Error.ledger
  let snapshot ← snapshot prepared completion
  match observed : completion.result.native.observation with
  | .succeeded value store =>
    have storeExact : StoreOf completion = store := by
      simp only [StoreOf, SourceCoreCallablePairedLedger.store,
        SourceCoreCompatibleMarkedLedger.observedStore, observed]
    have typed : RuntimeValueHasType (WorldOf completion) value completion.entry.native.resultType program.layouts.definitions := by
      obtain ⟨world, stored, typed⟩ := completion.result.native.success_typed observed
      have equal := stored.world_eq
      subst world
      simpa only [WorldOf, SourceCoreCallablePairedLedger.world, ← storeExact] using typed
    let decoded ← decodeData prepared completion ledger snapshot expected value completion.entry.native.resultType projected typed fuel
    pure ⟨ledger, snapshot, value, by simpa only [storeExact] using observed, decoded⟩
  | _ => throw .notSucceeded

end Solcore.Frontend.SourceCoreCallablePairedOutputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCallablePairedHeapOutputs
/-! Export actual recorded source cells, including generic principals and
deep callable data. Raw declarations come from the reached source-state
cache rather than the compiler's complete native substitution context.
The opaque source prefix and ordered physical allocation receipts survive.
This decoder does not evaluate source code or establish execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallablePairedHeapOutputs
open SourceInference
open SourceCoreCallablePairedOutputs
abbrev Cell := SourceTypedRuntime.Cell
abbrev Row {checked : Checked} {program : Program checked} (completion : Completion program) :=
  SourceCoreAllocationLedger.Row program.layouts (StoreOf completion)

inductive Error where
  | output (error : SourceCoreCallablePairedOutputs.Error)
  | headers (error : SourceCoreCallablePairedCellHeaders.Error)
  | principal (error : SourceCoreCallablePairedPrincipalAllocations.Error)
  | projection (location : SourceTypedRuntime.Location) (error : SourceCoreCompatibleCatalog.Error)
  | payloadTypeMismatch (location : SourceTypedRuntime.Location) (expected actual : Core.Ty)
  | principalTypeMismatch (location : SourceTypedRuntime.Location)
  | snapshotUnavailable
  deriving Repr

structure Prepared {checked : Checked} (program : Program checked) where private mk ::
  output : SourceCoreCallablePairedOutputs.Prepared program
  outputPrepared : SourceCoreCallablePairedOutputs.prepare program = .ok output
  headers : SourceCoreCallablePairedCellHeaders.Prepared (program := program) output.graph
  headersPrepared : SourceCoreCallablePairedCellHeaders.prepare (program := program) output.graph = .ok headers

def prepare {checked : Checked} (program : Program checked) : Except Error (Prepared program) := do
  match outputPrepared : SourceCoreCallablePairedOutputs.prepare program with
  | .error error => throw (.output error)
  | .ok output =>
    match headersPrepared : SourceCoreCallablePairedCellHeaders.prepare (program := program) output.graph with
    | .error error => throw (.headers error)
    | .ok headers => pure ⟨output, outputPrepared, headers, headersPrepared⟩

abbrev Selection {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {completion : Completion program} (row : Row completion) :=
  SourceCoreCallablePairedCellHeaders.Selected prepared.headers row

def rawType {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {row : Row completion} (selected : Selection prepared row) : TypeSystem.Ty :=
  selected.header.raw.binder.scheme.body

inductive CellDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial)
    (row : Row completion) : Cell → Prop where
  | absent (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      (missing : row.payload = none) :
      CellDecoded prepared completion ledger row ⟨rawType selected, none⟩
  | present (selected : Selection prepared row)
      (monomorphic : selected.header.raw.binder.scheme.quantified = [])
      {value : Core.Value} (present : row.payload = some value)
      (snapshot : SnapshotAt prepared.output completion)
      (decoded : Data ledger snapshot (rawType selected) value) :
      CellDecoded prepared completion ledger row ⟨rawType selected, some decoded.source⟩
  | principal (selected : Selection prepared row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallablePairedPrincipalAllocations.Restored prepared.output.headers row)
      (same : restored.cell.type = rawType selected) :
      CellDecoded prepared completion ledger row restored.cell

theorem CellDecoded.raw_header {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {row : Row completion} {cell : Cell} (decoded : CellDecoded prepared completion ledger row cell) :
    ∃ selected : Selection prepared row, cell.type = rawType selected ∧
      selected.header.raw.binder.id = row.entry.key.binder.id := by
  cases decoded with
  | absent selected _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | present selected _ _ _ _ => exact ⟨selected, rfl, selected.binder_identity⟩
  | principal selected _ _ same => exact ⟨selected, same, selected.binder_identity⟩

private def decodeCell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) :
    Except Error {cell : Cell // CellDecoded prepared completion ledger row cell} := do
  let selected ← (SourceCoreCallablePairedCellHeaders.select prepared.headers row).mapError Error.headers
  if monomorphic : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨rawType selected, none⟩, .absent selected monomorphic present⟩
    | some value =>
      match projected : checked.catalog.project (rawType selected) with
      | .error error => throw (.projection row.sourceLocation error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let snapshot ← match available with
            | none => throw .snapshotUnavailable
            | some snapshot => pure snapshot
          let typed := row.payload_typed ledger.typed present
          let decoded ← (decodeData prepared.output completion ledger snapshot (rawType selected) value
            row.entry.key.payloadType (by simpa only [same] using projected) typed fuel).mapError Error.output
          pure ⟨⟨rawType selected, some decoded.source⟩, .present selected monomorphic present snapshot decoded⟩
        else throw (.payloadTypeMismatch row.sourceLocation type row.entry.key.payloadType)
  else
    let restored ← (SourceCoreCallablePairedPrincipalAllocations.restore prepared.output.headers row).mapError Error.principal
    if same : restored.cell.type = rawType selected then
      pure ⟨restored.cell, .principal selected monomorphic restored same⟩
    else throw (.principalTypeMismatch row.sourceLocation)

private def cell {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) (row : Row completion) : Except Error Cell :=
  (decodeCell prepared completion ledger available fuel row).map Subtype.val

inductive CellsDecoded {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) {initial : SourceHeap} (ledger : Ledger completion initial) :
    List (Row completion) → List Cell → Prop where
  | nil : CellsDecoded prepared completion ledger [] []
  | cons {row rows cell cells} (head : CellDecoded prepared completion ledger row cell)
      (tail : CellsDecoded prepared completion ledger rows cells) :
      CellsDecoded prepared completion ledger (row :: rows) (cell :: cells)

private theorem cells_sound {checked : Checked} {program : Program checked}
    (prepared : Prepared program) (completion : Completion program) {initial : SourceHeap}
    (ledger : Ledger completion initial) (available : Option (SnapshotAt prepared.output completion))
    (fuel : Nat) {rows : List (Row completion)} {cells : List Cell}
    (accepted : rows.mapM (cell prepared completion ledger available fuel) = .ok cells) :
    CellsDecoded prepared completion ledger rows cells := by
  induction rows generalizing cells with
  | nil => simp at accepted; subst cells; exact .nil
  | cons row rows ih =>
    cases head : decodeCell prepared completion ledger available fuel row with
    | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind] at accepted
    | ok decoded =>
      cases tail : rows.mapM (cell prepared completion ledger available fuel) with
      | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail] at accepted
      | ok rest =>
        simp only [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst cells
        exact .cons decoded.property (ih tail)

theorem CellsDecoded.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) : cells.length = rows.length := by
  induction decoded <;> simp_all

theorem CellsDecoded.lookup {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} {ledger : Ledger completion initial}
    {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion ledger rows cells) {index : Nat} {row : Row completion}
    (found : rows[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ CellDecoded prepared completion ledger row cell := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst row; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

structure Export {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap) where private mk ::
  ledger : Ledger completion initial
  snapshot : Option (SnapshotAt prepared.output completion)
  cells : List Cell
  decoded : CellsDecoded prepared completion ledger ledger.ledger.rows cells
  private fuel : Nat
  private exported : ledger.ledger.exportHeap (cell prepared completion ledger snapshot fuel) = .ok (initial ++ cells)

def Export.heap {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) : SourceHeap :=
  initial ++ exported.cells

def exportHeap {checked : Checked} {program : Program checked} (prepared : Prepared program)
    (completion : Completion program) (initial : SourceHeap := []) (fuel : Nat := 1024) :
    Except Error (Export prepared completion initial) := do
  let ledger ← (SourceCoreCallablePairedLedger.scan completion initial).mapError (Error.output ∘ SourceCoreCallablePairedOutputs.Error.ledger)
  let available ← if ledger.ledger.rows.any (fun row => row.payload.isSome) then
      some <$> ((SourceCoreCallablePairedOutputs.snapshot prepared.output completion).mapError Error.output)
    else pure none
  match accepted : ledger.ledger.rows.mapM (cell prepared completion ledger available fuel) with
  | .error error => throw error
  | .ok cells => pure ⟨ledger, available, cells, cells_sound prepared completion ledger available fuel accepted, fuel, by
      simp [SourceCoreAllocationLedger.Ledger.exportHeap, accepted, Functor.map, Except.map]⟩

theorem Export.prefix_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.take initial.length = initial :=
  exported.ledger.ledger.exportHeap_prefix _ exported.exported

theorem Export.length_exact {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial) :
    exported.heap.length = initial.length + exported.ledger.ledger.rows.length := by
  simp only [heap, List.length_append, exported.decoded.length]

theorem Export.cell_at_sourceLocation {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {completion : Completion program} {initial : SourceHeap} (exported : Export prepared completion initial)
    (index : Fin exported.ledger.ledger.rows.length) :
    ∃ cell, exported.heap[(exported.ledger.ledger.rows[index]).sourceLocation.index]? = some cell ∧
      CellDecoded prepared completion exported.ledger (exported.ledger.ledger.rows[index]) cell := by
  obtain ⟨cell, found, decoded⟩ := exported.decoded.lookup (List.getElem?_eq_getElem index.isLt)
  refine ⟨cell, ?_, decoded⟩
  rw [exported.ledger.ledger.sourceLocation_exact]
  simpa [Export.heap, List.getElem?_append_right] using found

end Solcore.Frontend.SourceCoreCallablePairedHeapOutputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreCompatibleHeapOutputs
/-! Export the completed monomorphic source cells of an owned marked artifact.
Original binder types, source locations and capture metadata are retained.
Present values use the real compatible output decoder and actual typed store;
absent values need no native-value decoding. The initial source heap is opaque.

Generalized principal bundles and lambda reconstruction remain explicit
unsupported boundaries. No source evaluator or whole-program correspondence
is assumed or introduced. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCompatibleHeapOutputs
open SourceInference
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Marked := SourceCoreCompatibleMarkedFunctions.Prepared
abbrev Completion {checked : Checked} (marked : Marked checked) :=
  SourceCoreCompatibleMarkedFunctions.Completion marked
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev Cell := SourceTypedRuntime.Cell
abbrev Row {checked : Checked} {marked : Marked checked} (completion : Completion marked) :=
  SourceCoreAllocationLedger.Row marked.layouts (SourceCoreCompatibleMarkedLedger.store completion)

inductive Error where
  | ledger (error : SourceCoreAllocationLedger.Error)
  | output (error : SourceCoreCompatibleOutputs.Error)
  | generalizedBinding (location : SourceTypedRuntime.Location) (binder : Resolved.LocalId)
  | projection (location : SourceTypedRuntime.Location) (error : SourceCoreCompatibleCatalog.Error)
  | payloadTypeMismatch (location : SourceTypedRuntime.Location) (projected actual : Core.Ty)
  | snapshotUnavailable
  deriving Repr

structure Prepared {checked : Checked} (marked : Marked checked) where private mk ::
  recipe : SourceCoreCompatibleOutputs.Recipe checked marked.layouts.definitions
  authenticated : SourceCoreCompatibleOutputs.prepareMarked marked = .ok recipe

def prepare {checked : Checked} (marked : Marked checked) : Except Error (Prepared marked) :=
  match authenticated : SourceCoreCompatibleOutputs.prepareMarked marked with
  | .error error => .error (.output error)
  | .ok recipe => .ok ⟨recipe, authenticated⟩

structure SnapshotAt {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) where
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.recipe
  storeExact : snapshot.store = SourceCoreCompatibleMarkedLedger.store completion

private def snapshot {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) : Except Error (SnapshotAt prepared completion) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.recipe
      (SourceCoreCompatibleMarkedLedger.store completion) (SourceCoreCompatibleMarkedLedger.store_typed completion) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

def rawType {checked : Checked} {marked : Marked checked} {completion : Completion marked}
    (row : Row completion) : TypeSystem.Ty := row.entry.key.binder.scheme.body

/-- The present case retains the actual output decoder's sealed receipt.
Its source value is not inferred from native type preservation alone. -/
inductive CellDecoded {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (row : Row completion) : Cell → Prop where
  | absent (monomorphic : row.entry.key.binder.scheme.quantified = [])
      (missing : row.payload = none) : CellDecoded prepared completion row ⟨rawType row, none⟩
  | present {value : Core.Value}
      (monomorphic : row.entry.key.binder.scheme.quantified = [])
      (present : row.payload = some value)
      (snapshot : SnapshotAt prepared completion)
      (decoded : SourceCoreCompatibleOutputs.Decoded prepared.recipe snapshot.snapshot
        completion.result.context (rawType row) value) :
      CellDecoded prepared completion row ⟨rawType row, some decoded.source⟩

theorem CellDecoded.type_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) : cell.type = rawType row := by
  cases decoded <;> rfl

theorem CellDecoded.monomorphic {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) : row.entry.key.binder.scheme.quantified = [] := by
  cases decoded with
  | absent monomorphic _ => exact monomorphic
  | present monomorphic _ _ _ => exact monomorphic

theorem CellDecoded.initialized_projection {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {row : Row completion} {cell : Cell}
    (decoded : CellDecoded prepared completion row cell) {value : Core.Value}
    (present : row.payload = some value) :
    checked.catalog.project (rawType row) = .ok row.entry.key.payloadType := by
  cases decoded with
  | absent _ missing => rw [missing] at present; contradiction
  | present _ actual snapshot decoded =>
    have same := Option.some.inj (actual.symm.trans present)
    subst value
    have original := row.payload_typed (SourceCoreCompatibleMarkedLedger.store_typed completion) actual
    have typeEq := decoded.typed.type_eq.symm.trans original.type_eq
    rw [← typeEq]
    exact decoded.projected

private def decodeCell {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat) (row : Row completion) :
    Except Error {cell : Cell // CellDecoded prepared completion row cell} := do
  if monomorphic : row.entry.key.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨rawType row, none⟩, .absent monomorphic present⟩
    | some value =>
      match projected : checked.catalog.project (rawType row) with
      | .error error => throw (.projection row.sourceLocation error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          let snapshot ← match available with
            | none => throw .snapshotUnavailable
            | some snapshot => pure snapshot
          let typed : Core.RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type)
              value row.entry.key.payloadType marked.layouts.definitions := by
            rw [snapshot.storeExact]
            exact row.payload_typed (SourceCoreCompatibleMarkedLedger.store_typed completion) present
          let decoded ← (SourceCoreCompatibleOutputs.decode prepared.recipe snapshot.snapshot
            completion.result.context completion.result.contextOwner (rawType row) value row.entry.key.payloadType
            (by simpa only [same] using projected) typed fuel).mapError Error.output
          pure ⟨⟨rawType row, some decoded.source⟩, .present monomorphic present snapshot decoded⟩
        else throw (.payloadTypeMismatch row.sourceLocation type row.entry.key.payloadType)
  else throw (.generalizedBinding row.sourceLocation row.entry.key.binder.id)

private def cell {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat) (row : Row completion) : Except Error Cell :=
  (decodeCell prepared completion available fuel row).map Subtype.val

inductive CellsDecoded {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) : List (Row completion) → List Cell → Prop where
  | nil : CellsDecoded prepared completion [] []
  | cons {row : Row completion} {rows : List (Row completion)} {cell : Cell} {cells : List Cell}
      (head : CellDecoded prepared completion row cell)
      (tail : CellsDecoded prepared completion rows cells) :
      CellsDecoded prepared completion (row :: rows) (cell :: cells)

private theorem cells_sound {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked)
    (available : Option (SnapshotAt prepared completion)) (fuel : Nat)
    {rows : List (Row completion)} {cells : List Cell}
    (accepted : rows.mapM (cell prepared completion available fuel) = .ok cells) :
    CellsDecoded prepared completion rows cells := by
  induction rows generalizing cells with
  | nil => simp at accepted; subst cells; exact .nil
  | cons row rows ih =>
    cases head : decodeCell prepared completion available fuel row with
    | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind] at accepted
    | ok decoded =>
      cases tail : rows.mapM (cell prepared completion available fuel) with
      | error error => simp [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail] at accepted
      | ok rest =>
        simp only [List.mapM_cons, cell, head, Except.map, bind, Except.bind, tail, pure, Except.pure,
          Except.ok.injEq] at accepted
        subst cells
        exact .cons decoded.property (ih tail)

theorem CellsDecoded.types_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) : cells.map (·.type) = rows.map rawType := by
  induction decoded with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.type_exact, ih]

theorem CellsDecoded.length {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) : cells.length = rows.length := by
  induction decoded <;> simp_all

theorem CellsDecoded.lookup {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {rows : List (Row completion)} {cells : List Cell}
    (decoded : CellsDecoded prepared completion rows cells) {index : Nat} {row : Row completion}
    (found : rows[index]? = some row) :
    ∃ cell, cells[index]? = some cell ∧ CellDecoded prepared completion row cell := by
  induction decoded generalizing index with
  | nil => simp at found
  | cons head tail ih =>
    cases index with
    | zero => simp only [List.getElem?_cons_zero, Option.some.injEq] at found; subst row; exact ⟨_, rfl, head⟩
    | succ index => exact ih found

structure Export {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (initial : SourceHeap) where private mk ::
  receipt : SourceCoreCompatibleMarkedLedger.Receipt completion initial
  snapshot : Option (SnapshotAt prepared completion)
  cells : List Cell
  decoded : CellsDecoded prepared completion receipt.ledger.rows cells
  private fuel : Nat
  private exported : receipt.ledger.exportHeap (cell prepared completion snapshot fuel) = .ok (initial ++ cells)

def Export.heap {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) : SourceHeap := initial ++ exported.cells

/-- Empty/absent cell lists need no installed callable snapshot. In
particular, early fuel checkpoints retain their opaque prefix even before
the administrative globals have finished installation. -/
def exportHeap {checked : Checked} {marked : Marked checked}
    (prepared : Prepared marked) (completion : Completion marked) (initial : SourceHeap := []) (fuel : Nat := 1024) :
    Except Error (Export prepared completion initial) := do
  let receipt ← (SourceCoreCompatibleMarkedLedger.scan completion initial).mapError Error.ledger
  let available ← if receipt.ledger.rows.any (fun row => row.payload.isSome) then
      some <$> snapshot prepared completion
    else pure none
  match accepted : receipt.ledger.rows.mapM (cell prepared completion available fuel) with
  | .error error => throw error
  | .ok cells =>
    pure ⟨receipt, available, cells, cells_sound prepared completion available fuel accepted, fuel, by
      simp [SourceCoreAllocationLedger.Ledger.exportHeap, accepted, Functor.map, Except.map]⟩

theorem Export.prefix_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) : exported.heap.take initial.length = initial := by
  exact exported.receipt.ledger.exportHeap_prefix _ exported.exported

theorem Export.length_exact {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) :
    exported.heap.length = initial.length + exported.receipt.ledger.rows.length := by
  simp only [heap, List.length_append, exported.decoded.length]

theorem Export.cell_at_sourceLocation {checked : Checked} {marked : Marked checked}
    {prepared : Prepared marked} {completion : Completion marked} {initial : SourceHeap}
    (exported : Export prepared completion initial) (index : Fin exported.receipt.ledger.rows.length) :
    ∃ cell, exported.heap[(exported.receipt.ledger.rows[index]).sourceLocation.index]? = some cell ∧
      CellDecoded prepared completion (exported.receipt.ledger.rows[index]) cell := by
  obtain ⟨cell, found, decoded⟩ := exported.decoded.lookup (List.getElem?_eq_getElem index.isLt)
  refine ⟨cell, ?_, decoded⟩
  rw [exported.receipt.ledger.sourceLocation_exact]
  simpa [heap, List.getElem?_append_right] using found

end Solcore.Frontend.SourceCoreCompatibleHeapOutputs
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreHeapSnapshot
/-! Read-only source heap observations. Raw source callables remain private;
the public view exposes their signature, evidence and source capture indices,
but provides no source body, native reference, or registration operation.

Principal observations use the owning allocation/header restoration receipt.
In particular, an unused generic initializer may have a native Unit payload
and an open raw source type. It is never presented as a closed callable handle.
The Legacy namespace is the explicit migration boundary for checked inert
prefixes. None of these observation capabilities can be invoked. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreHeapSnapshot
open SourceInference TypeSystem

structure ObservedValue where private mk ::
  private source : SourceTypedRuntime.Value

instance : Repr ObservedValue where
  reprPrec _ _ := "<opaque source observation>"

inductive ValueView where
  | unit
  | bool (value : Bool)
  | word (value : Core.Word)
  | integer (value : Int)
  | product (left right : ObservedValue)
  | proxy (inner : Ty)
  | constructed (instantiation : DataConstructorInstantiation) (payloads : List ObservedValue)
  | mapping (keyType valueType : Ty) (entries : List (ObservedValue × ObservedValue))
  | closure (parameters : List TypedBinder) (resultType : Ty)
      (owner : SourceSpecialization.SpecializationKey)
      (captures : List (Resolved.LocalId × Nat))
      (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  | instantiated (substitution : Substitution)
      (requirements : List SourceTypedRuntime.LocalRequirementWitness) (principal : ObservedValue)
  | global (key : SourceSpecialization.SpecializationKey)
      (evidence : SourceTypedRuntime.RuntimeEvidenceEnvironment)
  | builtin (function : BuiltinFunctionId)
  deriving Repr

def ObservedValue.view (value : ObservedValue) : ValueView :=
  match value.source with
  | .unit => .unit
  | .bool value => .bool value
  | .word value => .word value
  | .integer value => .integer value
  | .product left right => .product ⟨left⟩ ⟨right⟩
  | .proxy inner => .proxy inner
  | .constructed instantiation payloads => .constructed instantiation (payloads.map ObservedValue.mk)
  | .mapping key value entries => .mapping key value (entries.map fun (key, value) => (⟨key⟩, ⟨value⟩))
  | .closure parameters result _ _ owner captures evidence =>
      .closure parameters result owner (captures.map fun (binder, location) => (binder, location.index)) evidence
  | .instantiated substitution requirements principal => .instantiated substitution requirements ⟨principal⟩
  | .global key evidence => .global key evidence
  | .builtin function => .builtin function

structure Principal where private mk ::
  private rawType : Ty
  private rawScheme : Scheme
  private source : ObservedValue

def Principal.type (principal : Principal) : Ty := principal.rawType
def Principal.scheme (principal : Principal) : Scheme := principal.rawScheme
def Principal.observation (principal : Principal) : ObservedValue := principal.source

instance : Repr Principal where
  reprPrec principal _ := "<principal " ++ repr principal.type ++ ">"

/-- This constructor needs an actual cached header/allocation join. The native
payload is deliberately not required to be a ground callable. -/
def Principal.ofRestored {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) : Principal :=
  ⟨restored.cell.type, restored.header.declaration.binder.scheme,
    ⟨restored.header.sourceValue row.environment⟩⟩

theorem Principal.ofRestored_type {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) :
    (Principal.ofRestored restored).type = restored.header.declaration.binder.scheme.body :=
  restored.raw_type

theorem Principal.ofRestored_captures {checked : SourceCoreCompatibleCatalog.Checked}
    {program : SourceCoreCallableIndexedPrograms.Prepared checked}
    {graph : SourceCoreCallableAncestryPairedPreparation.Prepared program.base}
    {headers : SourceCoreCallablePairedHeaders.Prepared graph}
    {store : Core.Store} {row : SourceCoreAllocationLedger.Row program.layouts store}
    (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored headers row) :
    (Principal.ofRestored restored).observation.view = .closure
      restored.header.parameters restored.header.resultType restored.header.state.metadata.owner
      (row.environment.map fun (binder, location) => (binder, location.index))
      restored.header.principal.context.evidence := rfl

inductive Contents where
  | data (value : SourceCorePublicValues.Value)
  | principal (value : Principal)
  | legacy (value : ObservedValue)
  deriving Repr

structure Cell where
  location : Nat
  type : Ty
  value : Option Contents
  deriving Repr

namespace Legacy

private def observeCell (location : Nat) (cell : SourceTypedRuntime.Cell) : Cell :=
  ⟨location, cell.type, cell.value.map fun value => .legacy ⟨value⟩⟩

/-- Migration-only factory. The existing deep validator decides admission;
read-only observation adds no closed-type, payload, or callable restriction.
The erased receipt means building the view does not rerun validation. -/
def observeAccepted (signatures : ProgramSignatures) (plan : SourceCompilationPlan.Plan)
    (state : SourceTypedRuntime.RuntimeState) (fuel : Nat)
    (_accepted : state.isDeeplySafe fuel signatures plan = true) : List Cell :=
  state.heap.zipIdx.map fun (cell, index) => observeCell index cell

theorem observeAccepted_length {signatures : ProgramSignatures} {plan : SourceCompilationPlan.Plan}
    {state : SourceTypedRuntime.RuntimeState} {fuel : Nat}
    (accepted : state.isDeeplySafe fuel signatures plan = true) :
    (observeAccepted signatures plan state fuel accepted).length = state.heap.length := by
  simp [observeAccepted]

theorem observeAccepted_types {signatures : ProgramSignatures} {plan : SourceCompilationPlan.Plan}
    {state : SourceTypedRuntime.RuntimeState} {fuel : Nat}
    (accepted : state.isDeeplySafe fuel signatures plan = true) :
    (observeAccepted signatures plan state fuel accepted).map Cell.type = state.heap.map SourceTypedRuntime.Cell.type := by
  simp only [observeAccepted, List.map_map]
  change state.heap.zipIdx.map (SourceTypedRuntime.Cell.type ∘ Prod.fst) = state.heap.map SourceTypedRuntime.Cell.type
  rw [← List.map_map (f := Prod.fst) (g := SourceTypedRuntime.Cell.type), List.zipIdx_map_fst]

end Legacy
end Solcore.Frontend.SourceCoreHeapSnapshot
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreIndexedHeapMigration
/-! Raw source cell reconstruction from an owned indexed program's current
typed store. This is a migration adapter, independent of seed completion.
Function leaves must be subvalues of actual allocation payloads. Cached exact
templates, read recipes, capture joins and installed named slots authenticate
their source reconstruction. No source body is traversed or evaluated.

The resulting heap still needs the existing deep source validator before it
can become an opaque inert prefix. These receipts establish reconstruction and
native provenance; they do not assert whole execution correspondence. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreIndexedHeapMigration
open SourceInference Core
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Program := SourceCoreCallableIndexedPrograms.Prepared
abbrev Prepared {checked : Checked} (program : Program checked) := SourceCoreCallableIndexedHeapOutputs.Prepared program
abbrev Values := SourceCoreCompatibleValues.Context
abbrev SourceHeap := SourceCoreAllocationLedger.SourceHeap
abbrev SourceCell := SourceTypedRuntime.Cell
abbrev SourceValue := SourceTypedRuntime.Value
abbrev Ledger {checked : Checked} (program : Program checked) (initial : SourceHeap) (world : StoreTyping) (store : Store) :=
  SourceCoreAllocationLedger.TypedLedger program.layouts initial world store

inductive Error where
  | output (error : SourceCoreCompatibleOutputs.Error)
  | projection (error : SourceCoreCompatibleCatalog.Error)
  | restore (error : SourceCoreCallableIndexedRestoration.Error)
  | principal (error : SourceCoreCallableIndexedPrincipalAllocations.Error)
  | header (error : SourceCoreCallableIndexedCellHeaders.Error)
  | unavailableLeaf
  | notCallable
  | typeMismatch (expected actual : Core.Ty)
  | rawTypeMismatch (expected actual : TypeSystem.Ty)
  deriving Repr

structure Located {checked : Checked} {program : Program checked} {initial : SourceHeap}
    {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) (value : Core.Value) where private mk ::
  ordinal : Fin ledger.ledger.rows.length
  root : Core.Value
  present : (ledger.ledger.rows[ordinal]).payload = some root
  inside : SourceCoreCallableNativeSlots.Subvalue value root
  typed : RuntimeValueHasType world value value.type program.layouts.definitions

def locate {checked : Checked} {program : Program checked} {initial : SourceHeap}
    {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) (value : Core.Value) :
    Except Error (Located ledger value) :=
  match (List.finRange ledger.ledger.rows.length).findSome? (fun ordinal =>
    match present : (ledger.ledger.rows[ordinal]).payload with
    | none => none
    | some root => match SourceCoreCallableNativeSubvalues.find value root with
      | none => none
      | some inside => some (⟨ordinal, root, present, inside.related,
          SourceCoreCallableNativeSubvalues.runtime_typed inside.related
            ((ledger.ledger.rows[ordinal]).payload_typed ledger.typed present)⟩ : Located ledger value)) with
  | none => .error .unavailableLeaf
  | some located => .ok located

inductive LeafRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (expected : TypeSystem.Ty) (value : Core.Value) : SourceValue → Prop where
  | ordinary (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedTemplates.Authenticated prepared.output.templates world store value)
      (restored : SourceCoreCallableIndexedRestoration.Ordinary prepared.output.headers authenticated ledger) :
      LeafRelated prepared ledger expected value restored.source
  | read (located : Located ledger value)
      (authenticated : SourceCoreCallableIndexedReadViews.Authenticated prepared.output.views world store value)
      (restored : SourceCoreCallableIndexedRestoration.Read prepared.output.headers authenticated ledger) :
      LeafRelated prepared ledger expected value restored.source
  | known (located : Located ledger value)
      {source : SourceValue}
      (decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.output.recipe expected value = .ok source) :
      LeafRelated prepared ledger expected value source

structure Leaf {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    (expected : TypeSystem.Ty) (value : Core.Value) where private mk ::
  source : SourceValue
  type : Core.Ty
  projected : checked.catalog.project expected = .ok type
  typed : RuntimeValueHasType world value type program.layouts.definitions
  related : LeafRelated prepared ledger expected value source

def decodeLeaf {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (expected : TypeSystem.Ty) (value : Core.Value) : Except Error (Leaf (prepared := prepared) (ledger := ledger) expected value) := do
  let located ← locate ledger value
  let .product (.product (.sum .unit .word) (.function parameter (.sum .word result))) .word := value.type
    | throw .notCallable
  match projected : checked.catalog.project expected with
  | .error error => throw (.projection error)
  | .ok type =>
    if same : type = CallableContract.functionType parameter result then
      if valueType : value.type = CallableContract.functionType parameter result then
        have typed : RuntimeValueHasType world value (CallableContract.functionType parameter result) program.layouts.definitions :=
          valueType ▸ located.typed
        have expectedTyped : RuntimeValueHasType world value type program.layouts.definitions := same.symm ▸ typed
        match SourceCoreCallableIndexedReadViews.authenticate prepared.output.views ledger.typed value parameter result typed with
        | .ok authenticated =>
          let restored ← (SourceCoreCallableIndexedRestoration.restoreRead prepared.output.headers authenticated ledger).mapError Error.restore
          pure ⟨restored.source, type, projected, expectedTyped, .read located authenticated restored⟩
        | .error _ =>
          match SourceCoreCallableIndexedTemplates.authenticate prepared.output.templates ledger.typed value parameter result typed with
          | .ok authenticated =>
            let restored ← (SourceCoreCallableIndexedRestoration.restoreOrdinary prepared.output.headers authenticated ledger).mapError Error.restore
            pure ⟨restored.source, type, projected, expectedTyped, .ordinary located authenticated restored⟩
          | .error _ =>
            match decoded : SourceCoreCompatibleOutputs.decodeCallable prepared.output.recipe expected value with
            | .error error => throw (.output error)
            | .ok source => pure ⟨source, type, projected, expectedTyped, .known located decoded⟩
      else throw (.typeMismatch (CallableContract.functionType parameter result) value.type)
    else throw (.typeMismatch (CallableContract.functionType parameter result) type)

def leafPolicy {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store) :
    SourceCoreCompatibleOutputs.LeafDecoder := fun expected value =>
  (decodeLeaf prepared ledger expected value).map (·.source) |>.mapError (fun _ => ⟨[], .callablePayloadMismatch⟩)

structure NativeSnapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {world : StoreTyping} {store : Store} where private mk ::
  snapshot : SourceCoreCompatibleOutputs.Snapshot prepared.output.recipe
  exact : snapshot.store = store

def nativeSnapshot {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {world : StoreTyping} {store : Store} (stored : RuntimeStoreHasTypes world store program.layouts.definitions) :
    Except Error (NativeSnapshot (world := world) (store := store) prepared) :=
  match accepted : SourceCoreCompatibleOutputs.snapshot prepared.output.recipe store
      (by simpa only [stored.world_eq] using stored) with
  | .error error => .error (.output error)
  | .ok snapshot => .ok ⟨snapshot, SourceCoreCompatibleOutputs.snapshot_store accepted⟩

inductive CellRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values)
    (row : SourceCoreAllocationLedger.Row program.layouts store) : SourceCell → Prop where
  | absent (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (mono : selected.header.raw.binder.scheme.quantified = []) (absent : row.payload = none) :
      CellRelated prepared ledger snapshot values row ⟨selected.header.raw.binder.scheme.body, none⟩
  | present (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (mono : selected.header.raw.binder.scheme.quantified = [])
      {value : Core.Value} (present : row.payload = some value)
      (decoded : SourceCoreCompatibleOutputs.LeafDecoded (leafPolicy prepared ledger)
        prepared.output.recipe snapshot.snapshot values selected.header.raw.binder.scheme.body value) :
      CellRelated prepared ledger snapshot values row ⟨selected.header.raw.binder.scheme.body, some decoded.source⟩
  | principal (selected : SourceCoreCallableIndexedCellHeaders.Selected prepared.headers row)
      (generic : selected.header.raw.binder.scheme.quantified ≠ [])
      (restored : SourceCoreCallableIndexedPrincipalAllocations.Restored prepared.output.headers row)
      (rawType : restored.cell.type = selected.header.raw.binder.scheme.body) :
      CellRelated prepared ledger snapshot values row restored.cell

structure CellDecoded {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values}
    (row : SourceCoreAllocationLedger.Row program.layouts store) where private mk ::
  cell : SourceCell
  related : CellRelated prepared ledger snapshot values row cell

def decodeCell {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared)
    (values : Values) (owner : values.checked = checked)
    (row : SourceCoreAllocationLedger.Row program.layouts store) (fuel : Nat) :
    Except Error (CellDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) row) := do
  let selected ← (SourceCoreCallableIndexedCellHeaders.select prepared.headers row).mapError Error.header
  if mono : selected.header.raw.binder.scheme.quantified = [] then
    match present : row.payload with
    | none => pure ⟨⟨selected.header.raw.binder.scheme.body, none⟩, .absent selected mono present⟩
    | some value =>
      match projected : checked.catalog.project selected.header.raw.binder.scheme.body with
      | .error error => throw (.projection error)
      | .ok type =>
        if same : type = row.entry.key.payloadType then
          have typed : RuntimeValueHasType (snapshot.snapshot.store.map Core.Value.type) value type program.layouts.definitions := by
            rw [snapshot.exact, ← ledger.typed.world_eq, same]
            exact row.payload_typed ledger.typed present
          let decoded ← (SourceCoreCompatibleOutputs.decodeWithLeaves (leafPolicy prepared ledger) prepared.output.recipe
            snapshot.snapshot values owner selected.header.raw.binder.scheme.body value type projected typed fuel).mapError Error.output
          pure ⟨⟨selected.header.raw.binder.scheme.body, some decoded.source⟩, .present selected mono present decoded⟩
        else throw (.typeMismatch row.entry.key.payloadType type)
  else
    let restored ← (SourceCoreCallableIndexedPrincipalAllocations.restore prepared.output.headers row).mapError Error.principal
    if rawType : restored.cell.type = selected.header.raw.binder.scheme.body then
      pure ⟨restored.cell, .principal selected mono restored rawType⟩
    else throw (.rawTypeMismatch selected.header.raw.binder.scheme.body restored.cell.type)

inductive CellsRelated {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values) :
    List (SourceCoreAllocationLedger.Row program.layouts store) → SourceHeap → Prop where
  | nil : CellsRelated prepared ledger snapshot values [] []
  | cons {row rows cell cells} (head : CellRelated prepared ledger snapshot values row cell)
      (tail : CellsRelated prepared ledger snapshot values rows cells) :
      CellsRelated prepared ledger snapshot values (row :: rows) (cell :: cells)

theorem CellsRelated.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values} {rows : List _} {cells : SourceHeap}
    (related : CellsRelated prepared ledger snapshot values rows cells) : cells.length = rows.length := by
  induction related with
  | nil => rfl
  | cons _ _ ih => simpa only [List.length_cons] using congrArg Nat.succ ih

structure CellsDecoded {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store}
    {snapshot : NativeSnapshot (world := world) (store := store) prepared} {values : Values}
    (rows : List (SourceCoreAllocationLedger.Row program.layouts store)) where private mk ::
  cells : SourceHeap
  related : CellsRelated prepared ledger snapshot values rows cells

def decodeCells {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (snapshot : NativeSnapshot (world := world) (store := store) prepared) (values : Values)
    (owner : values.checked = checked) (fuel : Nat) :
    (rows : List (SourceCoreAllocationLedger.Row program.layouts store)) →
    Except Error (CellsDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) rows)
  | [] => pure ⟨[], .nil⟩
  | row :: rows => do
    let head ← decodeCell prepared ledger snapshot values owner row fuel
    let tail ← decodeCells prepared ledger snapshot values owner fuel rows
    pure ⟨head.cell :: tail.cells, .cons head.related tail.related⟩

structure Export {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (values : Values) where private mk ::
  snapshot : NativeSnapshot (world := world) (store := store) prepared
  decoded : CellsDecoded (prepared := prepared) (ledger := ledger) (snapshot := snapshot) (values := values) ledger.ledger.rows

def Export.heap {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : SourceHeap := initial ++ exported.decoded.cells

def exportHeap {checked : Checked} {program : Program checked} (prepared : Prepared program)
    {initial : SourceHeap} {world : StoreTyping} {store : Store} (ledger : Ledger program initial world store)
    (values : Values) (owner : values.checked = checked) (fuel : Nat) : Except Error (Export prepared ledger values) := do
  let snapshot ← nativeSnapshot prepared ledger.typed
  let decoded ← decodeCells prepared ledger snapshot values owner fuel ledger.ledger.rows
  pure ⟨snapshot, decoded⟩

theorem Export.length {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : exported.heap.length = initial.length + ledger.ledger.rows.length := by
  simp only [Export.heap, List.length_append]
  rw [exported.decoded.related.length]

theorem Export.prefix {checked : Checked} {program : Program checked} {prepared : Prepared program}
    {initial : SourceHeap} {world : StoreTyping} {store : Store} {ledger : Ledger program initial world store} {values : Values}
    (exported : Export prepared ledger values) : exported.heap.take initial.length = initial := by
  simp [Export.heap]

end Solcore.Frontend.SourceCoreIndexedHeapMigration
end

section
-- leanmerge: from Solcore.Frontend.SourceCorePublicOutputShapes
/-! Structural native output shapes for the owned public codec. Metadata is
looked up in the actual boundary registry. Function leaves retain native
world typing. A mapping default is the pure default of its original raw
value type; the shape contains no decoding or export-success hypothesis. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicOutputShapes
open SourceInference TypeSystem
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Registry := SourceCoreRawMetadata.Registry
abbrev DataValue := SourceCoreDataValues.Value
abbrev runtimeType := SourceCoreRawMetadata.runtimeType

def pack : List Core.Value → Core.Value
  | [] => .unit
  | [value] => value
  | value :: values => .pair value (pack values)

mutual
  /-- Data carriers produced by the pure default operation. In particular,
  mapping defaults contain no entries and cannot hide function leaves. -/
  inductive DefaultData (checked : Checked) (registry : Registry) : Ty → DataValue → Core.Value → Prop where
    | unit : DefaultData checked registry .unit .unit .unit
    | bool (value : Bool) : DefaultData checked registry .bool (.bool value) (.bool value)
    | word (value : Core.Word) : DefaultData checked registry .word (.word value) (.word value)
    | integer (value : Int) : DefaultData checked registry .integer (.integer value) (.integer value)
    | product {leftType rightType : Ty} {left right : DataValue} {a b : Core.Value}
        (first : DefaultData checked registry leftType left a)
        (second : DefaultData checked registry rightType right b) :
        DefaultData checked registry (.product leftType rightType) (.product left right) (.pair a b)
    | proxy {inner : Ty} {owner : Core.DataTypeId} {id : Core.Word}
        (metadata : registry.lookup id = some (.proxy inner))
        (identity : checked.catalog.identity? (.proxy inner) = some owner) :
        DefaultData checked registry (.proxy inner) (.proxy inner) (.constructed ⟨owner, 0⟩ (.word id))
    | mapping {key value : Ty} {id : Core.Word} {layout : Core.OrderedMapping.Layout} {fallback : Core.Value}
        (metadata : registry.lookup id = some (.mapping key value))
        (layoutAt : checked.catalog.mappingLayout key value = .ok layout)
        (defaultValue : Default checked registry value layout.valueType fallback) :
        DefaultData checked registry (.mapping key value) (.mapping key value [])
          (.pair (.word id) (.pair fallback (Core.OrderedMapping.encode layout [])))
    | compatible {expected actual : Ty} {data : DataValue} {native : Core.Value}
        (same : runtimeType expected = runtimeType actual)
        (shape : DefaultData checked registry actual data native) :
        DefaultData checked registry expected data native
  inductive Default (checked : Checked) (registry : Registry) : Ty → Core.Ty → Core.Value → Prop where
    | absent {raw : Ty} {type : Core.Ty}
        (missing : SourceCoreCompatibleValues.defaultValue? (raw.size + 1) raw = none) :
        Default checked registry raw type (.inLeft type .unit)
    | present {raw : Ty} {type : Core.Ty} {data : DataValue} {native : Core.Value}
        (computed : SourceCoreCompatibleValues.defaultValue? (raw.size + 1) raw = some data)
        (shape : DefaultData checked registry raw data native) :
        Default checked registry raw type (.inRight .unit native)
end

mutual
  inductive Output (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : Ty → Core.Value → Prop where
    | unit : Output checked registry world definitions .unit .unit
    | bool (value : Bool) : Output checked registry world definitions .bool (.bool value)
    | word (value : Core.Word) : Output checked registry world definitions .word (.word value)
    | integer (value : Int) : Output checked registry world definitions .integer (.integer value)
    | product {leftType rightType : Ty} {left right : Core.Value}
        (first : Output checked registry world definitions leftType left)
        (second : Output checked registry world definitions rightType right) :
        Output checked registry world definitions (.product leftType rightType) (.pair left right)
    | function {parameter result : Ty} {native : Core.Value} {type : Core.Ty}
        (generated : checked.catalog.project (.function parameter result) = .ok type)
        (typed : Core.RuntimeValueHasType world native type definitions) :
        Output checked registry world definitions (.function parameter result) native
    | proxy {inner : Ty} {owner : Core.DataTypeId} {id : Core.Word}
        (metadata : registry.lookup id = some (.proxy inner))
        (identity : checked.catalog.identity? (.proxy inner) = some owner) :
        Output checked registry world definitions (.proxy inner) (.constructed ⟨owner, 0⟩ (.word id))
    | constructed {metadata : DataConstructorInstantiation} {id : Core.Word} {tag : Core.ConstructorId}
        {values : List Core.Value}
        (metadataAt : registry.lookup id = some (.constructor metadata))
        (resolved : checked.resolveConstructor metadata = .ok tag)
        (nominal : ∃ declaration arguments, metadata.resultType = Ty.nominal declaration arguments)
        (payloads : Payloads checked registry world definitions metadata.payloadTypes values) :
        Output checked registry world definitions metadata.resultType
          (.constructed tag (.pair (.word id) (pack values)))
    | mapping {key value : Ty} {id : Core.Word} {layout : Core.OrderedMapping.Layout}
        {entries : Core.OrderedMapping.Entries} {fallback : Core.Value}
        (metadata : registry.lookup id = some (.mapping key value))
        (layoutAt : checked.catalog.mappingLayout key value = .ok layout)
        (stored : Entries checked registry world definitions key value entries)
        (defaultValue : Default checked registry value layout.valueType fallback) :
        Output checked registry world definitions (.mapping key value)
          (.pair (.word id) (.pair fallback (Core.OrderedMapping.encode layout entries)))
    | compatible {expected actual : Ty} {native : Core.Value}
        (same : runtimeType expected = runtimeType actual)
        (shape : Output checked registry world definitions actual native) :
        Output checked registry world definitions expected native
  inductive Payloads (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : List Ty → List Core.Value → Prop where
    | nil : Payloads checked registry world definitions [] []
    | cons {type : Ty} {value : Core.Value} {types : List Ty} {values : List Core.Value}
        (head : Output checked registry world definitions type value)
        (tail : Payloads checked registry world definitions types values) :
        Payloads checked registry world definitions (type :: types) (value :: values)
  inductive Entries (checked : Checked) (registry : Registry) (world : Core.StoreTyping)
      (definitions : Core.DataEnvironment) : Ty → Ty → Core.OrderedMapping.Entries → Prop where
    | empty (key value : Ty) : Entries checked registry world definitions key value []
    | entry {key value : Ty} {a b : Core.Value} {rest : Core.OrderedMapping.Entries}
        (first : Output checked registry world definitions key a)
        (second : Output checked registry world definitions value b)
        (tail : Entries checked registry world definitions key value rest) :
        Entries checked registry world definitions key value ((a, b) :: rest)
end
end Solcore.Frontend.SourceCorePublicOutputShapes
end

section
-- leanmerge: from Solcore.Frontend.SourceCorePublicDefaultOutputCodec
/-! The actual data codec terminates and recovers each structurally represented
pure default. Existing metadata is reused; decoding and re-encoding keep the
same raw registry, including nested mapping defaults. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCorePublicOutputShapes
open TypeSystem SourceInference
namespace Codec
abbrev Context := SourceCoreCompatibleValues.Context
open SourceCoreCompatibleValues (decodeRaw encodeRaw decodeDefaultRaw encodeDefaultRaw defaultValue?)

theorem identity_eq {catalog : SourceCoreCompatibleCatalog.Catalog} {expected actual : Ty}
    (same : SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType actual) : catalog.identity? expected = catalog.identity? actual := by
  simp only [SourceCoreCompatibleCatalog.Catalog.identity?, same]

theorem mapping_layout_runtime {catalog : SourceCoreCompatibleCatalog.Catalog}
    {key value : Ty} {layout : Core.OrderedMapping.Layout}
    (accepted : catalog.mappingLayout key value = .ok layout) :
    catalog.mappingLayout (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value) = .ok layout := by
  have identity : catalog.identity? (.mapping (SourceCoreRawMetadata.runtimeType key) (SourceCoreRawMetadata.runtimeType value)) =
      catalog.identity? (.mapping key value) := by
    simp only [SourceCoreCompatibleCatalog.Catalog.identity?, SourceCoreRawMetadata.runtimeType,
      SourceCoreRawMetadata.runtimeType_idempotent]
    rfl
  unfold SourceCoreCompatibleCatalog.Catalog.mappingLayout at accepted ⊢
  rw [identity, catalog.project_runtimeType, catalog.project_runtimeType]
  cases selected : catalog.identity? (.mapping key value) with
  | none => simp [selected, throw, throwThe, bind, Except.bind] at accepted
  | some owner =>
    simp only [selected, pure, Except.pure, bind, Except.bind] at accepted ⊢
    cases first : catalog.project key with
    | error error => simp [first] at accepted
    | ok a =>
      cases second : catalog.project value with
      | error error => simp [first, second] at accepted
      | ok b =>
        simp only [first, second] at accepted ⊢
        split at accepted
        · rename_i registered
          simpa only [if_pos registered] using accepted
        · cases accepted

private def DataComplete (context : Context) (raw : Ty) (data : DataValue) (native : Core.Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel → ∀ expected, SourceCoreRawMetadata.runtimeType expected = SourceCoreRawMetadata.runtimeType raw →
    decodeRaw fuel context expected native = .ok data ∧
    encodeRaw fuel context.checked context.registry expected data = .ok (.pure context.registry native)

private def DefaultComplete (context : Context) (raw : Ty) (type : Core.Ty) (native : Core.Value) : Prop :=
  ∃ bound, ∀ fuel, bound ≤ fuel →
    decodeDefaultRaw fuel context raw type native = .ok (defaultValue? (raw.size + 1) raw) ∧
    encodeDefaultRaw fuel context.checked context.registry raw type = .ok (.pure context.registry native)

theorem data_complete (context : Context) {raw : Ty} {data : DataValue} {native : Core.Value}
    (shape : DefaultData context.checked context.registry raw data native) :
    DataComplete context raw data native := by
  induction shape using DefaultData.rec
    (motive_2 := fun raw type native _ => DefaultComplete context raw type native) with
  | unit =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | bool value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | word value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | integer value =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      unfold decodeRaw encodeRaw
      rw [same]
      exact ⟨rfl, rfl⟩
  | @product leftType rightType left right a b first second leftIH rightIH =>
    obtain ⟨leftBound, leftComplete⟩ := leftIH
    obtain ⟨rightBound, rightComplete⟩ := rightIH
    refine ⟨max leftBound rightBound + 1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨leftDecoded, leftEncoded⟩ := leftComplete fuel (by omega) (SourceCoreRawMetadata.runtimeType leftType)
        (SourceCoreRawMetadata.runtimeType_idempotent leftType)
      obtain ⟨rightDecoded, rightEncoded⟩ := rightComplete fuel (by omega) (SourceCoreRawMetadata.runtimeType rightType)
        (SourceCoreRawMetadata.runtimeType_idempotent rightType)
      constructor
      · unfold decodeRaw
        rw [same]
        simp only [SourceCoreRawMetadata.runtimeType, leftDecoded, rightDecoded, Except.mapError,
          bind, Except.bind, pure, Except.pure]
      · unfold encodeRaw
        rw [same]
        simp only [SourceCoreRawMetadata.runtimeType, leftEncoded, rightEncoded, SourceCoreCompatibleValues.Extended.pure, Except.mapError,
          bind, Except.bind, pure, Except.pure]
  | @proxy inner owner id metadata identity =>
    refine ⟨1, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      have expectedIdentity := (identity_eq same).trans identity
      exact ⟨SourceCoreCompatibleValues.decode_proxy_at context metadata same expectedIdentity fuel,
        SourceCoreCompatibleValues.encode_proxy_at context.checked metadata same expectedIdentity fuel⟩
  | @mapping key value id layout fallback metadata layoutAt defaultValue defaultIH =>
    obtain ⟨bound, complete⟩ := defaultIH
    refine ⟨bound + 2, ?_⟩
    intro fuel enough expected same
    cases fuel with
    | zero => omega
    | succ fuel =>
      obtain ⟨defaultDecoded, defaultEncoded⟩ := complete fuel (by omega)
      have rowsDecoded : SourceCoreCompatibleValues.decodeEntriesRaw fuel context key value layout
          (Core.OrderedMapping.encode layout []) 0 = .ok [] := by
        cases fuel with
        | zero => omega
        | succ fuel => simp [SourceCoreCompatibleValues.decodeEntriesRaw, Core.OrderedMapping.encode]
      exact ⟨SourceCoreCompatibleValues.decode_mapping_at context metadata same layoutAt rowsDecoded defaultDecoded,
        SourceCoreCompatibleValues.encode_mapping_at context.checked metadata same (mapping_layout_runtime layoutAt)
          (by simp [SourceCoreCompatibleValues.encodeEntriesRaw]) defaultEncoded⟩
  | compatible same shape ih =>
    obtain ⟨bound, complete⟩ := ih
    exact ⟨bound, fun fuel enough expected matched => complete fuel enough expected (matched.trans same)⟩
  | absent missing =>
    exact ⟨0, fun _ _ => ⟨by simp [decodeDefaultRaw, missing], by simp [encodeDefaultRaw, missing]⟩⟩
  | @present raw type data native computed shape ih =>
    obtain ⟨bound, complete⟩ := ih
    refine ⟨bound, ?_⟩
    intro fuel enough
    obtain ⟨decoded, encoded⟩ := complete fuel enough raw rfl
    constructor
    · simp [decodeDefaultRaw, computed, decoded]
      rfl
    · simp [encodeDefaultRaw, computed, encoded]
      rfl

theorem default_complete (context : Context) {raw : Ty} {type : Core.Ty} {native : Core.Value}
    (shape : Default context.checked context.registry raw type native) :
    DefaultComplete context raw type native := by
  cases shape with
  | absent missing =>
    exact ⟨0, fun _ _ => ⟨by simp [decodeDefaultRaw, missing], by simp [encodeDefaultRaw, missing]⟩⟩
  | present computed shape =>
    obtain ⟨bound, complete⟩ := data_complete context shape
    refine ⟨bound, ?_⟩
    intro fuel enough
    obtain ⟨decoded, encoded⟩ := complete fuel enough raw rfl
    constructor
    · simp [decodeDefaultRaw, computed, decoded]
      rfl
    · simp [encodeDefaultRaw, computed, encoded]
      rfl

end Codec
end Solcore.Frontend.SourceCorePublicOutputShapes
end
