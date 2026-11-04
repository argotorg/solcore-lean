import Solcore.Frontend.SourceCore.Lowering
import Solcore.Frontend.SourceSpecialization
import Solcore.Core.Check
import Solcore.Frontend.SourceCore.GeneralFunctions
import Solcore.Frontend.SourceCore.DataPlaces
import Solcore.Frontend.SourceCore.RawMetadata
import Solcore.Frontend.Internal.RuntimeValues
import Solcore.Core.Safety

/-!
# Allocation metadata

Allocation markers, their discovery, fixed layouts, the source ledger and canonical contexts.
-/

section
-- leanmerge: from Solcore.Frontend.SourceCoreAllocationCodebook
/-! A pure allocation-marker factory and AST catalog pass. Canonical context
inventories retain original binder metadata and complete local substitutions.
The emitter uses a fresh nominal identity outside the ambient definitions;
ordinary ambient-typed Core cannot contain that placeholder constructor.

The pass validates the entire placeholder shape, every key and exact scope
layout, preserves the actual capture references, and replaces it with ordinary
HeapMarkers allocation code. Each collected site retains its decoding receipt.
A receipt proves structural authentication, not historical emission of an
arbitrary externally supplied Core AST. Public compiler integration must retain
actual emitter provenance. This module neither evaluates source/Core code nor
claims source-heap export correctness. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationCodebook
open SourceInference Core

abbrev Key := SourceSpecialization.SpecializationKey
abbrev Scope := SourceCoreLocalCell.Scope

structure Binding where
  binder : TypedBinder
  payloadType : Core.Ty
  deriving Repr, DecidableEq

/-- Bindings include ordinary locals/parameters and explicitly inventoried
compiler-generated match/native-bundle cells. The caller must obtain those
rows from its original metadata receipts, not infer them from Core types. -/
structure ContextInventory where
  owner : Key
  active : TypeSystem.Substitution
  source : TypedSource
  bindings : List Binding
  deriving Repr, DecidableEq

structure IndexedBinding where
  key : Word
  binding : Binding
  deriving Repr, DecidableEq

structure IndexedContext where
  key : Word
  inventory : ContextInventory
  bindings : List IndexedBinding
  deriving Repr, DecidableEq

inductive Error where
  | invalidAmbientDefinitions
  | keyOverflow (index : Nat)
  | duplicateContexts
  | duplicateContextKeys
  | invalidContext (key : Word)
  | missingContext (owner : Key) (active : TypeSystem.Substitution)
  | sourceViewMismatch (key : Word)
  | missingBinder (key : Word) (id : Resolved.LocalId)
  | binderMismatch (id : Resolved.LocalId)
  | payloadMismatch (id : Resolved.LocalId) (expected actual : Core.Ty)
  | duplicateScope
  | duplicateReferences
  | unknownContextKey (key : Word)
  | unknownBinderKey (context binder : Word)
  | malformedPlaceholder
  | invalidCaptureShape
  | invalidType (type : Core.Ty)
  | reservedIdentity (id : DataTypeId)
  | emissionMismatch
  | traversalExhausted
  | invalidAllocationIndices
  | invalidFinalDefinitions
  | finalBodyType (expected : Core.Ty) (actual : Option Core.Ty)
  deriving Repr, DecidableEq

def wordKey (index : Nat) : Except Error Word :=
  match Word.ofNat? index with
  | some key => .ok key
  | none => .error (.keyOverflow index)

/-- Raw expression views may alter types/evidence on expression nodes, while
owner, inputs, roots, forms and complete statement metadata remain fixed. -/
inductive MetadataNode where
  | expression (id : ExpressionId) (form : ExpressionForm)
  | statement (node : StatementNode)
  deriving Repr, DecidableEq

structure MetadataSource where
  owner : Resolved.DeclarationId
  inputs : List TypedBinder
  roots : List NodeId
  nodes : List MetadataNode
  deriving Repr, DecidableEq

def sourceView (source : TypedSource) : MetadataSource :=
  ⟨source.owner, source.inputs, source.roots, source.nodes.map fun node => match node with
    | .expression expression => .expression expression.id expression.form
    | .statement statement => .statement statement⟩

def contextValid (ambient : DataEnvironment) (context : IndexedContext) : Bool :=
  decide (context.inventory.owner.declaration = context.inventory.source.owner) &&
  decide ((context.inventory.bindings.map (·.binder.id)).Nodup) &&
  decide ((context.bindings.map (·.key)).Nodup) &&
  decide (context.bindings.map (·.binding) = context.inventory.bindings) &&
  context.bindings.all (fun row =>
    decide (row.binding.binder.id.owner = context.inventory.source.owner) &&
    row.binding.payloadType.isWellFormed ambient)

def inventoriesValid (ambient : DataEnvironment) (contexts : List IndexedContext) : Bool :=
  decide ((contexts.map fun context => (context.inventory.owner, context.inventory.active)).Nodup) &&
  decide ((contexts.map (·.key)).Nodup) && contexts.all (contextValid ambient)

structure Prepared where
  ambient : DataEnvironment
  contexts : List IndexedContext
  ambientTyped : ambient.WellFormed
  valid : inventoriesValid ambient contexts = true
  deriving Repr

def Prepared.sentinel (prepared : Prepared) : DataTypeId := ⟨prepared.ambient.length⟩

def prepare (ambient : DataEnvironment) (inventories : List ContextInventory) (firstContextId : Nat := 0) :
    Except Error Prepared :=
  if valid : ambient.isWellFormed = true then do
    let _ ← wordKey firstContextId
    unless (inventories.map fun context => (context.owner, context.active)).Nodup do throw .duplicateContexts
    let contexts ← inventories.zipIdx.mapM fun (inventory, index) => do
      let key ← wordKey (firstContextId + index)
      let bindings ← inventory.bindings.zipIdx.mapM fun (binding, index) => do
        pure (⟨← wordKey index, binding⟩ : IndexedBinding)
      pure (⟨key, inventory, bindings⟩ : IndexedContext)
    if accepted : inventoriesValid ambient contexts = true then
      return ⟨ambient, contexts, DataEnvironment.isWellFormed_sound valid, accepted⟩
    else
      if !(decide (contexts.map (·.key)).Nodup) then throw .duplicateContextKeys
      else match contexts.find? (fun context => !(contextValid ambient context)) with
        | some context => throw (.invalidContext context.key)
        | none => throw .duplicateContexts
  else .error .invalidAmbientDefinitions

def Prepared.contextAt? (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution) : Option IndexedContext :=
  prepared.contexts.find? fun context => decide (context.inventory.owner = owner ∧ context.inventory.active = active)

def IndexedContext.bindingAt? (context : IndexedContext) (id : Resolved.LocalId) : Option IndexedBinding :=
  context.bindings.find? fun row => decide (row.binding.binder.id = id)

private def manifest : List Word → Expr
  | [] => .unit
  | key :: rest => .pair (.word key) (manifest rest)

private def manifest? : Expr → Option (List Word)
  | .unit => some []
  | .pair (.word key) rest => (manifest? rest).map (key :: ·)
  | _ => none

private def capturedIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (capturedIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

/-- The annotation is compile-time syntax only and disappears in the pass.
The capture expression sits outside its lambda, so ordinary renaming acts on
exactly the emitter's real lexical references. -/
def placeholder (prepared : Prepared) (context binder : Word) (scopeKeys : List Word)
    (captureType payloadType : Core.Ty) (captures : Expr) (payload : Option Expr) : Expr :=
  .construct ⟨prepared.sentinel, 0⟩
    (.pair (.word context) (.pair (.word binder)
      (.pair (.lambda captureType payloadType .unit)
        (.pair (manifest scopeKeys) (.pair captures (match payload with
          | none => .inLeft .unit .unit
          | some expression => .inRight .unit expression))))))

structure Receipt where
  context : IndexedContext
  binding : IndexedBinding
  scope : Scope
  scopeKeys : List Word
  captureType : Core.Ty
  payloadType : Core.Ty
  captures : Expr
  references : List Nat
  payload : Option Expr
  deriving Repr, DecidableEq

/-- Fully recognize one reserved placeholder; every other reserved shape is
rejected. No ordinary lambda/word/pair shape triggers allocation rewriting. -/
def decode (prepared : Prepared) (expression : Expr) : Except Error Receipt := do
  let .construct constructor
    (.pair (.word contextKey) (.pair (.word binderKey)
      (.pair (.lambda captureType payloadType .unit)
        (.pair keys (.pair captures payload))))) := expression | throw .malformedPlaceholder
  unless constructor = ⟨prepared.sentinel, 0⟩ do throw .malformedPlaceholder
  let context ← match prepared.contexts.find? (fun context => decide (context.key = contextKey)) with
    | some context => pure context | none => throw (.unknownContextKey contextKey)
  let binding ← match context.bindings.find? (fun binding => decide (binding.key = binderKey)) with
    | some binding => pure binding | none => throw (.unknownBinderKey contextKey binderKey)
  unless payloadType = binding.binding.payloadType do
    throw (.payloadMismatch binding.binding.binder.id binding.binding.payloadType payloadType)
  let scopeKeys ← match manifest? keys with | some keys => pure keys | none => throw .malformedPlaceholder
  unless scopeKeys.Nodup do throw .duplicateScope
  let scope ← scopeKeys.mapM fun key => do
    let row ← match context.bindings.find? (fun row => decide (row.key = key)) with
      | some row => pure row | none => throw (.unknownBinderKey contextKey key)
    pure (row.binding.binder.id, row.binding.payloadType)
  unless captureType = SourceCoreSourceCells.captureType scope do throw (.invalidType captureType)
  let references ← match capturedIndices? scope captures with
    | some references => pure references | none => throw .invalidCaptureShape
  unless references.Nodup do throw .duplicateReferences
  let payload ← match payload with
    | .inLeft .unit .unit => pure none
    | .inRight .unit expression => pure (some expression)
    | _ => throw .malformedPlaceholder
  pure ⟨context, binding, scope, scopeKeys, captureType, payloadType, captures, references, payload⟩

/-- The emitter's receipt additionally authenticates the exact requested
scope order, captures, payload and retained original binder metadata. -/
structure Emission (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) where
  expression : Expr
  receipt : Receipt
  decoded : decode prepared expression = .ok receipt
  ownerExact : receipt.context.inventory.owner = owner
  activeExact : receipt.context.inventory.active = active
  sourceExact : sourceView request.source = sourceView receipt.context.inventory.source
  binderExact : receipt.binding.binding.binder = request.binder
  scopeExact : receipt.scope = request.scope
  capturesExact : receipt.captures = SourceCoreSourceCells.captures request.references request.scope
  typeExact : receipt.payloadType = request.payloadType
  payloadExact : receipt.payload = request.payload

private abbrev emissionMatches (owner : Key) (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request)
    (receipt : Receipt) : Prop :=
  receipt.context.inventory.owner = owner ∧ receipt.context.inventory.active = active ∧
  sourceView request.source = sourceView receipt.context.inventory.source ∧
  receipt.binding.binding.binder = request.binder ∧ receipt.scope = request.scope ∧
  receipt.captures = SourceCoreSourceCells.captures request.references request.scope ∧
  receipt.payloadType = request.payloadType ∧ receipt.payload = request.payload

def emitWithReceipt (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Except Error (Emission prepared owner active request) := do
  let context ← match prepared.contextAt? owner active with
    | some context => pure context | none => throw (.missingContext owner active)
  unless sourceView request.source = sourceView context.inventory.source do throw (.sourceViewMismatch context.key)
  let binding ← match context.bindingAt? request.binder.id with
    | some binding => pure binding | none => throw (.missingBinder context.key request.binder.id)
  unless binding.binding.binder = request.binder do throw (.binderMismatch request.binder.id)
  unless binding.binding.payloadType = request.payloadType do
    throw (.payloadMismatch request.binder.id binding.binding.payloadType request.payloadType)
  unless (request.scope.map (·.1)).Nodup do throw .duplicateScope
  let keys ← request.scope.mapM fun (id, type) => do
    let row ← match context.bindingAt? id with
      | some row => pure row | none => throw (.missingBinder context.key id)
    unless type = row.binding.payloadType do throw (.payloadMismatch id row.binding.payloadType type)
    pure row.key
  let expression := placeholder prepared context.key binding.key keys
    (SourceCoreSourceCells.captureType request.scope) request.payloadType
    (SourceCoreSourceCells.captures request.references request.scope) request.payload
  match accepted : decode prepared expression with
  | .error error => throw error
  | .ok receipt =>
    if aligned : emissionMatches owner active request receipt then
      return {
        expression
        receipt
        decoded := accepted
        ownerExact := aligned.1
        activeExact := aligned.2.1
        sourceExact := aligned.2.2.1
        binderExact := aligned.2.2.2.1
        scopeExact := aligned.2.2.2.2.1
        capturesExact := aligned.2.2.2.2.2.1
        typeExact := aligned.2.2.2.2.2.2.1
        payloadExact := aligned.2.2.2.2.2.2.2 }
    else throw .emissionMismatch

def emit (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Except Error Expr :=
  (emitWithReceipt prepared owner active request).map (·.expression)

/-- The shared traversal retains its existing error type; the integration
chooses a faithful diagnostic conversion. No request is evaluated here. -/
def Prepared.allocatorAt (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (onError : Error → SourceCoreBasic.Error) : SourceCoreSourceCells.Allocator := fun request =>
  (emit prepared owner active request).mapError onError

theorem emit_receipt {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ receipt : Emission prepared owner active request, receipt.expression = expression := by
  cases emitted : emitWithReceipt prepared owner active request with
  | error error => simp [emit, emitted, Except.map] at accepted
  | ok receipt =>
    simp only [emit, emitted, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, accepted⟩

structure Entry (prepared : Prepared) where
  original : Expr
  receipt : Receipt
  decoded : decode prepared original = .ok receipt
  layout : SourceCoreHeapMarkers.Layout
  captureTypeExact : layout.captureType = receipt.captureType
  deriving Repr

private def validateType (prepared : Prepared) (type : Core.Ty) : Except Error Unit :=
  if type.isWellFormed prepared.ambient then .ok () else .error (.invalidType type)

private def validateIdentity (prepared : Prepared) (id : DataTypeId) : Except Error Unit :=
  if id.index < prepared.ambient.length then .ok () else .error (.reservedIdentity id)

abbrev State (prepared : Prepared) := List (Entry prepared)

mutual
  /-- Every input type/nominal identity outside a complete marker must belong
  to the original ambient prefix. Initializers are rewritten before installing
  their marker, matching the allocation helper's source-visible effect order. -/
  def rewrite (prepared : Prepared) : Nat → Expr → State prepared → Except Error (Expr × State prepared)
    | 0, _, _ => .error .traversalExhausted
    | fuel + 1, expression, entries => do
      match expression with
      | .construct constructor payload =>
        if constructor.owner = prepared.sentinel then
          match accepted : decode prepared expression with
          | .error error => throw error
          | .ok receipt =>
            let (payload, entries) ← match receipt.payload with
              | none => pure (none, entries)
              | some initializer => do
                  let (initializer, entries) ← rewrite prepared fuel initializer entries
                  pure (some initializer, entries)
            let layout : SourceCoreHeapMarkers.Layout := ⟨⟨prepared.ambient.length + entries.length⟩, receipt.captureType⟩
            let entry : Entry prepared := ⟨expression, receipt, accepted, layout, rfl⟩
            let result := match payload with
              | none => SourceCoreHeapMarkers.allocate layout receipt.payloadType receipt.captures
              | some initializer => SourceCoreHeapMarkers.allocateInitialized layout receipt.payloadType receipt.captures initializer
            pure (result, entries ++ [entry])
        else
          validateIdentity prepared constructor.owner
          let (payload, entries) ← rewrite prepared fuel payload entries
          pure (.construct constructor payload, entries)
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure (expression, entries)
      | .pair left right =>
        let (left, entries) ← rewrite prepared fuel left entries
        let (right, entries) ← rewrite prepared fuel right entries
        pure (.pair left right, entries)
      | .first operand =>
        let (operand, entries) ← rewrite prepared fuel operand entries
        pure (.first operand, entries)
      | .second operand =>
        let (operand, entries) ← rewrite prepared fuel operand entries
        pure (.second operand, entries)
      | .lambda parameter result body =>
        validateType prepared parameter
        validateType prepared result
        let (body, entries) ← rewrite prepared fuel body entries
        pure (.lambda parameter result body, entries)
      | .apply function argument =>
        let (function, entries) ← rewrite prepared fuel function entries
        let (argument, entries) ← rewrite prepared fuel argument entries
        pure (.apply function argument, entries)
      | .inLeft type payload =>
        validateType prepared type
        let (payload, entries) ← rewrite prepared fuel payload entries
        pure (.inLeft type payload, entries)
      | .inRight type payload =>
        validateType prepared type
        let (payload, entries) ← rewrite prepared fuel payload entries
        pure (.inRight type payload, entries)
      | .caseE condition left right =>
        let (condition, entries) ← rewrite prepared fuel condition entries
        let (left, entries) ← rewrite prepared fuel left entries
        let (right, entries) ← rewrite prepared fuel right entries
        pure (.caseE condition left right, entries)
      | .newCell type initializer =>
        validateType prepared type
        let (initializer, entries) ← rewrite prepared fuel initializer entries
        pure (.newCell type initializer, entries)
      | .loadCell reference =>
        let (reference, entries) ← rewrite prepared fuel reference entries
        pure (.loadCell reference, entries)
      | .storeCell reference value =>
        let (reference, entries) ← rewrite prepared fuel reference entries
        let (value, entries) ← rewrite prepared fuel value entries
        pure (.storeCell reference value, entries)
      | .matchData id type scrutinee branches =>
        validateIdentity prepared id
        validateType prepared type
        let (scrutinee, entries) ← rewrite prepared fuel scrutinee entries
        let (branches, entries) ← rewriteBranches prepared fuel branches entries
        pure (.matchData id type scrutinee branches, entries)
      | .unary operator operand =>
        let (operand, entries) ← rewrite prepared fuel operand entries
        pure (.unary operator operand, entries)
      | .binary operator left right =>
        let (left, entries) ← rewrite prepared fuel left entries
        let (right, entries) ← rewrite prepared fuel right entries
        pure (.binary operator left right, entries)
      | .ternary operator first second third =>
        let (first, entries) ← rewrite prepared fuel first entries
        let (second, entries) ← rewrite prepared fuel second entries
        let (third, entries) ← rewrite prepared fuel third entries
        pure (.ternary operator first second third, entries)
      | .letE value body =>
        let (value, entries) ← rewrite prepared fuel value entries
        let (body, entries) ← rewrite prepared fuel body entries
        pure (.letE value body, entries)
      | .ifE condition yes no =>
        let (condition, entries) ← rewrite prepared fuel condition entries
        let (yes, entries) ← rewrite prepared fuel yes entries
        let (no, entries) ← rewrite prepared fuel no entries
        pure (.ifE condition yes no, entries)

  def rewriteBranches (prepared : Prepared) : Nat → List Expr → State prepared → Except Error (List Expr × State prepared)
    | _, [], entries => pure ([], entries)
    | 0, _ :: _, _ => .error .traversalExhausted
    | fuel + 1, expression :: rest, entries => do
      let (expression, entries) ← rewrite prepared fuel expression entries
      let (rest, entries) ← rewriteBranches prepared fuel rest entries
      pure (expression :: rest, entries)
end

abbrev allocationIndices (prepared : Prepared) (entries : State prepared) : Prop :=
  entries.map (fun entry => entry.layout.dataType.index) =
    (List.range entries.length).map (prepared.ambient.length + ·)

structure Finalized (prepared : Prepared) (context : Core.Context) (expected : Core.Ty) where
  entries : State prepared
  expression : Expr
  indexed : allocationIndices prepared entries
  definitionsTyped : (prepared.ambient ++ entries.map (·.layout.definition)).WellFormed
  typed : HasType context expression expected (prepared.ambient ++ entries.map (·.layout.definition))
  deriving Repr

def Finalized.definitions {prepared : Prepared} {context : Core.Context} {expected : Core.Ty}
    (result : Finalized prepared context expected) : DataEnvironment :=
  prepared.ambient ++ result.entries.map (·.layout.definition)

def finalize (prepared : Prepared) (fuel : Nat) (context : Core.Context) (expected : Core.Ty) (expression : Expr) :
    Except Error (Finalized prepared context expected) := do
  validateType prepared expected
  for type in context do validateType prepared type
  let (expression, entries) ← rewrite prepared fuel expression []
  let definitions := prepared.ambient ++ entries.map (·.layout.definition)
  if definitionsValid : definitions.isWellFormed = true then
    if indexed : allocationIndices prepared entries then
      if typed : infer? context expression definitions = some expected then
        pure ⟨entries, expression, indexed, DataEnvironment.isWellFormed_sound definitionsValid, infer_sound typed⟩
      else throw (.finalBodyType expected (infer? context expression definitions))
    else throw .invalidAllocationIndices
  else throw .invalidFinalDefinitions

@[simp] theorem sentinel_fresh (prepared : Prepared) : prepared.ambient[prepared.sentinel.index]? = none := by
  simp [Prepared.sentinel]

/-- The reserved constructor cannot be confused with any ordinary term typed
against the original ambient catalog. -/
theorem placeholder_not_ambient_typed (prepared : Prepared) (context : Core.Context) (type : Core.Ty)
    (contextKey binderKey : Word) (scopeKeys : List Word) (captureType payloadType : Core.Ty)
    (captures : Expr) (payload : Option Expr) :
    ¬ HasType context (placeholder prepared contextKey binderKey scopeKeys captureType payloadType captures payload) type prepared.ambient := by
  intro typed
  cases typed with
  | construct found _ =>
    simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?, Prepared.sentinel] at found

@[simp] theorem Finalized.ambient_prefix {prepared : Prepared} {context : Core.Context} {expected : Core.Ty}
    (result : Finalized prepared context expected) : result.definitions.take prepared.ambient.length = prepared.ambient := by
  simp [Finalized.definitions]

/-- Artifact IDs index the appended definitions exactly, rather than a
separate numbering table that might drift from the final Core catalog. -/
theorem Finalized.entry_index {prepared : Prepared} {context : Core.Context} {expected : Core.Ty}
    (result : Finalized prepared context expected) {index : Nat} {entry : Entry prepared}
    (found : result.entries[index]? = some entry) :
    entry.layout.dataType.index = prepared.ambient.length + index := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have atIndex := congrArg (fun indices : List Nat => indices[index]?) result.indexed
  simpa only [List.getElem?_map, found, List.getElem?_range bound, Option.map_some, Option.some.injEq] using atIndex

theorem Finalized.entry_definition {prepared : Prepared} {context : Core.Context} {expected : Core.Ty}
    (result : Finalized prepared context expected) {index : Nat} {entry : Entry prepared}
    (found : result.entries[index]? = some entry) :
    result.definitions[entry.layout.dataType.index]? = some entry.layout.definition := by
  rw [result.entry_index found]
  simp only [Finalized.definitions, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, found, Option.map_some]

/-- Collected layouts satisfy the existing allocation helper's typing
interface in the final catalog. -/
theorem Finalized.entry_registered {prepared : Prepared} {context : Core.Context} {expected : Core.Ty}
    (result : Finalized prepared context expected) {index : Nat} {entry : Entry prepared}
    (found : result.entries[index]? = some entry) :
    entry.layout.Registered result.definitions := by
  refine ⟨?_, result.entry_definition found⟩
  apply result.definitionsTyped.constructorPayloadType_wellFormed
    (constructor := entry.layout.constructor)
  change result.definitions.lookupConstructorPayloadType? entry.layout.constructor =
    some entry.layout.captureType
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    SourceCoreHeapMarkers.Layout.constructor]
  rw [result.entry_definition found]
  rfl

end Solcore.Frontend.SourceCoreAllocationCodebook
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAllocationDiscovery
/-! Pure discovery of allocation inventories through the existing allocator
callback. Canonical contexts authenticate source forms and original binder
metadata before any Core type is discovered. Only actual requests contribute
payload types; captured outer bundles keep the types supplied by the real
lexical scope. Unreached source types are never projected here.

Reserved annotations carry keys, finite scope types and actual capture
references. The AST pass validates every reserved occurrence and rejects
inconsistent types before constructing the existing checked allocation
codebook. Structural decoding of an arbitrary AST is not emission history:
the integrating compiler must retain its actual compilation receipt. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationDiscovery
open SourceInference Core
abbrev Error := SourceCoreAllocationCodebook.Error
abbrev Key := SourceCoreAllocationCodebook.Key
abbrev Scope := SourceCoreAllocationCodebook.Scope

structure Context where
  owner : Key
  active : TypeSystem.Substitution
  source : TypedSource
  binders : List TypedBinder
  deriving Repr, DecidableEq

/-- Unit is only a placeholder in the metadata index. Discovered payload
representations are kept separately and are never inferred from this unit. -/
private def Context.metadata (context : Context) : SourceCoreAllocationCodebook.ContextInventory :=
  ⟨context.owner, context.active, context.source, context.binders.map (fun binder => ⟨binder, .unit⟩)⟩

structure Prepared where
  metadata : SourceCoreAllocationCodebook.Prepared
  deriving Repr

def Prepared.ambient (prepared : Prepared) : DataEnvironment := prepared.metadata.ambient
def Prepared.sentinel (prepared : Prepared) : DataTypeId := prepared.metadata.sentinel

def prepare (ambient : DataEnvironment) (contexts : List Context) (firstContextId : Nat := 0) :
    Except Error Prepared :=
  (SourceCoreAllocationCodebook.prepare ambient (contexts.map Context.metadata) firstContextId).map Prepared.mk

private def manifest : List (Word × Core.Ty) → Expr
  | [] => .unit
  | (key, type) :: rest => .pair (.pair (.word key) (.lambda type .unit .unit)) (manifest rest)

private def manifest? : Expr → Option (List (Word × Core.Ty))
  | .unit => some []
  | .pair (.pair (.word key) (.lambda type .unit .unit)) rest =>
      (manifest? rest).map ((key, type) :: ·)
  | _ => none

private def capturedIndices? : Scope → Expr → Option (List Nat)
  | [], .unit => some []
  | [_], .var index => some [index]
  | _ :: next :: rest, .pair (.var index) tail => (capturedIndices? (next :: rest) tail).map (index :: ·)
  | _, _ => none

/-- Types appear in compile-time lambda annotations only. Actual captures
remain outside those lambdas, so surrounding Core renaming acts correctly. -/
def placeholder (prepared : Prepared) (context binder : Word) (scope : List (Word × Core.Ty))
    (captureType payloadType : Core.Ty) (captures : Expr) (payload : Option Expr) : Expr :=
  .construct ⟨prepared.sentinel, 0⟩
    (.pair (.word context) (.pair (.word binder)
      (.pair (.lambda captureType payloadType .unit)
        (.pair (manifest scope) (.pair captures (match payload with
          | none => .inLeft .unit .unit
          | some expression => .inRight .unit expression))))))

structure Receipt where
  context : SourceCoreAllocationCodebook.IndexedContext
  binding : SourceCoreAllocationCodebook.IndexedBinding
  scope : Scope
  scopeKeys : List Word
  captureType : Core.Ty
  payloadType : Core.Ty
  captures : Expr
  references : List Nat
  payload : Option Expr
  deriving Repr, DecidableEq

private def validateType (prepared : Prepared) (type : Core.Ty) : Except Error Unit :=
  if type.isWellFormed prepared.ambient then .ok () else .error (.invalidType type)

private def validateIdentity (prepared : Prepared) (id : DataTypeId) : Except Error Unit :=
  if id.index < prepared.ambient.length then .ok () else .error (.reservedIdentity id)

def decode (prepared : Prepared) (expression : Expr) : Except Error Receipt := do
  let .construct constructor
    (.pair (.word contextKey) (.pair (.word binderKey)
      (.pair (.lambda captureType payloadType .unit)
        (.pair keys (.pair captures payload))))) := expression | throw .malformedPlaceholder
  unless constructor = ⟨prepared.sentinel, 0⟩ do throw .malformedPlaceholder
  let context ← match prepared.metadata.contexts.find? (fun context => decide (context.key = contextKey)) with
    | some context => pure context | none => throw (.unknownContextKey contextKey)
  let binding ← match context.bindings.find? (fun binding => decide (binding.key = binderKey)) with
    | some binding => pure binding | none => throw (.unknownBinderKey contextKey binderKey)
  validateType prepared payloadType
  let fields ← match manifest? keys with | some fields => pure fields | none => throw .malformedPlaceholder
  let scopeKeys := fields.map Prod.fst
  unless scopeKeys.Nodup do throw .duplicateScope
  let scope ← fields.mapM fun (key, type) => do
    let row ← match context.bindings.find? (fun row => decide (row.key = key)) with
      | some row => pure row | none => throw (.unknownBinderKey contextKey key)
    validateType prepared type
    pure (row.binding.binder.id, type)
  unless captureType = SourceCoreSourceCells.captureType scope do throw (.invalidType captureType)
  let references ← match capturedIndices? scope captures with
    | some references => pure references | none => throw .invalidCaptureShape
  unless references.Nodup do throw .duplicateReferences
  let payload ← match payload with
    | .inLeft .unit .unit => pure none
    | .inRight .unit expression => pure (some expression)
    | _ => throw .malformedPlaceholder
  pure ⟨context, binding, scope, scopeKeys, captureType, payloadType, captures, references, payload⟩

structure Emission (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) where
  expression : Expr
  receipt : Receipt
  decoded : decode prepared expression = .ok receipt
  ownerExact : receipt.context.inventory.owner = owner
  activeExact : receipt.context.inventory.active = active
  sourceExact : SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView receipt.context.inventory.source
  binderExact : receipt.binding.binding.binder = request.binder
  scopeExact : receipt.scope = request.scope
  capturesExact : receipt.captures = SourceCoreSourceCells.captures request.references request.scope
  typeExact : receipt.payloadType = request.payloadType
  payloadExact : receipt.payload = request.payload

private abbrev emissionMatches (owner : Key) (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request)
    (receipt : Receipt) : Prop :=
  receipt.context.inventory.owner = owner ∧ receipt.context.inventory.active = active ∧
  SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView receipt.context.inventory.source ∧
  receipt.binding.binding.binder = request.binder ∧ receipt.scope = request.scope ∧
  receipt.captures = SourceCoreSourceCells.captures request.references request.scope ∧
  receipt.payloadType = request.payloadType ∧ receipt.payload = request.payload

def emitWithReceipt (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Except Error (Emission prepared owner active request) := do
  let context ← match prepared.metadata.contextAt? owner active with
    | some context => pure context | none => throw (.missingContext owner active)
  unless SourceCoreAllocationCodebook.sourceView request.source = SourceCoreAllocationCodebook.sourceView context.inventory.source do throw (.sourceViewMismatch context.key)
  let binding ← match context.bindingAt? request.binder.id with
    | some binding => pure binding | none => throw (.missingBinder context.key request.binder.id)
  unless binding.binding.binder = request.binder do throw (.binderMismatch request.binder.id)
  unless (request.scope.map (·.1)).Nodup do throw .duplicateScope
  let fields ← request.scope.mapM fun (id, type) => do
    let row ← match context.bindingAt? id with
      | some row => pure row | none => throw (.missingBinder context.key id)
    pure (row.key, type)
  let expression := placeholder prepared context.key binding.key fields
    (SourceCoreSourceCells.captureType request.scope) request.payloadType
    (SourceCoreSourceCells.captures request.references request.scope) request.payload
  match accepted : decode prepared expression with
  | .error error => throw error
  | .ok receipt =>
    if aligned : emissionMatches owner active request receipt then
      return {
        expression, receipt, decoded := accepted
        ownerExact := aligned.1
        activeExact := aligned.2.1
        sourceExact := aligned.2.2.1
        binderExact := aligned.2.2.2.1
        scopeExact := aligned.2.2.2.2.1
        capturesExact := aligned.2.2.2.2.2.1
        typeExact := aligned.2.2.2.2.2.2.1
        payloadExact := aligned.2.2.2.2.2.2.2 }
    else throw .emissionMismatch

def emit (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Except Error Expr :=
  (emitWithReceipt prepared owner active request).map (·.expression)

def Prepared.allocatorAt (prepared : Prepared) (owner : Key) (active : TypeSystem.Substitution)
    (onError : Error → SourceCoreBasic.Error) : SourceCoreSourceCells.Allocator := fun request =>
  (emit prepared owner active request).mapError onError

theorem emit_receipt {prepared : Prepared} {owner : Key} {active : TypeSystem.Substitution}
    {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : emit prepared owner active request = .ok expression) :
    ∃ receipt : Emission prepared owner active request, receipt.expression = expression := by
  cases emitted : emitWithReceipt prepared owner active request with
  | error error => simp [emit, emitted, Except.map] at accepted
  | ok receipt =>
    simp only [emit, emitted, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, accepted⟩

structure Site (prepared : Prepared) where
  original : Expr
  receipt : Receipt
  decoded : decode prepared original = .ok receipt
  deriving Repr

mutual
  /-- Inspect all source allocation placeholders and every other nominal/type
  annotation. Initializer subexpressions are inspected as ordinary Core AST. -/
  def collect (prepared : Prepared) : Nat → Expr → List (Site prepared) → Except Error (List (Site prepared))
    | 0, _, _ => .error .traversalExhausted
    | fuel + 1, expression, sites => do
      match expression with
      | .construct constructor payload =>
        if constructor.owner = prepared.sentinel then
          match accepted : decode prepared expression with
          | .error error => throw error
          | .ok receipt =>
            let sites ← match receipt.payload with
              | none => pure sites
              | some initializer => collect prepared fuel initializer sites
            pure (sites ++ [⟨expression, receipt, accepted⟩])
        else
          validateIdentity prepared constructor.owner
          collect prepared fuel payload sites
      | .unit | .bool _ | .word _ | .integer _ | .var _ => pure sites
      | .pair left right | .apply left right | .storeCell left right
      | .binary _ left right | .letE left right =>
        collect prepared fuel right (← collect prepared fuel left sites)
      | .first operand | .second operand | .loadCell operand | .unary _ operand =>
        collect prepared fuel operand sites
      | .lambda parameter result body =>
        validateType prepared parameter
        validateType prepared result
        collect prepared fuel body sites
      | .inLeft type payload | .inRight type payload | .newCell type payload =>
        validateType prepared type
        collect prepared fuel payload sites
      | .caseE condition left right | .ifE condition left right | .ternary _ condition left right =>
        let sites ← collect prepared fuel condition sites
        let sites ← collect prepared fuel left sites
        collect prepared fuel right sites
      | .matchData id type scrutinee branches =>
        validateIdentity prepared id
        validateType prepared type
        collectBranches prepared fuel branches (← collect prepared fuel scrutinee sites)

  def collectBranches (prepared : Prepared) : Nat → List Expr → List (Site prepared) → Except Error (List (Site prepared))
    | _, [], sites => pure sites
    | 0, _ :: _, _ => .error .traversalExhausted
    | fuel + 1, expression :: rest, sites => do
      collectBranches prepared fuel rest (← collect prepared fuel expression sites)
end

structure Reached where
  context : Word
  binder : Word
  type : Core.Ty
  deriving Repr, DecidableEq

private def record (context : SourceCoreAllocationCodebook.IndexedContext) (key : Word) (type : Core.Ty)
    (rows : List Reached) : Except Error (List Reached) := do
  let binding ← match context.bindings.find? (fun row => decide (row.key = key)) with
    | some row => pure row | none => throw (.unknownBinderKey context.key key)
  match rows.find? (fun row => decide (row.context = context.key ∧ row.binder = key)) with
  | none => pure (rows ++ [⟨context.key, key, type⟩])
  | some old =>
      if old.type = type then pure rows
      else throw (.payloadMismatch binding.binding.binder.id old.type type)

private def gather (prepared : Prepared) (sites : List (Site prepared)) : Except Error (List Reached) :=
  sites.foldlM (fun rows site => do
    let receipt := site.receipt
    let rows ← record receipt.context receipt.binding.key receipt.payloadType rows
    (receipt.scopeKeys.zip receipt.scope).foldlM
      (fun rows (key, (_, type)) => record receipt.context key type rows) rows) []

private def materialize (prepared : Prepared) (rows : List Reached) : List SourceCoreAllocationCodebook.ContextInventory :=
  prepared.metadata.contexts.map fun context => {
    owner := context.inventory.owner
    active := context.inventory.active
    source := context.inventory.source
    bindings := context.bindings.filterMap fun binding =>
      (rows.find? (fun row => decide (row.context = context.key ∧ row.binder = binding.key))).map
        (fun row => ⟨binding.binding.binder, row.type⟩) }

def inventory (prepared : Prepared) (sites : List (Site prepared)) : Except Error (List SourceCoreAllocationCodebook.ContextInventory) :=
  (gather prepared sites).map (materialize prepared)

/-- The discovery pass preserves every canonical owner, complete context and
source table, including contexts that have no reached allocation. -/
theorem inventory_contexts {prepared : Prepared} {sites : List (Site prepared)}
    {inventories : List SourceCoreAllocationCodebook.ContextInventory}
    (accepted : inventory prepared sites = .ok inventories) :
    inventories.map (fun context => (context.owner, context.active, context.source)) =
      prepared.metadata.contexts.map (fun context =>
        (context.inventory.owner, context.inventory.active, context.inventory.source)) := by
  cases gathered : gather prepared sites with
  | error error => simp [inventory, gathered, Except.map] at accepted
  | ok rows =>
    simp only [inventory, gathered, Except.map, Except.ok.injEq] at accepted
    subst inventories
    simp only [materialize, List.map_map, Function.comp_def]

/-- Discovery records the actual scan and inventory computation, and already
prepares the existing second-pass checked allocator. It does not certify an
arbitrary AST as output of the integrating source compiler. -/
structure Discovered (prepared : Prepared) (fuel : Nat) (expression : Expr) where
  sites : List (Site prepared)
  scanned : collect prepared fuel expression [] = .ok sites
  inventories : List SourceCoreAllocationCodebook.ContextInventory
  extracted : inventory prepared sites = .ok inventories
  codebook : SourceCoreAllocationCodebook.Prepared
  checked : SourceCoreAllocationCodebook.prepare prepared.ambient inventories = .ok codebook
  deriving Repr

def discover (prepared : Prepared) (fuel : Nat) (expression : Expr) : Except Error (Discovered prepared fuel expression) :=
  match scanned : collect prepared fuel expression [] with
  | .error error => .error error
  | .ok sites =>
    match extracted : inventory prepared sites with
    | .error error => .error error
    | .ok inventories =>
      match checked : SourceCoreAllocationCodebook.prepare prepared.ambient inventories with
      | .error error => .error error
      | .ok codebook => .ok ⟨sites, scanned, inventories, extracted, codebook, checked⟩

@[simp] theorem sentinel_fresh (prepared : Prepared) : prepared.ambient[prepared.sentinel.index]? = none :=
  SourceCoreAllocationCodebook.sentinel_fresh prepared.metadata

theorem placeholder_not_ambient_typed (prepared : Prepared) (context : Core.Context) (type : Core.Ty)
    (contextKey binderKey : Word) (scope : List (Word × Core.Ty)) (captureType payloadType : Core.Ty)
    (captures : Expr) (payload : Option Expr) :
    ¬ HasType context (placeholder prepared contextKey binderKey scope captureType payloadType captures payload) type prepared.ambient := by
  intro typed
  cases typed with
  | construct found _ =>
    simp [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
      Prepared.sentinel, Prepared.ambient, SourceCoreAllocationCodebook.Prepared.sentinel] at found

end Solcore.Frontend.SourceCoreAllocationDiscovery
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAllocationContexts
/-! Canonical allocation metadata from the actual executable plan and sealed
contextual evidence receipts. All declared binders, including principal generic
lambda metadata, are retained. No source type is projected into Core here.

Match scrutinee cells use exactly the metadata constructed by the compatible
match lowerer. Each retained binder has a declaration or hidden-scrutinee
receipt. Equal owner/full-context keys may share a row only when source views
and complete ordered binder metadata agree. Payload representations are later
obtained from actual allocator requests by AllocationDiscovery. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationContexts
open SourceInference
abbrev Key := SourceSpecialization.SpecializationKey
abbrev Plan := SourceSpecializationWorklist.Plan
abbrev Context := SourceCoreAllocationDiscovery.Context

inductive Error where
  | contexts (error : SourceCoreStageCodebook.Error)
  | metadata (error : SourceCoreBasic.Error)
  | conflictingContext (owner : Key) (active : TypeSystem.Substitution)
  deriving Repr

def hiddenBinder (statement : StatementNode) (resolution : MatchResolution)
    (scrutinee : ExpressionNode) : TypedBinder := {
  id := resolution.hiddenScrutinee
  name := ""
  scheme := ⟨[], SourceCoreRawMetadata.runtimeType scrutinee.type⟩
  span := some statement.span
}

inductive BinderOrigin (source : TypedSource) : TypedBinder → Prop where
  | declared {binder : TypedBinder} (member : binder ∈ SourceCoreDataPlaces.declaredBinders source) :
      BinderOrigin source binder
  | hidden {statement : StatementNode} {resolution : MatchResolution} {scrutinee : ExpressionNode}
      (member : .statement statement ∈ source.nodes)
      (form : statement.form = .matchWith resolution)
      (found : source.lookupExpression? resolution.scrutinee = some scrutinee) :
      BinderOrigin source (hiddenBinder statement resolution scrutinee)

structure BinderReceipt (source : TypedSource) where
  binder : TypedBinder
  origin : BinderOrigin source binder

private def hiddenReceipts (source : TypedSource) : Except Error (List (BinderReceipt source)) := do
  let nested ← source.nodes.attach.mapM fun item => do
    match nodeEq : item.val with
    | .expression _ => pure []
    | .statement statement =>
      match form : statement.form with
      | .matchWith resolution =>
        if resolution.scrutinee.occurrence.owner ≠ source.owner then
          throw (.metadata (.ownerMismatch source.owner resolution.scrutinee.occurrence.owner))
        match found : source.lookupExpression? resolution.scrutinee with
        | none => throw (.metadata (.missingExpression resolution.scrutinee))
        | some scrutinee =>
          pure [⟨hiddenBinder statement resolution scrutinee,
            .hidden (by simpa [nodeEq] using item.property) form found⟩]
      | _ => pure []
  pure nested.flatten

def binders (source : TypedSource) : Except Error (List (BinderReceipt source)) := do
  let declared := (SourceCoreDataPlaces.declaredBinders source).attach.map fun item =>
    (⟨item.val, .declared item.property⟩ : BinderReceipt source)
  pure (declared ++ (← hiddenReceipts source))

/-- Provenance is membership in the actual supplied plan/receipt lists, not
an arbitrary Core type or an inferred source function identity. -/
inductive Origin (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  | root (specialized : SourceSpecialization.SpecializedFunction) (member : specialized ∈ plan.specializations)
  | contextual (prepared : SourceCoreLocalEvidence.Prepared) (member : prepared ∈ parents)

def Origin.owner {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} : Origin plan parents → Key
  | .root specialized _ => specialized.key
  | .contextual prepared _ => prepared.caller.key

def Origin.active {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} :
    Origin plan parents → TypeSystem.Substitution
  | .root _ _ => []
  | .contextual prepared _ => prepared.substitution

def Origin.source {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} : Origin plan parents → TypedSource
  | .root specialized _ => specialized.function.typedBody
  | .contextual prepared _ => prepared.source

structure Certified (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  origin : Origin plan parents
  context : Context
  ownerExact : context.owner = origin.owner
  activeExact : context.active = origin.active
  sourceExact : context.source = origin.source
  receipts : List (BinderReceipt context.source)
  collected : binders context.source = .ok receipts
  bindersExact : context.binders = receipts.map (·.binder)
  sourceOwner : context.source.owner = context.owner.declaration
  distinct : (context.binders.map (·.id)).Nodup
  binderOwners : ∀ binder ∈ context.binders, binder.id.owner = context.source.owner

def certify {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared} (origin : Origin plan parents) :
    Except Error (Certified plan parents) := do
  let owner := origin.owner
  let source := origin.source
  if sourceOwner : source.owner = owner.declaration then
    match collected : binders source with
    | .error error => throw error
    | .ok receipts =>
      let declared := receipts.map (·.binder)
      if distinct : (declared.map (·.id)).Nodup then
        if owned : declared.all (fun binder => decide (binder.id.owner = source.owner)) = true then
          pure {
            origin
            context := ⟨owner, origin.active, source, declared⟩
            ownerExact := rfl, activeExact := rfl, sourceExact := rfl
            receipts, collected, bindersExact := rfl, sourceOwner, distinct
            binderOwners := fun binder member => of_decide_eq_true (List.all_eq_true.mp owned binder member)
          }
        else
          match declared.find? (fun binder => decide (binder.id.owner ≠ source.owner)) with
          | some binder => throw (.metadata (.ownerMismatch source.owner binder.id.owner))
          | none => throw (.metadata (.ownerMismatch source.owner owner.declaration))
      else
        match declared.find? (fun binder => (declared.filter (fun other => decide (binder.id = other.id))).length > 1) with
        | some binder => throw (.metadata (.duplicateBinding binder.id))
        | none => throw (.metadata (.ownerMismatch source.owner owner.declaration))
  else throw (.metadata (.ownerMismatch owner.declaration source.owner))

/-- Reuse permits the raw/evidence expression views already accepted by the
emitter, while retaining exact forms, statements and ordered binder metadata. -/
def sameContext (left right : Context) : Prop :=
  left.owner = right.owner ∧ left.active = right.active ∧
  SourceCoreAllocationCodebook.sourceView left.source = SourceCoreAllocationCodebook.sourceView right.source ∧
  left.binders = right.binders

instance (left right : Context) : Decidable (sameContext left right) := inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

def insert {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (rows : List (Certified plan parents)) (candidate : Certified plan parents) : Except Error (List (Certified plan parents)) :=
  match rows.find? (fun row => decide (row.context.owner = candidate.context.owner ∧ row.context.active = candidate.context.active)) with
  | none => .ok (rows ++ [candidate])
  | some row =>
      if sameContext row.context candidate.context then .ok rows
      else .error (.conflictingContext candidate.context.owner candidate.context.active)

theorem insert_reuses {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    {rows : List (Certified plan parents)} {candidate existing : Certified plan parents}
    (found : rows.find? (fun row => decide
      (row.context.owner = candidate.context.owner ∧ row.context.active = candidate.context.active)) = some existing)
    (same : sameContext existing.context candidate.context) :
    insert rows candidate = .ok rows := by
  simp only [insert, found, if_pos same]

structure Inventory (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) where
  rows : List (Certified plan parents)
  unique : (rows.map (fun row => (row.context.owner, row.context.active))).Nodup

def Inventory.contexts {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (inventory : Inventory plan parents) : List Context := inventory.rows.map (·.context)

def fromPrepared (plan : Plan) (parents : List SourceCoreLocalEvidence.Prepared) : Except Error (Inventory plan parents) := do
  let origins : List (Origin plan parents) :=
    (plan.specializations.attach.map (fun row => .root row.val row.property)) ++
    (parents.attach.map (fun row => .contextual row.val row.property))
  let candidates ← origins.mapM certify
  let rows ← candidates.foldlM insert []
  if unique : (rows.map (fun row => (row.context.owner, row.context.active))).Nodup then
    pure ⟨rows, unique⟩
  else
    match rows with
    | row :: _ => throw (.conflictingContext row.context.owner row.context.active)
    | [] => throw (.contexts .duplicateId)

structure Prepared (program : CheckedProgram) (plan : Plan) (candidates : List SourceCoreLocalPolymorphism.Instance) where
  parents : List SourceCoreLocalEvidence.Prepared
  authenticated : SourceCoreStageCodebook.prepareContexts program plan candidates = .ok parents
  inventory : Inventory plan parents

def prepare (program : CheckedProgram) (plan : Plan) (candidates : List SourceCoreLocalPolymorphism.Instance) :
    Except Error (Prepared program plan candidates) :=
  match authenticated : SourceCoreStageCodebook.prepareContexts program plan candidates with
  | .error error => .error (.contexts error)
  | .ok parents => (fromPrepared plan parents).map (fun inventory => ⟨parents, authenticated, inventory⟩)

theorem binders_declared {source : TypedSource} {receipts : List (BinderReceipt source)}
    (accepted : binders source = .ok receipts) {binder : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders source) :
    binder ∈ receipts.map (·.binder) := by
  cases hidden : hiddenReceipts source with
  | error error => simp [binders, hidden, Functor.map, Except.map] at accepted
  | ok extra =>
    simp [binders, hidden, Functor.map, Except.map] at accepted
    subst receipts
    simp only [List.map_append, List.mem_append]
    left
    simpa using member

/-- The inventory keeps every original declaration, even when its type is
open or the compiler later emits no allocation for that binder. -/
theorem Certified.declared_mem {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder}
    (member : binder ∈ SourceCoreDataPlaces.declaredBinders row.context.source) :
    binder ∈ row.context.binders := by
  rw [row.bindersExact]
  exact binders_declared row.collected member

theorem Certified.binder_origin {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) {binder : TypedBinder} (member : binder ∈ row.context.binders) :
    BinderOrigin row.context.source binder := by
  rw [row.bindersExact] at member
  obtain ⟨receipt, _, equal⟩ := List.mem_map.mp member
  subst binder
  exact receipt.origin

theorem Certified.source_owned {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (row : Certified plan parents) : row.context.source.owner = row.origin.owner.declaration := by
  rw [← row.ownerExact]
  exact row.sourceOwner

theorem Inventory.contexts_unique {plan : Plan} {parents : List SourceCoreLocalEvidence.Prepared}
    (inventory : Inventory plan parents) :
    (inventory.contexts.map (fun context => (context.owner, context.active))).Nodup := by
  simpa only [Inventory.contexts, List.map_map, Function.comp_def] using inventory.unique

end Solcore.Frontend.SourceCoreAllocationContexts
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAllocationLayouts
/-! Fixed allocation layouts for all entries of one compiled artifact. The
first discovery AST determines a finite set of metadata keys. A later allocator
reauthenticates each real request against that discovery's checked codebook,
then emits an existing nominal marker layout directly. Capture positions and
initializer expressions remain request-specific and are not part of the key.

Sharing a layout shares only its static definition: each evaluation still
allocates its own marker followed by its own optional payload cell. Historical
source compilation provenance belongs to the integrating factory; this module
retains the actual discovery scan receipt and accepts no undefined site key. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationLayouts
open SourceInference Core

structure Key where
  owner : SourceSpecialization.SpecializationKey
  active : TypeSystem.Substitution
  binder : TypedBinder
  scope : SourceCoreLocalCell.Scope
  payloadType : Core.Ty
  initialized : Bool
  deriving Repr, DecidableEq

def Key.ofReceipt (receipt : SourceCoreAllocationDiscovery.Receipt) : Key :=
  ⟨receipt.context.inventory.owner, receipt.context.inventory.active, receipt.binding.binding.binder,
    receipt.scope, receipt.payloadType, receipt.payload.isSome⟩

def Key.ofRequest (owner : SourceSpecialization.SpecializationKey) (active : TypeSystem.Substitution)
    (request : SourceCoreSourceCells.Request) : Key :=
  ⟨owner, active, request.binder, request.scope, request.payloadType, request.payload.isSome⟩

structure Origin where
  prepared : SourceCoreAllocationDiscovery.Prepared
  fuel : Nat
  expression : Expr
  discovered : SourceCoreAllocationDiscovery.Discovered prepared fuel expression
  deriving Repr

def Origin.codebook (origin : Origin) : SourceCoreAllocationCodebook.Prepared := origin.discovered.codebook
def Origin.keys (origin : Origin) : List Key := origin.discovered.sites.map (fun site => Key.ofReceipt site.receipt)

structure Entry (origin : Origin) where
  key : Key
  observed : key ∈ origin.keys
  ordinal : Nat
  deriving Repr

def Entry.layout {origin : Origin} (entry : Entry origin) : SourceCoreHeapMarkers.Layout :=
  ⟨⟨origin.codebook.ambient.length + entry.ordinal⟩, SourceCoreSourceCells.captureType entry.key.scope⟩

private def enumerate (origin : Origin) : List (Entry origin) :=
  origin.keys.eraseDups.attach.zipIdx.map fun (key, index) =>
    ⟨key.val, List.mem_eraseDups.mp key.property, index⟩

private abbrev indexed (origin : Origin) (entries : List (Entry origin)) : Prop :=
  entries.map (fun entry => entry.layout.dataType.index) =
    (List.range entries.length).map (origin.codebook.ambient.length + ·)

inductive Error where
  | authentication (error : SourceCoreAllocationCodebook.Error)
  | duplicateLayouts
  | invalidIndices
  | invalidDefinitions
  | unobservedLayout (key : Key)
  deriving Repr, DecidableEq

structure Prepared where private mk ::
  origin : Origin
  entries : List (Entry origin)
  enumerated : entries = enumerate origin
  unique : (entries.map (·.key)).Nodup
  indices : indexed origin entries
  definitionsTyped : (origin.codebook.ambient ++ entries.map (·.layout.definition)).WellFormed
  deriving Repr

def Prepared.codebook (prepared : Prepared) : SourceCoreAllocationCodebook.Prepared := prepared.origin.codebook

def Prepared.definitions (prepared : Prepared) : DataEnvironment :=
  prepared.codebook.ambient ++ prepared.entries.map (·.layout.definition)

def prepare {initial : SourceCoreAllocationDiscovery.Prepared} {fuel : Nat} {expression : Expr}
    (discovered : SourceCoreAllocationDiscovery.Discovered initial fuel expression) : Except Error Prepared := do
  let origin : Origin := ⟨initial, fuel, expression, discovered⟩
  let entries := enumerate origin
  if unique : (entries.map (·.key)).Nodup then
    if indices : indexed origin entries then
      if valid : (origin.codebook.ambient ++ entries.map (·.layout.definition)).isWellFormed = true then
        pure ⟨origin, entries, rfl, unique, indices, DataEnvironment.isWellFormed_sound valid⟩
      else throw .invalidDefinitions
    else throw .invalidIndices
  else throw .duplicateLayouts

/-- A static layout determines no capture positions or payload expression. -/
def allocation {origin : Origin} (entry : Entry origin) (request : SourceCoreSourceCells.Request) : Expr :=
  let captures := SourceCoreSourceCells.captures request.references request.scope
  match request.payload with
  | none => SourceCoreHeapMarkers.allocate entry.layout request.payloadType captures
  | some initializer => SourceCoreHeapMarkers.allocateInitialized entry.layout request.payloadType captures initializer

structure Allocation (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) where
  authentication : SourceCoreAllocationCodebook.Emission prepared.codebook owner active request
  entry : Entry prepared.origin
  member : entry ∈ prepared.entries
  keyExact : entry.key = Key.ofRequest owner active request
  expression : Expr
  expressionExact : expression = allocation entry request

def allocateWithReceipt (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) :
    Except Error (Allocation prepared owner active request) := do
  let authenticated ← (SourceCoreAllocationCodebook.emitWithReceipt prepared.codebook owner active request)
    |>.mapError Error.authentication
  match found : prepared.entries.find? (fun entry : Entry prepared.origin => decide (entry.key = Key.ofRequest owner active request)) with
  | none => throw (.unobservedLayout (Key.ofRequest owner active request))
  | some entry =>
    have keyExact : entry.key = Key.ofRequest owner active request := by
      have tested := List.find?_some found
      exact of_decide_eq_true tested
    pure ⟨authenticated, entry, List.mem_of_find?_eq_some found,
      keyExact, allocation entry request, rfl⟩

def allocate (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (request : SourceCoreSourceCells.Request) : Except Error Expr :=
  (allocateWithReceipt prepared owner active request).map (·.expression)

def Prepared.allocatorAt (prepared : Prepared) (owner : SourceSpecialization.SpecializationKey)
    (active : TypeSystem.Substitution) (onError : Error → SourceCoreBasic.Error) : SourceCoreSourceCells.Allocator :=
  fun request => (allocate prepared owner active request).mapError onError

theorem allocate_receipt {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request} {expression : Expr}
    (accepted : allocate prepared owner active request = .ok expression) :
    ∃ receipt : Allocation prepared owner active request, receipt.expression = expression := by
  cases allocated : allocateWithReceipt prepared owner active request with
  | error error => simp [allocate, allocated, Except.map] at accepted
  | ok receipt =>
    simp only [allocate, allocated, Except.map, Except.ok.injEq] at accepted
    exact ⟨receipt, accepted⟩

/-- Every selected key occurs in the authenticated first scan. This is a
static discovery statement, not provenance of an arbitrary external AST. -/
theorem Allocation.observed {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) :
    ∃ site ∈ prepared.origin.discovered.sites, Key.ofReceipt site.receipt = Key.ofRequest owner active request := by
  have observed := receipt.entry.observed
  rw [receipt.keyExact] at observed
  exact List.mem_map.mp observed

@[simp] theorem Prepared.ambient_prefix (prepared : Prepared) :
    prepared.definitions.take prepared.codebook.ambient.length = prepared.codebook.ambient := by
  simp [Prepared.definitions]

theorem Prepared.entry_index (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) :
    entry.layout.dataType.index = prepared.codebook.ambient.length + index := by
  change entry.layout.dataType.index = prepared.origin.codebook.ambient.length + index
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp found
  have atIndex := congrArg (fun indices : List Nat => indices[index]?) prepared.indices
  simpa only [List.getElem?_map, found, List.getElem?_range bound, Option.map_some, Option.some.injEq] using atIndex

theorem Prepared.entry_definition (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) :
    prepared.definitions[entry.layout.dataType.index]? = some entry.layout.definition := by
  rw [prepared.entry_index found]
  simp only [Prepared.definitions, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_map, found, Option.map_some]

theorem Prepared.entry_registered (prepared : Prepared) {index : Nat} {entry : Entry prepared.origin}
    (found : prepared.entries[index]? = some entry) : entry.layout.Registered prepared.definitions := by
  refine ⟨?_, prepared.entry_definition found⟩
  apply prepared.definitionsTyped.constructorPayloadType_wellFormed (constructor := entry.layout.constructor)
  change prepared.definitions.lookupConstructorPayloadType? entry.layout.constructor = some entry.layout.captureType
  simp only [DataEnvironment.lookupConstructorPayloadType?, DataEnvironment.lookupDataType?,
    SourceCoreHeapMarkers.Layout.constructor]
  rw [prepared.entry_definition found]
  rfl

theorem Allocation.registered {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) : receipt.entry.layout.Registered prepared.definitions := by
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp receipt.member
  exact prepared.entry_registered found

theorem Allocation.hasType {prepared : Prepared} {owner : SourceSpecialization.SpecializationKey}
    {active : TypeSystem.Substitution} {request : SourceCoreSourceCells.Request}
    (receipt : Allocation prepared owner active request) {context : Core.Context}
    (payloadWellFormed : Ty.WellFormed prepared.definitions request.payloadType)
    (capturesTyped : HasType context (SourceCoreSourceCells.captures request.references request.scope)
      (SourceCoreSourceCells.captureType request.scope) prepared.definitions)
    (initializerTyped : ∀ expression, request.payload = some expression →
      HasType context expression request.payloadType prepared.definitions) :
    HasType context receipt.expression (OptionalCell.referenceType request.payloadType) prepared.definitions := by
  have captureType : receipt.entry.layout.captureType = SourceCoreSourceCells.captureType request.scope := by
    change SourceCoreSourceCells.captureType receipt.entry.key.scope = SourceCoreSourceCells.captureType request.scope
    rw [receipt.keyExact]
    rfl
  have capturesTyped : HasType context (SourceCoreSourceCells.captures request.references request.scope)
      receipt.entry.layout.captureType prepared.definitions := by
    rw [captureType]
    exact capturesTyped
  rw [receipt.expressionExact]
  cases payload : request.payload with
  | none =>
    simpa only [allocation, payload] using
      SourceCoreHeapMarkers.allocate_hasType receipt.registered capturesTyped payloadWellFormed
  | some initializer =>
    simpa only [allocation, payload] using SourceCoreHeapMarkers.allocateInitialized_hasType
      receipt.registered capturesTyped (initializerTyped initializer payload)

end Solcore.Frontend.SourceCoreAllocationLayouts
end

section
-- leanmerge: from Solcore.Frontend.SourceCoreAllocationLedger
/-! Source-visible allocation locations and captures observed in a Core store.
Only completed adjacent marker/optional-payload pairs produce rows. Unrelated
administrative cells are skipped and a marker-only tail remains pending.

The initial source heap is an opaque retained prefix; no value or closure in
that prefix is inspected or imported into Core. Payload interpretation, closure
code provenance and source-execution correspondence are later boundaries.
Typing a store alone does not establish its compilation or execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAllocationLedger
open SourceInference Core
abbrev SourceLocation := SourceTypedRuntime.Location
abbrev SourceEnvironment := SourceTypedRuntime.Environment
abbrev SourceHeap := List SourceTypedRuntime.Cell
abbrev Layouts := SourceCoreAllocationLayouts.Prepared
abbrev LayoutEntry (layouts : Layouts) := SourceCoreAllocationLayouts.Entry layouts.origin
abbrev Scope := SourceCoreLocalCell.Scope

inductive Error where
  | exhausted
  | invalidKnownConstructor (location : Nat) (actual expected : ConstructorId)
  | invalidCaptureShape
  | invalidReferenceType (actual expected : Ty)
  | unknownCaptureLocation (location : Nat)
  | capturePayloadMismatch (location : Nat) (actual expected : Ty)
  | invalidOptionalPayload (location : Nat) (expected : Ty)
  | invalidLedgerOrder
  deriving Repr, DecidableEq

structure LocationEntry where
  core : Core.Location
  source : SourceLocation
  payloadType : Ty
  deriving Repr, DecidableEq

inductive Reference (prior : List LocationEntry) (type : Ty) : Value → SourceLocation → Prop where
  | intro {entry : LocationEntry} (member : entry ∈ prior) (typeExact : entry.payloadType = type) :
      Reference prior type (.cellRef (OptionalCell.cellType type) entry.core) entry.source

inductive Captures (prior : List LocationEntry) : Scope → Value → SourceEnvironment → Prop where
  | nil : Captures prior [] .unit []
  | one {id : Resolved.LocalId} {type : Ty} {value : Value} {location : SourceLocation}
      (reference : Reference prior type value location) :
      Captures prior [(id, type)] value [(id, location)]
  | cons {id : Resolved.LocalId} {type : Ty} {next : Resolved.LocalId × Ty} {rest : Scope}
      {head tail : Value} {location : SourceLocation} {environment : SourceEnvironment}
      (reference : Reference prior type head location)
      (following : Captures prior (next :: rest) tail environment) :
      Captures prior ((id, type) :: next :: rest) (.pair head tail) ((id, location) :: environment)

theorem Reference.type_eq {prior : List LocationEntry} {type : Ty} {value : Value} {location : SourceLocation}
    (related : Reference prior type value location) : value.type = OptionalCell.referenceType type := by
  cases related
  rfl

theorem Captures.type_eq {prior : List LocationEntry} {scope : Scope} {value : Value} {environment : SourceEnvironment}
    (related : Captures prior scope value environment) : value.type = SourceCoreSourceCells.captureType scope := by
  induction related with
  | nil => rfl
  | one reference => exact reference.type_eq
  | cons reference following ih =>
    simpa only [Value.type, SourceCoreSourceCells.captureType, reference.type_eq] using congrArg (Ty.product _) ih

theorem Captures.binders_exact {prior : List LocationEntry} {scope : Scope} {value : Value} {environment : SourceEnvironment}
    (related : Captures prior scope value environment) : environment.map Prod.fst = scope.map Prod.fst := by
  induction related with
  | nil | one => rfl
  | cons reference following ih => simp only [List.map_cons, ih]

structure ReferenceReceipt (prior : List LocationEntry) (type : Ty) (value : Value) where
  location : SourceLocation
  related : Reference prior type value location

private def resolveReference (prior : List LocationEntry) (type : Ty) :
    (value : Value) → Except Error (ReferenceReceipt prior type value)
  | .cellRef element location =>
    if elementEq : element = OptionalCell.cellType type then
      match found : prior.find? (fun entry => decide (entry.core = location)) with
      | none => .error (.unknownCaptureLocation location)
      | some entry =>
        if typeEq : entry.payloadType = type then
          .ok ⟨entry.source, by
            have located : entry.core = location := by
              have tested := List.find?_some found
              exact of_decide_eq_true tested
            rw [elementEq, ← located]
            exact .intro (List.mem_of_find?_eq_some found) typeEq⟩
        else .error (.capturePayloadMismatch location entry.payloadType type)
    else .error (.invalidReferenceType element (OptionalCell.cellType type))
  | _ => .error .invalidCaptureShape

structure CaptureReceipt (prior : List LocationEntry) (scope : Scope) (value : Value) where
  environment : SourceEnvironment
  related : Captures prior scope value environment

def captureEnvironment (prior : List LocationEntry) :
    (scope : Scope) → (value : Value) → Except Error (CaptureReceipt prior scope value)
  | [], .unit => .ok ⟨[], .nil⟩
  | [], _ => .error .invalidCaptureShape
  | [(id, type)], value => do
    let found ← resolveReference prior type value
    pure ⟨[(id, found.location)], .one found.related⟩
  | (id, type) :: next :: rest, .pair head tail => do
    let found ← resolveReference prior type head
    let following ← captureEnvironment prior (next :: rest) tail
    pure ⟨(id, found.location) :: following.environment, .cons found.related following.related⟩
  | _ :: _ :: _, _ => .error .invalidCaptureShape

def optionalValue (type : Ty) : Option Value → Value
  | none => .inLeft type .unit
  | some value => .inRight .unit value

structure PayloadReceipt (type : Ty) (optional : Value) where
  payload : Option Value
  shape : optional = optionalValue type payload
  typeExact : optional.type = OptionalCell.cellType type

private def decodePayload (location : Nat) (type : Ty) :
    (optional : Value) → Except Error (PayloadReceipt type optional)
  | .inLeft annotation .unit =>
    if equal : annotation = type then .ok ⟨none, by simp [optionalValue, equal], by simp [Value.type, OptionalCell.cellType, equal]⟩
    else .error (.invalidOptionalPayload location type)
  | .inRight .unit value =>
    if typed : value.type = type then .ok ⟨some value, rfl, by simp [Value.type, OptionalCell.cellType, typed]⟩
    else .error (.invalidOptionalPayload location type)
  | _ => .error (.invalidOptionalPayload location type)

structure Row (layouts : Layouts) (store : Store) where
  entry : LayoutEntry layouts
  member : entry ∈ layouts.entries
  markerIndex : Nat
  sourceLocation : SourceLocation
  captures : Value
  optional : Value
  payload : Option Value
  environment : SourceEnvironment
  prior : List LocationEntry
  markerFound : store[markerIndex]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures)
  payloadFound : store[markerIndex + 1]? = some optional
  payloadShape : optional = optionalValue entry.key.payloadType payload
  payloadType : optional.type = OptionalCell.cellType entry.key.payloadType
  captured : Captures prior entry.key.scope captures environment
  deriving Repr

def Row.coreLocation {layouts : Layouts} {store : Store} (row : Row layouts store) : Core.Location := row.markerIndex + 1

def Row.location {layouts : Layouts} {store : Store} (row : Row layouts store) : LocationEntry :=
  ⟨row.coreLocation, row.sourceLocation, row.entry.key.payloadType⟩

structure Pending (layouts : Layouts) (store : Store) where
  entry : LayoutEntry layouts
  member : entry ∈ layouts.entries
  markerIndex : Nat
  captures : Value
  environment : SourceEnvironment
  prior : List LocationEntry
  markerFound : store[markerIndex]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures)
  payloadMissing : store[markerIndex + 1]? = none
  captured : Captures prior entry.key.scope captures environment
  deriving Repr

theorem Pending.is_tail {layouts : Layouts} {store : Store} (pending : Pending layouts store) :
    pending.markerIndex + 1 = store.length := by
  obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp pending.markerFound
  have ending := List.getElem?_eq_none_iff.mp pending.payloadMissing
  omega

structure Result (layouts : Layouts) (store : Store) where
  rows : List (Row layouts store)
  pending : Option (Pending layouts store)
  deriving Repr

private def scanFrom (layouts : Layouts) (initial : SourceHeap) (store : Store) :
    Nat → Nat → List (Row layouts store) → Except Error (Result layouts store)
  | 0, _, _ => .error .exhausted
  | fuel + 1, index, rows => do
    match current : store[index]? with
    | none => pure ⟨rows, none⟩
    | some value =>
      match valueEq : value with
      | .constructed constructor captures =>
        match found : layouts.entries.find? (fun entry => decide (entry.layout.dataType = constructor.owner)) with
        | none => scanFrom layouts initial store fuel (index + 1) rows
        | some entry =>
          if exactConstructor : constructor = entry.layout.constructor then
            let prior := rows.map Row.location
            let captured ← captureEnvironment prior entry.key.scope captures
            have marker : store[index]? = some (SourceCoreHeapMarkers.markerValue entry.layout captures) := by
              simpa only [SourceCoreHeapMarkers.markerValue, valueEq, exactConstructor] using current
            match payloadFound : store[index + 1]? with
            | none =>
              pure ⟨rows, some ⟨entry, List.mem_of_find?_eq_some found, index, captures,
                captured.environment, prior, marker, payloadFound, captured.related⟩⟩
            | some optional =>
              let payload ← decodePayload (index + 1) entry.key.payloadType optional
              let row : Row layouts store := {
                entry, member := List.mem_of_find?_eq_some found
                markerIndex := index
                sourceLocation := ⟨initial.length + rows.length⟩
                captures, optional, payload := payload.payload
                environment := captured.environment, prior
                markerFound := marker, payloadFound
                payloadShape := payload.shape, payloadType := payload.typeExact
                captured := captured.related }
              scanFrom layouts initial store fuel (index + 2) (rows ++ [row])
          else throw (.invalidKnownConstructor index constructor entry.layout.constructor)
      | _ => scanFrom layouts initial store fuel (index + 1) rows

/-- Independent finite checks connect every capture to exactly the preceding
completed rows and place source locations after the untouched initial prefix. -/
def RowsAligned {layouts : Layouts} {store : Store} (initial : SourceHeap) (rows : List (Row layouts store)) : Prop :=
  ∀ index : Fin rows.length,
    (rows[index]).sourceLocation.index = initial.length + index.val ∧
    (rows[index]).prior = (rows.take index.val).map Row.location ∧
    (rows.take index.val).all (fun previous => decide (previous.coreLocation < (rows[index]).markerIndex)) = true

def PendingAligned {layouts : Layouts} {store : Store} (rows : List (Row layouts store)) : Option (Pending layouts store) → Prop
  | none => True
  | some pending => pending.prior = rows.map Row.location ∧
      rows.all (fun row => decide (row.coreLocation < pending.markerIndex)) = true

instance {layouts : Layouts} {store : Store} (initial : SourceHeap) (rows : List (Row layouts store)) :
    Decidable (RowsAligned initial rows) := inferInstanceAs (Decidable (∀ _ : Fin rows.length, _ ∧ _ ∧ _))
instance {layouts : Layouts} {store : Store} (rows : List (Row layouts store)) (pending : Option (Pending layouts store)) :
    Decidable (PendingAligned rows pending) := by
  cases pending <;> unfold PendingAligned <;> infer_instance

structure Ledger (layouts : Layouts) (initial : SourceHeap) (store : Store) where private mk ::
  rows : List (Row layouts store)
  pending : Option (Pending layouts store)
  aligned : RowsAligned initial rows
  pendingAligned : PendingAligned rows pending
  deriving Repr

def scan (layouts : Layouts) (initial : SourceHeap) (store : Store) : Except Error (Ledger layouts initial store) := do
  let result ← scanFrom layouts initial store (store.length + 1) 0 []
  if aligned : RowsAligned initial result.rows then
    if pendingAligned : PendingAligned result.rows result.pending then
      pure ⟨result.rows, result.pending, aligned, pendingAligned⟩
    else throw .invalidLedgerOrder
  else throw .invalidLedgerOrder

def Ledger.initialHeap {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (_ledger : Ledger layouts initial store) : SourceHeap := initial

def Ledger.locations {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) : List LocationEntry := ledger.rows.map Row.location

def Ledger.locationAt? {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (location : Core.Location) : Option LocationEntry :=
  ledger.locations.find? (fun entry => decide (entry.core = location))

def Ledger.nextSourceLocation {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) : SourceLocation := ⟨initial.length + ledger.rows.length⟩

/-- Cell interpretation is supplied by the later value decoder. The prefix
is retained verbatim and is never sent through that decoder. -/
def Ledger.exportHeap {layouts : Layouts} {initial : SourceHeap} {store : Store} {ε : Type}
    (ledger : Ledger layouts initial store) (decode : Row layouts store → Except ε SourceTypedRuntime.Cell) : Except ε SourceHeap := do
  pure (initial ++ (← ledger.rows.mapM decode))

theorem Ledger.exportHeap_prefix {layouts : Layouts} {initial : SourceHeap} {store : Store} {ε : Type}
    (ledger : Ledger layouts initial store) (decode : Row layouts store → Except ε SourceTypedRuntime.Cell)
    {heap : SourceHeap} (exported : ledger.exportHeap decode = .ok heap) : heap.take initial.length = initial := by
  cases decoded : ledger.rows.mapM decode with
  | error error => simp [exportHeap, decoded, Functor.map, Except.map] at exported
  | ok cells =>
    simp [exportHeap, decoded, Functor.map, Except.map] at exported
    subst heap
    simp

theorem Ledger.sourceLocation_exact {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (index : Fin ledger.rows.length) :
    (ledger.rows[index]).sourceLocation.index = initial.length + index.val := (ledger.aligned index).1

theorem Ledger.sourceLocation_injective {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) :
    Function.Injective (fun index : Fin ledger.rows.length => (ledger.rows[index]).sourceLocation) := by
  intro left right equal
  apply Fin.ext
  have same := congrArg (fun location : SourceLocation => location.index) equal
  rw [ledger.sourceLocation_exact left, ledger.sourceLocation_exact right] at same
  omega

theorem Ledger.locationAt?_found {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) {location : Core.Location} {entry : LocationEntry}
    (found : ledger.locationAt? location = some entry) :
    entry ∈ ledger.locations ∧ entry.core = location := by
  have tested := List.find?_some found
  exact ⟨List.mem_of_find?_eq_some found, of_decide_eq_true tested⟩

theorem Ledger.capture_prior_exact {layouts : Layouts} {initial : SourceHeap} {store : Store}
    (ledger : Ledger layouts initial store) (index : Fin ledger.rows.length) :
    Captures ((ledger.rows.take index.val).map Row.location) (ledger.rows[index]).entry.key.scope
      (ledger.rows[index]).captures (ledger.rows[index]).environment := by
  rw [← (ledger.aligned index).2.1]
  exact (ledger.rows[index]).captured

private theorem value_typed_at {definitions : DataEnvironment} {world : StoreTyping} {store : Store}
    (typed : RuntimeStoreHasTypes world store definitions) {index : Nat} {value : Value}
    (found : store[index]? = some value) : RuntimeValueHasType world value value.type definitions := by
  have worldFound : world[index]? = some value.type := by
    rw [typed.world_eq]
    simp only [List.getElem?_map, found, Option.map_some]
  obtain ⟨actual, read, valueTyped⟩ := typed.read worldFound
  have same : actual = value := by
    have read : store[index]? = some actual := read
    exact Option.some.inj (read.symm.trans found)
  subst actual
  exact valueTyped

theorem Row.optional_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.optional (OptionalCell.cellType row.entry.key.payloadType) layouts.definitions := by
  rw [← row.payloadType]
  exact value_typed_at typed row.payloadFound

theorem Row.captures_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions) :
    RuntimeValueHasType world row.captures row.entry.layout.captureType layouts.definitions := by
  have markerTyped := value_typed_at typed row.markerFound
  obtain ⟨index, found⟩ := List.mem_iff_getElem?.mp row.member
  have registered := layouts.entry_registered found
  cases markerTyped with
  | constructed payloadFound capturesTyped =>
    rw [registered.payloadLookup] at payloadFound
    cases payloadFound
    exact capturesTyped

theorem Row.payload_typed {layouts : Layouts} {store : Store} (row : Row layouts store)
    {world : StoreTyping} (typed : RuntimeStoreHasTypes world store layouts.definitions)
    {value : Value} (present : row.payload = some value) :
    RuntimeValueHasType world value row.entry.key.payloadType layouts.definitions := by
  have valueTyped := row.optional_typed typed
  rw [row.payloadShape, present] at valueTyped
  cases valueTyped with
  | inRight payloadTyped => exact payloadTyped

structure TypedLedger (layouts : Layouts) (initial : SourceHeap) (world : StoreTyping) (store : Store) where
  ledger : Ledger layouts initial store
  typed : RuntimeStoreHasTypes world store layouts.definitions
  deriving Repr

def scanTyped (layouts : Layouts) (initial : SourceHeap) (world : StoreTyping) (store : Store)
    (typed : RuntimeStoreHasTypes world store layouts.definitions) : Except Error (TypedLedger layouts initial world store) :=
  (scan layouts initial store).map (fun ledger => ⟨ledger, typed⟩)

end Solcore.Frontend.SourceCoreAllocationLedger
end
