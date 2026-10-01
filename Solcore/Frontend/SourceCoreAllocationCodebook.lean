import Solcore.Frontend.SourceCoreSourceCells
import Solcore.Frontend.SourceSpecialization
import Solcore.Core.Check

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
