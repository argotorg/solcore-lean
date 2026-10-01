import Solcore.Frontend.SourceCoreAllocationCodebook

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
