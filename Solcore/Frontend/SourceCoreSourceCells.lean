import Solcore.Frontend.SourceCoreBasic
import Solcore.SourceSemantics.CaptureBinders
import Solcore.Frontend.SourceCoreHeapMarkers

/-! Source-visible allocations share the ordinary expression/statement
traversal. The allocator receives the actual embedding of lexical references,
including argument-bundle and temporary result binders. It returns only an
optional payload reference; any marker bindings stay inside its expression.
The enclosing prepared entry still checks the entire emitted Core body. -/

set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreSourceCells
open SourceInference Core
abbrev Scope := SourceCoreBasic.Scope
abbrev Error := SourceCoreBasic.Error

structure Request where
  source : TypedSource
  scope : Scope
  references : Renaming
  binder : TypedBinder
  payloadType : Core.Ty
  /-- An initialized payload expression, already inside the success branch.
  Allocation must evaluate it before creating any source cell. -/
  payload : Option Core.Expr

abbrev Allocator := Request → Except Error Core.Expr

def letUninitialized (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (references : Renaming) (binder : TypedBinder)
    (payloadType : Core.Ty) (body : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (LocalSequence.letUninitialized payloadType body)
  | some allocate =>
      pure (.letE (← allocate ⟨source, scope, references, binder, payloadType, none⟩) body)

def letInitialized (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (references : Renaming) (binder : TypedBinder)
    (outputType payloadType : Core.Ty) (initializer body : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (LocalSequence.letInitialized outputType payloadType initializer body)
  | some allocate =>
      let allocation ← allocate ⟨source, scope, Renaming.comp (Renaming.insertion 0) references,
        binder, payloadType, some (.var 0)⟩
      pure (LanguageResult.bind outputType initializer (.letE allocation (body.weakenAt 1)))

/-- Capture only lexical references, in source environment order. The argument
bundle and other administrative binders are skipped by `references`. -/
def captureType : Scope → Core.Ty
  | [] => .unit
  | [(_, type)] => OptionalCell.referenceType type
  | (_, type) :: next :: rest =>
      .product (OptionalCell.referenceType type) (captureType (next :: rest))

def captures (references : Renaming) : Scope → Core.Expr
  | [] => .unit
  | [_] => .var (references 0)
  | _ :: next :: rest => .pair (.var (references 0))
      (captures (fun index => references (index + 1)) (next :: rest))

theorem captures_hasType {definitions : DataEnvironment} {context : Core.Context}
    (scope : Scope) (references : Renaming)
    (slots : ∀ index binding, scope[index]? = some binding →
      context[references index]? = some (OptionalCell.referenceType binding.2)) :
    HasType context (captures references scope) (captureType scope) definitions := by
  induction scope generalizing references with
  | nil => exact .unit
  | cons head rest ih =>
      cases rest with
      | nil => exact .var (slots 0 head rfl)
      | cons next tail =>
          apply HasType.pair (.var (slots 0 head rfl))
          apply ih (fun index => references (index + 1))
          intro index binding found
          exact slots (index + 1) binding (by simpa using found)

/-- The profile authenticates the layout and original binder metadata. Marker
payloads contain source references selected at this exact allocation site. -/
def marked (layoutAt : Request → Except Error SourceCoreHeapMarkers.Layout) : Allocator := fun request => do
  let layout ← layoutAt request
  unless layout.captureType = captureType request.scope do
    throw (.typeMismatch (.binder request.binder.id) (captureType request.scope) layout.captureType)
  let captured := captures request.references request.scope
  pure (match request.payload with
    | none => SourceCoreHeapMarkers.allocate layout request.payloadType captured
    | some value => SourceCoreHeapMarkers.allocateInitialized layout request.payloadType captured value)

/-! ## Captures by value

A lambda copies the captured cells when it is created and again at each call.
`SourceSemantics.CaptureBinders.copiedBinder?` selects the copied slots, as it
selects the copied bindings in the source semantics: a slot is copied when its
identifier has a single monomorphic declaration. A hidden match scrutinee has
no declaration, and a generalized local's cell holds an immutable principal,
so both keep their cells. -/

open SourceSemantics.CaptureBinders (copiedBinder?)

/-- The copied slots of a scope, in scope order, with their scope index,
declaration and payload type. -/
def copiedSlots (source : TypedSource) (scope : Scope) : List (Nat × TypedBinder × Core.Ty) :=
  scope.zipIdx.filterMap fun ((id, type), index) =>
    (copiedBinder? source id).map fun binder => (index, binder, type)

/-- Copy the optional cell at `reference` into a fresh cell for `binder`. An
uninitialized cell stays uninitialized. Marked copies allocate in both branches
of the payload test, below the branch's payload binder. -/
def copyCell (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (references : Renaming) (binder : TypedBinder) (payloadType : Core.Ty)
    (reference : Core.Expr) : Except Error Core.Expr := do
  match allocator with
  | none => pure (.newCell (OptionalCell.cellType payloadType) (.loadCell reference))
  | some allocate =>
      let shifted := Renaming.comp (Renaming.insertion 0) references
      let absent ← allocate ⟨source, scope, shifted, binder, payloadType, none⟩
      let present ← allocate ⟨source, scope, shifted, binder, payloadType, some (.var 0)⟩
      pure (.caseE (.loadCell reference) absent present)

/-- After `count` copies of the slots at `positions` (in copy order), the
copy of the `ordinal`-th one is at `count - 1 - ordinal`; every other index
moves past the copies. -/
def copyRenaming (positions : List Nat) : Renaming := fun index =>
  match positions.findIdx? (fun position => decide (position = index)) with
  | some ordinal => positions.length - 1 - ordinal
  | none => index + positions.length

/-- References of one copy. A named input's own allocation counts the
packed-argument slot inside its references, so a copy of an input does too;
every index above the scope then keeps its administrative meaning. -/
def copyReferences (source : TypedSource) (scope : Scope) (binder : TypedBinder)
    (base : Nat → Nat) (ordinal : Nat) : Renaming := fun index =>
  if index < scope.length then base index + ordinal
  else if source.inputs.any (fun input => decide (input.id = binder.id)) then base (index + 1) + ordinal
  else base index + ordinal

/-- Copy the remaining slots `rest` of `scope`, the first of them at scope
index `index`, after `ordinal` earlier copies; then run `body`. `base` gives
each scope slot's index before the first copy. -/
def copyChain (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (base : Nat → Nat) : Scope → Nat → Nat → Core.Expr → Except Error Core.Expr
  | [], _, _, body => pure body
  | (id, type) :: rest, index, ordinal, body =>
      match copiedBinder? source id with
      | none => copyChain allocator source scope base rest (index + 1) ordinal body
      | some binder => do
          let copy ← copyCell allocator source scope (copyReferences source scope binder base ordinal)
            binder type (.var (base index + ordinal))
          let continuation ← copyChain allocator source scope base rest (index + 1) (ordinal + 1) body
          pure (.letE copy continuation)

/-- The renaming that redirects each copied slot of `scope` to its copy. -/
def scopeCopyRenaming (source : TypedSource) (scope : Scope) (base : Nat → Nat) : Renaming :=
  copyRenaming ((copiedSlots source scope).map fun slot => base slot.1)

/-- Copy the slots of `scope` that a closure copies, head first, then run
`body` with each copied slot redirected to its copy. -/
def copyScope (allocator : Option Allocator) (source : TypedSource) (scope : Scope)
    (base : Nat → Nat) (body : Core.Expr) : Except Error Core.Expr :=
  copyChain allocator source scope base scope 0 0 (body.rename (scopeCopyRenaming source scope base))

/-- `copyChain` without an allocator: each copy is a plain cell. -/
def copyChainPlain (source : TypedSource) (base : Nat → Nat) :
    Scope → Nat → Nat → Core.Expr → Core.Expr
  | [], _, _, body => body
  | (id, type) :: rest, index, ordinal, body =>
      match copiedBinder? source id with
      | none => copyChainPlain source base rest (index + 1) ordinal body
      | some _ => .letE (.newCell (OptionalCell.cellType type) (.loadCell (.var (base index + ordinal))))
          (copyChainPlain source base rest (index + 1) (ordinal + 1) body)

/-- `copyScope` without an allocator. -/
def copyScopePlain (source : TypedSource) (scope : Scope) (base : Nat → Nat)
    (body : Core.Expr) : Core.Expr :=
  copyChainPlain source base scope 0 0 (body.rename (scopeCopyRenaming source scope base))

/-- An empty scope has nothing to copy. -/
theorem copyScopePlain_nil (source : TypedSource) (base : Nat → Nat) (body : Core.Expr) :
    copyScopePlain source [] base body = body := by
  have identity : scopeCopyRenaming source [] base = Renaming.id := by
    funext index
    simp [scopeCopyRenaming, copiedSlots, copyRenaming, Renaming.id]
  simp only [copyScopePlain, copyChainPlain, identity, Expr.rename_id]

private theorem copyChain_none (source : TypedSource) (scope : Scope) (base : Nat → Nat) :
    ∀ (rest : Scope) (index ordinal : Nat) (body : Core.Expr),
      copyChain none source scope base rest index ordinal body =
        .ok (copyChainPlain source base rest index ordinal body)
  | [], _, _, _ => rfl
  | (id, type) :: rest, index, ordinal, body => by
      unfold copyChain copyChainPlain
      split
      · exact copyChain_none source scope base rest (index + 1) ordinal body
      · simp only [copyCell, copyChain_none source scope base rest (index + 1) (ordinal + 1) body,
          bind, Except.bind, pure, Except.pure]

theorem copyScope_none (source : TypedSource) (scope : Scope) (base : Nat → Nat)
    (body : Core.Expr) :
    copyScope none source scope base body = .ok (copyScopePlain source scope base body) :=
  copyChain_none source scope base scope 0 0 _

private theorem copyChainPlain_hasType_inv {definitions : DataEnvironment} {source : TypedSource}
    {base : Nat → Nat} {body : Core.Expr} {type : Core.Ty} :
    ∀ (rest : Scope) (index ordinal : Nat) (context : Core.Context),
      HasType context (copyChainPlain source base rest index ordinal body) type definitions →
      ∃ copies : Core.Context, HasType (copies ++ context) body type definitions
  | [], _, _, context, typed => ⟨[], typed⟩
  | (id, slotType) :: rest, index, ordinal, context, typed => by
      unfold copyChainPlain at typed
      split at typed
      · exact copyChainPlain_hasType_inv rest (index + 1) ordinal context typed
      · cases typed with
        | letE _ continuation =>
            obtain ⟨copies, inner⟩ :=
              copyChainPlain_hasType_inv rest (index + 1) (ordinal + 1) _ continuation
            exact ⟨copies ++ [_], by simpa using inner⟩

/-- Typing of plain copies exposes the renamed body under the copies' types. -/
theorem copyScopePlain_hasType_inv {definitions : DataEnvironment} {context : Core.Context}
    {source : TypedSource} {scope : Scope} {base : Nat → Nat} {body : Core.Expr} {type : Core.Ty}
    (typed : HasType context (copyScopePlain source scope base body) type definitions) :
    ∃ copies : Core.Context,
      HasType (copies ++ context) (body.rename (scopeCopyRenaming source scope base)) type definitions :=
  copyChainPlain_hasType_inv scope 0 0 context typed

/-- A generalized local copies its scope once: its instances and the
binder's own marker capture the copies, while the continuation keeps the
original cells. -/
def letInitializedSnapshot (allocator : Option Allocator) (source : TypedSource)
    (scope : Scope) (binder : TypedBinder) (outputType payloadType : Core.Ty)
    (initializer body : Core.Expr) : Except Error Core.Expr := do
  let allocation ← match allocator with
    | none => pure (OptionalCell.allocateInitialized payloadType (.var 0))
    | some allocate => allocate ⟨source, scope, Renaming.insertion 0, binder, payloadType, some (.var 0)⟩
  let captured ← copyScope allocator source scope (fun index => index)
    (LanguageResult.bind (OptionalCell.referenceType payloadType) initializer
      (LanguageResult.success allocation))
  pure (LanguageResult.bind outputType captured body)

/-- Each parameter sees earlier parameters followed by its original capture
scope. The packed argument binder sits between those two portions. -/
def bindParameters (allocate : Allocator) (source : TypedSource) (scope : Scope)
    (parameters : List (TypedBinder × Core.Ty)) (outputType : Core.Ty)
    (projection : Nat → Nat → Core.Expr → Core.Expr) (body : Core.Expr) : Except Error Core.Expr :=
  parameters.zipIdx.foldrM (fun ((binder, type), index) continuation =>
    let prior := (parameters.take index).reverse.map (fun binding => (binding.1.id, binding.2)) ++ scope
    letInitialized (some allocate) source prior (Renaming.insertion index) binder outputType type
      (LanguageResult.success (projection index parameters.length (.var index))) continuation) body

end Solcore.Frontend.SourceCoreSourceCells
