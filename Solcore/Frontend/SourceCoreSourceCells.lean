import Solcore.Frontend.SourceCoreBasic
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
