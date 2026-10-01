import Solcore.Frontend.SourceCoreCallableAncestry
import Solcore.Frontend.SourceCoreCallableContextFrameCodec
import Solcore.Frontend.SourceCoreAllocationLedger

/-! Keep allocation-time callable ancestry even for a generalized principal
whose native instance bundle is Unit. One ordinary administrative frame cell
precedes each source marker. Its index is excluded from the source ledger.

The original allocator still authenticates the exact source/binder/layout.
The extra cell is emitted after the source initializer has produced its
successful value. The enclosing assembled checker validates its placement.
A decoded adjacent snapshot proves its shape, not execution history. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreAncestryAllocationFrames
open SourceInference Core
abbrev Request := SourceCoreSourceCells.Request
abbrev Allocator := SourceCoreSourceCells.Allocator
abbrev Layout := SourceCoreCallableContextFrames.Layout
abbrev Checked := SourceCoreCompatibleCatalog.Checked
abbrev Base := SourceCoreCompatibleFunctions.Prepared

/-- Named inputs bind the incoming argument through `request.references`.
Other sites retain the caller's original packed-argument slot. Binder IDs are
selected from the authenticated source; lambda IDs are distinct from inputs. -/
def isNamedInput (request : Request) : Bool :=
  request.source.inputs.any (fun binder => decide (binder.id = request.binder.id))

def referenceIndex (globals : Nat) (request : Request) : Nat :=
  request.references (request.scope.length + (if isNamedInput request then 0 else 1) + globals)

/-- Administrative lexical insertion moves every original allocation variable
with its expression, including its actual captures and initialized payload. -/
def snapshotBefore (layout : Layout) (reference allocation : Expr) : Expr :=
  .letE (.newCell layout.type (.loadCell reference)) (allocation.weakenAt 0)

theorem snapshotBefore_hasType {definitions : DataEnvironment} {context : Core.Context}
    {layout : Layout} {reference allocation : Expr} {result : Ty}
    (_registered : layout.Registered definitions)
    (referenceTyped : HasType context reference (.cell layout.type) definitions)
    (allocationTyped : HasType context allocation result definitions) :
    HasType context (snapshotBefore layout reference allocation) result definitions := by
  apply HasType.letE (.newCell (.loadCell referenceTyped))
  simpa [Context.insertAt] using allocationTyped.weakenAt (inserted := .cell layout.type) 0

structure Annotated (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request) where private mk ::
  original : Expr
  allocated : allocate request = .ok original
  expression : Expr
  exact : expression = snapshotBefore layout (.var (referenceIndex globals request)) original

def annotateWithReceipt (layout : Layout) (globals : Nat) (allocate : Allocator) (request : Request) :
    Except SourceCoreBasic.Error (Annotated layout globals allocate request) :=
  match allocated : allocate request with
  | .error error => .error error
  | .ok original => .ok ⟨original, allocated,
      snapshotBefore layout (.var (referenceIndex globals request)) original, rfl⟩

def allocator (layout : Layout) (globals : Nat) (allocate : Allocator) : Allocator :=
  fun request => (annotateWithReceipt layout globals allocate request).map (·.expression)

/-- Apply to the actual frame-aware representation after selecting its common
source-allocation profile. No new source binder or global key is introduced. -/
def representation {checked : Checked} {base : Base checked}
    (ancestry : SourceCoreCallableAncestry.Prepared base)
    (original : SourceCoreGeneralFunctions.Representation) : SourceCoreGeneralFunctions.Representation :=
  {original with allocatorAt := fun owner active =>
    (original.allocatorAt owner active).map (allocator ancestry.layout.frame base.globals.length)}

inductive Error where
  | missingPredecessor
  | malformedSnapshot (index : Nat)
  deriving Repr

structure Snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) where private mk ::
  index : Nat
  preceding : index + 1 = row.markerIndex
  frame : SourceCoreCallableContextFrames.Frame
  exact : store[index]? = some (SourceCoreCallableContextFrames.encode layout frame)

def snapshot {layouts : SourceCoreAllocationLayouts.Prepared} {store : Store}
    (layout : Layout) (row : SourceCoreAllocationLedger.Row layouts store) : Except Error (Snapshot layout row) := do
  if preceding : row.markerIndex - 1 + 1 = row.markerIndex then
    match selected : store[row.markerIndex - 1]? with
    | none => throw (.malformedSnapshot (row.markerIndex - 1))
    | some value =>
      match decoded : SourceCoreCallableContextFrameCodec.decode layout value with
      | none => throw (.malformedSnapshot (row.markerIndex - 1))
      | some frame =>
        have same := SourceCoreCallableContextFrameCodec.decode_sound layout value frame decoded
        pure ⟨row.markerIndex - 1, preceding, frame, same ▸ selected⟩
  else throw .missingPredecessor

end Solcore.Frontend.SourceCoreAncestryAllocationFrames
