import Solcore.Frontend.SourceCoreElaboration
import Solcore.Core.OptionalCell

/-!
Executable lowering of monomorphic local reads to optional Core cells.

This is the local-reference boundary of the new runtime lowering path. Its
closed type profile is the existing unit/Bool/Word/product projection; other
source forms, generalized binders and coercions require their own lowering.
The reason word is supplied by the compiler's fault-site table.
-/

set_option autoImplicit false

namespace Solcore.Frontend.SourceCoreLocalCell

open SourceInference

/-- Slots retain source identities and the payload type of each Core cell. -/
abbrev Scope := List (Resolved.LocalId × Core.Ty)

def lookup? : Scope → Resolved.LocalId → Option (Nat × Core.Ty)
  | [], _ => none
  | (other, type) :: rest, id =>
      if other = id then some (0, type)
      else (lookup? rest id).map fun (index, type) => (index + 1, type)

def coreContext (scope : Scope) : Core.Context :=
  scope.map fun entry => .cell (Core.OptionalCell.cellType entry.2)

inductive Error where
  | missingExpression (id : ExpressionId)
  | expectedLocalReference (id : ExpressionId)
  | ownerMismatch (id : Resolved.LocalId)
  | missingBinding (id : Resolved.LocalId)
  | requirementsPresent (id : ExpressionId)
  | coercionsPresent (id : ExpressionId)
  | typeProjection (error : SourceCoreElaboration.Error)
  | slotTypeMismatch (expected actual : Core.Ty)
  deriving Repr

/-- Compile a local occurrence without reading or evaluating a source heap. -/
def lowerRead (source : TypedSource) (scope : Scope) (id : ExpressionId)
    (reason : Core.Word) : Except Error Core.Expr := do
  let node ← match source.lookupExpression? id with
    | some node => pure node
    | none => .error (.missingExpression id)
  let binder ← match node.form with
    | .reference _ (.local binder) => pure binder
    | _ => .error (.expectedLocalReference id)
  if binder.owner != source.owner then
    throw (.ownerMismatch binder)
  unless node.requirements.isEmpty do throw (.requirementsPresent id)
  unless node.coercions.isEmpty do throw (.coercionsPresent id)
  let (index, payloadType) ← match lookup? scope binder with
    | some slot => pure slot
    | none => .error (.missingBinding binder)
  let projected ← (SourceCoreElaboration.lowerType
    (.occurrence id.occurrence) node.type).mapError Error.typeProjection
  if projected ≠ payloadType then
    throw (.slotTypeMismatch projected payloadType)
  pure (Core.OptionalCell.read payloadType (.var index) reason)

/-- Exact metadata and a resolved slot suffice for actual lowering success. -/
theorem lowerRead_eq {source : TypedSource} {scope : Scope}
    {id : ExpressionId} {node : ExpressionNode} {binder : Resolved.LocalId}
    {name : String} {index : Nat} {payloadType : Core.Ty}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .reference name (.local binder))
    (owner : binder.owner = source.owner)
    (requirements : node.requirements = []) (coercions : node.coercions = [])
    (slot : lookup? scope binder = some (index, payloadType))
    (projection : SourceCoreElaboration.lowerType
      (.occurrence id.occurrence) node.type = .ok payloadType)
    (reason : Core.Word) :
    lowerRead source scope id reason =
      .ok (Core.OptionalCell.read payloadType (.var index) reason) := by
  simp [lowerRead, found, form, owner, requirements, coercions, slot, projection,
    Except.mapError, bind, Except.bind, pure, Pure.pure, Except.pure]

theorem lookup?_context {scope : Scope} {id : Resolved.LocalId}
    {index : Nat} {payloadType : Core.Ty}
    (slot : lookup? scope id = some (index, payloadType)) :
    (coreContext scope)[index]? =
      some (.cell (Core.OptionalCell.cellType payloadType)) := by
  induction scope generalizing index with
  | nil => simp [lookup?] at slot
  | cons head tail inductionHypothesis =>
      rcases head with ⟨other, type⟩
      by_cases same : other = id
      · simp [lookup?, same] at slot
        rcases slot with ⟨rfl, rfl⟩
        rfl
      · simp only [lookup?, same, ↓reduceIte] at slot
        cases found : lookup? tail id with
        | none => simp [found] at slot
        | some pair =>
            rcases pair with ⟨previous, foundType⟩
            simp only [found, Option.map_some, Option.some.injEq, Prod.mk.injEq] at slot
            rcases slot with ⟨rfl, rfl⟩
            exact inductionHypothesis found

end Solcore.Frontend.SourceCoreLocalCell
