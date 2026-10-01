import Solcore.Frontend.SourceCoreCallableContextFrames
import Solcore.Frontend.SourceCoreCallablePrincipals

/-! A finite table for callable ancestry metadata. Runtime lookup traverses the
finite frame and searches prepared rows; it does not substitute source types,
rewrite requirements, match schemes, resolve evidence, or evaluate source IR.

`Table` is a data carrier, not an ownership certificate. A compiler artifact
must retain both its preparation receipt and the completeness/meaning of its
rows. In particular, accepting a table's indices does not prove runtime
history, native closure code, or capture ownership. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryCache
open SourceInference TypeSystem
abbrev Frame := SourceCoreCallableContextFrames.Frame
abbrev Owner := SourceSpecialization.SpecializationKey

structure State where
  owner : Owner
  active : Substitution
  source : TypedSource
  deriving DecidableEq, Repr

structure Key where
  owner : Owner
  active : Substitution
  requirements : List (List RequirementId)
  deriving DecidableEq, Repr

def State.key (state : State) : Key :=
  ⟨state.owner, state.active, state.source.nodes.map fun
    | .expression node => node.requirements
    | .statement _ => []⟩

structure NamedEdge where
  origin : Core.Word
  destination : Nat
  deriving DecidableEq, Repr

structure LambdaEdge where
  state : Nat
  origin : Core.Word
  deriving DecidableEq, Repr

structure ViewEdge where
  state : Nat
  view : Core.Word
  target : Core.Word
  destination : Nat
  deriving DecidableEq, Repr

structure Table where
  states : List State
  named : List NamedEdge
  lambdas : List LambdaEdge
  views : List ViewEdge
  deriving DecidableEq, Repr

def Table.stateAt? (table : Table) (index : Nat) : Option State := table.states[index]?

def Table.namedAt? (table : Table) (origin : Core.Word) : Option Nat :=
  (table.named.find? fun edge => decide (edge.origin = origin)).map (·.destination)

def Table.lambdaAllowed (table : Table) (state : Nat) (origin : Core.Word) : Bool :=
  table.lambdas.any fun edge => decide (edge.state = state ∧ edge.origin = origin)

def Table.viewAt? (table : Table) (state : Nat) (view target : Core.Word) : Option Nat :=
  (table.views.find? fun edge => decide (edge.state = state ∧ edge.view = view ∧ edge.target = target)).map (·.destination)

/-- `some none` is the empty frame. `none` rejects a missing transition. A
lambda transition preserves its parent's state, regardless of frame depth. -/
def Table.lookupIndex? (table : Table) : Frame → Option (Option Nat)
  | .empty => some none
  | .named origin => (table.namedAt? origin).map some
  | .lambda origin captured =>
      match table.lookupIndex? captured with
      | some (some state) => if table.lambdaAllowed state origin then some (some state) else none
      | _ => none
  | .view view target parent =>
      match table.lookupIndex? parent with
      | some (some state) => (table.viewAt? state view target).map some
      | _ => none

/-- Table-only reconstruction. With list-backed tables the time is bounded by
frame depth times the transition-table size, plus one final state lookup. No
work depends on the size of a source body or on an execution fuel budget. -/
def Table.lookup? (table : Table) (frame : Frame) : Option (Option State) :=
  match table.lookupIndex? frame with
  | none => none
  | some none => some none
  | some (some index) => (table.stateAt? index).map some

end Solcore.Frontend.SourceCoreCallableAncestryCache
