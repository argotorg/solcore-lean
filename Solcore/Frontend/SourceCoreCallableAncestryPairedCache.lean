import Solcore.Frontend.SourceCoreCallableAncestryReadRecipes
import Solcore.Frontend.SourceCoreCallablePairedFrames

/-! Table-only lookup for read-time caller and lexical creation snapshots.
Both parents of an applied view are retained. Native code context and source
substitution are distinct key fields. This data table does not itself certify
compiler ownership, closure/capture provenance, or runtime reachability. -/
set_option autoImplicit false
namespace Solcore.Frontend.SourceCoreCallableAncestryPairedCache
open SourceInference TypeSystem
abbrev State := SourceCoreCallableAncestryReadRecipes.State
abbrev Frame := SourceCoreCallablePairedFrames.Frame
abbrev Owner := SourceSpecialization.SpecializationKey

structure Key where
  owner : Owner
  sourceActive : Substitution
  nativeActive : Substitution
  requirements : List (List RequirementId)
  deriving DecidableEq, Repr

def stateKey (state : State) : Key :=
  ⟨state.metadata.owner, state.metadata.active, state.nativeActive, state.metadata.source.nodes.map fun
    | .expression node => node.requirements
    | .statement _ => []⟩

abbrev NamedEdge := SourceCoreCallableAncestryCache.NamedEdge
abbrev LambdaEdge := SourceCoreCallableAncestryCache.LambdaEdge

structure ViewEdge where
  caller : Nat
  lexical : Nat
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
def Table.viewAt? (table : Table) (caller lexical : Nat) (view target : Core.Word) : Option Nat :=
  (table.views.find? fun edge => decide
    (edge.caller = caller ∧ edge.lexical = lexical ∧ edge.view = view ∧ edge.target = target)).map (·.destination)

/-- The transient read tag is installed only while invoking its underlying
lambda. It becomes an applied view when that lambda joins its own snapshot.
It has no principal execution-source state on its own. -/
def Table.lookupIndex? (table : Table) : Frame → Option (Option Nat)
  | .empty => some none
  | .named origin => (table.namedAt? origin).map some
  | .lambda origin lexical =>
    match table.lookupIndex? lexical with
    | some (some state) => if table.lambdaAllowed state origin then some (some state) else none
    | _ => none
  | .view .. => none
  | .appliedView view target caller lexical =>
    match table.lookupIndex? caller, table.lookupIndex? lexical with
    | some (some callerState), some (some lexicalState) =>
      (table.viewAt? callerState lexicalState view target).map some
    | _, _ => none

def Table.lookup? (table : Table) (frame : Frame) : Option (Option State) :=
  match table.lookupIndex? frame with
  | none => none
  | some none => some none
  | some (some position) => (table.stateAt? position).map some

end Solcore.Frontend.SourceCoreCallableAncestryPairedCache
