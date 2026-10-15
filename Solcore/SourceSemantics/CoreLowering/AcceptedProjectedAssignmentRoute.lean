import Solcore.SourceSemantics.Static
import Solcore.SourceSemantics.CoreLowering.DataPlaceKeyOrder

/-! Original mapping-index paths determine their declared root from the exact
stored key types and selected leaf. This supports genuine Source typing without
assuming that an arbitrary lexical context matches compiler binder metadata. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
open Core Frontend SourceInference

inductive Route (source : TypedSource) : TypeSystem.Ty → List PlaceProjection → TypeSystem.Ty → Prop where
  | nil {type} : Route source type [] type
  | index {key node keyType valueType rest leaf}
      (found : source.lookupExpression? key = some node)
      (same : node.type = keyType)
      (tail : Route source valueType rest leaf) :
      Route source (.mapping keyType valueType) (.index key :: rest) leaf

/-- The original key nodes and final leaf fix every mapping layer. -/
theorem Route.root_type {source : TypedSource} {context : SourceSemantics.Context}
    {declared actual leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (unique : NodeOccurrencesUnique source) (route : Route source declared projections leaf)
    (typed : SourceProjectionsHaveType source context actual projections leaf) : actual = declared := by
  induction route generalizing actual with
  | nil => cases typed; rfl
  | index found same tail ih =>
      cases typed with
      | index keyTyped restTyped =>
          obtain ⟨original, contains, stored⟩ := keyTyped.stored_type
          cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
          cases stored.symm.trans same
          cases ih restTyped
          rfl

theorem Route.key_found {source : TypedSource} {root leaf : TypeSystem.Ty}
    {projections : List PlaceProjection} (route : Route source root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ node, source.lookupExpression? id = some node := by
  induction route with
  | nil => cases member
  | @index key node keyType valueType rest leaf found same tail ih =>
      rcases List.mem_cons.mp member with equal | member
      · exact ⟨node, equal ▸ found⟩
      · exact ih member

theorem Route.key_typed {source : TypedSource} {context : SourceSemantics.Context}
    {root leaf : TypeSystem.Ty} {projections : List PlaceProjection}
    (unique : NodeOccurrencesUnique source) (route : Route source root projections leaf)
    (typed : SourceProjectionsHaveType source context root projections leaf)
    {id : ExpressionId} (member : id ∈ DataPlaceKeyOrder.sourceKeys projections) :
    ∃ node, source.lookupExpression? id = some node ∧ ExpressionHasType source context id node.type := by
  induction route with
  | nil => cases member
  | index found same tail ih =>
      cases typed with
      | index keyTyped restTyped =>
          rcases List.mem_cons.mp member with equal | member
          · subst id
            obtain ⟨original, contains, stored⟩ := keyTyped.stored_type
            cases Option.some.inj ((lookupExpression?_complete unique contains).symm.trans found)
            exact ⟨_, found, stored.symm ▸ keyTyped⟩
          · exact ih restTyped member

/-- This check follows the retained source path; members are outside this profile. -/
def check (source : TypedSource) (root : TypeSystem.Ty) (projections : List PlaceProjection)
    (leaf : TypeSystem.Ty) : Option (PLift (Route source root projections leaf)) :=
  match projections with
  | [] => if same : root = leaf then some ⟨same ▸ .nil⟩ else none
  | .member _ _ :: _ => none
  | .index key :: rest =>
      match root with
      | .mapping keyType valueType => do
          match found : source.lookupExpression? key with
          | none => none
          | some node =>
              if same : node.type = keyType then do
                let ⟨tail⟩ ← check source valueType rest leaf
                pure ⟨.index found same tail⟩
              else none
      | _ => none

end Solcore.SourceSemantics.CoreLowering.AcceptedProjectedAssignmentRoute
