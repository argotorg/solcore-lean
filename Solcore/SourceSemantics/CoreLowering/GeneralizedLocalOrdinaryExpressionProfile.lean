import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryReadSite
import Solcore.SourceSemantics.CoreLowering.CompatibleExpressionProductTree

/-! Finite ordinary expression profiles for the real materialized lambda view.
The tree contains only source metadata, never execution or compiler laws. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
open Core Frontend SourceInference

inductive Form : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : Form form
  | read (name : String) (binder : Resolved.LocalId) : Form (.reference name (.local binder))
  | group (inner : ExpressionId) : Form (.group inner)
  | pair (left right : ExpressionId) : Form (.tuple [left, right])

structure Site (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : Form node.form
  coercions : node.coercions = []
  requirements : (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])
  notInitializer : locals.bindings.find? (fun binding =>
    decide (binding.caller = owner ∧ binding.initializer = id)) = none
  ordinary : ∀ name binder, node.form = .reference name (.local binder) →
    locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false

private def form? (form : ExpressionForm) : Option (PLift (Form form)) :=
  match form with
  | .integerLiteral literal resolution => some ⟨.literal (.integer literal resolution)⟩
  | .reference name (.builtinBoolean value) => some ⟨.literal (.bool name value)⟩
  | .literal literal => some ⟨.literal (.word literal)⟩
  | .tuple [] => some ⟨.literal .unit⟩
  | .reference name (.local binder) => some ⟨.read name binder⟩
  | .group inner => some ⟨.group inner⟩
  | .tuple [left, right] => some ⟨.pair left right⟩
  | _ => none

private def ordinary? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (node : ExpressionNode) :
    Option (PLift (∀ name binder, node.form = .reference name (.local binder) →
      locals.bindings.any (fun binding => decide (binding.caller = owner ∧ binding.binder.id = binder)) = false)) := by
  cases form : node.form
  case reference name resolution =>
    cases resolution
    case «local» binder =>
      exact if ordinary : locals.bindings.any (fun binding =>
          decide (binding.caller = owner ∧ binding.binder.id = binder)) = false then
        some ⟨by
          intro actual actualBinder same
          obtain ⟨rfl, resolution⟩ := ExpressionForm.reference.inj same
          cases resolution
          exact ordinary⟩
      else none
    all_goals exact some ⟨by intro name binder same; simp at same⟩
  all_goals exact some ⟨by intro name binder same; simp at same⟩

private def requirements? (node : ExpressionNode) :
    Option (PLift (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])) :=
  if empty : node.requirements = [] then some ⟨by split <;> simp_all⟩
  else match node.form with | .integerLiteral .. => some ⟨True.intro⟩ | _ => none

def site? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) (id : ExpressionId) :
    Option (Site locals owner source id) := do
  match found : source.lookupExpression? id with
  | none => none
  | some node => do
    let ⟨form⟩ ← form? node.form
    if coercions : node.coercions = [] then do
      let ⟨requirements⟩ ← requirements? node
      if notInitializer : locals.bindings.find? (fun binding =>
          decide (binding.caller = owner ∧ binding.initializer = id)) = none then do
        let ⟨ordinary⟩ ← ordinary? locals owner node
        pure ⟨node, found, form, coercions, requirements, notInitializer, ordinary⟩
      else none
    else none

inductive Tree (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) : ExpressionId → Prop where
  | literal {id} (site : Site locals owner source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Tree locals owner source id
  | read {id name binder} (site : Site locals owner source id)
      (form : site.node.form = .reference name (.local binder)) : Tree locals owner source id
  | group {id inner} (site : Site locals owner source id) (form : site.node.form = .group inner)
      (child : Tree locals owner source inner) : Tree locals owner source id
  | pair {id left right} (site : Site locals owner source id) (form : site.node.form = .tuple [left, right])
      (first : Tree locals owner source left) (second : Tree locals owner source right) : Tree locals owner source id

variable {locals : SourceCoreLocalPolymorphism.Catalog} {owner : SourceCoreLocalPolymorphism.Key}
  {source : TypedSource} {id : ExpressionId}

theorem Tree.site (tree : Tree locals owner source id) : Nonempty (Site locals owner source id) := by
  cases tree <;> exact ⟨‹_›⟩

theorem Tree.syntax (tree : Tree locals owner source id) : CompatibleExpressionProducts.Syntax source id := by
  induction tree with
  | literal site atomic => exact .literal site.found atomic
  | read site form => exact .read site.found form
  | group site form _ ih => exact .group site.found form ih
  | pair site form _ _ left right => exact .pair site.found form left right

theorem Tree.children (tree : Tree locals owner source id) {node : ExpressionNode} {child : ExpressionId}
    (found : source.lookupExpression? id = some node)
    (member : (.expression child : NodeId) ∈ node.form.references) : Tree locals owner source child := by
  cases tree with
  | literal site atomic =>
    cases Option.some.inj (site.found.symm.trans found)
    generalize shape : site.node.form = form at atomic
    cases atomic <;> simp [shape, ExpressionForm.references] at member
  | read site form =>
    cases Option.some.inj (site.found.symm.trans found)
    simp [form, ExpressionForm.references] at member
  | group site form subtree =>
    cases Option.some.inj (site.found.symm.trans found)
    simp only [form, ExpressionForm.references, List.mem_singleton, NodeId.expression.injEq] at member
    exact member ▸ subtree
  | pair site form first second =>
    cases Option.some.inj (site.found.symm.trans found)
    simp [form, ExpressionForm.references] at member
    rcases member with rfl | rfl
    · exact first
    · exact second

def tree? (locals : SourceCoreLocalPolymorphism.Catalog)
    (owner : SourceCoreLocalPolymorphism.Key) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Tree locals owner source id))
  | 0, _ => none
  | fuel + 1, id => do
    let site ← site? locals owner source id
    match form : site.node.form with
    | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
    | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
    | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
    | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
    | .reference _ (.local _) => pure ⟨.read site form⟩
    | .group inner => do
      let ⟨child⟩ ← tree? locals owner source fuel inner
      pure ⟨.group site form child⟩
    | .tuple [left, right] => do
      let ⟨first⟩ ← tree? locals owner source fuel left
      let ⟨second⟩ ← tree? locals owner source fuel right
      pure ⟨.pair site form first second⟩
    | _ => none

end Solcore.SourceSemantics.CoreLowering.GeneralizedLocalOrdinaryExpressionProfile
