import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedRecipeCompilation
import Solcore.SourceSemantics.CoreLowering.GeneralizedLocalNamedReadCompilation
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates

/-! The bounded mixed-cell expression grammar keeps ordinary leaf policies
and generalized local reads distinct. Every accepted child belongs to the
original source graph; local-read normalization is retained at that leaf. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)

inductive Form : ExpressionForm → Prop where
  | literal {form} (atomic : CompatibleExpressionLiterals.Atomic form) : Form form
  | read (name : String) (binder : Resolved.LocalId) : Form (.reference name (.local binder))
  | group (inner : ExpressionId) : Form (.group inner)
  | pair (left right : ExpressionId) : Form (.tuple [left, right])
  | call (callee : ExpressionId) (arguments : List ExpressionId) (metadata : IndirectCallResolution)
      (coercions : metadata.argumentCoercions = []) : Form (.call callee arguments (.indirect metadata))

structure Site {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : Form node.form
  coercions : node.coercions = []
  requirements : (match node.form with | .integerLiteral .. => True | _ => node.requirements = [])
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  ordinary : ∀ name binder, node.form = .reference name (.local binder) →
    prepared.base.locals.bindings.any (fun binding =>
      decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false

private def form? (form : ExpressionForm) : Option (PLift (Form form)) :=
  match form with
  | .integerLiteral literal resolution => some ⟨.literal (.integer literal resolution)⟩
  | .reference name (.builtinBoolean value) => some ⟨.literal (.bool name value)⟩
  | .literal literal => some ⟨.literal (.word literal)⟩
  | .tuple [] => some ⟨.literal .unit⟩
  | .reference name (.local binder) => some ⟨.read name binder⟩
  | .group inner => some ⟨.group inner⟩
  | .tuple [left, right] => some ⟨.pair left right⟩
  | .call callee arguments (.indirect metadata) =>
    if empty : metadata.argumentCoercions = [] then some ⟨.call callee arguments metadata empty⟩ else none
  | _ => none

private def ordinary? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (node : ExpressionNode) :
    Option (PLift (∀ name binder, node.form = .reference name (.local binder) →
      prepared.base.locals.bindings.any (fun binding =>
        decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false)) := by
  cases form : node.form
  case reference name resolution =>
    cases resolution
    case «local» binder =>
      exact if ordinary : prepared.base.locals.bindings.any (fun binding =>
          decide (binding.caller = named.signature.key ∧ binding.binder.id = binder)) = false then
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
  if empty : node.requirements = [] then
    some ⟨by split <;> simp_all⟩
  else
    match form : node.form with
    | .integerLiteral .. => some ⟨True.intro⟩
    | _ => none

def site? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) : Option (Site prepared named source id) :=
  match found : source.lookupExpression? id with
  | none => none
  | some node => do
    let ⟨form⟩ ← form? node.form
    if coercions : node.coercions = [] then do
      let ⟨requirements⟩ ← requirements? node
      if notInitializer : prepared.base.locals.bindings.find? (fun binding =>
          decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none then do
        let ⟨ordinary⟩ ← ordinary? prepared named node
        pure ⟨node, found, form, coercions, requirements, notInitializer, ordinary⟩
      else none
    else none

inductive Syntax {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) : ExpressionId → Prop where
  | literal {id} (site : Site prepared named source id)
      (atomic : CompatibleExpressionLiterals.Atomic site.node.form) : Syntax prepared named source id
  | read {id name binder} (site : Site prepared named source id)
      (form : site.node.form = .reference name (.local binder)) : Syntax prepared named source id
  | generalized {id} (observed : GeneralizedLocalNamedReadCompilation.Observations prepared named source id)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source id) :
      Syntax prepared named source id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Syntax prepared named source inner) : Syntax prepared named source id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Syntax prepared named source left) (second : Syntax prepared named source right) :
      Syntax prepared named source id
  | call {id callee arguments metadata} (site : Site prepared named source id)
      (form : site.node.form = .call callee arguments (.indirect metadata))
      (calleeObserved : GeneralizedLocalNamedReadCompilation.Observations prepared named source callee)
      (calleeRecipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source callee)
      (children : ∀ child ∈ arguments, Syntax prepared named source child) : Syntax prepared named source id

private def all? {α : Type} (predicate : α → Prop)
    (check : (item : α) → Option (PLift (predicate item))) :
    (items : List α) → Option (PLift (∀ item ∈ items, predicate item))
  | [] => some ⟨by intro item member; cases member⟩
  | first :: rest => do
    let ⟨head⟩ ← check first
    let ⟨tail⟩ ← all? predicate check rest
    pure ⟨by
      intro item member
      rcases List.mem_cons.mp member with same | member
      · exact same ▸ head
      · exact tail item member⟩

def syntax? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Syntax prepared named source id))
  | 0, _ => none
  | fuel + 1, id =>
    match GeneralizedLocalNamedReadCompilation.observations? prepared named source id with
    | some observed => do
      let recipe ← GeneralizedLocalNamedRecipeCompilation.observations? prepared named source id
      pure ⟨.generalized observed recipe⟩
    | none => do
      let site ← site? prepared named source id
      match form : site.node.form with
      | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
      | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
      | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
      | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
      | .reference _name (.local _binder) => pure ⟨.read site form⟩
      | .group inner => do
        let ⟨child⟩ ← syntax? prepared named source fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← syntax? prepared named source fuel left
        let ⟨second⟩ ← syntax? prepared named source fuel right
        pure ⟨.pair site form first second⟩
      | .call callee arguments (.indirect _metadata) => do
        let calleeObserved ← GeneralizedLocalNamedReadCompilation.observations? prepared named source callee
        let calleeRecipe ← GeneralizedLocalNamedRecipeCompilation.observations? prepared named source callee
        let ⟨children⟩ ← all? (Syntax prepared named source) (syntax? prepared named source fuel) arguments
        pure ⟨.call site form calleeObserved calleeRecipe children⟩
      | _ => none

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax
