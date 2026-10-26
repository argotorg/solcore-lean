import Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedExpressions

/-! A finite check of the closed expression subset. It reads only a row's
Source nodes and the prepared local inventory, so it runs on an actually
compiled program, and its result is a proof that every expression node of the
row is a site of `CellAwareInvocationAcceptedExpressionTrees.Subset`. A site
depends on its row only through the row's key, so the proof transports to every
row with that key; `closed` turns it into `Closed` for the row's accepted-body
index. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)
open CellAwareInvocationAcceptedExpressionTrees (Subset)

/-- Proof-producing recognition of one subset site and its children. -/
def subset? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    (fuel : Nat) → (id : ExpressionId) → Option (PLift (Subset prepared named source id))
  | 0, _ => none
  | fuel + 1, id => do
    let site ← site? prepared named source id
    match form : site.node.form with
    | .integerLiteral literal resolution => pure ⟨.literal site (form ▸ .integer literal resolution)⟩
    | .reference name (.builtinBoolean value) => pure ⟨.literal site (form ▸ .bool name value)⟩
    | .literal literal => pure ⟨.literal site (form ▸ .word literal)⟩
    | .tuple [] => pure ⟨.literal site (form ▸ .unit)⟩
    | .reference _name (.local _binder) => pure ⟨.read site form⟩
    | .unary _operator operand => do
      let ⟨child⟩ ← subset? prepared named source fuel operand
      pure ⟨.unary site form child⟩
    | .binary left _operator right => do
      let ⟨first⟩ ← subset? prepared named source fuel left
      let ⟨second⟩ ← subset? prepared named source fuel right
      pure ⟨.binary site form first second⟩
    | .conditional condition thenId elseId => do
      let ⟨test⟩ ← subset? prepared named source fuel condition
      let ⟨yes⟩ ← subset? prepared named source fuel thenId
      let ⟨no⟩ ← subset? prepared named source fuel elseId
      pure ⟨.conditional site form test yes no⟩
    | .group inner => do
      let ⟨child⟩ ← subset? prepared named source fuel inner
      pure ⟨.group site form child⟩
    | .tuple [left, right] => do
      let ⟨first⟩ ← subset? prepared named source fuel left
      let ⟨second⟩ ← subset? prepared named source fuel right
      pure ⟨.pair site form first second⟩
    | _ => none

private def sweep? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource)
    (fuel : Nat) :
    (nodes : List Node) → Option (PLift (∀ node, Node.expression node ∈ nodes → Subset prepared named source node.id))
  | [] => some ⟨by intro node member; cases member⟩
  | .expression node :: rest => do
    let ⟨head⟩ ← subset? prepared named source fuel node.id
    let ⟨tail⟩ ← sweep? prepared named source fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
        exact head
      · exact tail other member⟩
  | .statement _ :: rest => do
    let ⟨tail⟩ ← sweep? prepared named source fuel rest
    pure ⟨by
      intro other member
      rcases List.mem_cons.mp member with same | member
      · cases same
      · exact tail other member⟩

/-- Every expression node of the Source is a subset site. The fuel bounds the
depth of the expression graph, which the node count bounds. -/
def nodes? {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function) (source : TypedSource) :
    Option (PLift (∀ id node, source.lookupExpression? id = some node → Subset prepared named source id)) := do
  let ⟨all⟩ ← sweep? prepared named source (source.nodes.length + 1) source.nodes
  pure ⟨by
    intro id node found
    obtain ⟨member, same⟩ := lookupExpression?_sound found
    exact same ▸ all node member⟩

section Transport
variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked} {source : TypedSource}
  {first second : SourceCoreGeneralFunctions.Function}

/-- A site retains its node and changes only the key of its local-inventory
lookups. -/
def transportSite (keyEq : first.signature.key = second.signature.key) {id : ExpressionId}
    (site : Site prepared first source id) : Site prepared second source id where
  node := site.node
  found := site.found
  form := site.form
  coercions := site.coercions
  requirements := site.requirements
  notInitializer := keyEq ▸ site.notInitializer
  ordinary := keyEq ▸ site.ordinary

/-- `Subset` depends on its row only through the row's key. -/
theorem transport (keyEq : first.signature.key = second.signature.key) {id : ExpressionId}
    (subset : Subset prepared first source id) : Subset prepared second source id := by
  induction subset with
  | literal site atomic => exact .literal (transportSite keyEq site) atomic
  | read site form => exact .read (transportSite keyEq site) form
  | unary site form _ child => exact .unary (transportSite keyEq site) form child
  | binary site form _ _ left right => exact .binary (transportSite keyEq site) form left right
  | conditional site form _ _ _ test yes no => exact .conditional (transportSite keyEq site) form test yes no
  | group site form _ child => exact .group (transportSite keyEq site) form child
  | pair site form _ _ left right => exact .pair (transportSite keyEq site) form left right
end Transport

/-- A named row whose every expression node is a subset site, checked at any
row with the same key, is closed. -/
theorem closed {whole : SourceCoreUnifiedCompilation.Compiled} {named : SourceCoreGeneralFunctions.Function}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
    (generation : CallableIndexedNamedGeneration.Compilation whole.indexed named diagnostics code)
    (record : SourceCompilationPlan.exactSpecialization whole.indexed.base.plan named.signature.key =
      .ok named.specialized)
    {checkedRow : SourceCoreGeneralFunctions.Function} (keyEq : checkedRow.signature.key = named.signature.key)
    (nodes : ∀ id node, (CallableIndexedNamedGeneration.source named).lookupExpression? id = some node →
      Subset whole.indexed checkedRow (CallableIndexedNamedGeneration.source named) id) :
    CellAwareInvocationAcceptedExpressions.Closed
      (ActualBodyInvocation.Index.named generation record :
        ActualBodyInvocation.Index whole ActualBodyInvocation.ReachedView) :=
  CellAwareInvocationAcceptedExpressions.closed_of_nodes _ fun id node found =>
    transport keyEq (nodes id node found)

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedSubsetCheck
