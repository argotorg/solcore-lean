import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax

/-! Actual factory output syntax whose leaves are specialized generalized
reads. The scanner retains every original observation and ordered child. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionSyntax
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared)
open CellAwareNamedExpressionSyntax (Site site?)

inductive Syntax {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) : ExpressionId → Prop where
  | generalized {id} (observed : GeneralizedLocalNamedReadCompilation.Observations prepared named source id)
      (recipe : GeneralizedLocalNamedRecipeCompilation.Observations prepared named source id) :
      Syntax prepared named source id
  | group {id inner} (site : Site prepared named source id) (form : site.node.form = .group inner)
      (child : Syntax prepared named source inner) : Syntax prepared named source id
  | pair {id left right} (site : Site prepared named source id) (form : site.node.form = .tuple [left, right])
      (first : Syntax prepared named source left) (second : Syntax prepared named source right) :
      Syntax prepared named source id

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
      | .group inner => do
        let ⟨child⟩ ← syntax? prepared named source fuel inner
        pure ⟨.group site form child⟩
      | .tuple [left, right] => do
        let ⟨first⟩ ← syntax? prepared named source fuel left
        let ⟨second⟩ ← syntax? prepared named source fuel right
        pure ⟨.pair site form first second⟩
      | _ => none

end Solcore.SourceSemantics.CoreLowering.CellAwareMaterializedExpressionSyntax
