import Solcore.SourceSemantics.CoreLowering.CallableAncestryPairedRecipes

#check_failure Solcore.Frontend.SourceTypedRuntime.run

/-! The actual final edge checker suffices for all recipe factories. Cached
selection then needs no runtime substitution or evidence resolution. -/
set_option autoImplicit false
namespace Tests.SourceCoreCallableAncestryPairedRecipes
open Solcore Solcore.Frontend
open Solcore.SourceSemantics.CoreLowering
open CallableAncestryPairedLookup CallableAncestryPairedRecipes

example {checked : Checked} {base : Base checked} {inputs : Inputs base} {table : Table}
    (validated : SourceCoreCallableAncestryPairedPreparation.valid inputs table = true) :
    ∃ recipes, table.views.attach.mapM (fun edge =>
      SourceCoreCallableAncestryPairedPreparation.prepareRecipe inputs table edge.val edge.property) = .ok recipes :=
  recipes_total validated

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {caller lexical destination : Nat} {id target : Core.Word}
    (selected : prepared.table.viewAt? caller lexical id target = some destination) :
    ∃ recipe, prepared.recipeAt? caller lexical id target = some recipe := recipeAt_complete prepared selected

example {checked : Checked} {base : Base checked}
    (prepared : SourceCoreCallableAncestryPairedPreparation.Prepared base)
    {edge : SourceCoreCallableAncestryPairedCache.ViewEdge} (member : edge ∈ prepared.table.views) :
    ∃ recipe ∈ prepared.recipes, recipe.edge = edge := prepared_recipe_member prepared member

end Tests.SourceCoreCallableAncestryPairedRecipes
