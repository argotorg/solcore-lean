import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes

/-! The same contextual compilation retains its actual public diagnostic issuer.
Body and expression policy receipts share that exact compilation witness. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
open Core Frontend SourceInference
open CallableIndexedNamedGeneration CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- Only the real compatible issuer's complete base table is retained; the
existing optional callable root-table replacement preserves this identity. -/
def IssuedAt (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (diagnostics : SourceCoreDataPlaceFaultSites.Program) : Prop :=
  ∃ issued : SourceCoreCompatibleDataPlaceFaultSites.Program (.initial checked),
    prepared.base.diagnostics = some issued ∧ diagnostics.base = issued.program.base

/-- One actual compilation supplies the body, the full root policy, and the
issued assignment inventory. Nested lambdas keep that same witness. -/
def Retained (named : Named) (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : Compilation prepared named diagnostics namedCode) (rootFuel : Nat),
    IssuedAt prepared diagnostics ∧
      CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code ∧
      CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel code.policy ∧
      code.compilation = context prepared named

theorem Retained.of_recipes
    (compilation : Compilation prepared named diagnostics namedCode)
    (issued : IssuedAt prepared diagnostics)
    {code : Code prepared function scope administrative} {rootFuel : Nat}
    (body : CallableIndexedOwnedContextualLambdaBodyRecipes.BodyRecipe compilation code)
    (policy : CallableIndexedOwnedContextualLambdaPolicyRecipes.PolicyRecipe compilation rootFuel code.policy)
    (sameCompilation : code.compilation = context prepared named) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, rootFuel, issued, body, policy, sameCompilation⟩

theorem Retained.body_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaBodyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, _, _, body, _, _⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, body⟩

theorem Retained.policy_recipe {code : Code prepared function scope administrative}
    (retained : Retained named code) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.Retained named code := by
  obtain ⟨diagnostics, namedCode, compilation, rootFuel, _, body, policy, same⟩ := retained
  exact ⟨diagnostics, namedCode, compilation, rootFuel, body, policy, same⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaIssuedRecipes
