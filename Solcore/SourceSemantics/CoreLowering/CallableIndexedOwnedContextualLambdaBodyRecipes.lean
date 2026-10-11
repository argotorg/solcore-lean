import Solcore.SourceSemantics.CoreLowering.CallableIndexedNamedGeneration
import Solcore.SourceSemantics.CoreLowering.CallableIndexedLambdaValues

/-! An exact production lowerer recipe is retained as a static proposition.
Its existential compilation is the one used at the same original Site.
Recapture preserves the lowerer; no compiler result or execution law is added. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
open Core Frontend SourceInference
open CallableIndexedLambdaValues

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked}
  {named : CallableIndexedNamedGeneration.Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {function : Dynamic.Closure} {scope : SourceCoreLocalCell.Scope} {administrative : Core.Context}

/-- The literal equation returned by the original contextual producer. -/
def BodyRecipe
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode)
    (code : Code prepared function scope administrative) : Prop :=
  code.lowerBody = SourceCoreGeneralFunctions.bodyLowererWithRepresentation
    ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
    (CallableIndexedNamedGeneration.context prepared named).solvedRequirements compilation.own.assignments diagnostics
    (CallableIndexedNamedGeneration.context prepared named).owner
    (SourceCoreGeneralFunctions.contextualBinder
      ((CallableIndexedNamedGeneration.representation prepared).atContext named.signature.key [])
      prepared.base.locals named.signature.key [])

/-- The selected compiler data stays inside Prop, at the exact named seed and Code. -/
def Retained (named : CallableIndexedNamedGeneration.Named)
    (code : Code prepared function scope administrative) : Prop :=
  ∃ (diagnostics : SourceCoreDataPlaceFaultSites.Program) (namedCode : Expr)
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode),
    BodyRecipe compilation code

/-- Existing exact recipes enter the retained proposition without selecting another Site. -/
theorem Retained.of_recipe
    (compilation : CallableIndexedNamedGeneration.Compilation prepared named diagnostics namedCode)
    {code : Code prepared function scope administrative}
    (recipe : BodyRecipe compilation code) : Retained named code :=
  ⟨diagnostics, namedCode, compilation, recipe⟩

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaBodyRecipes
