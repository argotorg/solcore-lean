import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles

/-! Original direct-call forms bypass contextual source normalization. Original
leaf forms construct their own syntax before using the retained metadata profile.
Neither producer requires a supplied recursive expression grammar. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedPreparedStagedRecursiveCallerCertificates (GeneralSyntax)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)

variable {checked : SourceCoreCompatibleCatalog.Checked}
  {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
  {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation prepared named diagnostics namedCode}
  {rootFuel : Nat} {policy : SourceCoreFunctions.Policy}
  {source : TypedSource} {id : ExpressionId} {node : ExpressionNode}

/-- A declaration call cannot enter local-reference normalization. The same
actual policy therefore reads its original Source occurrence directly. -/
theorem direct_read (recipe : PolicyRecipe compilation rootFuel policy)
    {callee : ExpressionId} {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation)) :
    policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  have same : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals (context prepared named).owner
      none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  rw [recipe.readExpression]
  simp only [same, bind, Except.bind]
  rfl

/-- Leaf syntax follows from the original read or atomic form. The existing
metadata profile then determines the actual reader and special callback at this
occurrence; no independent child grammar or local-read premise is supplied. -/
theorem leaf_profile (recipe : PolicyRecipe compilation rootFuel policy)
    {directSites : DeclarationInstantiation → Prop}
    (metadata : MetadataFor prepared named source directSites)
    (found : source.lookupExpression? id = some node)
    (form : CompatibleExpressionLiterals.Atomic node.form ∨
      ∃ name binder, node.form = .reference name (.local binder))
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat)
    (scope : SourceCoreLocalCell.Scope) (reasonAt : ExpressionId → Word) :
    GeneralSyntax source id directSites ∧
      policy.readExpression source id = SourceCoreCompatibleDataExpressions.readExpression checked source id ∧
      (match policy.lowerSpecial? with
        | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
        | some lower => lower (context prepared named) child budget source scope id reasonAt) = .ok none := by
  have leaf : CompatibleExpressionProducts.Syntax source id := by
    rcases form with atomic | ⟨name, binder, localForm⟩
    · exact .literal found atomic
    · exact .read found localForm
  refine ⟨.leaf leaf, ?_, ?_⟩
  · exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.read_policy recipe metadata (.leaf leaf)
  · rw [recipe.lowerSpecial]
    exact CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles.special_none
      compilation rootFuel metadata (.leaf leaf) (GeneralSyntax.leaf_nonDirect leaf)
      (GeneralSyntax.leaf_nonOperator leaf) child budget scope reasonAt

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionPolicy
