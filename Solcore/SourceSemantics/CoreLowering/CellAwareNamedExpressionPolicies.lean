import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionSyntax

/-! Ordinary sites derive their actual named compiler policy from finite raw
metadata observations. The generalized read branch retains its distinct
successful override and is never assigned an ordinary bypass law. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)
open CellAwareNamedExpressionSyntax (Site Form)

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id : ExpressionId}

theorem contextual (site : Site prepared named source id) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic =>
    cases atomic <;> simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]
  | read name binder =>
    have ordinary := site.ordinary name binder shape
    simp only [SourceCoreGeneralFunctions.contextualSource, site.found, bind, Except.bind, pure, Except.pure, shape, ordinary, Bool.false_eq_true, ↓reduceIte]
  | builtin name function | group inner | pair left right | call callee arguments metadata coercions =>
    simp [SourceCoreGeneralFunctions.contextualSource, site.found, shape]

private theorem evidence_none (site : Site prepared named source id)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  have ordinary : SourceCompilationPlan.ordinaryOwnedRequirements? site.node = some site.node.requirements := by
    unfold SourceCompilationPlan.ordinaryOwnedRequirements?
    rw [site.coercions]
    change (if site.node.requirements.length < 0 then none else
      if site.node.requirements = site.node.requirements.take (site.node.requirements.length - 0) ++ [] then
        some (site.node.requirements.take (site.node.requirements.length - 0)) else none) = some site.node.requirements
    simp
  have supported := site.form
  have requirements := site.requirements
  generalize shape : site.node.form = form at supported requirements
  cases supported with
  | literal atomic =>
    cases atomic with
    | integer literal resolution =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, site.coercions]
    | unit | bool name value | word literal =>
      simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  | builtin name function | read name binder | group inner | pair left right =>
    simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions]
  | call callee arguments metadata coercions =>
    simp [SourceCoreEvidence.lowerWithProjector, site.found, shape, ordinary, requirements, site.coercions, coercions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- Only a real ordinary site has an empty special result. -/
theorem special (site : Site prepared named source id) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  have supported := site.form
  generalize shape : site.node.form = form at supported
  cases supported with
  | literal atomic => cases atomic <;> simp
  | read name binder =>
    simp only
    rw [site.ordinary name binder shape]
    rfl
  | builtin name function | group inner | pair left right | call callee arguments metadata coercions => simp

theorem read (site : Site prepared named source id) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
