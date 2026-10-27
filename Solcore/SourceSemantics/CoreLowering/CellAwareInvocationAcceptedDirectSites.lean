import Solcore.SourceSemantics.CoreLowering.CellAwareNamedExpressionPolicies
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates

/-! Direct declaration calls of named-row bodies as compiler sites. A direct
site has no coercions or requirements, is not a generalized initializer,
selects a monomorphic declaration and lies in a row without evidence
assumptions, so the named policy's special callback
declines it and its read policy is the compatible reader, as for the ordinary
sites of `CellAwareNamedExpressionSyntax.Site`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
namespace Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
open Core Frontend SourceInference
open CallableIndexedNamedGeneration (Prepared Compilation context representation)
open GeneralizedLocalInitializerCompilation (namedPolicy namedLowerBody)

/-- A direct declaration call of a named-row body. -/
structure DirectSite {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : Prepared checked) (named : SourceCoreGeneralFunctions.Function)
    (source : TypedSource) (id : ExpressionId) (callee : ExpressionId) (arguments : List ExpressionId)
    (instantiation : DeclarationInstantiation) where
  node : ExpressionNode
  found : source.lookupExpression? id = some node
  form : node.form = .call callee arguments (.declaration instantiation)
  coercions : node.coercions = []
  requirements : node.requirements = []
  notInitializer : prepared.base.locals.bindings.find? (fun binding =>
    decide (binding.caller = named.signature.key ∧ binding.initializer = id)) = none
  monomorphic : CallableIndexedOwnedPreparedStagedDirectCallCertificates.Monomorphic instantiation
  assumptions : named.specialized.assumptions = []

variable {checked : SourceCoreCompatibleCatalog.Checked} {prepared : Prepared checked}
  {named : SourceCoreGeneralFunctions.Function} {source : TypedSource} {id callee : ExpressionId}
  {arguments : List ExpressionId} {instantiation : DeclarationInstantiation}

theorem contextual (site : DirectSite prepared named source id callee arguments instantiation) :
    SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      (context prepared named).plan prepared.base.locals named.signature.key none source id = .ok source := by
  simp [SourceCoreGeneralFunctions.contextualSource, site.found, site.form]

private theorem evidence_none (site : DirectSite prepared named source id callee arguments instantiation)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized (context prepared named) child budget source scope id reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) = .ok none := by
  simp [SourceCoreEvidence.lowerWithProjector, site.found, site.form, site.requirements, site.coercions,
    site.assumptions]

variable {diagnostics : SourceCoreDataPlaceFaultSites.Program} {code : Expr}
  (compiled : Compilation prepared named diagnostics code)

/-- The named policy's special callback declines a direct site. -/
theorem special (site : DirectSite prepared named source id callee arguments instantiation) (rootFuel : Nat)
    (child : SourceCoreFunctions.ExpressionLowerer) (budget : Nat) (scope : SourceCoreLocalCell.Scope)
    (reasonAt : ExpressionId → Word) :
    CallableIndexedOwnedContextualLambdaPolicyRecipes.special compiled rootFuel
      (context prepared named) child budget source scope id reasonAt = .ok none := by
  unfold CallableIndexedOwnedContextualLambdaPolicyRecipes.special
  have ownerEq : (context prepared named).owner = named.signature.key := rfl
  simp only [ownerEq, contextual site, bind, Except.bind, pure, Except.pure, site.found,
    site.notInitializer, Option.filter_none]
  rw [evidence_none site child budget scope reasonAt]
  simp [site.form]

theorem read (site : DirectSite prepared named source id callee arguments instantiation) (rootFuel : Nat) :
    (namedPolicy compiled rootFuel).readExpression source id =
      SourceCoreCompatibleDataExpressions.readExpression checked source id := by
  simp only [namedPolicy, contextual site, bind, Except.bind]
  rfl

end Solcore.SourceSemantics.CoreLowering.CellAwareInvocationAcceptedDirectSites
