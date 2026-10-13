import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedContextualLambdaPolicyRecipes
import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedPreparedStagedDirectCallCertificates

/-! The actual contextual direct-call hook either selects an original local
initializer or exposes the same evidence action on the original source. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualLambdaPolicyRecipes
open CallableIndexedOwnedPreparedStagedDirectCallCertificates

structure InitializerAt {checked : SourceCoreCompatibleCatalog.Checked}
    (prepared : CallableIndexedNamedGeneration.Prepared checked)
    (current : SourceCoreFunctions.Context) (id : ExpressionId) where
  binding : SourceCoreLocalPolymorphism.Binding
  found : (prepared.base.locals.bindings.find? fun candidate =>
    decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
      (fun _ => (none : Option ExpressionId) ≠ some id) = some binding

/-- The special callback is the one retained by the actual compilation recipe.
The residual keeps its precise initializer selection; otherwise the evidence
receipt retains the original callee, arguments, dictionary and output path. -/
theorem of_special
    {checked : SourceCoreCompatibleCatalog.Checked}
    {prepared : CallableIndexedNamedGeneration.Prepared checked} {named : Named}
    {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
    (compilation : Compilation prepared named diagnostics namedCode)
    {rootFuel fuel : Nat} {policy : SourceCoreFunctions.Policy}
    {body : SourceCoreFunctions.BodyLowerer} {current : SourceCoreFunctions.Context}
    {source : TypedSource} {scope : SourceCoreLocalCell.Scope}
    {id callee : ExpressionId} {arguments : List ExpressionId}
    {instantiation : DeclarationInstantiation} {node : ExpressionNode}
    {reasonAt : ExpressionId → Word} {output : SourceCoreBasic.LoweredExpr}
    (recipe : PolicyRecipe compilation rootFuel policy)
    (found : source.lookupExpression? id = some node)
    (form : node.form = .call callee arguments (.declaration instantiation))
    (accepted : (match policy.lowerSpecial? with
      | none => (Except.ok none : Except SourceCoreBasic.Error (Option SourceCoreBasic.LoweredExpr))
      | some lower => lower current (Child policy body fuel current)
          (fuel + 1) source scope id reasonAt) = .ok (some output)) :
    Nonempty (CallableCoercionExpressionCertificates.Direct prepared.base.sourceProgram
      ((representation prepared).atContext named.signature.key []).expressions.projectType
      named.specialized current (Child policy body fuel current) (fuel + 1)
      source scope id callee arguments instantiation reasonAt
      (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) node output) ∨
      Nonempty (InitializerAt prepared current id) := by
  rw [recipe.lowerSpecial] at accepted
  change special compilation rootFuel current (Child policy body fuel current)
    (fuel + 1) source scope id reasonAt = .ok (some output) at accepted
  have sameSource : SourceCoreGeneralFunctions.contextualSource prepared.base.sourceProgram
      current.plan prepared.base.locals current.owner none source id = .ok source := by
    simp [SourceCoreGeneralFunctions.contextualSource, found, form]
  unfold special at accepted
  simp only [sameSource, bind, Except.bind, found, pure, Except.pure] at accepted
  cases selected : (prepared.base.locals.bindings.find? fun candidate =>
      decide (candidate.caller = current.owner ∧ candidate.initializer = id)).filter
        (fun _ => (none : Option ExpressionId) ≠ some id) with
  | some binding => exact .inr ⟨⟨binding, selected⟩⟩
  | none =>
    rw [selected] at accepted
    cases evidence : SourceCoreEvidence.lowerWithProjector prepared.base.sourceProgram
        ((representation prepared).atContext named.signature.key []).expressions.projectType
        named.specialized current (Child policy body fuel current) (fuel + 1)
        source scope id reasonAt (SourceCoreGeneralFunctions.callablePolicy prepared.base.callableContext []) with
    | error error => simp [evidence] at accepted
    | ok value =>
      cases value with
      | none => simp [evidence, form] at accepted
      | some result =>
        simp only [evidence] at accepted
        cases accepted
        exact .inl (CallableCoercionExpressionCertificates.direct_of_accepted found form evidence)

end Solcore.SourceSemantics.CoreLowering.AcceptedContextualDirectReceipt
