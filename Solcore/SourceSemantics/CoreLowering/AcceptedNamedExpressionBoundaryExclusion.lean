import Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionSyntax

/-! A finite set of reached original occurrences excludes expression boundaries.
Closure follows actual ordered call arguments, without traversing callee names. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2400000
namespace Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
open Core Frontend SourceInference
open CallableIndexedNamedGeneration
open CallableIndexedOwnedContextualCompilerPolicyProfiles (RootPolicyReceipt)
open CallableIndexedOwnedPreparedStagedGeneralCallerMethodProfiles (MetadataFor)
open CallableIndexedOwnedPreparedStagedDirectCallCertificates (Child)

variable {compiled : SourceCoreUnifiedCompilation.Compiled}
  {named : Named} {diagnostics : SourceCoreDataPlaceFaultSites.Program} {namedCode : Expr}
  {compilation : Compilation compiled.indexed named diagnostics namedCode}
  {rootFuel : Nat} {rootSource : TypedSource} {rootScope : SourceCoreLocalCell.Scope}
  {rootId : ExpressionId} {rootReasonAt : ExpressionId → Word} {rootLowered : SourceCoreBasic.LoweredExpr}
  {root : RootPolicyReceipt (compiled := compiled) named diagnostics namedCode compilation
    rootFuel rootSource rootScope rootId rootReasonAt rootLowered}
  {source : TypedSource} {scope : SourceCoreLocalCell.Scope} {reasonAt : ExpressionId → Word}
  {fuel : Nat} {id : ExpressionId} {lowered : SourceCoreBasic.LoweredExpr}
  {directSites : DeclarationInstantiation → Prop} {reached : ExpressionId → Prop}

/-- Only original occurrences that are actually reached need these form facts. -/
def ReachedForms (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    LeafForm node.form ∨ DirectForm node.form

/-- Every argument occurrence is retained, including duplicate positions. -/
def ReachedArguments (source : TypedSource) (reached : ExpressionId → Prop) : Prop :=
  ∀ id node, reached id → source.lookupExpression? id = some node →
    ∀ callee arguments instantiation, node.form = .call callee arguments (.declaration instantiation) →
      ∀ argument ∈ arguments, reached argument

theorem Cause.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    {head : Head root.selected.policy root.selected.lowerBody fuel (context compiled.indexed named)
      source scope id reasonAt lowered}
    (cause : Cause root head) (present : reached id) : False := by
  have form := forms id head.node present head.found
  cases cause with
  | form _ notLeaf notDirect =>
    rcases form with leaf | direct
    · exact notLeaf leaf
    · exact notDirect direct
  | initializer _ selected => exact initializers id present ⟨selected⟩
  | special selected outside =>
    rcases form with leaf | direct
    · have profile := AcceptedNamedExpressionPolicy.leaf_profile root.compilerPolicy metadata
        head.found leaf.view (Child root.selected.policy root.selected.lowerBody fuel
          (context compiled.indexed named)) (fuel + 1) scope reasonAt
      have same := head.selected.symm.trans profile.2.2
      rw [selected] at same
      cases same
    · exact outside direct

theorem Step.child_reached
    (arguments : ReachedArguments source reached)
    (step : Step root source scope reasonAt fuel id lowered)
    (present : reached id) {entry : ExpressionId × SourceCoreBasic.LoweredExpr}
    (member : entry ∈ step.children) : reached entry.1 := by
  cases step with
  | leaf => cases member
  | boundary => cases member
  | ordinary head _ receipt =>
    exact arguments id receipt.node present receipt.metadata.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1
  | evidence head _ receipt =>
    exact arguments id head.node present receipt.found _ _ _ receipt.form
      entry.1 (List.of_mem_zip member).1

/-- The excluded endpoint belongs to this same trace and its actual child path. -/
theorem Boundary.impossible
    (metadata : MetadataFor compiled.indexed named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id →
      ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt compiled.indexed (context compiled.indexed named) id))
    (arguments : ReachedArguments source reached)
    {tree : Trace root source scope reasonAt fuel id lowered}
    (boundary : Boundary tree) (present : reached id) : False := by
  induction boundary with
  | here head cause children => exact cause.impossible metadata forms initializers present
  | child step children entry member next ih => exact ih (step.child_reached arguments present member)

/-- The Header residual is excluded by forms and actual argument reachability.
No recursive expression grammar is a premise. -/
theorem Residual.impossible {row : SourceSpecialization.SpecializedFunction}
    {prepared : RecursiveNamedPublicSpecializationMeaning.Prepared compiled row}
    {header : CallableIndexedOwnedFunctionValues.Header compiled (Program.ofChecked compiled.sourceProgram)}
    (residual : Residual prepared header directSites fuel source scope id lowered)
    (metadata : MetadataFor compiled.indexed prepared.named source directSites)
    (forms : ReachedForms source reached)
    (initializers : ∀ id, reached id → ¬ Nonempty (AcceptedContextualDirectReceipt.InitializerAt
      compiled.indexed (context compiled.indexed prepared.named) id))
    (arguments : ReachedArguments source reached)
    (present : reached id) : False :=
  residual.boundary.impossible metadata forms initializers arguments present

end Solcore.SourceSemantics.CoreLowering.AcceptedNamedExpressionFlow
