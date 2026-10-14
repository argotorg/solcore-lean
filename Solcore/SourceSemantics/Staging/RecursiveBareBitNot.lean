import Solcore.SourceSemantics.Staging.RecursiveBareTarget

/-! Bare unary updates have no projection or right-hand expression. A failed
leaf therefore retains exactly its incoming heap. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.Staging.Recursive
open Frontend Frontend.SourceInference Solcore.SourceSemantics.Dynamic

theorem bitNot_fault_heap {program : Program} {context : Context}
    {evidence : EvidenceEnvironment} {source : TypedSource}
    {environment : Environment} {before after : Heap} {place : PlaceResolution}
    {reason : SemanticFault} (bare : place.projections = [])
    (failed : SourcePlaceBitNotFaults program context evidence source environment
      before place reason after) : after = before := by
  cases failed with
  | target failed =>
    cases failed with
    | unbound | dangling => rfl
    | projectionExpression _ _ failed => rw [bare] at failed; cases failed
    | danglingAfterProjections _ _ evaluated _
    | projectionRead _ _ evaluated _ _ _
    | uninitialized _ _ evaluated _ _ _ _ =>
      rw [bare] at evaluated
      cases evaluated
      rfl
  | uninitialized resolved _ | operand resolved _ _ =>
    exact (BareTarget.of_resolves bare resolved).1.symm

end Solcore.SourceSemantics.Staging.Recursive
