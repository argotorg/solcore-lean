import Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedAssignmentAdmission
import Solcore.SourceSemantics.Staging.RecursiveBareTarget

/-! A plain bare write needs only the successful RHS admission and the
original writable lexical target. It does not rerun whole-program preservation.
The real write retains the captured cell type even if the RHS changed its value. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
open Frontend SourceInference Staging.Recursive

/-- The actual current-cell write preserves deep heap typing at the exact RHS
endpoint. Both raw type identities come from the accepted Source assignment. -/
theorem heap_after_equal
    {source : TypedSource} {context : SourceSemantics.Context}
    {assignment : AssignmentResolution} {rhs : ExpressionId} {node : ExpressionNode}
    {environment : Dynamic.Environment} {before middle after : Dynamic.Heap}
    {target : Dynamic.ResolvedPlace} {right updated : Dynamic.Value}
    (unique : NodeOccurrencesUnique source)
    (found : source.lookupExpression? rhs = some node)
    (typed : SourceAssignmentHasType source context assignment .equal rhs)
    (locals : Dynamic.EnvironmentAgrees before context.locals environment)
    (snapshot : BareTarget environment before assignment.target target)
    (heapTyped : Dynamic.HeapWellTyped context middle)
    (rightTyped : Dynamic.ValueHasType context middle right node.type)
    (write : Dynamic.ResolvedPlaceWrites
      (fun _ replacement => Dynamic.AssignmentValueApplies .equal target.selected right replacement)
      middle target updated after) :
    Dynamic.HeapWellTyped context after := by
  cases typed with
  | wordCompound operator _ _ _ => cases operator
  | equal targetTyped rhsTyped _ =>
    obtain ⟨actual, contains, storedType⟩ := rhsTyped.stored_type
    have sameNode : actual = node := Option.some.inj
      ((lookupExpression?_complete unique contains).symm.trans found)
    subst actual
    cases snapshot with
    | intro bare lookup read initial =>
      cases targetTyped with
      | intro writable projections _ =>
        rw [bare] at projections
        cases projections
        obtain ⟨scheme, staticLookup, _schemeTyped, _mono, bodyType⟩ := writable.scheme
        obtain ⟨location, cell, typedLookup, typedRead, cellType, _storage⟩ := locals.lookup staticLookup
        cases lookup.functional typedLookup
        cases read.functional typedRead
        cases write with
        | intro currentRead currentType _ update written =>
          cases update with
          | leaf modified =>
            cases modified
            refine Dynamic.HeapWellTyped.write heapTyped currentRead (.some ?_) written
            rw [currentType, cellType, bodyType, ← storedType]
            exact rightTyped

end Solcore.SourceSemantics.CoreLowering.CallableIndexedOwnedBareAssignmentAdmission
