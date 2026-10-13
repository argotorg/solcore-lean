import Solcore.SourceSemantics.CoreLowering.CallableCoercionSelectionIdentity

/-! Independent method selection retains an ordered dictionary assembled for
exactly the method assumptions. Empty method assumptions therefore determine
that dictionary; nonempty dictionaries are not equated from body identity. -/
set_option autoImplicit false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- This follows from the real selected method's assembly, not from evidence
coverage (which may also hold for a larger dictionary). -/
theorem dictionary_empty {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance}
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary)
    (empty : body.context.assumptions = []) : dictionary = [] := by
  cases selected with
  | intro _ _ _ _ _ _ _ _ _ _ _ instantiated assembled _ =>
    cases instantiated with
    | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
      have assumptions := congrArg Context.assumptions contextEq
      change body.context.assumptions = _ at assumptions
      have goalsEmpty := assumptions.symm.trans empty
      dsimp [declarationContext, Context.withSolvedRequirements, Context.withAssumptions, Context.forDeclaration, Context.ofSignatures, Context.withResidualTypeVariables] at goalsEmpty
      rw [goalsEmpty] at assembled
      cases assembled
      rfl

/-- The actual catalog and reached primary requirement identify the method
body. Its genuine empty assumption list also identifies the full dictionary. -/
theorem same_empty {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance} {expectedDictionary actualDictionary : EvidenceEnvironment}
    (unique : ∀ first second, ContainsRequirement context primary first → ContainsRequirement context primary second → first = second)
    (expected : OperatorMethodSelected program context caller traitName methodName (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName (primary :: rest) actualBody actualDictionary)
    (empty : expectedBody.context.assumptions = []) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog unique actual expected
  refine ⟨same, ?_⟩
  exact (dictionary_empty actual (by simpa only [same] using empty)).trans (dictionary_empty expected empty).symm

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity
