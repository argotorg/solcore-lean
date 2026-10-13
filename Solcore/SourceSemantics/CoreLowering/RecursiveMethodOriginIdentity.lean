import Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity

/-! Ordered dictionary identity depends on the concrete caller and selected
evidence roots. Unrelated valid implementations are outside this condition. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

def Coherent (caller : EvidenceEnvironment) (roots : List TraitEvidence)
    (goals : List ProgramPredicate) : Prop :=
  ∀ goal ∈ goals, ∀ left right,
    EvidenceEntryOriginates caller roots goal left →
    EvidenceEntryOriginates caller roots goal right → left = right

theorem assembled_functional {caller left right : EvidenceEnvironment}
    {roots : List TraitEvidence} {goals : List ProgramPredicate}
    (coherent : Coherent caller roots goals)
    (first : EvidenceEnvironment.AssembledFrom caller roots goals left)
    (second : EvidenceEnvironment.AssembledFrom caller roots goals right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | cons head _ induction =>
    cases second with
    | cons other tail =>
      have same := coherent _ (by simp) _ _ head other
      cases same
      exact congrArg (List.cons _) (induction
        (fun goal member => coherent goal (by simp [member])) tail)

theorem requirements_functional {context : Context} {caller : EvidenceEnvironment}
    {ids : List RequirementId} {leftGoals rightGoals : List ProgramPredicate}
    {left right : EvidenceEnvironment}
    (unique : RequirementIdsUnique context)
    (first : RequirementsProduceEnvironment context caller ids leftGoals left)
    (second : RequirementsProduceEnvironment context caller ids rightGoals right) :
    leftGoals = rightGoals ∧ left = right := by
  induction first generalizing rightGoals right with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons head _ induction =>
    cases second with
    | cons other tail =>
      obtain ⟨rfl, rfl⟩ := CallableCoercionSelectionIdentity.requirement_functional
        (fun _ _ => unique.contains_unique) head other
      obtain ⟨rfl, rfl⟩ := induction tail
      exact ⟨rfl, rfl⟩

/-- The exact primary and method requirements produce these roots in order. -/
inductive RootsProduced (context : Context) (caller : EvidenceEnvironment) :
    List RequirementId → List TraitEvidence → Prop where
  | intro {primary : RequirementId} {rest : List RequirementId}
      {goal : ProgramPredicate} {tree : TraitEvidence}
      {goals : List ProgramPredicate} {dictionary : EvidenceEnvironment}
      (head : RequirementProducesEvidence context caller primary goal tree)
      (tail : RequirementsProduceEnvironment context caller rest goals dictionary) :
      RootsProduced context caller (primary :: rest) (tree :: dictionary.map Prod.snd)

theorem RootsProduced.functional {context : Context} {caller : EvidenceEnvironment}
    {ids : List RequirementId} {left right : List TraitEvidence}
    (unique : RequirementIdsUnique context)
    (first : RootsProduced context caller ids left)
    (second : RootsProduced context caller ids right) : left = right := by
  cases first with
  | intro head tail =>
    cases second with
    | intro other remaining =>
      obtain ⟨_, rfl⟩ := CallableCoercionSelectionIdentity.requirement_functional
        (fun _ _ => unique.contains_unique) head other
      obtain ⟨_, rfl⟩ := requirements_functional unique tail remaining
      rfl

theorem selected_assembly {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {ids : List RequirementId} {body : BodyInstance}
    (selected : OperatorMethodSelected program context caller traitName methodName ids body dictionary) :
    ∃ roots, RootsProduced context caller ids roots ∧
      EvidenceEnvironment.AssembledFrom caller roots body.context.assumptions dictionary := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ requirements instantiated assembled _ =>
    cases selects with
    | intro produced _ =>
      refine ⟨_, .intro produced requirements, ?_⟩
      cases instantiated with
      | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
        rw [contextEq]
        exact assembled

/-- Independent Source selection reuses exactly the actual caller and roots.
Only their finite reachable alternatives must agree. -/
theorem same_from_origins {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance}
    {expectedDictionary actualDictionary : EvidenceEnvironment} {roots : List TraitEvidence}
    (unique : RequirementIdsUnique context)
    (produced : RootsProduced context caller (primary :: rest) roots)
    (expected : OperatorMethodSelected program context caller traitName methodName
      (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName
      (primary :: rest) actualBody actualDictionary)
    (coherent : Coherent caller roots expectedBody.context.assumptions) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog
    (fun _ _ => unique.contains_unique) actual expected
  obtain ⟨expectedRoots, expectedProduced, expectedAssembly⟩ := selected_assembly expected
  obtain ⟨actualRoots, actualProduced, actualAssembly⟩ := selected_assembly actual
  have expectedEq := expectedProduced.functional unique produced
  have actualEq := actualProduced.functional unique produced
  subst expectedRoots actualRoots
  refine ⟨same, assembled_functional coherent ?_ expectedAssembly⟩
  simpa only [same] using actualAssembly

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodOriginIdentity
