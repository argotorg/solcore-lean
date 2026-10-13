import Solcore.SourceSemantics.CoreLowering.RecursiveMethodSelectionIdentity

/-! Actual dictionary assembly retains an ordered, pointwise valid evidence
spine. Catalog uniqueness for the reached assumptions identifies that entire
spine, including repeated goals. -/
set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
open Frontend SourceInference Solcore.SourceSemantics.Dynamic

/-- Uniqueness is required only for the selected body's actual assumptions. -/
def Coherent (rules : List ProgramImplRule) (goals : List ProgramPredicate) : Prop :=
  ∀ goal ∈ goals, ∀ left right,
    EvidenceValid [] rules goal left → EvidenceValid [] rules goal right → left = right

theorem Coherent.empty (rules : List ProgramImplRule) : Coherent rules [] := by
  intro goal member
  cases member

/-- Every ordered entry carries its own validity, even when keys repeat. -/
def OrderedValid (rules : List ProgramImplRule) (goals : List ProgramPredicate)
    (dictionary : EvidenceEnvironment) : Prop :=
  Forall₂ (fun goal entry => entry.1 = goal ∧ EvidenceValid [] rules goal entry.2)
    goals dictionary

private theorem valid_member {rules : List ProgramImplRule}
    {goals : List ProgramPredicate} {trees : List TraitEvidence}
    (valid : Forall₂ (EvidenceValid [] rules) goals trees) :
    ∀ tree ∈ trees, EvidenceValid [] rules tree.goal tree := by
  induction valid with
  | nil => simp
  | cons head _ induction =>
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.evidence_goal_eq ▸ head
    · exact induction tree member

theorem subtree_valid {rules : List ProgramImplRule} {root tree : TraitEvidence}
    (valid : EvidenceValid [] rules root.goal root)
    (subtree : EvidenceSubtree root tree) :
    EvidenceValid [] rules tree.goal tree := by
  induction subtree with
  | self => exact valid
  | premise member _ induction =>
    cases valid with
    | implementation _ _ _ premises =>
      exact induction (valid_member premises _ member)

theorem origin_valid {rules : List ProgramImplRule}
    {caller : EvidenceEnvironment} {roots : List TraitEvidence}
    {goal : ProgramPredicate} {tree : TraitEvidence}
    (callerValid : caller.Valid rules)
    (rootsValid : ∀ root ∈ roots, EvidenceValid [] rules root.goal root)
    (origin : EvidenceEntryOriginates caller roots goal tree) :
    EvidenceValid [] rules goal tree := by
  cases origin with
  | caller found => exact callerValid _ _ found
  | root member subtree same =>
    exact same ▸ subtree_valid (rootsValid _ member) subtree

theorem assembled_valid {rules : List ProgramImplRule}
    {caller dictionary : EvidenceEnvironment} {roots : List TraitEvidence}
    {goals : List ProgramPredicate}
    (callerValid : caller.Valid rules)
    (rootsValid : ∀ root ∈ roots, EvidenceValid [] rules root.goal root)
    (assembled : EvidenceEnvironment.AssembledFrom caller roots goals dictionary) :
    OrderedValid rules goals dictionary := by
  induction assembled with
  | nil => exact .nil
  | cons head _ induction =>
    exact .cons ⟨rfl, origin_valid callerValid rootsValid head⟩ induction

private theorem requirements_valid {context : Context} {caller dictionary : EvidenceEnvironment}
    {ids : List RequirementId} {goals : List ProgramPredicate}
    (produced : RequirementsProduceEnvironment context caller ids goals dictionary) :
    ∀ tree ∈ dictionary.map Prod.snd,
      EvidenceValid [] context.signatures.resolutionRules tree.goal tree := by
  induction produced with
  | nil => simp
  | cons head _ induction =>
    intro tree member
    rcases List.mem_cons.mp member with rfl | member
    · exact head.evidence_goal_eq ▸ head.closed_valid
    · exact induction tree member

/-- Validity follows from the actual caller and selected roots, not merely
from first-match coverage of the returned dictionary. -/
theorem selected_valid {program : Program} {context : Context}
    {caller dictionary : EvidenceEnvironment} {traitName methodName : String}
    {requirements : List RequirementId} {body : BodyInstance}
    (signatures : context.signatures = program.signatures)
    (callerValid : caller.Valid program.signatures.resolutionRules)
    (selected : OperatorMethodSelected program context caller traitName methodName requirements body dictionary) :
    OrderedValid program.signatures.resolutionRules body.context.assumptions dictionary := by
  cases selected with
  | intro selects _ _ _ _ _ _ _ _ _ requirements instantiated assembled _ =>
    have valid := assembled_valid (assembled := assembled) callerValid (by
      intro root member
      rcases List.mem_cons.mp member with rfl | member
      · cases selects with
        | intro produced _ =>
          have rootValid := produced.closed_valid
          rw [← produced.evidence_goal_eq, signatures] at rootValid
          exact rootValid
      · simpa only [signatures] using requirements_valid requirements root member)
    cases instantiated with
    | intro _ _ _ _ _ _ _ _ _ _ _ contextEq =>
      rw [contextEq]
      exact valid

theorem ordered_functional {rules : List ProgramImplRule}
    {goals : List ProgramPredicate} {left right : EvidenceEnvironment}
    (coherent : Coherent rules goals)
    (first : OrderedValid rules goals left)
    (second : OrderedValid rules goals right) : left = right := by
  induction first generalizing right with
  | nil => cases second; rfl
  | @cons goal entry goals entries head tail induction =>
    cases second with
    | @cons _ other _ others otherHead otherTail =>
      have same : entry = other := Prod.ext (head.1.trans otherHead.1.symm)
        (coherent goal (by simp) _ _ head.2 otherHead.2)
      cases same
      exact congrArg (List.cons entry)
        (induction (fun goal member => coherent goal (by simp [member])) otherTail)

/-- Source body identity and reached catalog coherence determine the whole
independently assembled dictionary in its original order. -/
theorem same_coherent {program : Program}
    (catalog : CallableCoercionSelectionIdentity.Catalog program)
    {context : Context} {caller : EvidenceEnvironment}
    {traitName methodName : String} {primary : RequirementId} {rest : List RequirementId}
    {expectedBody actualBody : BodyInstance}
    {expectedDictionary actualDictionary : EvidenceEnvironment}
    (unique : ∀ first second, ContainsRequirement context primary first → ContainsRequirement context primary second → first = second)
    (signatures : context.signatures = program.signatures)
    (callerValid : caller.Valid program.signatures.resolutionRules)
    (expected : OperatorMethodSelected program context caller traitName methodName (primary :: rest) expectedBody expectedDictionary)
    (actual : OperatorMethodSelected program context caller traitName methodName (primary :: rest) actualBody actualDictionary)
    (coherent : Coherent program.signatures.resolutionRules expectedBody.context.assumptions) :
    actualBody = expectedBody ∧ actualDictionary = expectedDictionary := by
  have same := CallableCoercionSelectionIdentity.body_eq catalog unique actual expected
  refine ⟨same, ordered_functional coherent ?_ (selected_valid signatures callerValid expected)⟩
  simpa only [same] using selected_valid signatures callerValid actual

end Solcore.SourceSemantics.CoreLowering.RecursiveMethodDictionaryIdentity
