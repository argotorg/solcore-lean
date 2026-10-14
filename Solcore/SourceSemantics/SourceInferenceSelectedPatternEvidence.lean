import Solcore.SourceSemantics.SourceInferenceSubtreeTransport
import Solcore.SourceSemantics.SourceInferenceSoundness

set_option autoImplicit false
set_option Elab.async false
namespace Solcore.SourceSemantics.SourceInferenceSoundness
open Frontend.SourceInference TypeSystem

/-- The complete root record preserves each requirement's owning occurrence. -/
theorem SubtreePreserved.primaryRequirementOccursAt
    {substitution : Substitution} {before after : TypedSource}
    {occurrence : NodeId} {requirement : RequirementId}
    (preserved : SubtreePreserved substitution before after occurrence)
    (occurs : PrimaryRequirementOccursAt (before.applySubstitution substitution)
      occurrence requirement) :
    PrimaryRequirementOccursAt after occurrence requirement := by
  have original : PrimaryRequirementOccursAt before occurrence requirement := by
    simpa using occurs
  obtain ⟨node, member, owned⟩ := List.mem_flatMap.mp original
  have same : node.id = occurrence := by
    cases node with
    | expression expression =>
      obtain ⟨_, _, equality⟩ := List.mem_map.mp owned
      exact congrArg PrimaryRequirementSite.occurrence equality
    | statement statement =>
      obtain ⟨_, _, equality⟩ := List.mem_map.mp owned
      exact congrArg PrimaryRequirementSite.occurrence equality
  exact List.mem_flatMap.mpr ⟨node.applySubstitution substitution,
    preserved.nodes node member (.inl same), by simpa using owned⟩

/-- Match-pattern evidence restricts to the retained statement subtree even
when unrelated earlier expression records have changed during inference. -/
theorem IntegerPatternEvidenceAt.restrictSubtree
    {substitution : Substitution} {before after : TypedSource}
    {context : SourceSemantics.Context} {state : Frontend.SourceInference.State}
    {occurrence : NodeId}
    (preserved : SubtreePreserved substitution before after occurrence)
    (evidence : IntegerPatternEvidenceAt after context substitution state occurrence) :
    IntegerPatternEvidenceAt (before.applySubstitution substitution)
      context substitution state occurrence := by
  constructor
  intro literal resolution origin decoded targetEq requirementEq originMember
    requirementMember occurs
  exact evidence.valid decoded targetEq requirementEq originMember requirementMember
    (preserved.primaryRequirementOccursAt occurs)

end Solcore.SourceSemantics.SourceInferenceSoundness
