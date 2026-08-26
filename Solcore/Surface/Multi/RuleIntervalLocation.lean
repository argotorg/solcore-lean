import Solcore.Surface.Multi.AuxiliaryLocation
import Solcore.Surface.Multi.CoherentIntervalLocation
import Solcore.Surface.Multi.RuleLocationSubfragment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- A source-rule reduction preserves exact interval location evidence. -/
def RuleReduction.LocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    (_reduces : RuleReduction file tokens rule origin finish input output) :
    Prop :=
  ∀ trace : SourceAnchorTrace file tokens,
    IntervalLocationEvidence file tokens origin finish
        input.locationFragment trace →
      IntervalLocationEvidence file tokens origin finish
        (RuleLocationView.ofRuleValue rule output) trace

namespace RuleReduction.SemanticPassThrough

/-- Every classified source-rule pass-through preserves the retained child
fragment while keeping the complete physical trace. -/
theorem locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (passThrough : RuleReduction.SemanticPassThrough reduces) :
    RuleReduction.LocationSound reduces := by
  intro trace evidence
  rcases passThrough.location with
    ⟨childRule, childValue, inside, outputLocation⟩
  apply IntervalLocationEvidence.restrict
  · rw [outputLocation]
    exact inside.locationFragment_isSubfragment
  · exact evidence

end RuleReduction.SemanticPassThrough

namespace ActionReduces

/-- Source-rule location soundness lifts through the canonical root tuple. -/
theorem root_locationSound
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens (ProductionId.root rule).rhs}
    {output : RuleValue rule}
    (reduces : RuleReduction file tokens rule origin finish
      (RootAction.unpack rule input) output)
    (sound : RuleReduction.LocationSound reduces) :
    ActionLocationSound
      (ActionReduces.root rule origin finish input output reduces) := by
  intro trace evidence
  apply sound trace
  exact IntervalLocationEvidence.replaceFragment
    (RootAction.unpack_locationFragment rule input).symm evidence

end ActionReduces

end Solcore.Surface.Multi
