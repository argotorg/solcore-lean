import Solcore.Surface.Multi.ExactTokenCoherentEvidence
import Solcore.Surface.Multi.ExactTokenGeneratedActions

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The only semantic callback required by token-plan action dispatch: a
source-rule reduction transforms complete input-plan evidence into evidence
for the rule visitor's output plan over the same parser interval. -/
def RootActionTokenPlanSound (layout : RuleTokenPlanLayout) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule},
    RuleReduction file tokens rule origin finish input output →
      TokenPlanEvidence
        (EbnfValue.tokenPlan? layout input)
        (PhysicalTokens tokens origin finish) →
      TokenPlanEvidence
        (layout.plan? rule output)
        (PhysicalTokens tokens origin finish)

namespace ActionTokenPlanSound

/-- Generated actions preserve token-plan evidence structurally, including the
comma-tail constraint weakening; root actions delegate to the supplied
source-rule callback. -/
theorem ofRoot
    {layout : RuleTokenPlanLayout}
    (rootSound : RootActionTokenPlanSound layout) :
    ActionTokenPlanSound layout := by
  intro file tokens actionId origin finish input output action inputEvidence
  cases action with
  | root rule origin finish input output reduction =>
      simp only [ActionId.production_actionFor] at inputEvidence ⊢
      apply rootSound reduction
      rw [RootAction.unpack_tokenPlan?]
      exact inputEvidence
  | atom site origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .atom site) layout trivial
        (ActionReduces.atom site origin finish input) inputEvidence
  | seq site origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .seq site) layout trivial
        (ActionReduces.seq site origin finish input) inputEvidence
  | group site origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .group site) layout trivial
        (ActionReduces.group site origin finish input) inputEvidence
  | choice site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .choice site branch) layout trivial
        (ActionReduces.choice site branch origin finish input) inputEvidence
  | opt site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .opt site branch) layout trivial
        (ActionReduces.opt site branch origin finish input) inputEvidence
  | star site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .star site branch) layout trivial
        (ActionReduces.star site branch origin finish input) inputEvidence
  | plus site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .plus site branch) layout trivial
        (ActionReduces.plus site branch origin finish input) inputEvidence
  | list0 site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .list0 site branch) layout trivial
        (ActionReduces.list0 site branch origin finish input) inputEvidence
  | list1 site origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .list1 site) layout trivial
        (ActionReduces.list1 site origin finish input) inputEvidence
  | tail site branch origin finish input =>
      exact ActionReduces.generated_tokenPlanEvidence
        (production := .tail site branch) layout trivial
        (ActionReduces.tail site branch origin finish input) inputEvidence

end ActionTokenPlanSound

end Solcore.Surface.Multi
