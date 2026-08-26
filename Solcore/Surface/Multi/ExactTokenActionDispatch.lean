import Solcore.Surface.Multi.ExactTokenCoherentEvidence
import Solcore.Surface.Multi.ExactTokenGeneratedActions

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace

/-- The only semantic callback required by token-plan action dispatch: every
coherent source-rule reduction preserves its complete interval plan. -/
def RootActionTokenPlanSound (layout : RuleTokenPlanLayout) : Prop :=
  ∀ rule : GrammarRuleId,
    CoherentGrammarRuleTokenPlanSound layout rule

namespace ActionTokenPlanSound

/-- Generated actions preserve token-plan evidence structurally, including the
comma-tail constraint weakening; root actions delegate to the supplied
source-rule callback. -/
theorem ofRoot
    {layout : RuleTokenPlanLayout}
    (rootSound : RootActionTokenPlanSound layout) :
    ActionTokenPlanSound layout := by
  intro file tokens memo correct final item priorValues output owned sourceExact
    reached complete coherentPrefix action inputEvidence
  cases item with
  | mk raw context =>
    cases raw with
    | mk production dot itemOrigin itemFinish =>
      have fullInputEvidence : TokenPlanEvidence
          (GrammarSymbolValues.tokenPlan? layout production.rhs
            (PrefixValues.fullValue
              ⟨⟨production, dot, itemOrigin, itemFinish⟩, context⟩
              complete priorValues))
          (PhysicalTokens tokens itemOrigin itemFinish) := by
        apply inputEvidence.candidate_eq
        exact (PrefixValues.tokenPlan?_fullValue layout
          ⟨⟨production, dot, itemOrigin, itemFinish⟩, context⟩
          complete priorValues).symm
      cases production with
      | root rule =>
          cases action with
          | root _ _ _ _ _ reduction =>
              have dotEq : dot =
                  ⟨(ProductionId.root rule).rhs.length,
                    Nat.lt_succ_self _⟩ := by
                apply Fin.ext
                exact complete
              subst dot
              exact rootSound rule complete owned sourceExact coherentPrefix
                reduction inputEvidence
      | atom site =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .atom site) layout trivial action
            fullInputEvidence
      | seq site =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .seq site) layout trivial action
            fullInputEvidence
      | group site =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .group site) layout trivial action
            fullInputEvidence
      | choice site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .choice site branch) layout trivial action
            fullInputEvidence
      | opt site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .opt site branch) layout trivial action
            fullInputEvidence
      | star site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .star site branch) layout trivial action
            fullInputEvidence
      | plus site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .plus site branch) layout trivial action
            fullInputEvidence
      | list0 site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .list0 site branch) layout trivial action
            fullInputEvidence
      | list1 site =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .list1 site) layout trivial action
            fullInputEvidence
      | tail site branch =>
          exact ActionReduces.generated_tokenPlanEvidence
            (production := .tail site branch) layout trivial action
            fullInputEvidence

end ActionTokenPlanSound

end Solcore.Surface.Multi
