import Solcore.Surface.Multi.ExactTokenActionDispatch

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- Exact-token preservation for all source reductions of one public grammar
rule over tokens owned by the parsed file. This rule-indexed form lets the full
callback be assembled in small, exhaustively checked modules. -/
def GrammarRuleTokenPlanSound (rule : GrammarRuleId) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule},
    TokensOwnedBy file tokens →
      RuleReduction file tokens rule origin finish input output →
      TokenPlanEvidence
        (input.tokenPlan? sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) →
      TokenPlanEvidence
        (ruleTokenPlan? rule output)
        (PhysicalTokens tokens origin finish)

namespace RootActionTokenPlanSound

/-- Pointwise soundness for all seventy-five public rules supplies the root
callback consumed by coherent parser recursion. -/
theorem ofRules
    (sound : ∀ rule : GrammarRuleId, GrammarRuleTokenPlanSound rule) :
    RootActionTokenPlanSound sourceRuleTokenPlanLayout := by
  intro rule file tokens memo correct final origin finish context priorValues
    output complete owned _sourceExact _coherentPrefix reduces inputEvidence
  apply sound rule owned reduces
  apply inputEvidence.candidate_eq
  symm
  rw [RootAction.unpack_tokenPlan?]
  simpa only [CanonicalCompleteRootItem] using
    (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
      (CanonicalCompleteRootItem tokens rule origin finish context)
      complete priorValues)

end RootActionTokenPlanSound

/-- The rule-indexed coverage domain remains synchronized with the grammar. -/
theorem grammarRuleTokenPlanSound_rule_count :
    allGrammarRuleIds.length = 75 := by
  rfl

end Solcore.Surface.Multi
