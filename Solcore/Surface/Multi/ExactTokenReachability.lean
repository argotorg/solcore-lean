import Solcore.Surface.Multi.CoherentSourceTrace
import Solcore.Surface.Multi.ExactTokenCoherenceBase
import Solcore.Surface.Multi.ExactTokenRuleLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A complete root item is definitionally the canonical complete item once
its source rule is known. -/
theorem ContextualItemKey.eq_canonicalCompleteRoot
    {tokens : List Token} {rule : GrammarRuleId}
    (item : ContextualItemKey tokens)
    (production : item.raw.production = .root rule)
    (complete : CompleteItem item.raw) :
    item = CanonicalCompleteRootItem tokens rule item.raw.origin
      item.raw.current item.context := by
  cases item with
  | mk raw context =>
      cases raw with
      | mk productionId dot origin finish =>
          simp only at production complete ⊢
          subst productionId
          have dotEq : dot =
              ⟨(ProductionId.root rule).rhs.length,
                Nat.lt_succ_self _⟩ := by
            apply Fin.ext
            exact complete
          subst dot
          rfl

/-- Every reached chart item retains the enablement of the production instance
that originally introduced it. -/
theorem ContextualReach.enabledProductionInstance
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    EnabledProductionInstance file tokens memo correct final {
      production := item.raw.production
      origin := item.raw.origin
      context := item.context
    } := by
  induction reached with
  | root =>
      intro guard polarity member
      simp [guardOf] at member
  | predict waiting predicted waitingReached next enabled induction =>
      exact enabled
  | scan before after cursor beforeReached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have contextEq := structural.2
      simpa only [productionEq, originEq, ← contextEq] using induction
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, finishedComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have contextEq := structural.2.2
      simpa only [productionEq, originEq, ← contextEq] using waitingInduction

/-- Exact-token preservation for one public source rule, restricted to
complete root reductions that are reachable in the finalized guarded chart. -/
def ReachableGrammarRuleTokenPlanSound
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule},
    TokensOwnedBy file tokens →
      ContextualReach file tokens memo correct final
        (CanonicalCompleteRootItem tokens rule origin finish context) →
      RuleReduction file tokens rule origin finish input output →
      TokenPlanEvidence
        (input.tokenPlan? layout)
        (PhysicalTokens tokens origin finish) →
      TokenPlanEvidence
        (layout.plan? rule output)
        (PhysicalTokens tokens origin finish)

/-- Exact-token preservation for one source rule when its input is the full
semantic value of a coherent, complete root item. Keeping the prefix evidence
in the callback preserves the guarded derivation chosen by the parser. -/
def CoherentGrammarRuleTokenPlanSound
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens rule origin finish context)}
    {output : RuleValue rule}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw),
    TokensOwnedBy file tokens →
      TokensSourceExact file tokens →
      CoherentPrefix file tokens memo correct final
        (CanonicalCompleteRootItem tokens rule origin finish context)
        priorValues →
      RuleReduction file tokens rule origin finish
        (RootAction.unpack rule <|
          PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens rule origin finish context)
            complete priorValues)
        output →
      TokenPlanEvidence
        (PrefixValues.tokenPlan? layout
          (CanonicalCompleteRootItem tokens rule origin finish context)
          priorValues)
        (PhysicalTokens tokens origin finish) →
      TokenPlanEvidence
        (layout.plan? rule output)
        (PhysicalTokens tokens origin finish)

end Solcore.Surface.Multi
