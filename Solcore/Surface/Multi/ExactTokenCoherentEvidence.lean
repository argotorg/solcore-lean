import Solcore.Surface.Multi.CoherentSourceTrace
import Solcore.Surface.Multi.ExactTokenCoherenceBase
import Solcore.Surface.Multi.ExactTokenReachability
import Solcore.Surface.Multi.ExactTokenRuleLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A callback proving that one checked semantic action preserves the complete
token-plan match carried by its parser interval. Source ownership supplies the
file identity needed by spans synthesized from child values. -/
def ActionTokenPlanSound (layout : RuleTokenPlanLayout) : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs},
    TokensOwnedBy file tokens →
      TokensSourceExact file tokens →
      ContextualReach file tokens memo correct final item →
      (complete : CompleteItem item.raw) →
      CoherentPrefix file tokens memo correct final item priorValues →
      ActionReduces file tokens (.actionFor item.raw.production)
        item.raw.origin item.raw.current
        (PrefixValues.fullValue item complete priorValues) output →
      TokenPlanEvidence
        (PrefixValues.tokenPlan? layout item priorValues)
        (PhysicalTokens tokens item.raw.origin item.raw.current) →
      TokenPlanEvidence
        (NonterminalValue.tokenPlan? layout
          item.raw.production.lhs output)
        (PhysicalTokens tokens item.raw.origin item.raw.current)

private def PrefixTokenPlanMotive
    (layout : RuleTokenPlanLayout)
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    (coherent : CoherentPrefix file tokens memo correct final item values)
    (trace : SourceAnchorTrace file tokens)
    (_carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) : Prop :=
  TokenPlanEvidence
    (PrefixValues.tokenPlan? layout item values)
    (PhysicalTokens tokens item.raw.origin item.raw.current)

private def ReductionTokenPlanMotive
    (layout : RuleTokenPlanLayout)
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    (coherent : CoherentReduction file tokens memo correct final item value)
    (trace : SourceAnchorTrace file tokens)
    (_carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) : Prop :=
  TokenPlanEvidence
    (NonterminalValue.tokenPlan? layout item.raw.production.lhs value)
    (PhysicalTokens tokens item.raw.origin item.raw.current)

private theorem prefixTokenPlanZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (layout : RuleTokenPlanLayout) (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixTokenPlanMotive layout file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  unfold PrefixTokenPlanMotive
  rw [PrefixValues.tokenPlan?_zeroValue]
  rw [contextualReach_zero_origin_eq_current reached zero]
  rw [PhysicalTokens.self]
  exact TokenPlanEvidence.empty

private theorem prefixTokenPlanScanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (layout : RuleTokenPlanLayout) (owned : TokensOwnedBy file tokens)
    (before after : ContextualItemKey tokens)
    (cursor : TerminalCursor tokens)
    (priorValues : PrefixValues file tokens before)
    (witness : ScannedEdgeWitness
      file tokens before.raw after.raw cursor)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.scanned before after cursor))
    (prior : CoherentPrefix file tokens memo correct final
      before priorValues)
    (priorTrace : SourceAnchorTrace file tokens)
    (priorCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned prior priorTrace)
    (priorIH : PrefixTokenPlanMotive layout file tokens memo correct final
      owned prior priorTrace priorCarries) :
    PrefixTokenPlanMotive layout file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  unfold PrefixTokenPlanMotive at priorIH ⊢
  rw [PrefixValues.tokenPlan?_scanValue]
  rw [witness.advance.2.2.1, witness.advance.2.2.2]
  rw [← witness.atCurrent] at priorIH
  rw [← witness.sameCursor] at priorIH
  exact priorIH.appendMatchedTerminal witness.matched
    (by
      rw [witness.sameCursor, witness.atCurrent]
      exact contextualReach_ordered edge.2.1)

private theorem prefixTokenPlanCompleteCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (layout : RuleTokenPlanLayout) (owned : TokensOwnedBy file tokens)
    (waiting finished after : ContextualItemKey tokens)
    (shared : Boundary tokens)
    (priorValues : PrefixValues file tokens waiting)
    (childValue : NonterminalValue file tokens
      finished.raw.production.lhs)
    (witness : CompletedEdgeWitness
      tokens waiting.raw finished.raw after.raw shared)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.completed waiting finished after shared))
    (prior : CoherentPrefix file tokens memo correct final
      waiting priorValues)
    (child : CoherentReduction file tokens memo correct final
      finished childValue)
    (priorTrace childTrace : SourceAnchorTrace file tokens)
    (priorCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned prior priorTrace)
    (childCarries : ReductionCarriesSourceTrace
      file tokens memo correct final owned child childTrace)
    (priorIH : PrefixTokenPlanMotive layout file tokens memo correct final
      owned prior priorTrace priorCarries)
    (childIH : ReductionTokenPlanMotive layout file tokens memo correct final
      owned child childTrace childCarries) :
    PrefixTokenPlanMotive layout file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  unfold PrefixTokenPlanMotive at priorIH ⊢
  unfold ReductionTokenPlanMotive at childIH
  rw [PrefixValues.tokenPlan?_completeValue]
  rw [witness.advance.2.2.1, witness.advance.2.2.2]
  rw [witness.waitingAtShared] at priorIH
  rw [witness.finishedAtShared] at childIH
  exact TokenPlanEvidence.appendPhysical
    (by
      rw [← witness.waitingAtShared]
      exact contextualReach_ordered edge.2.1)
    (by
      rw [← witness.finishedAtShared]
      exact contextualReach_ordered edge.2.2.1)
    priorIH childIH

private theorem reductionTokenPlanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (layout : RuleTokenPlanLayout)
    (actionSound : ActionTokenPlanSound layout)
    (owned : TokensOwnedBy file tokens)
    (sourceExact : TokensSourceExact file tokens)
    (item : ContextualItemKey tokens)
    (priorValues : PrefixValues file tokens item)
    (output : NonterminalValue file tokens item.raw.production.lhs)
    (reached : ContextualReach file tokens memo correct final item)
    (complete : CompleteItem item.raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output)
    (trace : SourceAnchorTrace file tokens)
    (prefixCarries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace)
    (prefixIH : PrefixTokenPlanMotive layout file tokens memo correct final
      owned coherentPrefix trace prefixCarries) :
    ReductionTokenPlanMotive layout file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  unfold PrefixTokenPlanMotive at prefixIH
  unfold ReductionTokenPlanMotive
  exact actionSound owned sourceExact reached complete coherentPrefix action
    prefixIH

namespace PrefixCarriesSourceTrace

/-- Coherent prefix recursion carries a complete token-plan match when every
semantic action preserves its interval evidence. -/
theorem tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (layout : RuleTokenPlanLayout)
    (actionSound : ActionTokenPlanSound layout)
    (sourceExact : TokensSourceExact file tokens)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    TokenPlanEvidence
      (PrefixValues.tokenPlan? layout item values)
      (PhysicalTokens tokens item.raw.origin item.raw.current) :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixTokenPlanMotive
      layout file tokens memo correct final owned)
    (motive_2 := ReductionTokenPlanMotive
      layout file tokens memo correct final owned)
    (prefixTokenPlanZeroCase layout owned)
    (prefixTokenPlanScanCase layout owned)
    (prefixTokenPlanCompleteCase layout owned)
    (reductionTokenPlanCase layout actionSound owned sourceExact)
    carries

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

/-- Coherent reduction recursion carries a complete token-plan match when
every semantic action preserves its interval evidence. -/
theorem tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (layout : RuleTokenPlanLayout)
    (actionSound : ActionTokenPlanSound layout)
    (sourceExact : TokensSourceExact file tokens)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    TokenPlanEvidence
      (NonterminalValue.tokenPlan? layout item.raw.production.lhs value)
      (PhysicalTokens tokens item.raw.origin item.raw.current) :=
  ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixTokenPlanMotive
      layout file tokens memo correct final owned)
    (motive_2 := ReductionTokenPlanMotive
      layout file tokens memo correct final owned)
    (prefixTokenPlanZeroCase layout owned)
    (prefixTokenPlanScanCase layout owned)
    (prefixTokenPlanCompleteCase layout owned)
    (reductionTokenPlanCase layout actionSound owned sourceExact)
    carries

end ReductionCarriesSourceTrace

end Solcore.Surface.Multi
