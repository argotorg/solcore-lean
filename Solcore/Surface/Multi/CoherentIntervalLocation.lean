import Solcore.Surface.Multi.CoherentSourceTrace
import Solcore.Surface.Multi.IntervalLocationEvidence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

/-- One semantic action preserves exact interval location evidence. -/
def ActionLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {action : ActionId}
    {origin finish : Boundary tokens}
    {input : GrammarSymbolValues file tokens action.production.rhs}
    {output : NonterminalValue file tokens action.production.lhs}
    (_reduces : ActionReduces file tokens action origin finish input output) :
    Prop :=
  ∀ trace : SourceAnchorTrace file tokens,
    IntervalLocationEvidence file tokens origin finish
        (GrammarSymbolValues.locationFragment action.production.rhs input)
        trace →
      IntervalLocationEvidence file tokens origin finish
        (NonterminalValue.locationFragment action.production.lhs output)
        trace

/-- One semantic action preserves interval evidence while retaining the exact
coherent prefix derivation that produced its input.  Source-rule actions whose
spans depend on named endpoints use this stronger boundary; generated actions
may discharge it through `ActionLocationSound`. -/
def CoherentActionLocationSound
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    (complete : CompleteItem item.raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues)
    (_action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output)
    (trace : SourceAnchorTrace file tokens)
    (_carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace) : Prop :=
  IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (GrammarSymbolValues.locationFragment item.raw.production.rhs
        (PrefixValues.fullValue item complete priorValues)) trace →
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.locationFragment item.raw.production.lhs output) trace

namespace ActionLocationSound

/-- Context-free action soundness is sufficient at every coherent prefix. -/
theorem coherent
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {priorValues : PrefixValues file tokens item}
    {output : NonterminalValue file tokens item.raw.production.lhs}
    {complete : CompleteItem item.raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      item priorValues}
    {action : ActionReduces file tokens (.actionFor item.raw.production)
      item.raw.origin item.raw.current
      (PrefixValues.fullValue item complete priorValues) output}
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherentPrefix trace}
    (sound : ActionLocationSound action) :
    CoherentActionLocationSound complete coherentPrefix action trace carries :=
  sound trace

end ActionLocationSound

private def PrefixIntervalLocationMotive
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
  IntervalLocationEvidence file tokens item.raw.origin item.raw.current
    (PrefixValues.locationFragment item values) trace

private def ReductionIntervalLocationMotive
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
  item.raw.production.lhs ≠ .rule .module →
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.locationFragment item.raw.production.lhs value) trace

private theorem prefixIntervalLocationZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixIntervalLocationMotive file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  unfold PrefixIntervalLocationMotive
  simpa only [PrefixValues.locationFragment_zeroValue] using
    IntervalLocationEvidence.empty (file := file)
      item.raw.origin item.raw.current

private theorem prefixIntervalLocationScanCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixIntervalLocationMotive
      file tokens memo correct final owned prior priorTrace priorCarries) :
    PrefixIntervalLocationMotive file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  unfold PrefixIntervalLocationMotive at priorIH ⊢
  have boundaries := witness.sourceBoundaries
  have priorAligned : IntervalLocationEvidence file tokens
      after.raw.origin before.raw.current
      (PrefixValues.locationFragment before priorValues) priorTrace := by
    simpa only [boundaries.1] using priorIH
  have terminalAligned : IntervalLocationEvidence file tokens
      before.raw.current after.raw.current witness.matched.locationFragment
      (witness.matched.sourceAnchorTrace owned) := by
    simpa only [boundaries.2.1, boundaries.2.2] using
      witness.matched.locationEvidence owned
  have beforeOrdered := contextualReach_ordered edge.2.1
  have intervalOrdered :
      after.raw.origin.val ≤ before.raw.current.val ∧
        before.raw.current.val ≤ after.raw.current.val := by
    constructor
    · simpa only [boundaries.1] using beforeOrdered
    · calc
        before.raw.current.val = witness.matched.cursor.val := by
          rw [← boundaries.2.1]
          rfl
        _ ≤ witness.matched.cursor.val + 1 := Nat.le_succ _
        _ = after.raw.current.val := by
          rw [boundaries.2.2]
          rfl
  simpa only [PrefixValues.locationFragment_scanValue] using
    IntervalLocationEvidence.mergeAcross priorAligned terminalAligned
      intervalOrdered

private theorem prefixIntervalLocationCompleteCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (priorIH : PrefixIntervalLocationMotive
      file tokens memo correct final owned prior priorTrace priorCarries)
    (childIH : ReductionIntervalLocationMotive
      file tokens memo correct final owned child childTrace childCarries) :
    PrefixIntervalLocationMotive file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  unfold PrefixIntervalLocationMotive at priorIH ⊢
  unfold ReductionIntervalLocationMotive at childIH
  have boundaries := witness.sourceBoundaries
  have priorAligned : IntervalLocationEvidence file tokens
      after.raw.origin shared
      (PrefixValues.locationFragment waiting priorValues) priorTrace := by
    simpa only [boundaries.1, boundaries.2.1] using priorIH
  have childAligned : IntervalLocationEvidence file tokens
      shared after.raw.current
      (NonterminalValue.locationFragment
        finished.raw.production.lhs childValue) childTrace := by
    have childNotModule :
        finished.raw.production.lhs ≠ .rule .module := by
      intro moduleLhs
      apply ProductionId.rhs_no_moduleRule waiting.raw.production
      rw [← moduleLhs]
      exact List.mem_of_getElem? witness.next.2
    simpa only [boundaries.2.2.1, boundaries.2.2.2] using
      childIH childNotModule
  have waitingOrdered := contextualReach_ordered edge.2.1
  have finishedOrdered := contextualReach_ordered edge.2.2.1
  have intervalOrdered :
      after.raw.origin.val ≤ shared.val ∧
        shared.val ≤ after.raw.current.val := by
    constructor
    · simpa only [boundaries.1, boundaries.2.1] using waitingOrdered
    · simpa only [boundaries.2.2.1, boundaries.2.2.2] using
        finishedOrdered
  simpa only [PrefixValues.locationFragment_completeValue] using
    IntervalLocationEvidence.mergeAcross priorAligned childAligned
      intervalOrdered

private theorem reductionIntervalLocationCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (sound : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationSound complete coherentPrefix action trace
        carries)
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
    (prefixIH : PrefixIntervalLocationMotive
      file tokens memo correct final owned coherentPrefix trace
        prefixCarries) :
    ReductionIntervalLocationMotive file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  unfold PrefixIntervalLocationMotive at prefixIH
  unfold ReductionIntervalLocationMotive
  intro notModule
  apply sound complete coherentPrefix action trace prefixCarries notModule
  exact IntervalLocationEvidence.replaceFragment
    (PrefixValues.locationFragment_fullValue item complete priorValues).symm
    prefixIH

namespace PrefixCarriesSourceTrace

theorem locationEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (sound : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationSound complete coherentPrefix action trace
        carries)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (PrefixValues.locationFragment item values) trace :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixIntervalLocationMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionIntervalLocationMotive
      file tokens memo correct final owned)
    (prefixIntervalLocationZeroCase owned)
    (prefixIntervalLocationScanCase owned)
    (prefixIntervalLocationCompleteCase owned)
    (reductionIntervalLocationCase owned sound)
    carries

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

theorem locationEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    (sound : ∀ {item : ContextualItemKey tokens}
        {priorValues : PrefixValues file tokens item}
        {output : NonterminalValue file tokens item.raw.production.lhs}
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (carries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace)
        (_notModule : item.raw.production.lhs ≠ .rule .module),
      CoherentActionLocationSound complete coherentPrefix action trace
        carries)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace)
    (notModule : item.raw.production.lhs ≠ .rule .module) :
    IntervalLocationEvidence file tokens item.raw.origin item.raw.current
      (NonterminalValue.locationFragment item.raw.production.lhs value) trace :=
  (ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixIntervalLocationMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionIntervalLocationMotive
      file tokens memo correct final owned)
    (prefixIntervalLocationZeroCase owned)
    (prefixIntervalLocationScanCase owned)
    (prefixIntervalLocationCompleteCase owned)
    (reductionIntervalLocationCase owned sound)
    carries) notModule

end ReductionCarriesSourceTrace

end Solcore.Surface.Multi
