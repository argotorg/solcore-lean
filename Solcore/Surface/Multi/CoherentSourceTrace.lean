import Solcore.Surface.Multi.EdgeLocationProperties
import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Solcore.Workspace
open Grammar

mutual

  /-- The physical terminal trace carried by one coherent consumed prefix.
  Its constructors record the chosen scan and completion derivation. -/
  inductive PrefixCarriesSourceTrace
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo)
      (owned : TokensOwnedBy file tokens) :
      {item : ContextualItemKey tokens} →
        {values : PrefixValues file tokens item} →
        CoherentPrefix file tokens memo correct final item values →
          SourceAnchorTrace file tokens → Prop where
    | zero
        (item : ContextualItemKey tokens)
        (reached : ContextualReach file tokens memo correct final item)
        (zero : item.raw.dot.val = 0) :
        PrefixCarriesSourceTrace file tokens memo correct final owned
          (.zero item reached zero) []
    | scan
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
          file tokens memo correct final owned prior priorTrace) :
        PrefixCarriesSourceTrace file tokens memo correct final owned
          (.scan before after cursor priorValues witness edge prior)
          (priorTrace ++ witness.matched.sourceAnchorTrace owned)
    | complete
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
          file tokens memo correct final owned child childTrace) :
        PrefixCarriesSourceTrace file tokens memo correct final owned
          (.complete waiting finished after shared priorValues childValue
            witness edge prior child)
          (priorTrace ++ childTrace)

  /-- The physical terminal trace carried by one coherent completed
  reduction. Semantic actions preserve the prefix trace, including terminals
  such as list separators that are absent from the reduced value. -/
  inductive ReductionCarriesSourceTrace
      (file : WorkspaceFile) (tokens : List Token)
      (memo : GuardMemo tokens)
      (correct : PhaseBCorrect file tokens memo)
      (final : AllGuardsFinal memo)
      (owned : TokensOwnedBy file tokens) :
      {item : ContextualItemKey tokens} →
        {value : NonterminalValue file tokens item.raw.production.lhs} →
        CoherentReduction file tokens memo correct final item value →
          SourceAnchorTrace file tokens → Prop where
    | reduce
        (item : ContextualItemKey tokens)
        (priorValues : PrefixValues file tokens item)
        (output : NonterminalValue file tokens item.raw.production.lhs)
        (reached : ContextualReach file tokens memo correct final item)
        (complete : CompleteItem item.raw)
        (coherentPrefix : CoherentPrefix file tokens memo correct final
          item priorValues)
        (action : ActionReduces file tokens
          (.actionFor item.raw.production)
          item.raw.origin item.raw.current
          (PrefixValues.fullValue item complete priorValues) output)
        (trace : SourceAnchorTrace file tokens)
        (prefixCarries : PrefixCarriesSourceTrace
          file tokens memo correct final owned coherentPrefix trace) :
        ReductionCarriesSourceTrace file tokens memo correct final owned
          (.reduce item priorValues output reached complete coherentPrefix
            action) trace

end

private def PrefixSourceTraceExistenceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item)
    (coherent : CoherentPrefix file tokens memo correct final item values) :
    Prop :=
  ∃ trace : SourceAnchorTrace file tokens,
    PrefixCarriesSourceTrace file tokens memo correct final owned
      coherent trace

private def ReductionSourceTraceExistenceMotive
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (value : NonterminalValue file tokens item.raw.production.lhs)
    (coherent : CoherentReduction file tokens memo correct final item value) :
    Prop :=
  ∃ trace : SourceAnchorTrace file tokens,
    ReductionCarriesSourceTrace file tokens memo correct final owned
      coherent trace

private theorem prefixSourceTraceZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixSourceTraceExistenceMotive file tokens memo correct final owned
      item (PrefixValues.zeroValue item zero) (.zero item reached zero) := by
  exact ⟨[], .zero item reached zero⟩

private theorem prefixSourceTraceScanCase
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
    (priorIH : PrefixSourceTraceExistenceMotive
      file tokens memo correct final owned before priorValues prior) :
    PrefixSourceTraceExistenceMotive file tokens memo correct final owned
      after
      (PrefixValues.scanValue before after witness.terminal witness.next
        witness.matched witness.advance priorValues)
      (.scan before after cursor priorValues witness edge prior) := by
  rcases priorIH with ⟨priorTrace, priorCarries⟩
  exact ⟨priorTrace ++ witness.matched.sourceAnchorTrace owned,
    .scan before after cursor priorValues witness edge prior
      priorTrace priorCarries⟩

private theorem prefixSourceTraceCompleteCase
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
    (priorIH : PrefixSourceTraceExistenceMotive
      file tokens memo correct final owned waiting priorValues prior)
    (childIH : ReductionSourceTraceExistenceMotive
      file tokens memo correct final owned finished childValue child) :
    PrefixSourceTraceExistenceMotive file tokens memo correct final owned
      after
      (PrefixValues.completeValue waiting finished after witness.next
        witness.advance priorValues childValue)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child) := by
  rcases priorIH with ⟨priorTrace, priorCarries⟩
  rcases childIH with ⟨childTrace, childCarries⟩
  exact ⟨priorTrace ++ childTrace,
    .complete waiting finished after shared priorValues childValue witness
      edge prior child priorTrace childTrace priorCarries childCarries⟩

private theorem reductionSourceTraceCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (prefixIH : PrefixSourceTraceExistenceMotive
      file tokens memo correct final owned item priorValues coherentPrefix) :
    ReductionSourceTraceExistenceMotive file tokens memo correct final owned
      item output
      (.reduce item priorValues output reached complete coherentPrefix
        action) := by
  rcases prefixIH with ⟨trace, prefixCarries⟩
  exact ⟨trace, .reduce item priorValues output reached complete
    coherentPrefix action trace prefixCarries⟩

namespace CoherentPrefix

/-- Every coherent prefix carries a physical source trace assembled in scan
and completion order. -/
theorem sourceTrace_exists
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    (coherent : CoherentPrefix file tokens memo correct final item values) :
    ∃ trace : SourceAnchorTrace file tokens,
      PrefixCarriesSourceTrace file tokens memo correct final owned
        coherent trace :=
  CoherentPrefix.rec
    (motive_1 := PrefixSourceTraceExistenceMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionSourceTraceExistenceMotive
      file tokens memo correct final owned)
    (prefixSourceTraceZeroCase owned)
    (prefixSourceTraceScanCase owned)
    (prefixSourceTraceCompleteCase owned)
    (reductionSourceTraceCase owned)
    coherent

end CoherentPrefix

namespace CoherentReduction

/-- Every coherent reduction carries the physical trace of its completed
prefix, unchanged by its semantic action. -/
theorem sourceTrace_exists
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    (coherent : CoherentReduction file tokens memo correct final item value) :
    ∃ trace : SourceAnchorTrace file tokens,
      ReductionCarriesSourceTrace file tokens memo correct final owned
        coherent trace :=
  CoherentReduction.rec
    (motive_1 := PrefixSourceTraceExistenceMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionSourceTraceExistenceMotive
      file tokens memo correct final owned)
    (prefixSourceTraceZeroCase owned)
    (prefixSourceTraceScanCase owned)
    (prefixSourceTraceCompleteCase owned)
    (reductionSourceTraceCase owned)
    coherent

end CoherentReduction

private def PrefixSourceTraceGeometryMotive
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
  trace.Within item.raw.origin item.raw.current ∧ trace.Ordered

private def ReductionSourceTraceGeometryMotive
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
  trace.Within item.raw.origin item.raw.current ∧ trace.Ordered

private theorem prefixSourceTraceGeometryZeroCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
    (item : ContextualItemKey tokens)
    (reached : ContextualReach file tokens memo correct final item)
    (zero : item.raw.dot.val = 0) :
    PrefixSourceTraceGeometryMotive file tokens memo correct final owned
      (.zero item reached zero) [] (.zero item reached zero) := by
  exact ⟨by simp, by simp⟩

private theorem prefixSourceTraceGeometryScanCase
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
    (priorIH : PrefixSourceTraceGeometryMotive
      file tokens memo correct final owned prior priorTrace priorCarries) :
    PrefixSourceTraceGeometryMotive file tokens memo correct final owned
      (.scan before after cursor priorValues witness edge prior)
      (priorTrace ++ witness.matched.sourceAnchorTrace owned)
      (.scan before after cursor priorValues witness edge prior priorTrace
        priorCarries) := by
  have beforeOrdered := contextualReach_ordered edge.2.1
  exact ⟨witness.sourceAnchorTrace_within owned beforeOrdered priorIH.1,
    witness.sourceAnchorTrace_ordered owned priorIH.1 priorIH.2⟩

private theorem prefixSourceTraceGeometryCompleteCase
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
    (priorIH : PrefixSourceTraceGeometryMotive
      file tokens memo correct final owned prior priorTrace priorCarries)
    (childIH : ReductionSourceTraceGeometryMotive
      file tokens memo correct final owned child childTrace childCarries) :
    PrefixSourceTraceGeometryMotive file tokens memo correct final owned
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child)
      (priorTrace ++ childTrace)
      (.complete waiting finished after shared priorValues childValue witness
        edge prior child priorTrace childTrace priorCarries childCarries) := by
  have waitingOrdered := contextualReach_ordered edge.2.1
  have finishedOrdered := contextualReach_ordered edge.2.2.1
  exact ⟨witness.sourceAnchorTraces_within waitingOrdered finishedOrdered
      priorIH.1 childIH.1,
    witness.sourceAnchorTraces_ordered
      priorIH.1 childIH.1 priorIH.2 childIH.2⟩

private theorem reductionSourceTraceGeometryCase
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (owned : TokensOwnedBy file tokens)
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
    (prefixIH : PrefixSourceTraceGeometryMotive
      file tokens memo correct final owned coherentPrefix trace
        prefixCarries) :
    ReductionSourceTraceGeometryMotive file tokens memo correct final owned
      (.reduce item priorValues output reached complete coherentPrefix action)
      trace
      (.reduce item priorValues output reached complete coherentPrefix action
        trace prefixCarries) := by
  exact prefixIH

namespace PrefixCarriesSourceTrace

/-- A coherent prefix trace stays inside the prefix interval and is ordered by
parser boundary. -/
theorem within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    trace.Within item.raw.origin item.raw.current ∧ trace.Ordered :=
  PrefixCarriesSourceTrace.rec
    (motive_1 := PrefixSourceTraceGeometryMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionSourceTraceGeometryMotive
      file tokens memo correct final owned)
    (prefixSourceTraceGeometryZeroCase owned)
    (prefixSourceTraceGeometryScanCase owned)
    (prefixSourceTraceGeometryCompleteCase owned)
    (reductionSourceTraceGeometryCase owned)
    carries

/-- Every physical span retained by a coherent prefix trace lies inside the
consumed span of that prefix interval. -/
theorem spans_containedBy
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {values : PrefixValues file tokens item}
    {coherent : CoherentPrefix file tokens memo correct final item values}
    {trace : SourceAnchorTrace file tokens}
    {outerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens item.raw.origin item.raw.current
      outerSpan)
    (carries : PrefixCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    ∀ span ∈ trace.spans, outerSpan.Contains span :=
  SourceAnchorTrace.spans_containedBy tokensOrdered outer
    carries.within_and_ordered.1

end PrefixCarriesSourceTrace

namespace ReductionCarriesSourceTrace

/-- A coherent reduction trace stays inside its completed item interval and is
ordered by parser boundary. -/
theorem within_and_ordered
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    trace.Within item.raw.origin item.raw.current ∧ trace.Ordered :=
  ReductionCarriesSourceTrace.rec
    (motive_1 := PrefixSourceTraceGeometryMotive
      file tokens memo correct final owned)
    (motive_2 := ReductionSourceTraceGeometryMotive
      file tokens memo correct final owned)
    (prefixSourceTraceGeometryZeroCase owned)
    (prefixSourceTraceGeometryScanCase owned)
    (prefixSourceTraceGeometryCompleteCase owned)
    (reductionSourceTraceGeometryCase owned)
    carries

/-- Every physical span retained by a coherent reduction trace lies inside the
consumed span of that completed item. -/
theorem spans_containedBy
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {item : ContextualItemKey tokens}
    {value : NonterminalValue file tokens item.raw.production.lhs}
    {coherent : CoherentReduction file tokens memo correct final item value}
    {trace : SourceAnchorTrace file tokens}
    {outerSpan : SourceSpan}
    (tokensOrdered : TokenSpansOrdered tokens)
    (outer : ConsumedSpan file tokens item.raw.origin item.raw.current
      outerSpan)
    (carries : ReductionCarriesSourceTrace
      file tokens memo correct final owned coherent trace) :
    ∀ span ∈ trace.spans, outerSpan.Contains span :=
  SourceAnchorTrace.spans_containedBy tokensOrdered outer
    carries.within_and_ordered.1

end ReductionCarriesSourceTrace

end Solcore.Surface.Multi
