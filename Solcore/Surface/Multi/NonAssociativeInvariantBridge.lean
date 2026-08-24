import Solcore.Surface.Multi.DiagnosticExhaustiveness
import Solcore.Surface.Multi.NonAssociativeCompletionAlignment

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The remaining semantic-to-structural direction for G10.  It excludes the
known unrestricted pass-through counterexample by requiring a completed
coherent result to have some reached present-optional completion in the same
canonical root chart. -/
def CoherentNonAssociativeCompletedHasPresentCompletion
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel) (origin cursor : Boundary tokens)
      (context : GuardContext tokens) (output : RuleValue level.rule),
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens level.rule origin cursor context)
      output →
    (∃ first, CompletedNonAssociativeValue level output first) →
    ∃ (rootWaiting sequence : ContextualItemKey tokens)
        (rootShared : Boundary tokens)
        (sequenceWaiting optional : ContextualItemKey tokens)
        (optionalShared : Boundary tokens) (site : OptionalSite),
      ContextualEdgeReach file tokens memo correct final
          (.completed rootWaiting sequence
            (CanonicalCompleteRootItem tokens level.rule origin cursor context)
            rootShared) ∧
        ContextualEdgeReach file tokens memo correct final
          (.completed sequenceWaiting optional sequence optionalShared) ∧
        optional.raw.production = .opt site .some

/-- Operand-prefix exclusion and local optional inversion replace global
completion-backpointer uniqueness once coherent completed results are known
to originate in a present optional. -/
theorem coherentNonAssociativeRootCompletedInvariant_of_operandPrefixExclusive
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (exclusive : NonAssociativeOperandPrefixExclusive
      file tokens memo correct final)
    (present : CoherentNonAssociativeCompletedHasPresentCompletion
      file tokens memo correct final) :
    CoherentNonAssociativeRootCompletedInvariant
      file tokens memo correct final := by
  intro level origin cursor context left right leftCoherent rightCoherent
  constructor
  · intro leftCompleted
    rcases present level origin cursor context left leftCoherent leftCompleted with
      ⟨rootWaiting, sequence, rootShared, sequenceWaiting, optional,
        optionalShared, site, rootEdge, optionalEdge, optionalProduction⟩
    exact g10CompletedValue_of_presentCompletionEdges_of_operandPrefixExclusive
      exclusive rightCoherent rootEdge optionalEdge optionalProduction
  · intro rightCompleted
    rcases present level origin cursor context right rightCoherent rightCompleted with
      ⟨rootWaiting, sequence, rootShared, sequenceWaiting, optional,
        optionalShared, site, rootEdge, optionalEdge, optionalProduction⟩
    exact g10CompletedValue_of_presentCompletionEdges_of_operandPrefixExclusive
      exclusive leftCoherent rootEdge optionalEdge optionalProduction

end Solcore.Surface.Multi
