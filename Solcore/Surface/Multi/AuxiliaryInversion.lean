import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

inductive AuxiliaryProductionView (site : GrammarSite)
    (production : ProductionId) : EbnfNodeKind → Type where
  | atom (refined : AtomSite) (same : refined.site = site)
      (exact : production = .atom refined) :
      AuxiliaryProductionView site production .atom
  | sequence (refined : SequenceSite) (same : refined.site = site)
      (exact : production = .seq refined) :
      AuxiliaryProductionView site production .sequence
  | group (refined : GroupSite) (same : refined.site = site)
      (exact : production = .group refined) :
      AuxiliaryProductionView site production .group
  | choice (refined : ChoiceSite) (branch : Fin refined.branchCount)
      (same : refined.site = site) (exact : production = .choice refined branch) :
      AuxiliaryProductionView site production .choice
  | optional (refined : OptionalSite) (branch : OptionalBranch)
      (same : refined.site = site) (exact : production = .opt refined branch) :
      AuxiliaryProductionView site production .optional
  | star (refined : StarSite) (branch : NilConsBranch)
      (same : refined.site = site) (exact : production = .star refined branch) :
      AuxiliaryProductionView site production .star
  | plus (refined : PlusSite) (branch : OneConsBranch)
      (same : refined.site = site) (exact : production = .plus refined branch) :
      AuxiliaryProductionView site production .plus
  | list0 (refined : List0Site) (branch : NilConsBranch)
      (same : refined.site = site) (exact : production = .list0 refined branch) :
      AuxiliaryProductionView site production .list0
  | list1 (refined : List1Site) (same : refined.site = site)
      (exact : production = .list1 refined) :
      AuxiliaryProductionView site production .list1

def auxiliaryProductionView
    (site : GrammarSite) (production : ProductionId)
    (lhs : production.lhs = .aux site) :
    AuxiliaryProductionView site production site.expression.kind := by
  cases production with
  | root rule => cases lhs
  | tail listSite branch => cases lhs
  | atom refined =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.atom refined rfl rfl
  | seq refined =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.sequence refined rfl rfl
  | group refined =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.group refined rfl rfl
  | choice refined branch =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.choice refined branch rfl rfl
  | opt refined branch =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.optional refined branch rfl rfl
  | star refined branch =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.star refined branch rfl rfl
  | plus refined branch =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.plus refined branch rfl rfl
  | list0 refined branch =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.list0 refined branch rfl rfl
  | list1 refined =>
      have same := NonterminalSymbol.aux.inj lhs
      subst site
      simpa [refined.hasKind] using
        AuxiliaryProductionView.list1 refined rfl rfl

theorem contextualReach_nonterminal_step
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    {index : Nat} {childLhs : NonterminalSymbol}
    (reached : ContextualReach file tokens memo correct final item)
    (dot : item.raw.dot.val = index + 1)
    (selected : item.raw.production.rhs[index]? =
      some (.nonterminal childLhs)) :
    ∃ waiting child : ContextualItemKey tokens,
      ContextualReach file tokens memo correct final waiting ∧
      ContextualReach file tokens memo correct final child ∧
      CompleteItem child.raw ∧
      child.raw.production.lhs = childLhs ∧
      waiting.raw.dot.val = index ∧
      waiting.raw.production = item.raw.production ∧
      waiting.raw.origin = item.raw.origin ∧
      child.raw.origin = waiting.raw.current ∧
      child.raw.current = item.raw.current := by
  cases reached with
  | root =>
      change 0 = index + 1 at dot
      omega
  | predict =>
      change 0 = index + 1 at dot
      omega
  | scan before target cursor beforeReached structural =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with ⟨productionEq, dotEq, originEq, currentEq⟩
      have beforeDot : before.raw.dot.val = index := by omega
      have impossible : some (GrammarSymbol.nonterminal childLhs) =
          some (GrammarSymbol.terminal terminal) := by
        calc
          _ = item.raw.production.rhs[index]? := selected.symm
          _ = before.raw.production.rhs[index]? := congrArg
            (fun production : ProductionId => production.rhs[index]?)
              productionEq
          _ = before.raw.production.rhs[before.raw.dot.val]? := by rw [beforeDot]
          _ = _ := next.2
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete waiting child target shared waitingReached childReached structural =>
      obtain ⟨witness⟩ := packedEdge_completed_valid_iff.mp structural.1
      have waitingDot : waiting.raw.dot.val = index := by
        have advanced := witness.advance.2.1
        omega
      have childLhsEq : child.raw.production.lhs = childLhs := by
        have exactLookup : some (GrammarSymbol.nonterminal childLhs) =
            some (GrammarSymbol.nonterminal child.raw.production.lhs) := by
          calc
            _ = item.raw.production.rhs[index]? := selected.symm
            _ = waiting.raw.production.rhs[index]? := congrArg
              (fun production : ProductionId => production.rhs[index]?)
                witness.advance.1
            _ = waiting.raw.production.rhs[waiting.raw.dot.val]? := by
              rw [waitingDot]
            _ = _ := witness.next.2
        exact (GrammarSymbol.nonterminal.inj
          (Option.some.inj exactLookup)).symm
      exact ⟨waiting, child, waitingReached, childReached, witness.complete,
        childLhsEq, waitingDot, witness.advance.1.symm,
        witness.advance.2.2.1.symm,
        witness.finishedAtShared.trans witness.waitingAtShared.symm,
        witness.advance.2.2.2.symm⟩

theorem contextualReach_terminal_step_strict
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    {index : Nat} {terminal : TerminalSymbol}
    (reached : ContextualReach file tokens memo correct final item)
    (dot : item.raw.dot.val = index + 1)
    (selected : item.raw.production.rhs[index]? = some (.terminal terminal)) :
    item.raw.origin.val < item.raw.current.val := by
  cases reached with
  | root =>
      change 0 = index + 1 at dot
      omega
  | predict =>
      change 0 = index + 1 at dot
      omega
  | scan before target cursor beforeReached structural =>
      rcases structural.1 with
        ⟨scannedTerminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      have ordered := contextualReach_ordered beforeReached
      rcases advance with ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [originEq, currentEq]
      have atValue := congrArg Fin.val atCurrent
      change cursor.val = before.raw.current.val at atValue
      have afterValue : cursor.afterBoundary.val = cursor.val + 1 := rfl
      omega
  | complete waiting child target shared waitingReached childReached structural =>
      obtain ⟨witness⟩ := packedEdge_completed_valid_iff.mp structural.1
      have waitingDot : waiting.raw.dot.val = index := by
        have advanced := witness.advance.2.1
        omega
      have impossible : some (GrammarSymbol.terminal terminal) =
          some (GrammarSymbol.nonterminal child.raw.production.lhs) := by
        calc
          _ = item.raw.production.rhs[index]? := selected.symm
          _ = waiting.raw.production.rhs[index]? := congrArg
            (fun production : ProductionId => production.rhs[index]?)
              witness.advance.1
          _ = waiting.raw.production.rhs[waiting.raw.dot.val]? := by
            rw [waitingDot]
          _ = _ := witness.next.2
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)

/-- A reached item immediately after its first terminal recovers the exact
matched terminal, starting at the item's production origin. -/
theorem contextualReach_one_terminal
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    {terminal : TerminalSymbol}
    (reached : ContextualReach file tokens memo correct final item)
    (one : item.raw.dot.val = 1)
    (selected : item.raw.production.rhs[0]? = some (.terminal terminal)) :
    ∃ matched : MatchedTerminal file tokens terminal,
      matched.cursor.beforeBoundary = item.raw.origin ∧
      matched.cursor.afterBoundary = item.raw.current := by
  cases reached with
  | root => contradiction
  | predict => contradiction
  | scan before target cursor beforeReached structural =>
      rcases structural.1 with
        ⟨scannedTerminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with ⟨productionEq, dotEq, originEq, currentEq⟩
      have beforeZero : before.raw.dot.val = 0 := by omega
      have terminalEq : terminal = scannedTerminal := by
        apply GrammarSymbol.terminal.inj
        apply Option.some.inj
        calc
          some (GrammarSymbol.terminal terminal) =
              item.raw.production.rhs[0]? := selected.symm
          _ = before.raw.production.rhs[0]? := congrArg
            (fun production : ProductionId => production.rhs[0]?) productionEq
          _ = before.raw.production.rhs[before.raw.dot.val]? := by rw [beforeZero]
          _ = some (GrammarSymbol.terminal scannedTerminal) := next.2
      subst scannedTerminal
      have beforeOriginCurrent := contextualReach_zero_origin_eq_current
        beforeReached beforeZero
      refine ⟨⟨cursor, value, span, terminalAt, terminalMatches⟩, ?_, ?_⟩
      · exact atCurrent.trans
          (beforeOriginCurrent.symm.trans originEq.symm)
      · exact currentEq.symm
  | complete waiting child target shared waitingReached childReached structural =>
      obtain ⟨witness⟩ := packedEdge_completed_valid_iff.mp structural.1
      have waitingZero : waiting.raw.dot.val = 0 := by
        have advanced := witness.advance.2.1
        omega
      have impossible : some (GrammarSymbol.terminal terminal) =
          some (GrammarSymbol.nonterminal child.raw.production.lhs) := by
        calc
          _ = item.raw.production.rhs[0]? := selected.symm
          _ = waiting.raw.production.rhs[0]? := congrArg
            (fun production : ProductionId => production.rhs[0]?)
              witness.advance.1
          _ = waiting.raw.production.rhs[waiting.raw.dot.val]? := by
            rw [waitingZero]
          _ = _ := witness.next.2
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)

end Solcore.Surface.Multi
