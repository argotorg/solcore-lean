import Solcore.Surface.Multi.ParserJudgment

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

mutual

/-- One grammar symbol derives one exact token interval. -/
inductive UnguardedSymbolDerives
    (file : WorkspaceFile) (tokens : List Token) :
    GrammarSymbol → Boundary tokens → Boundary tokens → Prop where
  | terminal
      (terminal : TerminalSymbol)
      (matched : MatchedTerminal file tokens terminal) :
      UnguardedSymbolDerives file tokens (.terminal terminal)
        matched.cursor.beforeBoundary matched.cursor.afterBoundary
  | nonterminal
      (production : ProductionId)
      (start finish : Boundary tokens)
      (body : UnguardedSymbolsDerive file tokens production.rhs start finish) :
      UnguardedSymbolDerives file tokens (.nonterminal production.lhs)
        start finish

/-- A grammar-symbol list derives one contiguous token interval. -/
inductive UnguardedSymbolsDerive
    (file : WorkspaceFile) (tokens : List Token) :
    List GrammarSymbol → Boundary tokens → Boundary tokens → Prop where
  | nil (cursor : Boundary tokens) :
      UnguardedSymbolsDerive file tokens [] cursor cursor
  | cons
      (symbol : GrammarSymbol) (rest : List GrammarSymbol)
      (start middle finish : Boundary tokens)
      (head : UnguardedSymbolDerives file tokens symbol start middle)
      (tail : UnguardedSymbolsDerive file tokens rest middle finish) :
      UnguardedSymbolsDerive file tokens (symbol :: rest) start finish

end

namespace UnguardedSymbolDerives

/-- Transport one symbol derivation along exact index equalities. -/
theorem transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : GrammarSymbol}
    {leftStart leftFinish rightStart rightFinish : Boundary tokens}
    (symbol : left = right)
    (start : leftStart = rightStart)
    (finish : leftFinish = rightFinish)
    (derives : UnguardedSymbolDerives
      file tokens left leftStart leftFinish) :
    UnguardedSymbolDerives file tokens right rightStart rightFinish := by
  subst right
  subst rightStart
  subst rightFinish
  exact derives

end UnguardedSymbolDerives

namespace UnguardedSymbolsDerive

/-- Transport a derivation along exact symbol and boundary equalities. -/
theorem transport
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol}
    {leftStart leftFinish rightStart rightFinish : Boundary tokens}
    (symbols : left = right)
    (start : leftStart = rightStart)
    (finish : leftFinish = rightFinish)
    (derives : UnguardedSymbolsDerive
      file tokens left leftStart leftFinish) :
    UnguardedSymbolsDerive file tokens right rightStart rightFinish := by
  subst right
  subst rightStart
  subst rightFinish
  exact derives

/-- Concatenate two contiguous symbol-list derivations. -/
theorem append
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List GrammarSymbol}
    {start middle finish : Boundary tokens}
    (leftDerives : UnguardedSymbolsDerive
      file tokens left start middle)
    (rightDerives : UnguardedSymbolsDerive
      file tokens right middle finish) :
    UnguardedSymbolsDerive file tokens (left ++ right) start finish := by
  induction left generalizing start with
  | nil =>
      cases leftDerives
      exact rightDerives
  | cons symbol rest induction =>
      cases leftDerives with
      | cons _ _ _ inner _ head tail =>
          exact .cons symbol (rest ++ right) start inner finish head
            (induction tail)

end UnguardedSymbolsDerive

/-- Every reached dotted item carries a derivation of exactly its consumed
right-hand-side prefix. -/
theorem UnguardedReach.prefixDerives
    {file : WorkspaceFile} {tokens : List Token}
    {item : DottedItem tokens}
    (reached : UnguardedReach file tokens item) :
    UnguardedSymbolsDerive file tokens
      (item.production.rhs.take item.dot.val) item.origin item.current := by
  induction reached with
  | seed production cursor =>
      exact (UnguardedSymbolsDerive.nil cursor).transport
        (prefix_zero_layout _ rfl) rfl rfl
  | predict waiting predicted waitingReached next induction =>
      exact (UnguardedSymbolsDerive.nil waiting.current).transport
        (prefix_zero_layout _ rfl) rfl rfl
  | scan before after cursor terminal value span beforeReached next atCurrent
      terminalAt terminalMatches advance induction =>
      let matched : MatchedTerminal file tokens terminal := {
        cursor := cursor
        value := value
        span := span
        «at» := terminalAt
        «matches» := terminalMatches
      }
      have terminalDerives : UnguardedSymbolsDerive file tokens
          [.terminal terminal] before.current cursor.afterBoundary :=
        .cons (.terminal terminal) [] before.current cursor.afterBoundary
          cursor.afterBoundary
          ((UnguardedSymbolDerives.terminal terminal matched).transport
            rfl atCurrent rfl)
          (.nil cursor.afterBoundary)
      have combined := induction.append terminalDerives
      exact combined.transport
        (prefix_scan_layout before after terminal cursor.afterBoundary
          next advance)
        advance.2.2.1.symm advance.2.2.2.symm
  | complete waiting finished after waitingReached finishedReached next
      finishedComplete sameCursor advance waitingInduction
      finishedInduction =>
      have finishedBody : UnguardedSymbolsDerive file tokens
          finished.production.rhs finished.origin finished.current :=
        finishedInduction.transport
          (prefix_full_layout finished finishedComplete) rfl rfl
      have finishedSymbol : UnguardedSymbolsDerive file tokens
          [.nonterminal finished.production.lhs]
          waiting.current finished.current :=
        .cons (.nonterminal finished.production.lhs) [] waiting.current
          finished.current finished.current
          ((UnguardedSymbolDerives.nonterminal finished.production
            finished.origin finished.current finishedBody).transport
              rfl sameCursor.symm rfl)
          (.nil finished.current)
      have combined := waitingInduction.append finishedSymbol
      exact combined.transport
        (prefix_complete_layout waiting finished after next advance)
        advance.2.2.1.symm advance.2.2.2.symm

/-- A complete reached item derives its whole expanded production. -/
theorem UnguardedReach.completeDerives
    {file : WorkspaceFile} {tokens : List Token}
    {item : DottedItem tokens}
    (reached : UnguardedReach file tokens item)
    (complete : CompleteItem item) :
    UnguardedSymbolsDerive file tokens item.production.rhs
      item.origin item.current :=
  reached.prefixDerives.transport
    (prefix_full_layout item complete) rfl rfl

/-- Unguarded recognition exposes a source production with an exact
interval derivation. -/
theorem UnguardedRecognizes.derivation
    {file : WorkspaceFile} {tokens : List Token}
    {symbol : NonterminalSymbol} {start finish : Boundary tokens}
    (recognized : UnguardedRecognizes file tokens symbol start finish) :
    ∃ production : ProductionId,
      production.lhs = symbol ∧
      UnguardedSymbolsDerive file tokens production.rhs start finish := by
  rcases recognized with
    ⟨item, reached, complete, lhs, origin, current⟩
  exact ⟨item.production, lhs,
    (reached.completeDerives complete).transport rfl origin current⟩

end Solcore.Surface.Multi
