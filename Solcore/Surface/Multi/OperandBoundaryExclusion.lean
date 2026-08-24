import Solcore.Surface.Multi.ParserJudgment

namespace Solcore.Surface.Multi

open Grammar
open Solcore.Workspace
/-- Recognition by one complete contextual item over an exact interval. -/
def ContextualRecognizes
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) : Prop :=
  ∃ item : ContextualItemKey tokens,
    ContextualReach file tokens memo correct final item ∧
    CompleteItem item.raw ∧ item.raw.production.lhs = symbol ∧
    item.raw.origin = start ∧ item.raw.current = finish

private def contextualRecognizingItemDecision
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens)
    (item : ContextualItemKey tokens) :
    Decidable
      (ContextualReach file tokens memo correct final item ∧
        CompleteItem item.raw ∧ item.raw.production.lhs = symbol ∧
        item.raw.origin = start ∧ item.raw.current = finish) := by
  unfold CompleteItem
  letI : Decidable
      (ContextualReach file tokens memo correct final item) :=
    contextualReachDecision owned correct final item
  infer_instance

/-- Executable recognition test for one exact contextual interval. -/
def contextualRecognizesBool
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) : Bool :=
  (allContextualItems tokens).any fun item =>
    @decide
      (ContextualReach file tokens memo correct final item ∧
        CompleteItem item.raw ∧ item.raw.production.lhs = symbol ∧
        item.raw.origin = start ∧ item.raw.current = finish)
      (contextualRecognizingItemDecision
        owned correct final symbol start finish item)

/-- The executable interval test accepts exactly contextual recognition. -/
theorem contextualRecognizesBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (symbol : NonterminalSymbol)
    (start finish : Boundary tokens) :
    contextualRecognizesBool file tokens owned correct final
        symbol start finish = true ↔
      ContextualRecognizes file tokens memo correct final
        symbol start finish := by
  unfold contextualRecognizesBool ContextualRecognizes
  rw [List.any_eq_true]
  constructor
  · rintro ⟨item, _member, accepted⟩
    letI : Decidable
        (ContextualReach file tokens memo correct final item ∧
          CompleteItem item.raw ∧ item.raw.production.lhs = symbol ∧
          item.raw.origin = start ∧ item.raw.current = finish) :=
      contextualRecognizingItemDecision
        owned correct final symbol start finish item
    exact ⟨item, of_decide_eq_true accepted⟩
  · rintro ⟨item, evidence⟩
    letI : Decidable
        (ContextualReach file tokens memo correct final item ∧
          CompleteItem item.raw ∧ item.raw.production.lhs = symbol ∧
          item.raw.origin = start ∧ item.raw.current = finish) :=
      contextualRecognizingItemDecision
        owned correct final symbol start finish item
    exact ⟨item, allContextualItems_complete item,
      decide_eq_true evidence⟩

private theorem symbolAtBoundary_of_matched
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : Boundary tokens} {symbol : Symbol}
    (terminal : MatchedTerminal file tokens (.symbol symbol))
    (atCursor : terminal.cursor.beforeBoundary = cursor) :
    SymbolAtBoundary file tokens cursor symbol := by
  rcases terminal with
    ⟨terminalCursor, value, span, terminalAt, matchedEvidence⟩
  cases value with
  | retained token =>
      have payload : token.payload = .symbol symbol := by
        simpa [TerminalMatches] using matchedEvidence
      cases terminalAt with
      | retained token inRange lookup valid =>
          exact ⟨terminalCursor, token, atCursor,
            .retained terminalCursor token inRange lookup valid, payload⟩
  | endOfFile => simp [TerminalMatches] at matchedEvidence

/-- Executable observation that a token at one boundary belongs to a
nonassociative operator level. -/
def nonAssociativeOperatorAtBool
    (tokens : List Token) (cursor : Boundary tokens) :
    NonAssociativeLevel → Bool
  | .relational =>
      symbolAtBoundaryBool tokens cursor .less ||
      symbolAtBoundaryBool tokens cursor .greater ||
      symbolAtBoundaryBool tokens cursor .lessEqual ||
      symbolAtBoundaryBool tokens cursor .greaterEqual
  | .equality =>
      symbolAtBoundaryBool tokens cursor .equalEqual ||
      symbolAtBoundaryBool tokens cursor .notEqual

/-- Every declaratively found nonassociative operator is accepted by its
level observation. -/
theorem nonAssociativeOperatorAtBool_eq_true_of_found
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {cursor : Boundary tokens} {level : NonAssociativeLevel}
    {operator : Located InfixOperator}
    (found : FoundNonAssociativeOperatorAt
      file tokens cursor level operator) :
    nonAssociativeOperatorAtBool tokens cursor level = true := by
  cases found with
  | less terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .less).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]
  | greater terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .greater).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]
  | lessEqual terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .lessEqual).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]
  | greaterEqual terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .greaterEqual).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]
  | equal terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .equalEqual).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]
  | notEqual terminal atCursor =>
      have accepted := (symbolAtBoundaryBool_eq_true_iff
        owned cursor .notEqual).mpr
          (symbolAtBoundary_of_matched terminal atCursor)
      simp [nonAssociativeOperatorAtBool, accepted]

private theorem matchedSymbolAtBoundary_exists
    {file : WorkspaceFile} {tokens : List Token}
    {cursor : Boundary tokens} {symbol : Symbol}
    (evidence : SymbolAtBoundary file tokens cursor symbol) :
    ∃ terminal : MatchedTerminal file tokens (.symbol symbol),
      terminal.cursor.beforeBoundary = cursor := by
  rcases evidence with
    ⟨terminalCursor, token, atCursor, terminalAt, payload⟩
  refine ⟨{
    cursor := terminalCursor
    value := .retained token
    span := token.span
    «at» := terminalAt
    «matches» := ?_
  }, atCursor⟩
  simpa [TerminalMatches] using payload

/-- The level observation is exact: acceptance exposes one declaratively
found operator, and every found operator is accepted. -/
theorem nonAssociativeOperatorAtBool_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    (cursor : Boundary tokens) (level : NonAssociativeLevel) :
    nonAssociativeOperatorAtBool tokens cursor level = true ↔
      ∃ operator : Located InfixOperator,
        FoundNonAssociativeOperatorAt
          file tokens cursor level operator := by
  constructor
  · intro accepted
    cases level with
    | relational =>
        simp only [nonAssociativeOperatorAtBool, Bool.or_eq_true]
            at accepted
        rw [symbolAtBoundaryBool_eq_true_iff owned cursor .less,
          symbolAtBoundaryBool_eq_true_iff owned cursor .greater,
          symbolAtBoundaryBool_eq_true_iff owned cursor .lessEqual,
          symbolAtBoundaryBool_eq_true_iff owned cursor .greaterEqual]
            at accepted
        rcases accepted with
          ((less | greater) | lessEqual) | greaterEqual
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            less
          exact ⟨_, .less terminal atCursor⟩
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            greater
          exact ⟨_, .greater terminal atCursor⟩
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            lessEqual
          exact ⟨_, .lessEqual terminal atCursor⟩
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            greaterEqual
          exact ⟨_, .greaterEqual terminal atCursor⟩
    | equality =>
        simp only [nonAssociativeOperatorAtBool, Bool.or_eq_true]
            at accepted
        rw [symbolAtBoundaryBool_eq_true_iff owned cursor .equalEqual,
          symbolAtBoundaryBool_eq_true_iff owned cursor .notEqual]
            at accepted
        rcases accepted with equal | notEqual
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            equal
          exact ⟨_, .equal terminal atCursor⟩
        · obtain ⟨terminal, atCursor⟩ := matchedSymbolAtBoundary_exists
            notEqual
          exact ⟨_, .notEqual terminal atCursor⟩
  · rintro ⟨operator, found⟩
    exact nonAssociativeOperatorAtBool_eq_true_of_found owned found

/-- Forget contextual guard bookkeeping from one reached chart item. -/
theorem ContextualReach.toUnguarded
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item) :
    UnguardedReach file tokens item.raw := by
  induction reached with
  | root => exact .seed (.root .module) (Boundary.start tokens)
  | predict waiting predicted waitingReached next enabled induction =>
      exact .predict waiting.raw predicted induction next
  | scan before after cursor beforeReached structural induction =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      exact .scan before.raw after.raw cursor terminal value span induction
        next atCurrent terminalAt terminalMatches advance
  | complete waiting finished after shared waitingReached finishedReached
      structural waitingInduction finishedInduction =>
      rcases structural.1 with
        ⟨symbol, next, complete, lhs, waitingAtShared,
          finishedAtShared, advance⟩
      have exactNext : NextSymbol waiting.raw
          (.nonterminal finished.raw.production.lhs) := by
        rw [lhs]
        exact next
      exact .complete waiting.raw finished.raw after.raw waitingInduction
        finishedInduction exactNext complete
        (waitingAtShared.trans finishedAtShared.symm) advance

/-- Every reached complete source root recognizes its exact interval after
guard erasure. -/
theorem contextualCompleteRoot_unguardedRecognizes
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    (reached : ContextualReach file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context)) :
    UnguardedRecognizes file tokens (.rule rule) origin finish := by
  refine ⟨(CanonicalCompleteRootItem tokens rule origin finish context).raw,
    reached.toUnguarded, ?_, rfl, rfl, rfl⟩
  exact canonicalCompleteRootItem_complete rule origin finish context

/-- A reached item immediately after its first nonterminal recovers the exact
completed child which advanced that first symbol. -/
theorem contextualReach_one_firstNonterminal
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    {childLhs : NonterminalSymbol} {rest : List GrammarSymbol}
    (reached : ContextualReach file tokens memo correct final item)
    (rhs : item.raw.production.rhs =
      GrammarSymbol.nonterminal childLhs :: rest)
    (one : item.raw.dot.val = 1) :
    ∃ child : ContextualItemKey tokens,
      ContextualReach file tokens memo correct final child ∧
      CompleteItem child.raw ∧
      child.raw.production.lhs = childLhs ∧
      child.raw.origin = item.raw.origin ∧
      child.raw.current = item.raw.current := by
  cases reached with
  | root => contradiction
  | predict => contradiction
  | scan before after cursor beforeReached structural =>
      rcases structural.1 with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have beforeZero : before.raw.dot.val = 0 := by omega
      let index : Nat := before.raw.dot.val
      have impossible : some (GrammarSymbol.nonterminal childLhs) =
          some (GrammarSymbol.terminal terminal) := by
        calc
          _ = item.raw.production.rhs[index]? := by
            rw [rhs]
            simp [index, beforeZero]
          _ = before.raw.production.rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) productionEq
          _ = before.raw.production.rhs[before.raw.dot.val]? := rfl
          _ = _ := next.2
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete waiting finished after shared waitingReached finishedReached
      structural =>
      rcases structural.1 with
        ⟨symbol, next, finishedComplete, lhsEq, waitingAtShared,
          finishedAtShared, advance⟩
      rcases advance with
        ⟨productionEq, dotEq, originEq, currentEq⟩
      have waitingZero : waiting.raw.dot.val = 0 := by omega
      have waitingOriginCurrent := contextualReach_zero_origin_eq_current
        waitingReached waitingZero
      have exactNext : NextSymbol waiting.raw
          (.nonterminal finished.raw.production.lhs) := by
        rw [lhsEq]
        exact next
      let index : Nat := waiting.raw.dot.val
      have selected : some (GrammarSymbol.nonterminal childLhs) =
          some (GrammarSymbol.nonterminal finished.raw.production.lhs) := by
        calc
          _ = item.raw.production.rhs[index]? := by
            rw [rhs]
            simp [index, waitingZero]
          _ = waiting.raw.production.rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) productionEq
          _ = waiting.raw.production.rhs[waiting.raw.dot.val]? := rfl
          _ = _ := exactNext.2
      have finishedLhs : finished.raw.production.lhs = childLhs :=
        (GrammarSymbol.nonterminal.inj (Option.some.inj selected)).symm
      have finishedOrigin : finished.raw.origin = item.raw.origin := by
        calc
          finished.raw.origin = shared := finishedAtShared
          _ = waiting.raw.current := waitingAtShared.symm
          _ = waiting.raw.origin := waitingOriginCurrent.symm
          _ = item.raw.origin := originEq.symm
      exact ⟨finished, finishedReached, finishedComplete, finishedLhs,
        finishedOrigin, currentEq.symm⟩

/-- An auxiliary item for an atom site can only use that site's atom
production. -/
theorem production_eq_atom_of_lhs
    (site : AtomSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    production = .atom site := by
  have impossible {kind : EbnfNodeKind}
      (other : GrammarSiteOfKind kind) (different : kind ≠ .atom)
      (same : other.site = site.site) : False := by
    have otherKind := other.hasKind
    have siteKind := site.hasKind
    rw [same, siteKind] at otherKind
    exact different otherKind.symm
  cases production with
  | root rule => cases lhs
  | atom other =>
      have same : other.site = site.site := NonterminalSymbol.aux.inj lhs
      have exactSite : other = site := by
        cases other
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst other
      rfl
  | seq other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | group other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | choice other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | opt other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | star other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | plus other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list0 other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list1 other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | tail other branch => cases lhs

/-- A reached nonassociative sequence prefix immediately after its first
child contains an unguarded recognition of the lower-precedence operand over
exactly the prefix interval. -/
theorem g10SequencePrefix_contextualOperand
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (level : NonAssociativeLevel)
    (sequenceSite : SequenceSite) (firstSite secondSite : GrammarSite)
    (children : sequenceSite.children = [firstSite, secondSite])
    (firstShape : firstSite.expression =
      .atom (.nonterminal level.operandRule))
    (item : ContextualItemKey tokens)
    (production : item.raw.production = .seq sequenceSite)
    (one : item.raw.dot.val = 1)
    (reached : ContextualReach file tokens memo correct final item) :
    ContextualRecognizes file tokens memo correct final
      (.rule level.operandRule)
      item.raw.origin item.raw.current := by
  let atomSite : AtomSite := ⟨firstSite, by
    rw [firstShape]
    rfl⟩
  have atomSiteEq : atomSite.site = firstSite := rfl
  have itemRhs : item.raw.production.rhs =
      GrammarSymbol.nonterminal (.aux firstSite) ::
        [GrammarSymbol.nonterminal (.aux secondSite)] := by
    rw [production, ProductionId.rhs_seq, children]
    rfl
  obtain ⟨atomItem, atomReached, atomComplete, atomLhs,
      atomOrigin, atomCurrent⟩ :=
    contextualReach_one_firstNonterminal reached itemRhs one
  have exactAtomLhs : atomItem.raw.production.lhs = .aux atomSite.site := by
    simpa only [atomSiteEq] using atomLhs
  have atomProduction : atomItem.raw.production = .atom atomSite :=
    production_eq_atom_of_lhs atomSite atomItem.raw.production exactAtomLhs
  have selectedAtom : atomSite.atom = .nonterminal level.operandRule := by
    exact EbnfExpr.atom.inj
      (atomSite.expression_eq_atom.symm.trans firstShape)
  have atomRhs : atomItem.raw.production.rhs =
      [GrammarSymbol.nonterminal (.rule level.operandRule)] := by
    rw [atomProduction, ProductionId.rhs_atom]
    simp [AtomSite.symbol, selectedAtom, EbnfAtom.grammarSymbol]
  obtain ⟨operand, operandReached, operandComplete, operandLhs,
      operandOrigin, operandCurrent⟩ :=
    contextualReach_complete_singleNonterminal atomReached atomRhs atomComplete
  refine ⟨operand, operandReached, operandComplete,
    operandLhs, ?_, ?_⟩
  · exact operandOrigin.trans atomOrigin
  · exact operandCurrent.trans atomCurrent

/-- The remaining context-free grammar fact needed by G10: once a lower
precedence operand has completed immediately before a same-level operator, a
second operand from the same origin cannot absorb that operator and finish
later.  Delimiter-protected recursive expressions are intentionally allowed;
the shorter recognition at the operator frontier is what makes this the exact
prefix-exclusion statement. -/
def NonAssociativeOperandPrefixExclusive
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel)
      (origin split finish : Boundary tokens)
      (operator : Located InfixOperator),
    ContextualRecognizes file tokens memo correct final
      (.rule level.operandRule) origin split →
    ContextualRecognizes file tokens memo correct final
      (.rule level.operandRule) origin finish →
    FoundNonAssociativeOperatorAt file tokens split level operator →
    split.val < finish.val → False

/-- Stable finite enumeration of the two nonassociative levels. -/
def allNonAssociativeLevels : List NonAssociativeLevel :=
  [.relational, .equality]

theorem allNonAssociativeLevels_complete
    (level : NonAssociativeLevel) :
    level ∈ allNonAssociativeLevels := by
  cases level <;> simp [allNonAssociativeLevels]

/-- Stable finite enumeration of every boundary of one retained stream. -/
def allOperandBoundaries (tokens : List Token) :
    List (Boundary tokens) :=
  List.ofFn id

theorem allOperandBoundaries_complete
    {tokens : List Token} (cursor : Boundary tokens) :
    cursor ∈ allOperandBoundaries tokens := by
  rw [allOperandBoundaries, List.mem_ofFn]
  exact ⟨cursor, rfl⟩

/-- One executable cell rejects an operand recognition that extends across a
same-level operator after an already completed prefix. -/
def nonAssociativeOperandPrefixExclusiveCell
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (level : NonAssociativeLevel)
    (origin split finish : Boundary tokens) : Bool :=
  !(
    contextualRecognizesBool file tokens owned correct final
      (.rule level.operandRule) origin split &&
    contextualRecognizesBool file tokens owned correct final
      (.rule level.operandRule) origin finish &&
    nonAssociativeOperatorAtBool tokens split level &&
    decide (split.val < finish.val))

/-- One cell is exact for its fixed origin, split, finish, and level. -/
theorem nonAssociativeOperandPrefixExclusiveCell_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (level : NonAssociativeLevel)
    (origin split finish : Boundary tokens) :
    nonAssociativeOperandPrefixExclusiveCell
        file tokens owned correct final level origin split finish = true ↔
      ¬ (ContextualRecognizes file tokens memo correct final
            (.rule level.operandRule) origin split ∧
          ContextualRecognizes file tokens memo correct final
            (.rule level.operandRule) origin finish ∧
          (∃ operator : Located InfixOperator,
            FoundNonAssociativeOperatorAt
              file tokens split level operator) ∧
          split.val < finish.val) := by
  let bad :=
    contextualRecognizesBool file tokens owned correct final
        (.rule level.operandRule) origin split &&
      contextualRecognizesBool file tokens owned correct final
        (.rule level.operandRule) origin finish &&
      nonAssociativeOperatorAtBool tokens split level &&
      decide (split.val < finish.val)
  have badTrue : bad = true ↔
      ContextualRecognizes file tokens memo correct final
          (.rule level.operandRule) origin split ∧
        ContextualRecognizes file tokens memo correct final
          (.rule level.operandRule) origin finish ∧
        (∃ operator : Located InfixOperator,
          FoundNonAssociativeOperatorAt
            file tokens split level operator) ∧
        split.val < finish.val := by
    simp [bad, contextualRecognizesBool_eq_true_iff
      owned correct final,
      nonAssociativeOperatorAtBool_eq_true_iff owned, and_assoc]
  unfold nonAssociativeOperandPrefixExclusiveCell
  change Bool.not bad = true ↔ _
  constructor
  · intro accepted evidence
    have badAccepted := badTrue.mpr evidence
    simp [badAccepted] at accepted
  · intro excluded
    cases badEq : bad with
    | false => simp
    | true => exact (excluded (badTrue.mp badEq)).elim

/-- Finite executable certificate for every origin, split, finish, and
nonassociative level in one contextual ledger. -/
def nonAssociativeOperandPrefixExclusiveTable
    (file : WorkspaceFile) (tokens : List Token)
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Bool :=
  allNonAssociativeLevels.all fun level =>
    (allOperandBoundaries tokens).all fun origin =>
      (allOperandBoundaries tokens).all fun split =>
        (allOperandBoundaries tokens).all fun finish =>
          nonAssociativeOperandPrefixExclusiveCell
            file tokens owned correct final level origin split finish

/-- An accepted finite table constructs the exact operand-prefix exclusion
interface consumed by G10 completion alignment. -/
theorem nonAssociativeOperandPrefixExclusive_of_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (accepted : nonAssociativeOperandPrefixExclusiveTable
      file tokens owned correct final = true) :
    NonAssociativeOperandPrefixExclusive
      file tokens memo correct final := by
  intro level origin split finish operator short long found later
  have levelAccepted := (List.all_eq_true.mp accepted)
    level (allNonAssociativeLevels_complete level)
  have originAccepted := (List.all_eq_true.mp levelAccepted)
    origin (allOperandBoundaries_complete origin)
  have splitAccepted := (List.all_eq_true.mp originAccepted)
    split (allOperandBoundaries_complete split)
  have cellAccepted := (List.all_eq_true.mp splitAccepted)
    finish (allOperandBoundaries_complete finish)
  have shortAccepted :=
    (contextualRecognizesBool_eq_true_iff owned correct final
      (.rule level.operandRule) origin split).mpr short
  have longAccepted :=
    (contextualRecognizesBool_eq_true_iff owned correct final
      (.rule level.operandRule) origin finish).mpr long
  have foundAccepted :=
    nonAssociativeOperatorAtBool_eq_true_of_found owned found
  have laterAccepted : decide (split.val < finish.val) = true :=
    decide_eq_true later
  simp [nonAssociativeOperandPrefixExclusiveCell, shortAccepted,
    longAccepted, foundAccepted, laterAccepted] at cellAccepted

/-- The finite table is equivalent to the declarative operand-prefix
exclusion property. -/
theorem nonAssociativeOperandPrefixExclusiveTable_eq_true_iff
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) :
    nonAssociativeOperandPrefixExclusiveTable
        file tokens owned correct final = true ↔
      NonAssociativeOperandPrefixExclusive
        file tokens memo correct final := by
  constructor
  · exact nonAssociativeOperandPrefixExclusive_of_table
      owned correct final
  · intro exclusive
    unfold nonAssociativeOperandPrefixExclusiveTable
    apply List.all_eq_true.mpr
    intro level _levelMember
    apply List.all_eq_true.mpr
    intro origin _originMember
    apply List.all_eq_true.mpr
    intro split _splitMember
    apply List.all_eq_true.mpr
    intro finish _finishMember
    apply (nonAssociativeOperandPrefixExclusiveCell_eq_true_iff
      owned correct final level origin split finish).mpr
    rintro ⟨short, long, ⟨operator, found⟩, later⟩
    exact exclusive level origin split finish operator
      short long found later

/-- The pure prefix-exclusion fact bounds any competing reached sequence
prefix by the operand frontier immediately before the same-level operator. -/
theorem g10SequencePrefix_competitor_le
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (exclusive : NonAssociativeOperandPrefixExclusive
      file tokens memo correct final)
    (level : NonAssociativeLevel)
    (sequenceSite : SequenceSite) (firstSite secondSite : GrammarSite)
    (children : sequenceSite.children = [firstSite, secondSite])
    (firstShape : firstSite.expression =
      .atom (.nonterminal level.operandRule))
    (left right : ContextualItemKey tokens)
    (leftProduction : left.raw.production = .seq sequenceSite)
    (rightProduction : right.raw.production = .seq sequenceSite)
    (leftOne : left.raw.dot.val = 1)
    (rightOne : right.raw.dot.val = 1)
    (leftReached : ContextualReach file tokens memo correct final left)
    (rightReached : ContextualReach file tokens memo correct final right)
    (sameOrigin : left.raw.origin = right.raw.origin)
    {operator : Located InfixOperator}
    (found : FoundNonAssociativeOperatorAt file tokens left.raw.current
      level operator) :
    right.raw.current.val ≤ left.raw.current.val := by
  apply Nat.le_of_not_gt
  intro later
  have leftOperand := g10SequencePrefix_contextualOperand level sequenceSite
    firstSite secondSite children firstShape left leftProduction leftOne
      leftReached
  have rightOperand := g10SequencePrefix_contextualOperand level sequenceSite
    firstSite secondSite children firstShape right rightProduction rightOne
      rightReached
  exact exclusive level left.raw.origin left.raw.current right.raw.current
    operator leftOperand (sameOrigin ▸ rightOperand) found later

end Solcore.Surface.Multi
