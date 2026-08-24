import Solcore.Surface.Multi.OperandBoundaryExclusion
import Solcore.Surface.Multi.NonAssociativeOptionalStrict

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The local fact produced by inversion of a reached present optional: its
first token is the level operator, and the optional consumes input. -/
def NonAssociativeOptionalSomeOperatorProducer
    (file : WorkspaceFile) (tokens : List Token)
    (memo : GuardMemo tokens)
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo) : Prop :=
  ∀ (level : NonAssociativeLevel) (site : OptionalSite)
      (item : ContextualItemKey tokens),
    ContextualReach file tokens memo correct final item →
    item.raw.production = .opt site .some →
    site.site.expression = .optional level.tailExpr →
    CompleteItem item.raw →
    ∃ operator, FoundNonAssociativeOperatorAt file tokens item.raw.origin
      level operator

/-- A production whose auxiliary left-hand side is an optional grammar site
is one of that site's two optional productions. -/
theorem g10Production_optional_of_lhs
    (site : GrammarSite) (child : EbnfExpr)
    (shape : site.expression = .optional child)
    (production : ProductionId)
    (lhs : production.lhs = .aux site) :
    ∃ refined branch,
      refined.site = site ∧ production = .opt refined branch := by
  have siteKind : site.expression.kind = .optional := by
    simp [shape, EbnfExpr.kind]
  have impossible {kind : EbnfNodeKind}
      (refined : GrammarSiteOfKind kind) (different : kind ≠ .optional)
      (same : refined.site = site) : False := by
    have actual := refined.hasKind
    rw [same, siteKind] at actual
    exact different actual.symm
  cases production with
  | root rule => cases lhs
  | atom refined => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | seq refined => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | group refined => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | choice refined branch => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | opt refined branch =>
      exact ⟨refined, branch, NonterminalSymbol.aux.inj lhs, rfl⟩
  | star refined branch => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | plus refined branch => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list0 refined branch => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list1 refined => exact (impossible refined (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | tail refined branch => cases lhs

/-- A completion advancing the second child of a complete two-child sequence
has exactly the optional production and prefix coordinates expected by G10. -/
theorem g10OptionalCompletionView
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (level : NonAssociativeLevel)
    (sequenceSite : SequenceSite) (firstSite secondSite : GrammarSite)
    (children : sequenceSite.children = [firstSite, secondSite])
    (secondShape : secondSite.expression = .optional level.tailExpr)
    {waiting finished sequence : ContextualItemKey tokens}
    {shared : Boundary tokens}
    (sequenceProduction : sequence.raw.production = .seq sequenceSite)
    (sequenceComplete : CompleteItem sequence.raw)
    (edge : ContextualEdgeReach file tokens memo correct final
      (.completed waiting finished sequence shared)) :
    ∃ site branch,
      finished.raw.production = .opt site branch ∧
      site.site = secondSite ∧
      waiting.raw.production = .seq sequenceSite ∧
      waiting.raw.dot.val = 1 := by
  obtain ⟨witness⟩ := packedEdge_completed_valid_iff.mp edge.1.1
  have sequenceDot : sequence.raw.dot.val = 2 := by
    calc
      _ = sequence.raw.production.rhs.length := sequenceComplete
      _ = (ProductionId.seq sequenceSite).rhs.length := congrArg
        (fun production : ProductionId => production.rhs.length)
          sequenceProduction
      _ = 2 := by simp [ProductionId.rhs_seq, children]
  have waitingProduction : waiting.raw.production = .seq sequenceSite :=
    witness.advance.1.symm.trans sequenceProduction
  have waitingOne : waiting.raw.dot.val = 1 := by
    have advanced := witness.advance.2.1
    omega
  have finishedLhs : finished.raw.production.lhs = .aux secondSite := by
    have lookup : some (GrammarSymbol.nonterminal
          finished.raw.production.lhs) =
        some (GrammarSymbol.nonterminal (.aux secondSite)) := by
      calc
        _ = waiting.raw.production.rhs[waiting.raw.dot.val]? :=
          witness.next.2.symm
        _ = (ProductionId.seq sequenceSite).rhs[1]? := by
          rw [waitingOne, waitingProduction]
        _ = _ := by simp [ProductionId.rhs_seq, children]
    exact GrammarSymbol.nonterminal.inj (Option.some.inj lookup)
  obtain ⟨site, branch, siteEq, production⟩ :=
    g10Production_optional_of_lhs secondSite level.tailExpr secondShape
      finished.raw.production finishedLhs
  exact ⟨site, branch, production, siteEq, waitingProduction, waitingOne⟩

/-- Operand-prefix exclusion makes a reached present optional the unique
completed child that can advance the canonical two-child sequence. -/
theorem g10NonAssociativeOptional_finished_eq
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (exclusive : NonAssociativeOperandPrefixExclusive
      file tokens memo correct final)
    (producer : NonAssociativeOptionalSomeOperatorProducer
      file tokens memo correct final)
    (level : NonAssociativeLevel)
    (sequenceSite : SequenceSite) (firstSite secondSite : GrammarSite)
    (children : sequenceSite.children = [firstSite, secondSite])
    (firstShape : firstSite.expression =
      .atom (.nonterminal level.operandRule))
    (secondShape : secondSite.expression = .optional level.tailExpr)
    {sequence leftWaiting leftFinished rightWaiting rightFinished :
      ContextualItemKey tokens}
    {leftShared rightShared : Boundary tokens}
    {site : OptionalSite}
    (sequenceProduction : sequence.raw.production = .seq sequenceSite)
    (sequenceComplete : CompleteItem sequence.raw)
    (leftEdge : ContextualEdgeReach file tokens memo correct final
      (.completed leftWaiting leftFinished sequence leftShared))
    (siteEq : site.site = secondSite)
    (leftProduction : leftFinished.raw.production = .opt site .some)
    (rightEdge : ContextualEdgeReach file tokens memo correct final
      (.completed rightWaiting rightFinished sequence rightShared)) :
    rightFinished = leftFinished := by
  obtain ⟨leftWitness⟩ := packedEdge_completed_valid_iff.mp leftEdge.1.1
  obtain ⟨rightWitness⟩ := packedEdge_completed_valid_iff.mp rightEdge.1.1
  obtain ⟨leftSite, leftBranch, leftProduction', leftViewSiteEq,
      leftWaitingProduction, leftOne⟩ :=
    g10OptionalCompletionView level sequenceSite firstSite secondSite children
      secondShape sequenceProduction sequenceComplete leftEdge
  obtain ⟨rightSite, rightBranch, rightProduction, rightViewSiteEq,
      rightWaitingProduction, rightOne⟩ :=
    g10OptionalCompletionView level sequenceSite firstSite secondSite children
      secondShape sequenceProduction sequenceComplete rightEdge
  have leftSiteFixed : leftSite = site := by
    cases leftSite
    cases site
    simp only at leftViewSiteEq siteEq ⊢
    subst_vars
    rfl
  have rightSiteFixed : rightSite = site := by
    cases rightSite
    cases site
    simp only at rightViewSiteEq siteEq ⊢
    subst_vars
    rfl
  subst leftSite
  subst rightSite
  have leftBranchSome : leftBranch = .some := by
    rw [leftProduction'] at leftProduction
    exact ProductionId.opt.inj leftProduction |>.2
  subst leftBranch
  have fixedShape : site.site.expression =
      .optional level.tailExpr :=
    (congrArg GrammarSite.expression siteEq).trans secondShape
  obtain ⟨leftOperator, leftFound⟩ :=
    producer level site leftFinished leftEdge.2.2.1
      leftProduction fixedShape leftWitness.complete
  have leftStrict :=
    contextualReach_complete_nonAssociativeOptionalSome_strict level site
      leftEdge.2.2.1 leftProduction fixedShape leftWitness.complete
  have foundAtLeft : FoundNonAssociativeOperatorAt file tokens
      leftWaiting.raw.current level leftOperator := by
    rw [leftWitness.waitingAtShared, ← leftWitness.finishedAtShared]
    exact leftFound
  have sameOrigin : leftWaiting.raw.origin = rightWaiting.raw.origin :=
    leftWitness.advance.2.2.1.symm.trans rightWitness.advance.2.2.1
  have rightLeLeft := g10SequencePrefix_competitor_le exclusive level
    sequenceSite firstSite secondSite children firstShape leftWaiting
    rightWaiting leftWaitingProduction rightWaitingProduction leftOne rightOne
    leftEdge.2.1 rightEdge.2.1 sameOrigin foundAtLeft
  cases rightBranch with
  | none =>
      have rightZero : rightFinished.raw.dot.val = 0 := by
        have rightComplete := rightWitness.complete
        unfold CompleteItem at rightComplete
        calc
          _ = rightFinished.raw.production.rhs.length := rightComplete
          _ = (ProductionId.opt site .none).rhs.length := congrArg
            (fun production : ProductionId => production.rhs.length)
              rightProduction
          _ = 0 := rfl
      have rightOriginCurrent := contextualReach_zero_origin_eq_current
        rightEdge.2.2.1 rightZero
      have leftOriginVal := congrArg Fin.val leftWitness.finishedAtShared
      have leftCurrentVal := congrArg Fin.val
        leftWitness.advance.2.2.2.symm
      have leftWaitingVal := congrArg Fin.val leftWitness.waitingAtShared
      have rightOriginVal := congrArg Fin.val rightWitness.finishedAtShared
      have rightCurrentVal := congrArg Fin.val
        rightWitness.advance.2.2.2.symm
      have rightWaitingVal := congrArg Fin.val rightWitness.waitingAtShared
      have rightZeroVal := congrArg Fin.val rightOriginCurrent
      omega
  | some =>
      obtain ⟨rightOperator, rightFound⟩ :=
        producer level site rightFinished rightEdge.2.2.1
          rightProduction fixedShape rightWitness.complete
      have foundAtRight : FoundNonAssociativeOperatorAt file tokens
          rightWaiting.raw.current level rightOperator := by
        rw [rightWitness.waitingAtShared, ← rightWitness.finishedAtShared]
        exact rightFound
      have leftLeRight := g10SequencePrefix_competitor_le exclusive level
        sequenceSite firstSite secondSite children firstShape rightWaiting
        leftWaiting rightWaitingProduction leftWaitingProduction rightOne leftOne
        rightEdge.2.1 leftEdge.2.1 sameOrigin.symm foundAtRight
      have waitingCurrentEq : rightWaiting.raw.current =
          leftWaiting.raw.current := Fin.ext (Nat.le_antisymm rightLeLeft leftLeRight)
      have sharedEq : rightShared = leftShared :=
        rightWitness.waitingAtShared.symm.trans
          (waitingCurrentEq.trans leftWitness.waitingAtShared)
      exact g10CompletedEdge_finished_eq_of_coordinates rightEdge leftEdge
        sharedEq (rightProduction.trans leftProduction.symm)

/-- A structural present-optional completion forces every coherent semantic
reduction of the same canonical root to expose a completed operation, using
only root-local and optional-local completion alignment. -/
theorem g10CompletedValue_of_presentCompletionEdges_of_operandPrefixExclusive
    {file : WorkspaceFile} {tokens : List Token} {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo} {final : AllGuardsFinal memo}
    (exclusive : NonAssociativeOperandPrefixExclusive
      file tokens memo correct final)
    (producer : NonAssociativeOptionalSomeOperatorProducer
      file tokens memo correct final)
    {cursor : Boundary tokens} {level : NonAssociativeLevel}
    {origin : Boundary tokens} {context : GuardContext tokens}
    {output : RuleValue level.rule}
    (rootReduction : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens level.rule origin cursor context) output)
    {rootWaiting sequence : ContextualItemKey tokens}
    {rootShared : Boundary tokens}
    (rootReached : ContextualEdgeReach file tokens memo correct final
      (.completed rootWaiting sequence (CanonicalCompleteRootItem tokens
        level.rule origin cursor context) rootShared))
    {sequenceWaiting optional : ContextualItemKey tokens}
    {optionalShared : Boundary tokens} {site : OptionalSite}
    (optionalReached : ContextualEdgeReach file tokens memo correct final
      (.completed sequenceWaiting optional sequence optionalShared))
    (optionalProduction : optional.raw.production = .opt site .some) :
    ∃ first, CompletedNonAssociativeValue level output first := by
  obtain ⟨rootWitness⟩ := packedEdge_completed_valid_iff.mp rootReached.1.1
  have rootWaitingProduction : rootWaiting.raw.production = .root level.rule :=
    rootWitness.advance.1.symm
  have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
    have advanced := rootWitness.advance.2.1
    change 1 = rootWaiting.raw.dot.val + 1 at advanced
    omega
  have sequenceLhs : sequence.raw.production.lhs =
      .aux (GrammarSite.root level.rule) := by
    have selected : some (GrammarSymbol.nonterminal
          sequence.raw.production.lhs) =
        some (GrammarSymbol.nonterminal
          (.aux (GrammarSite.root level.rule))) := by
      calc
        _ = rootWaiting.raw.production.rhs[rootWaiting.raw.dot.val]? :=
          rootWitness.next.2.symm
        _ = (ProductionId.root level.rule).rhs[0]? := by
          rw [rootWaitingDot, rootWaitingProduction]
        _ = _ := by simp [ProductionId.rhs]
    exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
  obtain ⟨sequenceSite, sequenceProduction⟩ :=
    g10NonAssociativeRootChild_isSequence level sequence.raw.production
      sequenceLhs
  have sequenceSiteRoot : sequenceSite.site = GrammarSite.root level.rule := by
    rw [sequenceProduction] at sequenceLhs
    exact NonterminalSymbol.aux.inj sequenceLhs
  have childrenExpressions := SequenceSite.children_expression sequenceSite
  rw [sequenceSiteRoot, GrammarSite.root_expression,
    g10NonAssociative_rhs_eq] at childrenExpressions
  simp only [EbnfExpr.children] at childrenExpressions
  have childrenLength : sequenceSite.children.length = 2 := by
    have exactLength := congrArg List.length childrenExpressions
    simpa using exactLength
  obtain ⟨firstSite, secondSite, children⟩ :=
    g10List_eq_pair_of_length_two sequenceSite.children childrenLength
  have shapes : firstSite.expression =
        .atom (.nonterminal level.operandRule) ∧
      secondSite.expression = .optional level.tailExpr := by
    simpa [children] using childrenExpressions
  obtain ⟨viewSite, branch, viewProduction, viewSiteEq,
      _, _⟩ := g10OptionalCompletionView level sequenceSite firstSite
    secondSite children shapes.2 sequenceProduction rootWitness.complete
      optionalReached
  have viewSiteIsSite : viewSite = site :=
    (ProductionId.opt.inj
      (viewProduction.symm.trans optionalProduction)).1
  have siteEq : site.site = secondSite :=
    (congrArg GrammarSiteOfKind.site viewSiteIsSite).symm.trans viewSiteEq
  apply g10CompletedValue_of_presentCompletionEdges_of_aligned rootReduction
    rootReached optionalReached optionalProduction
  · intro waiting finished shared edge
    rcases g10NonAssociativeRoot_completion_backpointer edge rootReached with
      ⟨sharedEq, productionEq⟩
    exact g10CompletedEdge_finished_eq_of_coordinates edge rootReached
      sharedEq productionEq
  · intro waiting finished shared edge
    exact g10NonAssociativeOptional_finished_eq exclusive producer level
      sequenceSite firstSite secondSite children shapes.1 shapes.2
      sequenceProduction rootWitness.complete optionalReached siteEq
      optionalProduction edge

end Solcore.Surface.Multi
