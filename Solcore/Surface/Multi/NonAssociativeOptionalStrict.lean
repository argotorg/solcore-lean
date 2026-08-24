import Solcore.Surface.Multi.AuxiliaryInversion

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- The present outer optional of a relational/equality tail necessarily
crosses one operator terminal. -/
theorem contextualReach_complete_nonAssociativeOptionalSome_strict
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    (level : NonAssociativeLevel) (site : OptionalSite)
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .opt site .some)
    (shape : site.site.expression = .optional level.tailExpr)
    (complete : CompleteItem item.raw) :
    item.raw.origin.val < item.raw.current.val := by
  obtain ⟨operators, operand, tailShape⟩ :
      ∃ (operators : List TerminalSymbol) (operand : EbnfExpr),
        site.site.expression = .optional (.sequence [
          .group (.choice (operators.map fun terminal =>
            .atom (.terminal terminal))), operand]) := by
    cases level
    · exact ⟨[.symbol .less, .symbol .greater, .symbol .lessEqual,
        .symbol .greaterEqual], .atom (.nonterminal .bitOr), shape⟩
    · exact ⟨[.symbol .equalEqual, .symbol .notEqual],
        .atom (.nonterminal .relational), shape⟩
  have childShape : site.child.expression = .sequence [
      .group (.choice (operators.map fun terminal =>
        .atom (.terminal terminal))), operand] :=
    EbnfExpr.optional.inj
      ((OptionalSite.expression_eq_optional site).symm.trans tailShape)
  have itemRhs : item.raw.production.rhs =
      [GrammarSymbol.nonterminal (.aux site.child)] := by
    rw [production]
    rfl
  rcases contextualReach_complete_singleNonterminal reached itemRhs complete with
    ⟨sequence, sequenceReached, sequenceComplete, sequenceLhs,
      sequenceOrigin, sequenceCurrent⟩
  have sequenceView := auxiliaryProductionView site.child
    sequence.raw.production sequenceLhs
  have exactSequenceView : AuxiliaryProductionView site.child
      sequence.raw.production .sequence := by
    simpa [childShape, EbnfExpr.kind] using sequenceView
  cases exactSequenceView with
  | sequence sequenceSite sequenceSiteEq sequenceProduction =>
    have childrenExpressions := SequenceSite.children_expression sequenceSite
    rw [sequenceSiteEq, childShape] at childrenExpressions
    simp only [EbnfExpr.children] at childrenExpressions
    have childrenLength : sequenceSite.children.length = 2 := by
      have exactLength := congrArg List.length childrenExpressions
      simpa using exactLength
    obtain ⟨operatorSite, operandSite, childrenEq⟩ :=
      g10List_eq_pair_of_length_two sequenceSite.children childrenLength
    have childExpressions : operatorSite.expression =
          .group (.choice (operators.map fun terminal =>
            .atom (.terminal terminal))) ∧
        operandSite.expression = operand := by
      simpa [childrenEq] using childrenExpressions
    have sequenceDot : sequence.raw.dot.val = 2 := by
      calc
        _ = sequence.raw.production.rhs.length := sequenceComplete
        _ = (ProductionId.seq sequenceSite).rhs.length := congrArg
          (fun selected : ProductionId => selected.rhs.length)
            sequenceProduction
        _ = 2 := by simp [ProductionId.rhs_seq, childrenEq]
    have operandSelected : sequence.raw.production.rhs[1]? =
        some (.nonterminal (.aux operandSite)) := by
      rw [sequenceProduction]
      simp [ProductionId.rhs_seq, childrenEq]
    rcases contextualReach_nonterminal_step sequenceReached sequenceDot
        operandSelected with
      ⟨sequenceWaiting, operandItem, sequenceWaitingReached, operandReached,
        operandComplete, operandLhs, sequenceWaitingDot,
        sequenceWaitingProduction, sequenceWaitingOrigin,
        operandOriginWaiting, operandCurrent⟩
    have operatorSelected : sequenceWaiting.raw.production.rhs[0]? =
        some (.nonterminal (.aux operatorSite)) := by
      rw [sequenceWaitingProduction]
      rw [sequenceProduction]
      simp [ProductionId.rhs_seq, childrenEq]
    rcases contextualReach_nonterminal_step sequenceWaitingReached
        sequenceWaitingDot operatorSelected with
      ⟨firstWaiting, groupItem, firstWaitingReached, groupReached,
        groupComplete, groupLhs, firstWaitingDot, firstWaitingProduction,
        firstWaitingOrigin, groupOriginWaiting, groupCurrent⟩
    have firstWaitingOriginCurrent :=
      contextualReach_zero_origin_eq_current firstWaitingReached firstWaitingDot
    have groupOrigin : groupItem.raw.origin = sequence.raw.origin :=
      groupOriginWaiting.trans (firstWaitingOriginCurrent.symm.trans
        (firstWaitingOrigin.trans sequenceWaitingOrigin))
    have groupView := auxiliaryProductionView operatorSite
      groupItem.raw.production groupLhs
    have exactGroupView : AuxiliaryProductionView operatorSite
        groupItem.raw.production .group := by
      simpa [childExpressions.1, EbnfExpr.kind] using groupView
    cases exactGroupView with
    | group groupSite groupSiteEq groupProduction =>
      have choiceShape : groupSite.child.expression =
          .choice (operators.map fun terminal => .atom (.terminal terminal)) :=
        EbnfExpr.group.inj ((GroupSite.expression_eq_group groupSite).symm.trans
          ((congrArg GrammarSite.expression groupSiteEq).trans
            childExpressions.1))
      have groupRhs : groupItem.raw.production.rhs =
          [GrammarSymbol.nonterminal (.aux groupSite.child)] := by
        rw [groupProduction]
        rfl
      rcases contextualReach_complete_singleNonterminal groupReached groupRhs
          groupComplete with
        ⟨choiceItem, choiceReached, choiceComplete, choiceLhs,
          choiceOrigin, choiceCurrent⟩
      have choiceView := auxiliaryProductionView groupSite.child
        choiceItem.raw.production choiceLhs
      have exactChoiceView : AuxiliaryProductionView groupSite.child
          choiceItem.raw.production .choice := by
        simpa [choiceShape, EbnfExpr.kind] using choiceView
      cases exactChoiceView with
      | choice choiceSite branch choiceSiteEq choiceProduction =>
        have branchShape : choiceSite.branchExpressions.get branch ∈
            operators.map (fun terminal => .atom (.terminal terminal)) := by
          have member := List.get_mem choiceSite.branchExpressions.toList
            (choiceSite.branchListIndex branch)
          rw [ChoiceSite.branch_get_toList] at member
          have branchesEq : choiceSite.branchExpressions.toList =
              operators.map (fun terminal => .atom (.terminal terminal)) :=
            EbnfExpr.choice.inj ((ChoiceSite.expression_eq_choice choiceSite).symm.trans
              ((congrArg GrammarSite.expression choiceSiteEq).trans choiceShape))
          simpa [branchesEq] using member
        rcases List.mem_map.mp branchShape with
          ⟨terminal, terminalMember, branchExpression⟩
        have atomShape : (choiceSite.branch branch).expression =
            .atom (.terminal terminal) :=
          (ChoiceSite.branch_expression choiceSite branch).trans
            branchExpression.symm
        have choiceRhs : choiceItem.raw.production.rhs =
            [GrammarSymbol.nonterminal (.aux (choiceSite.branch branch))] := by
          rw [choiceProduction]
          rfl
        rcases contextualReach_complete_singleNonterminal choiceReached choiceRhs
            choiceComplete with
          ⟨atomItem, atomReached, atomComplete, atomLhs,
            atomOrigin, atomCurrent⟩
        have atomView := auxiliaryProductionView (choiceSite.branch branch)
          atomItem.raw.production atomLhs
        have exactAtomView : AuxiliaryProductionView
            (choiceSite.branch branch) atomItem.raw.production .atom := by
          simpa [atomShape, EbnfExpr.kind] using atomView
        cases exactAtomView with
        | atom atomSite atomSiteEq atomProduction =>
          have atomEq : atomSite.atom = .terminal terminal :=
            EbnfExpr.atom.inj ((AtomSite.expression_eq_atom atomSite).symm.trans
              ((congrArg GrammarSite.expression atomSiteEq).trans atomShape))
          have atomDot : atomItem.raw.dot.val = 1 := by
            calc
              _ = atomItem.raw.production.rhs.length := atomComplete
              _ = (ProductionId.atom atomSite).rhs.length := congrArg
                (fun selected : ProductionId => selected.rhs.length)
                  atomProduction
              _ = 1 := rfl
          have atomSelected : atomItem.raw.production.rhs[0]? =
              some (.terminal terminal) := by
            rw [atomProduction]
            change some atomSite.atom.grammarSymbol =
              some (GrammarSymbol.terminal terminal)
            rw [atomEq]
            rfl
          have atomStrict := contextualReach_terminal_step_strict atomReached
            atomDot atomSelected
          have operandOrdered := contextualReach_ordered operandReached
          rw [atomOrigin, choiceOrigin, groupOrigin, atomCurrent,
            choiceCurrent, groupCurrent] at atomStrict
          have operandOriginValue := congrArg Fin.val operandOriginWaiting
          have operandCurrentValue := congrArg Fin.val operandCurrent
          have sequenceOriginValue := congrArg Fin.val sequenceOrigin
          have sequenceCurrentValue := congrArg Fin.val sequenceCurrent
          omega

/-- Inversion of a present optional exposes the first matched terminal of its
operator-choice child at the optional's origin. -/
theorem contextualReach_complete_optionalSome_firstTerminal
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    (site : OptionalSite) (operators : List TerminalSymbol)
    (operand : EbnfExpr)
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .opt site .some)
    (shape : site.site.expression = .optional (.sequence [
      .group (.choice (operators.map fun terminal =>
        .atom (.terminal terminal))), operand]))
    (complete : CompleteItem item.raw) :
    ∃ terminal, terminal ∈ operators ∧
      ∃ matched : MatchedTerminal file tokens terminal,
        matched.cursor.beforeBoundary = item.raw.origin := by
  have childShape : site.child.expression = .sequence [
      .group (.choice (operators.map fun terminal =>
        .atom (.terminal terminal))), operand] :=
    EbnfExpr.optional.inj
      ((OptionalSite.expression_eq_optional site).symm.trans shape)
  have itemRhs : item.raw.production.rhs =
      [GrammarSymbol.nonterminal (.aux site.child)] := by
    rw [production]
    rfl
  rcases contextualReach_complete_singleNonterminal reached itemRhs complete with
    ⟨sequence, sequenceReached, sequenceComplete, sequenceLhs,
      sequenceOrigin, sequenceCurrent⟩
  have sequenceView := auxiliaryProductionView site.child
    sequence.raw.production sequenceLhs
  have exactSequenceView : AuxiliaryProductionView site.child
      sequence.raw.production .sequence := by
    simpa [childShape, EbnfExpr.kind] using sequenceView
  cases exactSequenceView with
  | sequence sequenceSite sequenceSiteEq sequenceProduction =>
    have childrenExpressions := SequenceSite.children_expression sequenceSite
    rw [sequenceSiteEq, childShape] at childrenExpressions
    simp only [EbnfExpr.children] at childrenExpressions
    have childrenLength : sequenceSite.children.length = 2 := by
      have exactLength := congrArg List.length childrenExpressions
      simpa using exactLength
    obtain ⟨operatorSite, operandSite, childrenEq⟩ :=
      g10List_eq_pair_of_length_two sequenceSite.children childrenLength
    have childExpressions : operatorSite.expression =
          .group (.choice (operators.map fun terminal =>
            .atom (.terminal terminal))) ∧
        operandSite.expression = operand := by
      simpa [childrenEq] using childrenExpressions
    have operatorShape := childExpressions.1
    have sequenceDot : sequence.raw.dot.val = 2 := by
      calc
        _ = sequence.raw.production.rhs.length := sequenceComplete
        _ = (ProductionId.seq sequenceSite).rhs.length := congrArg
          (fun selected : ProductionId => selected.rhs.length)
            sequenceProduction
        _ = 2 := by simp [ProductionId.rhs_seq, childrenEq]
    have operandSelected : sequence.raw.production.rhs[1]? =
        some (.nonterminal (.aux operandSite)) := by
      rw [sequenceProduction]
      simp [ProductionId.rhs_seq, childrenEq]
    rcases contextualReach_nonterminal_step sequenceReached sequenceDot
        operandSelected with
      ⟨sequenceWaiting, operandItem, sequenceWaitingReached, operandReached,
        operandComplete, operandLhs, sequenceWaitingDot,
        sequenceWaitingProduction, sequenceWaitingOrigin,
        operandOriginWaiting, operandCurrent⟩
    have operatorSelected : sequenceWaiting.raw.production.rhs[0]? =
        some (.nonterminal (.aux operatorSite)) := by
      rw [sequenceWaitingProduction, sequenceProduction]
      simp [ProductionId.rhs_seq, childrenEq]
    rcases contextualReach_nonterminal_step sequenceWaitingReached
        sequenceWaitingDot operatorSelected with
      ⟨firstWaiting, groupItem, firstWaitingReached, groupReached,
        groupComplete, groupLhs, firstWaitingDot, firstWaitingProduction,
        firstWaitingOrigin, groupOriginWaiting, groupCurrent⟩
    have firstWaitingOriginCurrent :=
      contextualReach_zero_origin_eq_current firstWaitingReached firstWaitingDot
    have groupOrigin : groupItem.raw.origin = sequence.raw.origin :=
      groupOriginWaiting.trans (firstWaitingOriginCurrent.symm.trans
        (firstWaitingOrigin.trans sequenceWaitingOrigin))
    have groupView := auxiliaryProductionView operatorSite
      groupItem.raw.production groupLhs
    have exactGroupView : AuxiliaryProductionView operatorSite
        groupItem.raw.production .group := by
      simpa [operatorShape, EbnfExpr.kind] using groupView
    cases exactGroupView with
    | group groupSite groupSiteEq groupProduction =>
      have choiceShape : groupSite.child.expression =
          .choice (operators.map fun terminal => .atom (.terminal terminal)) :=
        EbnfExpr.group.inj ((GroupSite.expression_eq_group groupSite).symm.trans
          ((congrArg GrammarSite.expression groupSiteEq).trans operatorShape))
      have groupRhs : groupItem.raw.production.rhs =
          [GrammarSymbol.nonterminal (.aux groupSite.child)] := by
        rw [groupProduction]
        rfl
      rcases contextualReach_complete_singleNonterminal groupReached groupRhs
          groupComplete with
        ⟨choiceItem, choiceReached, choiceComplete, choiceLhs,
          choiceOrigin, choiceCurrent⟩
      have choiceView := auxiliaryProductionView groupSite.child
        choiceItem.raw.production choiceLhs
      have exactChoiceView : AuxiliaryProductionView groupSite.child
          choiceItem.raw.production .choice := by
        simpa [choiceShape, EbnfExpr.kind] using choiceView
      cases exactChoiceView with
      | choice choiceSite branch choiceSiteEq choiceProduction =>
        have branchShape : choiceSite.branchExpressions.get branch ∈
            operators.map (fun terminal => .atom (.terminal terminal)) := by
          have member := List.get_mem choiceSite.branchExpressions.toList
            (choiceSite.branchListIndex branch)
          rw [ChoiceSite.branch_get_toList] at member
          have branchesEq : choiceSite.branchExpressions.toList =
              operators.map (fun terminal => .atom (.terminal terminal)) :=
            EbnfExpr.choice.inj
              ((ChoiceSite.expression_eq_choice choiceSite).symm.trans
                ((congrArg GrammarSite.expression choiceSiteEq).trans
                  choiceShape))
          simpa [branchesEq] using member
        rcases List.mem_map.mp branchShape with
          ⟨terminal, terminalMember, branchExpression⟩
        have atomShape : (choiceSite.branch branch).expression =
            .atom (.terminal terminal) :=
          (ChoiceSite.branch_expression choiceSite branch).trans
            branchExpression.symm
        have choiceRhs : choiceItem.raw.production.rhs =
            [GrammarSymbol.nonterminal (.aux (choiceSite.branch branch))] := by
          rw [choiceProduction]
          rfl
        rcases contextualReach_complete_singleNonterminal choiceReached choiceRhs
            choiceComplete with
          ⟨atomItem, atomReached, atomComplete, atomLhs,
            atomOrigin, atomCurrent⟩
        have atomView := auxiliaryProductionView (choiceSite.branch branch)
          atomItem.raw.production atomLhs
        have exactAtomView : AuxiliaryProductionView
            (choiceSite.branch branch) atomItem.raw.production .atom := by
          simpa [atomShape, EbnfExpr.kind] using atomView
        cases exactAtomView with
        | atom atomSite atomSiteEq atomProduction =>
          have atomEq : atomSite.atom = .terminal terminal :=
            EbnfExpr.atom.inj ((AtomSite.expression_eq_atom atomSite).symm.trans
              ((congrArg GrammarSite.expression atomSiteEq).trans atomShape))
          have atomDot : atomItem.raw.dot.val = 1 := by
            calc
              _ = atomItem.raw.production.rhs.length := atomComplete
              _ = (ProductionId.atom atomSite).rhs.length := congrArg
                (fun selected : ProductionId => selected.rhs.length)
                  atomProduction
              _ = 1 := rfl
          have atomSelected : atomItem.raw.production.rhs[0]? =
              some (.terminal terminal) := by
            rw [atomProduction]
            change some atomSite.atom.grammarSymbol =
              some (GrammarSymbol.terminal terminal)
            rw [atomEq]
            rfl
          obtain ⟨matched, matchedOrigin, matchedCurrent⟩ :=
            contextualReach_one_terminal atomReached atomDot atomSelected
          refine ⟨terminal, terminalMember, matched, ?_⟩
          exact matchedOrigin.trans (atomOrigin.trans (choiceOrigin.trans
            (groupOrigin.trans sequenceOrigin)))

/-- A reached present nonassociative optional starts with an exact same-level
operator at its source boundary. -/
theorem contextualReach_complete_nonAssociativeOptionalSome_operator
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo} {item : ContextualItemKey tokens}
    (level : NonAssociativeLevel) (site : OptionalSite)
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .opt site .some)
    (shape : site.site.expression = .optional level.tailExpr)
    (complete : CompleteItem item.raw) :
    ∃ operator, FoundNonAssociativeOperatorAt file tokens item.raw.origin
      level operator := by
  cases level with
  | relational =>
      obtain ⟨terminal, member, matched, atOrigin⟩ :=
        contextualReach_complete_optionalSome_firstTerminal site
          [.symbol .less, .symbol .greater, .symbol .lessEqual,
            .symbol .greaterEqual]
          (.atom (.nonterminal .bitOr)) reached production shape complete
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact ⟨_, .less matched atOrigin⟩
      · exact ⟨_, .greater matched atOrigin⟩
      · exact ⟨_, .lessEqual matched atOrigin⟩
      · exact ⟨_, .greaterEqual matched atOrigin⟩
  | equality =>
      obtain ⟨terminal, member, matched, atOrigin⟩ :=
        contextualReach_complete_optionalSome_firstTerminal site
          [.symbol .equalEqual, .symbol .notEqual]
          (.atom (.nonterminal .relational)) reached production shape complete
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨_, .equal matched atOrigin⟩
      · exact ⟨_, .notEqual matched atOrigin⟩

end Solcore.Surface.Multi
