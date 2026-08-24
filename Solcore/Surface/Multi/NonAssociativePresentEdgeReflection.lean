import Solcore.Surface.Multi.NonAssociativePassThroughSafety
set_option autoImplicit false
namespace Solcore.Surface.Multi
open Grammar Solcore.Workspace
theorem GrammarSymbolValues.transport_append_empty_single_to {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol} (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full) (viewLayout : full = [target]) (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens []) (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport viewLayout (GrammarSymbolValues.transport fullLayout
      (GrammarSymbolValues.append (GrammarSymbolValues.transport priorLayout.symm empty) (value, ()))) =
      (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout) value, ()) := by
  cases priorLayout; cases symbolLayout; cases viewLayout; rcases empty with ⟨⟩
  have fullProof : fullLayout = rfl := Subsingleton.elim _ _
  rw [fullProof]; rfl
theorem optionalView_sequence_ofAuxiliary_pair_eq {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {firstSite secondSite : GrammarSite} {first child : EbnfExpr}
    (childrenEq : children = [firstSite, secondSite]) (firstEq : firstSite.expression = first)
    (secondEq : secondSite.expression = .optional child)
    (symbolLayout : children.map (fun site => GrammarSymbol.nonterminal (.aux site)) =
      [GrammarSymbol.nonterminal (.aux firstSite), GrammarSymbol.nonterminal (.aux secondSite)])
    (expressionLayout : children.map GrammarSite.expression = [first, .optional child])
    (firstValue : EbnfValue file tokens firstSite.expression) (secondValue : EbnfValue file tokens secondSite.expression) :
    EbnfValue.optionalView child (EbnfValue.sequence2View first (.optional child)
      (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
        (EbnfValue.sequence (children.map GrammarSite.expression) (EbnfValues.ofAuxiliaries children
          (GrammarSymbolValues.transport symbolLayout.symm (firstValue, (secondValue, ()))))))).2 =
      EbnfValue.optionalView child (EbnfValue.atShape secondEq secondValue) := by
  subst children
  have canonicalExpressionLayout : [firstSite.expression, secondSite.expression] = [first, .optional child] := by simpa using expressionLayout
  have expressionProofEq : congrArg EbnfExpr.sequence expressionLayout = congrArg EbnfExpr.sequence canonicalExpressionLayout := Subsingleton.elim _ _
  rw [expressionProofEq]
  have exactSymbolLayout : symbolLayout = rfl := Subsingleton.elim _ _
  rw [exactSymbolLayout]; simp only [List.map, GrammarSymbolValues.transport_self]
  rw [sequence2View_transport_pair_eq firstEq secondEq canonicalExpressionLayout]
  have firstAuxView := EbnfValues.ofAuxiliaries_cons_eq firstSite [secondSite] firstValue (secondValue, ())
  have tailEq : (EbnfValues.consView firstSite.expression [secondSite.expression]
      (EbnfValues.ofAuxiliaries [firstSite, secondSite] (firstValue, (secondValue, ())))).2 =
      EbnfValues.ofAuxiliaries [secondSite] (secondValue, ()) := congrArg Prod.snd firstAuxView
  change EbnfValue.optionalView child (EbnfValue.transport secondEq
    (EbnfValues.consView secondSite.expression [] (EbnfValues.consView firstSite.expression [secondSite.expression]
      (EbnfValues.ofAuxiliaries [firstSite, secondSite] (firstValue, (secondValue, ())))).2).1) = _
  rw [tailEq]
  have secondAuxView := EbnfValues.ofAuxiliaries_cons_eq secondSite [] secondValue ()
  have secondViewEq : (EbnfValues.consView secondSite.expression []
      (EbnfValues.ofAuxiliaries [secondSite] (secondValue, ()))).1 = secondValue := congrArg Prod.fst secondAuxView
  rw [secondViewEq]; rfl
theorem EbnfValue.transport_optional_none_eq {file : WorkspaceFile} {tokens : List Token}
    {source target : EbnfExpr} (shape : source = target) : EbnfValue.transport (file := file) (tokens := tokens)
      (congrArg EbnfExpr.optional shape) (EbnfValue.optional (file := file) (tokens := tokens) source none) =
      EbnfValue.optional (file := file) (tokens := tokens) target none := by
  cases shape; simp only [EbnfValue.transport_self]
theorem optionalView_atShape_pack_none_eq {file : WorkspaceFile} {tokens : List Token} (site : OptionalSite)
    {target : EbnfExpr} (shape : site.site.expression = .optional target)
    (values : GrammarSymbolValues file tokens (ProductionId.opt site .none).rhs) :
    EbnfValue.optionalView target (EbnfValue.atShape shape (OptionalSite.pack site .none values)) = none := by
  have childShape : site.child.expression = target := EbnfExpr.optional.inj
    (site.expression_eq_optional.symm.trans shape)
  have shapeEq : shape = site.expression_eq_optional.trans (congrArg EbnfExpr.optional childShape) := Subsingleton.elim _ _
  rw [shapeEq]
  change EbnfValue.optionalView target (EbnfValue.transport
    (site.expression_eq_optional.trans (congrArg EbnfExpr.optional childShape))
    (OptionalSite.pack site .none values)) = none
  rw [← EbnfValue.transport_trans]
  change EbnfValue.optionalView target (EbnfValue.transport (congrArg EbnfExpr.optional childShape)
    (EbnfValue.atShape site.expression_eq_optional (OptionalSite.pack site .none values))) = none
  rw [OptionalSite.pack_none_eq, EbnfValue.transport_optional_none_eq]
  simp [EbnfValue.optionalView, EbnfValue.optional]; exact childShape

theorem coherentNonAssociativePresentInputHasPresentCompletion {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo} {final : AllGuardsFinal memo} :
    CoherentNonAssociativePresentInputHasPresentCompletion file tokens memo correct final := by
  intro level origin cursor context priorValues complete coherent present
  cases coherent with
  | zero _ _ zero => change 1 = 0 at zero; omega
  | scan before _ _ _ witness _ _ =>
      have beforeProduction : before.raw.production = .root level.rule := witness.advance.1.symm
      have beforeDot : before.raw.dot.val = 0 := by
        have advanced := witness.advance.2.1; change 1 = before.raw.dot.val + 1 at advanced; omega
      have impossible : some (GrammarSymbol.terminal witness.terminal) =
          some (GrammarSymbol.nonterminal (.aux (GrammarSite.root level.rule))) := by
        let index := before.raw.dot.val
        have indexZero : index = 0 := beforeDot
        calc
          _ = before.raw.production.rhs[index]? := witness.next.2.symm
          _ = (ProductionId.root level.rule).rhs[index]? := congrArg (fun production : ProductionId => production.rhs[index]?) beforeProduction
          _ = (ProductionId.root level.rule).rhs[0]? := by rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting sequence _ rootShared rootPriorValues sequenceValue rootWitness rootEdge rootPrior sequenceReduction =>
      have rootWaitingProduction : rootWaiting.raw.production = .root level.rule := rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1; change 1 = rootWaiting.raw.dot.val + 1 at advanced; omega
      have sequenceLhs : sequence.raw.production.lhs = .aux (GrammarSite.root level.rule) := by
        let index := rootWaiting.raw.dot.val
        have indexZero : index = 0 := rootWaitingDot
        have selected : some (GrammarSymbol.nonterminal sequence.raw.production.lhs) =
            some (GrammarSymbol.nonterminal (.aux (GrammarSite.root level.rule))) := by
          calc
            _ = rootWaiting.raw.production.rhs[index]? := rootWitness.next.2.symm
            _ = (ProductionId.root level.rule).rhs[index]? := congrArg (fun production : ProductionId => production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root level.rule).rhs[0]? := by rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      obtain ⟨sequenceSite, sequenceProduction⟩ := g10NonAssociativeRootChild_isSequence level sequence.raw.production sequenceLhs
      have sequenceSiteRoot : sequenceSite.site = GrammarSite.root level.rule := by
        rw [sequenceProduction] at sequenceLhs; exact NonterminalSymbol.aux.inj sequenceLhs
      have childrenExpressions := SequenceSite.children_expression sequenceSite
      rw [sequenceSiteRoot, GrammarSite.root_expression, g10NonAssociative_rhs_eq] at childrenExpressions
      simp only [EbnfExpr.children] at childrenExpressions
      have childrenLength : sequenceSite.children.length = 2 := by
        have exactLength := congrArg List.length childrenExpressions; simpa using exactLength
      obtain ⟨firstSite, secondSite, children⟩ := g10List_eq_pair_of_length_two sequenceSite.children childrenLength
      have shapes : firstSite.expression = .atom (.nonterminal level.operandRule) ∧
          secondSite.expression = .optional level.tailExpr := by simpa [children] using childrenExpressions
      have secondShape := shapes.2
      rcases sequence with ⟨⟨sequenceProductionId, sequenceDot, sequenceOrigin, sequenceCurrent⟩, sequenceContext⟩
      simp only at sequenceProduction; subst sequenceProductionId
      let sequenceItem : ContextualItemKey tokens := ⟨⟨.seq sequenceSite, sequenceDot, sequenceOrigin, sequenceCurrent⟩, sequenceContext⟩
      have sequenceItemProduction : sequenceItem.raw.production = .seq sequenceSite := rfl
      change CoherentReduction file tokens memo correct final sequenceItem sequenceValue at sequenceReduction
      cases sequenceReduction with
      | reduce _ sequenceValues _ _ sequenceComplete sequenceCoherent sequenceAction =>
          cases sequenceCoherent with
          | zero _ _ zero =>
              have sequenceDotValue : sequenceItem.raw.dot.val = 2 := by
                calc _ = sequenceItem.raw.production.rhs.length := sequenceComplete
                  _ = 2 := by simp [sequenceItem, ProductionId.rhs_seq, children]
              omega
          | scan sequenceBefore _ _ _ scanWitness _ _ =>
              have beforeProduction : sequenceBefore.raw.production = .seq sequenceSite := scanWitness.advance.1.symm.trans sequenceItemProduction
              have sequenceDotValue : sequenceItem.raw.dot.val = 2 := by
                calc _ = sequenceItem.raw.production.rhs.length := sequenceComplete
                  _ = 2 := by simp [sequenceItem, ProductionId.rhs_seq, children]
              have beforeDot : sequenceBefore.raw.dot.val = 1 := by
                have advanced := scanWitness.advance.2.1; omega
              have impossible : some (GrammarSymbol.terminal scanWitness.terminal) =
                  some (GrammarSymbol.nonterminal (.aux secondSite)) := by
                let index := sequenceBefore.raw.dot.val; have indexOne : index = 1 := beforeDot
                calc
                  _ = sequenceBefore.raw.production.rhs[index]? := scanWitness.next.2.symm
                  _ = (ProductionId.seq sequenceSite).rhs[index]? := congrArg (fun production : ProductionId => production.rhs[index]?) beforeProduction
                  _ = (ProductionId.seq sequenceSite).rhs[1]? := by rw [indexOne]
                  _ = _ := by simp [ProductionId.rhs_seq, children]
              exact GrammarSymbol.noConfusion (Option.some.inj impossible)
          | complete sequenceWaiting optional _ optionalShared sequencePriorValues optionalValue optionalWitness optionalEdge sequencePrior optionalReduction =>
              obtain ⟨site, branch, optionalProduction, siteEq, sequenceWaitingProduction, sequenceWaitingOne⟩ :=
                g10OptionalCompletionView level sequenceSite firstSite secondSite children secondShape sequenceItemProduction sequenceComplete optionalEdge
              cases branch with
              | none =>
                  rcases optional with ⟨⟨optionalProductionId, optionalDot, optionalOrigin, optionalCurrent⟩, optionalContext⟩
                  simp only at optionalProduction; subst optionalProductionId
                  let optionalItem : ContextualItemKey tokens := ⟨⟨.opt site .none, optionalDot, optionalOrigin, optionalCurrent⟩, optionalContext⟩
                  change CoherentReduction file tokens memo correct final optionalItem optionalValue at optionalReduction
                  cases optionalReduction with
                  | reduce _ optionalValues _ _ optionalComplete optionalCoherent optionalAction =>
                      have optionalPackedEq : optionalValue = OptionalSite.pack site .none
                          (PrefixValues.fullValue optionalItem optionalComplete optionalValues) := by
                        have exact := actionReduces_eleven_shapes_exact.mp optionalAction; simpa using exact
                      have sequencePackedEq : sequenceValue = SequenceSite.pack sequenceSite
                          (PrefixValues.fullValue sequenceItem sequenceComplete (PrefixValues.completeValue sequenceWaiting
                            optionalItem sequenceItem optionalWitness.next optionalWitness.advance sequencePriorValues optionalValue)) := by
                        have exact := actionReduces_eleven_shapes_exact.mp sequenceAction; simpa using exact
                      rw [PrefixValues.fullValue_completeValue_eq] at sequencePackedEq
                      rw [PrefixValues.fullValue_completeValue_eq] at present; rw [optionalPackedEq] at sequencePackedEq
                      have rootPriorLayout : rootWaiting.raw.production.rhs.take rootWaiting.raw.dot.val = [] := by
                        let index := rootWaiting.raw.dot.val; have indexZero : index = 0 := rootWaitingDot
                        calc
                          _ = (ProductionId.root level.rule).rhs.take index := congrArg (fun production : ProductionId => production.rhs.take index) rootWaitingProduction
                          _ = (ProductionId.root level.rule).rhs.take 0 := by rw [indexZero]
                          _ = [] := by simp
                      let rootEmpty := GrammarSymbolValues.transport rootPriorLayout rootPriorValues
                      have rootPriorRecover : GrammarSymbolValues.transport rootPriorLayout.symm rootEmpty = rootPriorValues := by
                        dsimp only [rootEmpty]; rw [GrammarSymbolValues.transport_trans]; exact GrammarSymbolValues.transport_self _ _
                      rw [← rootPriorRecover] at present
                      rcases sequenceWaiting with ⟨⟨waitingProduction, waitingDot, waitingOrigin, waitingCurrent⟩, waitingContext⟩
                      simp only at sequenceWaitingProduction sequenceWaitingOne; subst waitingProduction
                      rcases waitingDot with ⟨waitingDotValue, waitingDotBound⟩
                      simp only at sequenceWaitingOne; subst waitingDotValue
                      have sequencePriorLayout : (ProductionId.seq sequenceSite).rhs.take 1 =
                          [GrammarSymbol.nonterminal (.aux firstSite)] := by simp [ProductionId.rhs_seq, children]
                      generalize canonicalEq : GrammarSymbolValues.transport sequencePriorLayout sequencePriorValues = canonicalPrior
                      rcases canonicalPrior with ⟨firstValue, priorTail⟩; rcases priorTail with ⟨⟩
                      have sequencePriorRecover : GrammarSymbolValues.transport sequencePriorLayout.symm (firstValue, ()) = sequencePriorValues := by
                        rw [← canonicalEq, GrammarSymbolValues.transport_trans]; exact GrammarSymbolValues.transport_self _ _
                      rw [← sequencePriorRecover] at sequencePackedEq
                      let optionalPacked := OptionalSite.pack site .none (PrefixValues.fullValue optionalItem optionalComplete optionalValues)
                      have sequenceTargetLayout : sequenceSite.children.map (fun child => GrammarSymbol.nonterminal (.aux child)) =
                          [GrammarSymbol.nonterminal (.aux firstSite), GrammarSymbol.nonterminal (.aux site.site)] := by rw [children, siteEq]; rfl
                      have sequenceTupleEq := GrammarSymbolValues.transport_append_pair_to sequencePriorLayout
                        ((prefix_complete_layout { production := .seq sequenceSite, dot := ⟨1, waitingDotBound⟩, origin := waitingOrigin, current := waitingCurrent } optionalItem.raw sequenceItem.raw
                          optionalWitness.next optionalWitness.advance).trans (prefix_full_layout sequenceItem.raw sequenceComplete))
                        (ProductionId.rhs_seq sequenceSite) sequenceTargetLayout firstValue optionalPacked
                      dsimp only [optionalPacked] at sequenceTupleEq
                      simp only [SequenceSite.pack, GrammarSymbolValues.view] at sequencePackedEq
                      conv at sequencePackedEq in (GrammarSymbolValues.transport _ _) => rw [sequenceTupleEq]
                      let rawSequenceValue := EbnfValue.sequence (sequenceSite.children.map GrammarSite.expression)
                        (EbnfValues.ofAuxiliaries sequenceSite.children (GrammarSymbolValues.transport sequenceTargetLayout.symm
                          (firstValue, (optionalPacked, ()))))
                      let sequencePacked := EbnfValue.ofShape sequenceSite.expression_eq_sequence rawSequenceValue
                      let rootSequencePacked : NonterminalValue file tokens sequenceItem.raw.production.lhs := sequencePacked
                      change sequenceValue = rootSequencePacked at sequencePackedEq
                      rw [sequencePackedEq] at present
                      have rootSymbolLayout := congrArg (fun child => GrammarSymbol.nonterminal child) sequenceLhs
                      let rootFullLayout := (prefix_complete_layout rootWaiting.raw sequenceItem.raw
                        (CanonicalCompleteRootItem tokens level.rule origin cursor context).raw rootWitness.next rootWitness.advance).trans
                        (prefix_full_layout (CanonicalCompleteRootItem tokens level.rule origin cursor context).raw complete)
                      have rootTupleEq := GrammarSymbolValues.transport_append_empty_single_to
                        (source := GrammarSymbol.nonterminal sequenceItem.raw.production.lhs)
                        (target := GrammarSymbol.nonterminal (.aux (GrammarSite.root level.rule))) rootPriorLayout rootFullLayout
                        (ProductionId.rhs_root level.rule) rootSymbolLayout rootEmpty rootSequencePacked
                      simp only [CanonicalCompleteRootItem] at rootTupleEq
                      let rootValues := GrammarSymbolValues.transport rootFullLayout
                        (GrammarSymbolValues.append (GrammarSymbolValues.transport rootPriorLayout.symm rootEmpty) (rootSequencePacked, ()))
                      change NonAssociativeInputPresent level (RootAction.unpack level.rule rootValues) at present
                      have rootUnpackEq : RootAction.unpack level.rule rootValues =
                          EbnfValue.atShape (GrammarSite.root_expression level.rule)
                            (Eq.mp (congrArg (GrammarSymbolValue file tokens) rootSymbolLayout) rootSequencePacked) := by
                        simp only [rootValues, RootAction.unpack, GrammarSymbolValues.view]
                        exact congrArg (EbnfValue.atShape (GrammarSite.root_expression level.rule)) (congrArg Prod.fst rootTupleEq)
                      rw [rootUnpackEq] at present
                      have rootLayout : EbnfExpr.sequence (sequenceSite.children.map GrammarSite.expression) = m2cV1.rhs level.rule :=
                        (congrArg EbnfExpr.sequence childrenExpressions).trans (g10NonAssociative_rhs_eq level).symm
                      have rootInputEq := nonAssociativeRoot_sequenceTransport_eq level sequenceSite sequenceSiteRoot rootLayout rawSequenceValue
                      have packedEq : Eq.mp (congrArg (GrammarSymbolValue file tokens) rootSymbolLayout) rootSequencePacked =
                          Eq.mp (congrArg (GrammarSymbolValue file tokens) (congrArg
                            (fun child => GrammarSymbol.nonterminal (.aux child)) sequenceSiteRoot)) sequencePacked := by
                        dsimp only [rootSequencePacked, sequenceItem]
                        have proofEq : congrArg (GrammarSymbolValue file tokens) rootSymbolLayout = congrArg
                            (GrammarSymbolValue file tokens) (congrArg (fun child => GrammarSymbol.nonterminal (.aux child)) sequenceSiteRoot) := Subsingleton.elim _ _
                        exact congrArg (fun equality => Eq.mp equality sequencePacked) proofEq
                      have present' : NonAssociativeInputPresent level (EbnfValue.atShape
                          (GrammarSite.root_expression level.rule) (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                            (congrArg (fun child => GrammarSymbol.nonterminal (.aux child)) sequenceSiteRoot)) sequencePacked)) :=
                        Eq.mp (congrArg (NonAssociativeInputPresent level) (congrArg
                          (EbnfValue.atShape (GrammarSite.root_expression level.rule)) packedEq)) present
                      rw [rootInputEq] at present'
                      rcases (nonAssociativeInputPresent_iff_optionalPresent level _).mp present' with ⟨tail, viewEq⟩
                      have optionalShape : site.site.expression = .optional level.tailExpr :=
                        (congrArg GrammarSite.expression siteEq).trans secondShape
                      have childrenSite : sequenceSite.children = [firstSite, site.site] :=
                        children.trans (congrArg (fun second => [firstSite, second]) siteEq.symm)
                      cases level <;>
                        simp only [NonAssociativeLevel.operandRule] at childrenExpressions shapes viewEq <;>
                        have rootProofEq : rootLayout = congrArg EbnfExpr.sequence childrenExpressions := Subsingleton.elim _ _ <;>
                        have transportedEq : EbnfValue.transport rootLayout rawSequenceValue = EbnfValue.transport
                            (congrArg EbnfExpr.sequence childrenExpressions) rawSequenceValue := congrArg
                          (fun equality => EbnfValue.transport equality rawSequenceValue) rootProofEq <;>
                        simp only [nonAssociativeOptionalView] at viewEq <;>
                        rw [transportedEq] at viewEq <;>
                        rw [optionalView_sequence_ofAuxiliary_pair_eq childrenSite shapes.1 optionalShape
                          sequenceTargetLayout childrenExpressions firstValue optionalPacked] at viewEq <;>
                        rw [optionalView_atShape_pack_none_eq site optionalShape
                          (PrefixValues.fullValue optionalItem optionalComplete optionalValues)] at viewEq <;>
                        simp at viewEq
              | some =>
                  exact ⟨rootWaiting, sequenceItem, rootShared, sequenceWaiting, optional, optionalShared, site,
                    rootEdge, optionalEdge, optionalProduction⟩

/-- Pass-through safety and one accepted finite operand-boundary table
construct the complete coherent G10 invariant. -/
theorem coherentNonAssociativeRootCompletedInvariant_of_safe_and_table
    {file : WorkspaceFile} {tokens : List Token}
    (owned : TokensOwnedBy file tokens)
    {memo : GuardMemo tokens}
    (correct : PhaseBCorrect file tokens memo)
    (final : AllGuardsFinal memo)
    (safe : CoherentNonAssociativePassThroughSafe
      file tokens memo correct final)
    (accepted : nonAssociativeOperandPrefixExclusiveTable
      file tokens owned correct final = true) :
    CoherentNonAssociativeRootCompletedInvariant
      file tokens memo correct final := by
  exact coherentNonAssociativeRootCompletedInvariant_of_operandPrefixExclusive
    (nonAssociativeOperandPrefixExclusive_of_table
      owned correct final accepted)
    (coherentNonAssociativeCompletedHasPresentCompletion_of_safe safe
      coherentNonAssociativePresentInputHasPresentCompletion)
end Solcore.Surface.Multi
