import Solcore.Surface.Multi.AuxiliaryInversion
import Solcore.Surface.Multi.CoherentAtomRuleInversion
import Solcore.Surface.Multi.ExactTokenCoherentRuleSoundness
import Solcore.Surface.Multi.ExactTokenRuleExpressionFolds

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

universe u v

local macro "solve_atom_site" : tactic => `(tactic|
  simp [GrammarSiteKey.valid, GrammarSite.expression, m2cV1, m2cV1Rhs,
    EbnfExpr.nodeAt?, EbnfExpr.children, EbnfExpr.kind,
    Grammar.terminal, Grammar.hardKeyword, Grammar.contextualKeyword,
    Grammar.pragmaName, Grammar.symbol, Grammar.category,
    Grammar.nonterminal, Grammar.sequence, Grammar.choice, Grammar.group,
    Grammar.optional, Grammar.star, Grammar.plus, Grammar.list0,
    Grammar.list1, Grammar.identifier, Grammar.pathComponent])

private def atomRootChoiceSite : ChoiceSite := {
  site := GrammarSite.root .atom
  hasKind := by
    rw [GrammarSite.root_expression]
    rfl
}

private def atomDotChoiceBranch : Fin atomRootChoiceSite.branchCount :=
  ⟨2, by
    unfold atomRootChoiceSite ChoiceSite.branchCount
    rw [GrammarSite.root_expression]
    change 2 < 8
    omega⟩

private def atomLambdaChoiceBranch : Fin atomRootChoiceSite.branchCount :=
  ⟨4, by
    unfold atomRootChoiceSite ChoiceSite.branchCount
    rw [GrammarSite.root_expression]
    change 4 < 8
    omega⟩

private def atomDotRootBranch :
    Fin (EbnfExpr.children (m2cV1.rhs .atom)).length :=
  ⟨2, by decide⟩

private def atomLambdaRootBranch :
    Fin (EbnfExpr.children (m2cV1.rhs .atom)).length :=
  ⟨4, by decide⟩

private def atomDotSequenceSite : SequenceSite := {
  site := ⟨{ rule := .atom, path := [2] }, by solve_atom_site⟩
  hasKind := by solve_atom_site
}

private def atomDotTokenSite : AtomSite := {
  site := ⟨{ rule := .atom, path := [2, 0] }, by solve_atom_site⟩
  hasKind := by solve_atom_site
}

private def atomDotNameSite : AtomSite := {
  site := ⟨{ rule := .atom, path := [2, 1] }, by solve_atom_site⟩
  hasKind := by solve_atom_site
}

private def atomDotOptionalSite : OptionalSite := {
  site := ⟨{ rule := .atom, path := [2, 2] }, by solve_atom_site⟩
  hasKind := by solve_atom_site
}

private def atomLambdaAtomSite : AtomSite := {
  site := ⟨{ rule := .atom, path := [4] }, by solve_atom_site⟩
  hasKind := by solve_atom_site
}

private theorem atomDotChoiceBranch_site :
    atomRootChoiceSite.branch atomDotChoiceBranch =
      atomDotSequenceSite.site := by
  rfl

private theorem atomLambdaChoiceBranch_site :
    atomRootChoiceSite.branch atomLambdaChoiceBranch =
      atomLambdaAtomSite.site := by
  rfl

private theorem atomDotSequenceSite_children :
    atomDotSequenceSite.children = [
      atomDotTokenSite.site,
      atomDotNameSite.site,
      atomDotOptionalSite.site] := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem atomDotDirectChild_shape :
    (EbnfExpr.children (m2cV1.rhs .atom)).get atomDotRootBranch =
      EbnfExpr.sequence
        (atomDotSequenceSite.children.map GrammarSite.expression) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem atomLambdaDirectChild_shape :
    (EbnfExpr.children (m2cV1.rhs .atom)).get atomLambdaRootBranch =
      atomLambdaAtomSite.site.expression := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem eqMp_congrArg_trans
    {index : Sort u} (family : index → Sort v)
    {first second third : index}
    (left : first = second) (right : second = third)
    (value : family first) :
    Eq.mp (congrArg family right)
        (Eq.mp (congrArg family left) value) =
      Eq.mp (congrArg family (left.trans right)) value := by
  cases left
  cases right
  rfl

/-- A reached postfix root carries the invocation context introduced at its
own prediction boundary. -/
private theorem contextualReach_rootPostfix_context
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {item : ContextualItemKey tokens}
    (reached : ContextualReach file tokens memo correct final item)
    (production : item.raw.production = .root .postfix) :
    item.context = .postfixInvocation item.raw.origin := by
  induction reached with
  | root =>
      simp at production
  | predict waiting predicted _ _ _ induction =>
      change predicted = .root .postfix at production
      subst predicted
      rfl
  | scan before after cursor _ structural induction =>
      rcases structural with ⟨valid, contextEq⟩
      rcases valid with
        ⟨terminal, value, span, next, atCurrent, terminalAt,
          terminalMatches, advance⟩
      rcases advance with ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [← contextEq, originEq]
      exact induction (productionEq.symm.trans production)
  | complete waiting finished after shared _ _ structural
      waitingInduction finishedInduction =>
      rcases structural with ⟨valid, finishedContext, afterContext⟩
      rcases valid with
        ⟨symbol, next, complete, lhs, waitingAt, finishedAt, advance⟩
      rcases advance with ⟨productionEq, dotEq, originEq, currentEq⟩
      rw [afterContext, originEq]
      exact waitingInduction (productionEq.symm.trans production)

/-- Descending further inside one postfix/atom expansion preserves the
invocation context, except at the postfix root that introduces it. -/
private theorem descendContext_eq_of_postfixRegion_not_root_local
    {tokens : List Token}
    (waiting : ContextualItemKey tokens)
    (predicted : ProductionId)
    (inRegion : predicted.sourceRule = .postfix ∨
      predicted.sourceRule = .atom)
    (notRoot : predicted ≠ .root .postfix) :
    descendContext waiting predicted = waiting.context := by
  rcases waiting with
    ⟨⟨waitingProduction, waitingDot, waitingOrigin, waitingCurrent⟩,
      waitingContext⟩
  cases predicted with
  | root rule =>
      simp only [ProductionId.sourceRule] at inRegion
      rcases inRegion with rfl | rfl
      · exact (notRoot rfl).elim
      · simp [descendContext, ProductionId.lhs]
  | atom site
  | seq site
  | group site
  | choice site branch
  | opt site branch
  | star site branch
  | plus site branch
  | list0 site branch
  | list1 site =>
      simp only [ProductionId.sourceRule] at inRegion
      rcases inRegion with ruleEq | ruleEq <;>
        cases waitingProduction <;>
        simp [descendContext, ProductionId.lhs, GrammarSite.isAt,
          ruleEq]
  | tail site branch =>
      simp [descendContext, ProductionId.lhs]

/-- Completion within a postfix/atom region preserves the inherited
invocation context from the waiting item to the finished child. -/
private theorem completedEdge_sameContext_of_postfixRegion
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {waiting finished after : ContextualItemKey tokens}
    {shared : Boundary tokens}
    (edge : ContextualEdgeReach file tokens memo correct final
      (.completed waiting finished after shared))
    (inRegion : finished.raw.production.sourceRule = .postfix ∨
      finished.raw.production.sourceRule = .atom)
    (notRoot : finished.raw.production ≠ .root .postfix) :
    finished.context = after.context := by
  calc
    finished.context =
        descendContext waiting finished.raw.production := edge.1.2.1
    _ = waiting.context :=
      descendContext_eq_of_postfixRegion_not_root_local
        waiting finished.raw.production inRegion notRoot
    _ = after.context := edge.1.2.2.symm

/-- A negative enabled G07 cell refutes exactly the leading-dot argument
shape observed at its anchored invocation and site boundaries. -/
private theorem enabledG07Negative_notLeadingDotArguments
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (productionInstance : ProductionInstanceKey tokens)
    (start site : Boundary tokens)
    (context : productionInstance.context = .postfixInvocation start)
    (origin : productionInstance.origin = site)
    (enabled : EnabledProductionInstance file tokens memo correct final
      productionInstance)
    (member : (.G07_leadingDotArguments, .negative) ∈
      guardOf productionInstance.production) :
    ¬ (ExactSlice file tokens start site [
        .symbol .dot, .category .identifier] ∧
      SymbolAtBoundary file tokens site .leftParen) := by
  rcases enabled .G07_leadingDotArguments .negative member with
    ⟨key, productionEq, guardEq, polarityEq, witness⟩
  change key.val.productionInstance = productionInstance at productionEq
  change key.val.guardInstance.guard = .G07_leadingDotArguments at guardEq
  change key.val.polarity = .negative at polarityEq
  rcases witness with ⟨decision, _stored, evidence, allowed⟩
  have anchor := key.property.2
  rw [productionEq, guardEq, polarityEq] at anchor
  have siteEq : key.guardInstance.siteCursor = site := by
    change key.val.guardInstance.siteCursor = site
    exact anchor.2.2.1.trans origin
  have startEq : key.guardInstance.contextStart = start := by
    have selected := anchor.2.2.2
    change (match productionInstance.context with
      | .postfixInvocation postfixStart => some postfixStart
      | _ => none) = some key.val.guardInstance.contextStart at selected
    rw [context] at selected
    exact (Option.some.inj selected).symm
  cases decision with
  | positive =>
      have denied : false = true := by
        simpa only [GuardWitnessKey.polarity, polarityEq,
          GuardDecision.allows, Polarity.accepts] using allowed
      exact False.elim (Bool.false_ne_true denied)
  | negative =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      intro leading
      apply evidence.2
      change ExactSlice file tokens key.val.guardInstance.contextStart
          key.val.guardInstance.siteCursor [
            .symbol .dot, .category .identifier] ∧
        SymbolAtBoundary file tokens key.val.guardInstance.siteCursor
          .leftParen
      change key.val.guardInstance.contextStart = start at startEq
      change key.val.guardInstance.siteCursor = site at siteEq
      simpa only [startEq, siteEq] using leading
  | neutral =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      exact False.elim evidence.2

private abbrev postfixSourceChildren : List EbnfExpr := [
  .atom (.nonterminal .atom),
  .star (.atom (.nonterminal .postfixPart))]

private def postfixSourceValue
    {file : WorkspaceFile} {tokens : List Token}
    (atom : RuleValue .atom) (parts : List (RuleValue .postfixPart)) :
    EbnfValue file tokens (m2cV1.rhs .postfix) :=
  EbnfValue.sequence (EbnfExpr.children (m2cV1.rhs .postfix)) <|
    EbnfValues.cons _ [_] (EbnfValue.ruleAtom .atom atom) <|
      EbnfValues.cons _ []
        (EbnfValue.star _
          (parts.map (EbnfValue.ruleAtom .postfixPart))) EbnfValues.nil

private theorem postfixSourceValue_sequence2View
    {file : WorkspaceFile} {tokens : List Token}
    (atom : Expression) (parts : List PostfixPartValue) :
    EbnfValue.sequence2View
        (.atom (.nonterminal .atom))
        (.star (.atom (.nonterminal .postfixPart)))
        (postfixSourceValue (file := file) (tokens := tokens)
          atom parts) =
      (EbnfValue.ruleAtom .atom atom,
        EbnfValue.star (.atom (.nonterminal .postfixPart))
          (parts.map (EbnfValue.ruleAtom .postfixPart))) := by
  let sourceValues : EbnfValues file tokens postfixSourceChildren :=
    EbnfValues.cons _ [_]
      (EbnfValue.ruleAtom .atom atom)
      (EbnfValues.cons _ []
        (EbnfValue.star _
          (parts.map (EbnfValue.ruleAtom .postfixPart)))
        EbnfValues.nil)
  let sourceLayout : EbnfExpr.sequence postfixSourceChildren =
      m2cV1.rhs .postfix := by rfl
  have sourceEq :
      postfixSourceValue (file := file) (tokens := tokens) atom parts =
        EbnfValue.transport sourceLayout
          (EbnfValue.sequence postfixSourceChildren sourceValues) := by
    unfold postfixSourceValue
    rfl
  rw [sourceEq]
  change EbnfValue.sequence2View
      (.atom (.nonterminal .atom))
      (.star (.atom (.nonterminal .postfixPart)))
      (EbnfValue.transport
        (rfl : EbnfExpr.sequence postfixSourceChildren =
          EbnfExpr.sequence postfixSourceChildren)
        (EbnfValue.sequence postfixSourceChildren sourceValues)) = _
  rw [EbnfValue.transport_self]
  simp [EbnfValue.sequence2View, EbnfValue.sequenceView,
    EbnfValue.sequence]
  dsimp only [sourceValues]
  simp [EbnfValues.consView]

private theorem list_eq_pair_of_length_two
    {α : Type} (values : List α) (length : values.length = 2) :
    ∃ first second, values = [first, second] := by
  cases values with
  | nil => simp at length
  | cons first rest =>
      cases rest with
      | nil => simp at length
      | cons second tail =>
          cases tail with
          | nil => exact ⟨first, second, rfl⟩
          | cons third tail => simp at length

private theorem ruleAtomValues_tokenPlan?_map
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (values : List (RuleValue rule)) :
    (values.map (EbnfValue.ruleAtom (file := file) (tokens := tokens)
        rule)).mapM
        (EbnfValue.tokenPlan? sourceRuleTokenPlanLayout) =
      values.mapM (ruleTokenPlan? rule) := by
  induction values with
  | nil => rfl
  | cons value rest induction =>
      rw [List.map_cons, List.mapM_cons, List.mapM_cons]
      have headEq :
          (EbnfValue.ruleAtom (file := file) (tokens := tokens)
            rule value).tokenPlan? sourceRuleTokenPlanLayout =
            ruleTokenPlan? rule value := by
        exact EbnfValue.tokenPlan?_ruleAtom sourceRuleTokenPlanLayout
          rule value
      rw [headEq, induction]

private theorem postfixSourceValue_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (atom : Expression) (parts : List PostfixPartValue) :
    (postfixSourceValue (file := file) (tokens := tokens)
        atom parts).tokenPlan? sourceRuleTokenPlanLayout =
      postfixFoldSourceTokenPlan? atom parts := by
  unfold postfixSourceValue postfixFoldSourceTokenPlan?
  change (EbnfValue.sequence postfixSourceChildren
      (EbnfValues.cons _ [_]
        (EbnfValue.ruleAtom .atom atom)
        (EbnfValues.cons _ []
          (EbnfValue.star _
            (parts.map (EbnfValue.ruleAtom .postfixPart)))
          EbnfValues.nil))).tokenPlan? sourceRuleTokenPlanLayout = _
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons, EbnfValue.tokenPlan?_ruleAtom]
  rw [EbnfValues.tokenPlan?_cons, EbnfValue.tokenPlan?_star]
  rw [ruleAtomValues_tokenPlan?_map]
  simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?,
    EbnfValues.tokenPlan?_nil]
  have partsPlanEq :
      parts.mapM (ruleTokenPlan? .postfixPart) =
        parts.mapM postfixPartTokenPlan? := rfl
  rw [partsPlanEq]
  cases atomExpressionTokenPlan? atom <;>
    cases parts.mapM postfixPartTokenPlan? <;>
      simp [TokenPlan.append_empty]

private theorem postfixRootChild_isSequence
    (production : ProductionId)
    (lhs : production.lhs = .aux (GrammarSite.root .postfix)) :
    ∃ site : SequenceSite, production = .seq site := by
  have rootKind :
      (GrammarSite.root .postfix).expression.kind = .sequence := by
    rw [GrammarSite.root_expression]
    rfl
  have impossible {kind : EbnfNodeKind}
      (site : GrammarSiteOfKind kind) (different : kind ≠ .sequence)
      (same : site.site = GrammarSite.root .postfix) : False := by
    have actual := site.hasKind
    rw [same, rootKind] at actual
    exact different actual.symm
  cases production with
  | root rule => cases lhs
  | atom site => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | seq site => exact ⟨site, rfl⟩
  | group site => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | choice site branch => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | opt site branch => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | star site branch => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | plus site branch => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list0 site branch => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list1 site => exact (impossible site (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | tail site branch => cases lhs

private theorem auxiliaryAtomProduction
    (production : ProductionId) (site : GrammarSite)
    (lhs : production.lhs = .aux site)
    (kind : site.expression.kind = .atom) :
    ∃ atomSite : AtomSite,
      production = .atom atomSite ∧ atomSite.site = site := by
  have impossible {otherKind : EbnfNodeKind}
      (other : GrammarSiteOfKind otherKind)
      (different : otherKind ≠ .atom)
      (same : other.site = site) : False := by
    have actual := other.hasKind
    rw [same, kind] at actual
    exact different actual.symm
  cases production with
  | root rule => cases lhs
  | atom atomSite =>
      exact ⟨atomSite, rfl, NonterminalSymbol.aux.inj lhs⟩
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
  | tail listSite branch => cases lhs

private theorem auxiliaryStarProduction
    (production : ProductionId) (site : GrammarSite)
    (lhs : production.lhs = .aux site)
    (kind : site.expression.kind = .star) :
    ∃ starSite : StarSite, ∃ branch : NilConsBranch,
      production = .star starSite branch ∧ starSite.site = site := by
  have impossible {otherKind : EbnfNodeKind}
      (other : GrammarSiteOfKind otherKind)
      (different : otherKind ≠ .star)
      (same : other.site = site) : False := by
    have actual := other.hasKind
    rw [same, kind] at actual
    exact different actual.symm
  cases production with
  | root rule => cases lhs
  | atom other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | seq other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | group other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | choice other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | opt other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | star starSite branch =>
      exact ⟨starSite, branch, rfl, NonterminalSymbol.aux.inj lhs⟩
  | plus other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list0 other branch => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | list1 other => exact (impossible other (by decide)
      (NonterminalSymbol.aux.inj lhs)).elim
  | tail listSite branch => cases lhs

private theorem auxiliaryChoiceProduction
    (production : ProductionId) (site : GrammarSite)
    (lhs : production.lhs = .aux site)
    (kind : site.expression.kind = .choice) :
    ∃ choiceSite : ChoiceSite, ∃ branch : Fin choiceSite.branchCount,
      production = .choice choiceSite branch ∧ choiceSite.site = site := by
  have view := auxiliaryProductionView site production lhs
  rw [kind] at view
  cases view with
  | choice choiceSite branch same exact =>
      exact ⟨choiceSite, branch, exact, same⟩

private theorem auxiliarySequenceProduction
    (production : ProductionId) (site : GrammarSite)
    (lhs : production.lhs = .aux site)
    (kind : site.expression.kind = .sequence) :
    ∃ sequenceSite : SequenceSite,
      production = .seq sequenceSite ∧ sequenceSite.site = site := by
  have view := auxiliaryProductionView site production lhs
  rw [kind] at view
  cases view with
  | sequence sequenceSite same exact =>
      exact ⟨sequenceSite, exact, same⟩

private theorem auxiliaryOptionalProduction
    (production : ProductionId) (site : GrammarSite)
    (lhs : production.lhs = .aux site)
    (kind : site.expression.kind = .optional) :
    ∃ optionalSite : OptionalSite, ∃ branch : OptionalBranch,
      production = .opt optionalSite branch ∧ optionalSite.site = site := by
  have view := auxiliaryProductionView site production lhs
  rw [kind] at view
  cases view with
  | optional optionalSite branch same exact =>
      exact ⟨optionalSite, branch, exact, same⟩

private theorem production_of_rule_lhs
    (production : ProductionId) (rule : GrammarRuleId)
    (lhs : production.lhs = .rule rule) :
    production = .root rule := by
  cases production with
  | root sourceRule =>
      have same : sourceRule = rule := NonterminalSymbol.rule.inj lhs
      subst sourceRule
      rfl
  | atom site => cases lhs
  | seq site => cases lhs
  | group site => cases lhs
  | choice site branch => cases lhs
  | opt site branch => cases lhs
  | star site branch => cases lhs
  | plus site branch => cases lhs
  | list0 site branch => cases lhs
  | list1 site => cases lhs
  | tail site branch => cases lhs

private theorem postfixRoot_sequenceTransport_eq
    {file : WorkspaceFile} {tokens : List Token}
    (site : SequenceSite)
    (siteRoot : site.site = GrammarSite.root .postfix)
    (layout : EbnfExpr.sequence
        (site.children.map GrammarSite.expression) =
      m2cV1.rhs .postfix)
    (value : EbnfValue file tokens
      (.sequence (site.children.map GrammarSite.expression))) :
    EbnfValue.atShape (GrammarSite.root_expression .postfix)
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg (fun child =>
              GrammarSymbol.nonterminal (.aux child)) siteRoot))
          (EbnfValue.ofShape site.expression_eq_sequence value)) =
      EbnfValue.transport layout value := by
  let packed := EbnfValue.ofShape site.expression_eq_sequence value
  have outerAligned :
      EbnfValue.atShape (GrammarSite.root_expression .postfix)
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
              (congrArg (fun child =>
                GrammarSymbol.nonterminal (.aux child)) siteRoot)) packed) =
        EbnfValue.atShape (GrammarSite.root_expression .postfix)
          (EbnfValue.transport
            (congrArg GrammarSite.expression siteRoot) packed) :=
    congrArg (EbnfValue.atShape
      (GrammarSite.root_expression .postfix))
      (auxiliaryValue_transport_eq siteRoot packed)
  rw [outerAligned]
  unfold EbnfValue.atShape packed EbnfValue.ofShape
  rw [EbnfValue.transport_trans, EbnfValue.transport_trans]

private theorem rootChoice_transport_eq
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (site : ChoiceSite)
    (siteRoot : site.site = GrammarSite.root rule)
    (layout : EbnfExpr.choice site.branchExpressions.toList =
      m2cV1.rhs rule)
    (value : EbnfValue file tokens
      (.choice site.branchExpressions.toList)) :
    EbnfValue.atShape (GrammarSite.root_expression rule)
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg (fun child =>
              GrammarSymbol.nonterminal (.aux child)) siteRoot))
          (EbnfValue.ofShape site.expression_eq_choice value)) =
      EbnfValue.transport layout value := by
  let packed := EbnfValue.ofShape site.expression_eq_choice value
  have outerAligned :
      EbnfValue.atShape (GrammarSite.root_expression rule)
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
              (congrArg (fun child =>
                GrammarSymbol.nonterminal (.aux child)) siteRoot)) packed) =
        EbnfValue.atShape (GrammarSite.root_expression rule)
          (EbnfValue.transport
            (congrArg GrammarSite.expression siteRoot) packed) :=
    congrArg (EbnfValue.atShape (GrammarSite.root_expression rule))
      (auxiliaryValue_transport_eq siteRoot packed)
  rw [outerAligned]
  unfold EbnfValue.atShape packed EbnfValue.ofShape
  rw [EbnfValue.transport_trans, EbnfValue.transport_trans]

private theorem choiceView_transport_branch_val
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List EbnfExpr}
    (layout : EbnfExpr.choice left = EbnfExpr.choice right)
    (branch : Fin left.length)
    (value : EbnfValue file tokens (left.get branch)) :
    (EbnfValue.choiceView right
      (EbnfValue.transport layout
        (EbnfValue.choice left ⟨branch, value⟩))).1.val = branch.val := by
  have lists : left = right := EbnfExpr.choice.inj layout
  have layoutEq : layout = congrArg EbnfExpr.choice lists :=
    Subsingleton.elim _ _
  rw [layoutEq]
  subst right
  simp [EbnfValue.choiceView, EbnfValue.choice,
    EbnfValue.transport, cast_cast]

private theorem choiceView_choice_branch_val
    {file : WorkspaceFile} {tokens : List Token}
    (branches : List EbnfExpr) (branch : Fin branches.length)
    (value : EbnfValue file tokens (branches.get branch)) :
    (EbnfValue.choiceView branches
      (EbnfValue.choice branches ⟨branch, value⟩)).1.val = branch.val := by
  exact choiceView_transport_branch_val rfl branch value

private theorem choice_transport_pair_heq
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List EbnfExpr} (layout : left = right)
    (leftBranch : Fin left.length)
    (leftValue : EbnfValue file tokens (left.get leftBranch))
    (rightBranch : Fin right.length)
    (rightValue : EbnfValue file tokens (right.get rightBranch))
    (equal : EbnfValue.transport (congrArg EbnfExpr.choice layout)
        (EbnfValue.choice left ⟨leftBranch, leftValue⟩) =
      EbnfValue.choice right ⟨rightBranch, rightValue⟩) :
    leftBranch.val = rightBranch.val ∧ HEq leftValue rightValue := by
  cases layout
  have equal' :
      EbnfValue.choice left ⟨leftBranch, leftValue⟩ =
        EbnfValue.choice left ⟨rightBranch, rightValue⟩ := by
    simpa [EbnfValue.transport] using equal
  have pairEq := EbnfValue.choice_injective left equal'
  cases pairEq
  exact ⟨rfl, HEq.rfl⟩

private theorem transport_sequence_values
    {file : WorkspaceFile} {tokens : List Token}
    {left right : List EbnfExpr} (layout : left = right)
    (values : EbnfValues file tokens left) :
    EbnfValue.transport (congrArg EbnfExpr.sequence layout)
        (EbnfValue.sequence left values) =
      EbnfValue.sequence right
        (Eq.mp (congrArg (EbnfValues file tokens) layout) values) := by
  cases layout
  simp [EbnfValue.transport]

private abbrev atomDotArgumentsExpression : EbnfExpr :=
  .sequence [
    .atom (.terminal (.symbol .leftParen)),
    .list0 (.atom (.nonterminal .expression)),
    .atom (.terminal (.symbol .rightParen))]

private abbrev atomDotChildExpressions : List EbnfExpr := [
  .atom (.terminal (.symbol .dot)),
  .atom (.terminal (.category .identifier)),
  .optional atomDotArgumentsExpression]

private theorem atomDotSequenceSite_expressions :
    atomDotSequenceSite.children.map GrammarSite.expression =
      atomDotChildExpressions := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem atomDotDirectChild_explicitShape :
    (EbnfExpr.children (m2cV1.rhs .atom)).get atomDotRootBranch =
      EbnfExpr.sequence atomDotChildExpressions := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private def atomDotWithoutArgumentsExplicitValues
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    EbnfValues file tokens atomDotChildExpressions :=
  EbnfValues.cons _ _
    (EbnfValue.terminalAtom (.symbol .dot) dot)
    (EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.category .identifier) name)
      (EbnfValues.cons _ []
        (EbnfValue.optional _ none)
        EbnfValues.nil))

private def atomDotWithoutArgumentsChild
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    EbnfValue file tokens
      ((EbnfExpr.children (m2cV1.rhs .atom)).get atomDotRootBranch) :=
  EbnfValue.sequence atomDotChildExpressions
    (atomDotWithoutArgumentsExplicitValues dot name)

private def atomDotWithoutArgumentsSequenceValues
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    EbnfValues file tokens
      (atomDotSequenceSite.children.map GrammarSite.expression) :=
  Eq.mp
    (congrArg (EbnfValues file tokens)
      atomDotSequenceSite_expressions.symm)
    (atomDotWithoutArgumentsExplicitValues dot name)

private theorem atomDotWithoutArgumentsChild_shape_eq
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    EbnfValue.transport atomDotDirectChild_shape
        (atomDotWithoutArgumentsChild dot name) =
      EbnfValue.sequence
        (atomDotSequenceSite.children.map GrammarSite.expression)
        (atomDotWithoutArgumentsSequenceValues dot name) := by
  unfold atomDotWithoutArgumentsChild
    atomDotWithoutArgumentsSequenceValues
  have shapeProof : atomDotDirectChild_shape =
      atomDotDirectChild_explicitShape.trans
        (congrArg EbnfExpr.sequence
          atomDotSequenceSite_expressions.symm) :=
    Subsingleton.elim _ _
  have directTransport :
      EbnfValue.transport atomDotDirectChild_explicitShape
          (EbnfValue.sequence atomDotChildExpressions
            (atomDotWithoutArgumentsExplicitValues dot name)) =
        EbnfValue.sequence atomDotChildExpressions
          (atomDotWithoutArgumentsExplicitValues dot name) := by
    run_tac
      Lean.Meta.withTransparency .all do
        (← Lean.Elab.Tactic.getMainGoal).refl
  rw [shapeProof]
  calc
    _ = EbnfValue.transport
          (congrArg EbnfExpr.sequence
            atomDotSequenceSite_expressions.symm)
          (EbnfValue.transport atomDotDirectChild_explicitShape
            (EbnfValue.sequence atomDotChildExpressions
              (atomDotWithoutArgumentsExplicitValues dot name))) :=
        (EbnfValue.transport_trans atomDotDirectChild_explicitShape
          (congrArg EbnfExpr.sequence
            atomDotSequenceSite_expressions.symm) _).symm
    _ = EbnfValue.transport
          (congrArg EbnfExpr.sequence
            atomDotSequenceSite_expressions.symm)
          (EbnfValue.sequence atomDotChildExpressions
            (atomDotWithoutArgumentsExplicitValues dot name)) :=
      congrArg _ directTransport
    _ = _ := transport_sequence_values
      atomDotSequenceSite_expressions.symm _

private theorem atomDotOptionalSite_expression :
    atomDotOptionalSite.site.expression =
      .optional atomDotArgumentsExpression := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem atomDotTokenSite_expression :
    atomDotTokenSite.site.expression =
      .atom (.terminal (.symbol .dot)) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem atomDotNameSite_expression :
    atomDotNameSite.site.expression =
      .atom (.terminal (.category .identifier)) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private def expressionThirdValue
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {first second third : GrammarSite}
    (childrenEq : children = [first, second, third])
    (values : EbnfValues file tokens
      (children.map GrammarSite.expression)) :
    EbnfValue file tokens third.expression :=
  let canonical : EbnfValues file tokens
      [first.expression, second.expression, third.expression] :=
    Eq.mp (congrArg (EbnfValues file tokens)
      (congrArg (List.map GrammarSite.expression) childrenEq)) values
  (EbnfValues.consView third.expression []
    (EbnfValues.consView second.expression [third.expression]
      (EbnfValues.consView first.expression
        [second.expression, third.expression] canonical).2).2).1

private def auxiliaryThirdValue
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {first second third : GrammarSite}
    (childrenEq : children = [first, second, third])
    (values : GrammarSymbolValues file tokens
      (children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)))) :
    EbnfValue file tokens third.expression :=
  let canonical : GrammarSymbolValues file tokens [
      .nonterminal (.aux first), .nonterminal (.aux second),
      .nonterminal (.aux third)] :=
    Eq.mp (congrArg (GrammarSymbolValues file tokens)
      (congrArg (List.map (fun child =>
        GrammarSymbol.nonterminal (.aux child))) childrenEq)) values
  canonical.2.2.1

private theorem expressionThirdValue_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {first second third : GrammarSite}
    (childrenEq : children = [first, second, third])
    (values : GrammarSymbolValues file tokens
      (children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)))) :
    expressionThirdValue childrenEq
        (EbnfValues.ofAuxiliaries children values) =
      auxiliaryThirdValue childrenEq values := by
  subst children
  rcases values with ⟨firstValue, secondValue, thirdValue, empty⟩
  rcases empty with ⟨⟩
  simp [expressionThirdValue, auxiliaryThirdValue,
    EbnfValues.ofAuxiliaries, EbnfValues.consView, cast_cast]

private theorem expressionThirdValue_transport_explicit
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {firstSite secondSite thirdSite : GrammarSite}
    {firstTarget secondTarget thirdTarget : EbnfExpr}
    (childrenEq : children = [firstSite, secondSite, thirdSite])
    (firstEq : firstSite.expression = firstTarget)
    (secondEq : secondSite.expression = secondTarget)
    (thirdEq : thirdSite.expression = thirdTarget)
    (layout : children.map GrammarSite.expression =
      [firstTarget, secondTarget, thirdTarget])
    (firstValue : EbnfValue file tokens firstTarget)
    (secondValue : EbnfValue file tokens secondTarget)
    (thirdValue : EbnfValue file tokens thirdTarget) :
    EbnfValue.transport thirdEq
        (expressionThirdValue childrenEq
          (Eq.mp (congrArg (EbnfValues file tokens) layout.symm)
            (EbnfValues.cons firstTarget [secondTarget, thirdTarget]
              firstValue
              (EbnfValues.cons secondTarget [thirdTarget] secondValue
                (EbnfValues.cons thirdTarget [] thirdValue
                  EbnfValues.nil))))) =
      thirdValue := by
  subst children
  subst firstTarget
  subst secondTarget
  subst thirdTarget
  have layoutProof : layout = rfl := Subsingleton.elim _ _
  rw [layoutProof]
  simp [expressionThirdValue, EbnfValues.consView,
    EbnfValue.transport]

private def atomDotOptionalValue
    {file : WorkspaceFile} {tokens : List Token}
    (values : EbnfValues file tokens
      (atomDotSequenceSite.children.map GrammarSite.expression)) :
    EbnfValue file tokens (.optional atomDotArgumentsExpression) :=
  EbnfValue.atShape atomDotOptionalSite_expression
    (expressionThirdValue atomDotSequenceSite_children values)

private theorem atomDotOptionalValue_withoutArguments
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    atomDotOptionalValue
        (atomDotWithoutArgumentsSequenceValues dot name) =
      EbnfValue.optional atomDotArgumentsExpression none := by
  unfold atomDotOptionalValue atomDotWithoutArgumentsSequenceValues
    atomDotWithoutArgumentsExplicitValues
  exact expressionThirdValue_transport_explicit
    atomDotSequenceSite_children atomDotTokenSite_expression
    atomDotNameSite_expression atomDotOptionalSite_expression
    atomDotSequenceSite_expressions
    (EbnfValue.terminalAtom (.symbol .dot) dot)
    (EbnfValue.terminalAtom (.category .identifier) name)
    (EbnfValue.optional atomDotArgumentsExpression none)

private theorem atomDotOptionalValue_auxiliaryTuple
    {file : WorkspaceFile} {tokens : List Token}
    (firstValue : EbnfValue file tokens atomDotTokenSite.site.expression)
    (secondValue : EbnfValue file tokens atomDotNameSite.site.expression)
    (thirdValue : EbnfValue file tokens atomDotOptionalSite.site.expression) :
    atomDotOptionalValue
        (EbnfValues.ofAuxiliaries atomDotSequenceSite.children
          (Eq.mp
            (congrArg (GrammarSymbolValues file tokens)
              (congrArg
                (List.map (fun child =>
                  GrammarSymbol.nonterminal (.aux child)))
                atomDotSequenceSite_children).symm)
            (firstValue, (secondValue, (thirdValue, ()))))) =
      EbnfValue.atShape atomDotOptionalSite_expression thirdValue := by
  unfold atomDotOptionalValue
  rw [expressionThirdValue_ofAuxiliaries]
  unfold auxiliaryThirdValue
  simp [EbnfValue.atShape, cast_cast]

private theorem atomDotOptionalValue_auxiliaryTuple_of_lhs
    {file : WorkspaceFile} {tokens : List Token}
    {secondLhs thirdLhs : NonterminalSymbol}
    (secondLhsEq : secondLhs = .aux atomDotNameSite.site)
    (thirdLhsEq : thirdLhs = .aux atomDotOptionalSite.site)
    (symbolLayout : atomDotSequenceSite.children.map
        (fun child => GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal (.aux atomDotTokenSite.site),
      .nonterminal secondLhs, .nonterminal thirdLhs])
    (firstValue : EbnfValue file tokens atomDotTokenSite.site.expression)
    (secondValue : GrammarSymbolValue file tokens (.nonterminal secondLhs))
    (thirdValue : GrammarSymbolValue file tokens (.nonterminal thirdLhs)) :
    atomDotOptionalValue
        (EbnfValues.ofAuxiliaries atomDotSequenceSite.children
          (GrammarSymbolValues.transport symbolLayout.symm
            (firstValue, (secondValue, (thirdValue, ()))))) =
      EbnfValue.atShape atomDotOptionalSite_expression
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
          (congrArg GrammarSymbol.nonterminal thirdLhsEq)) thirdValue) := by
  subst secondLhs
  subst thirdLhs
  have symbolProof : symbolLayout =
      congrArg
        (List.map (fun child =>
          GrammarSymbol.nonterminal (.aux child)))
        atomDotSequenceSite_children := Subsingleton.elim _ _
  rw [symbolProof]
  exact atomDotOptionalValue_auxiliaryTuple
    firstValue secondValue thirdValue

private def atomDotWithoutArgumentsInput
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
  EbnfValue file tokens (m2cV1.rhs .atom) :=
  EbnfValue.choice (EbnfExpr.children (m2cV1.rhs .atom))
    ⟨atomDotRootBranch, atomDotWithoutArgumentsChild dot name⟩

private theorem atomDotWithoutArgumentsInput_branchTag
    {file : WorkspaceFile} {tokens : List Token}
    (dot : MatchedTerminal file tokens (.symbol .dot))
    (name : MatchedTerminal file tokens (.category .identifier)) :
    (EbnfValue.choiceView (EbnfExpr.children (m2cV1.rhs .atom))
      (atomDotWithoutArgumentsInput dot name)).1.val = 2 := by
  unfold atomDotWithoutArgumentsInput
  exact choiceView_choice_branch_val _ atomDotRootBranch _

private def atomLambdaInput
    {file : WorkspaceFile} {tokens : List Token}
    (value : Expression) :
  EbnfValue file tokens (m2cV1.rhs .atom) :=
  EbnfValue.choice (EbnfExpr.children (m2cV1.rhs .atom))
    ⟨atomLambdaRootBranch, EbnfValue.ruleAtom .lambda value⟩

private theorem atomLambdaInput_branchTag
    {file : WorkspaceFile} {tokens : List Token}
    (value : Expression) :
    (EbnfValue.choiceView (EbnfExpr.children (m2cV1.rhs .atom))
      (atomLambdaInput (file := file) (tokens := tokens) value)).1.val = 4 := by
  unfold atomLambdaInput
  exact choiceView_choice_branch_val _ atomLambdaRootBranch _

private theorem transport_append_empty_single_to
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol}
    (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full)
    (viewLayout : full = [target])
    (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens prior)
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append empty (value, ()))) =
      (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout) value,
        ()) := by
  subst prior
  rcases empty with ⟨⟩
  exact GrammarSymbolValues.transport_append_single_to
    fullLayout viewLayout symbolLayout value

private theorem GrammarSymbolValues.transport_append_three_direct
    {file : WorkspaceFile} {tokens : List Token}
    {prior middle full : List GrammarSymbol}
    {first second third : GrammarSymbol}
    (priorLayout : prior = [first])
    (middleLayout : prior ++ [second] = middle)
    (fullLayout : middle ++ [third] = full)
    (targetLayout : full = [first, second, third])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second)
    (thirdValue : GrammarSymbolValue file tokens third) :
    GrammarSymbolValues.transport fullLayout
        (GrammarSymbolValues.append
          (GrammarSymbolValues.transport middleLayout
            (GrammarSymbolValues.append
              (GrammarSymbolValues.transport priorLayout.symm
                (firstValue, ()))
              (secondValue, ())))
          (thirdValue, ())) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, (thirdValue, ()))) := by
  subst prior
  subst middle
  subst full
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem prefixValues_eq_zeroValue
    {file : WorkspaceFile} {tokens : List Token}
    (item : ContextualItemKey tokens)
    (values : PrefixValues file tokens item)
    (zero : item.raw.dot.val = 0) :
    values = PrefixValues.zeroValue item zero := by
  let layout := prefix_zero_layout item.raw zero
  generalize emptyEq :
    GrammarSymbolValues.transport layout.symm values = empty
  rcases empty with ⟨⟩
  have transported := congrArg
    (GrammarSymbolValues.transport layout) emptyEq
  rw [GrammarSymbolValues.transport_trans] at transported
  exact (GrammarSymbolValues.transport_self _ values).symm.trans transported

private theorem sequencePairView_ofAuxiliaries
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {firstSite secondSite : GrammarSite}
    {secondSymbol : GrammarSymbol}
    {first second : EbnfExpr}
    (childrenEq : children = [firstSite, secondSite])
    (firstEq : firstSite.expression = first)
    (secondEq : secondSite.expression = second)
    (secondSymbolEq : secondSymbol =
      GrammarSymbol.nonterminal (.aux secondSite))
    (symbolLayout :
      children.map (fun site => GrammarSymbol.nonterminal (.aux site)) =
        [GrammarSymbol.nonterminal (.aux firstSite),
          secondSymbol])
    (expressionLayout : children.map GrammarSite.expression =
      [first, second])
    (firstValue : EbnfValue file tokens firstSite.expression)
    (secondValue : GrammarSymbolValue file tokens secondSymbol) :
    EbnfValue.sequence2View first second
        (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
          (EbnfValue.sequence (children.map GrammarSite.expression)
            (EbnfValues.ofAuxiliaries children
              (GrammarSymbolValues.transport symbolLayout.symm
                (firstValue, (secondValue, ())))))) =
      (EbnfValue.transport firstEq firstValue,
        EbnfValue.transport secondEq
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            secondSymbolEq) secondValue)) := by
  subst secondSymbol
  subst children
  have exactSymbolLayout : symbolLayout = rfl :=
    Subsingleton.elim _ _
  rw [exactSymbolLayout]
  simp only [List.map, GrammarSymbolValues.transport_self]
  have canonicalExpressionLayout :
      [firstSite.expression, secondSite.expression] =
        [first, second] := by
    rw [firstEq, secondEq]
  have exactExpressionLayout : expressionLayout =
      canonicalExpressionLayout := Subsingleton.elim _ _
  rw [exactExpressionLayout]
  rw [sequence2View_transport_pair_eq firstEq secondEq
    canonicalExpressionLayout]
  have firstAuxView := EbnfValues.ofAuxiliaries_cons_eq
    firstSite [secondSite] firstValue (secondValue, ())
  have firstViewEq :
      (EbnfValues.consView firstSite.expression [secondSite.expression]
        (EbnfValues.ofAuxiliaries [firstSite, secondSite]
          (firstValue, (secondValue, ())))).1 = firstValue :=
    congrArg Prod.fst firstAuxView
  have tailEq :
      (EbnfValues.consView firstSite.expression [secondSite.expression]
        (EbnfValues.ofAuxiliaries [firstSite, secondSite]
          (firstValue, (secondValue, ())))).2 =
        EbnfValues.ofAuxiliaries [secondSite]
          (secondValue, ()) :=
    congrArg Prod.snd firstAuxView
  have secondAuxView := EbnfValues.ofAuxiliaries_cons_eq
    secondSite [] secondValue ()
  have secondViewEq :
      (EbnfValues.consView secondSite.expression []
        (EbnfValues.ofAuxiliaries [secondSite]
          (secondValue, ()))).1 = secondValue :=
    congrArg Prod.fst secondAuxView
  apply Prod.ext
  · exact congrArg (EbnfValue.transport firstEq) firstViewEq
  · calc
      _ = EbnfValue.transport secondEq
          (EbnfValues.consView secondSite.expression []
            (EbnfValues.ofAuxiliaries [secondSite]
              (secondValue, ()))).1 :=
        congrArg
          (fun tail => EbnfValue.transport secondEq
            (EbnfValues.consView secondSite.expression [] tail).1)
          tailEq
      _ = _ := congrArg (EbnfValue.transport secondEq) secondViewEq

private theorem postfixDotCall_physicalPrefix
    {tokens : List Token}
    {origin finish : Boundary tokens}
    (span : SourceSpan) (marker : Located Unit)
    (name : IdentifierOccurrence) (openParen : SourceSpan)
    (arguments : List Expression) (closeParen : SourceSpan)
    (rest : List PostfixPartValue)
    (evidence : TokenPlanEvidence
      (postfixFoldSourceTokenPlan?
        { span := span
          payload := .dotConstructor marker name none }
        (.call openParen arguments closeParen :: rest))
      (PhysicalTokens tokens origin finish)) :
    ∃ dotToken nameToken openToken tail,
      PhysicalTokens tokens origin finish =
        dotToken :: nameToken :: openToken :: tail ∧
      dotToken.payload = .symbol .dot ∧
      nameToken.payload = .identifier name.payload.render ∧
      openToken.payload = .symbol .leftParen := by
  rcases evidence with ⟨plan, candidate, relation⟩
  unfold postfixFoldSourceTokenPlan? at candidate
  simp only [atomExpressionTokenPlan?, expressionTokenPlanAt?,
    List.mapM_cons, postfixPartTokenPlan?] at candidate
  cases argumentsEq : expressionTokenPlans? arguments with
  | none => simp [argumentsEq] at candidate
  | some argumentPlans =>
      cases restEq : List.mapM postfixPartTokenPlan? rest with
      | none => simp [argumentsEq, restEq] at candidate
      | some restPlans =>
          simp [argumentsEq, restEq] at candidate
          subst plan
          simp [TokenPlan.append, TokenPlan.enclose, TokenPlan.concat,
            TokenPlan.exact, identifierPlan, TokenSlot.enclose] at relation
          generalize actualEq : PhysicalTokens tokens origin finish = actual
            at relation
          change TokenSlot.ListMatches
            (.required _ :: .required _ :: .required _ :: _) _ at relation
          cases relation with
          | required dotMatches relation =>
              cases relation with
              | required nameMatches relation =>
                  cases relation with
                  | required openMatches relation =>
                      refine ⟨_, _, _, _, rfl, ?_, ?_, ?_⟩
                      · exact dotMatches.1.symm
                      · exact nameMatches.1.symm
                      · exact openMatches.1.symm

private theorem leadingDotArguments_of_physicalPrefix
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish site : Boundary tokens}
    {dotToken nameToken openToken : Token} {tail : List Token}
    (name : IdentifierOccurrence)
    (owned : TokensOwnedBy file tokens)
    (siteEq : site.val = origin.val + 2)
    (physicalEq : PhysicalTokens tokens origin finish =
      dotToken :: nameToken :: openToken :: tail)
    (dotPayload : dotToken.payload = .symbol .dot)
    (namePayload : nameToken.payload = .identifier name.payload.render)
    (openPayload : openToken.payload = .symbol .leftParen) :
    ExactSlice file tokens origin site [
        .symbol .dot, .category .identifier] ∧
      SymbolAtBoundary file tokens site .leftParen := by
  have lengthThree : 3 ≤ (PhysicalTokens tokens origin finish).length := by
    rw [physicalEq]
    simp
  unfold PhysicalTokens at lengthThree
  simp only [List.length_take, List.length_drop] at lengthThree
  have originLe : origin.val ≤ tokens.length := by
    by_cases candidate : origin.val ≤ tokens.length
    · exact candidate
    · have minEq : Nat.min origin.val tokens.length = tokens.length :=
        Nat.min_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge candidate))
      rw [minEq] at lengthThree
      simp at lengthThree
  have startEq : Nat.min origin.val tokens.length = origin.val :=
    Nat.min_eq_left originLe
  rw [startEq] at lengthThree
  have originBound : origin.val + 2 < tokens.length := by omega
  have dotAt := congrArg (fun values : List Token => values[0]?) physicalEq
  have nameAt := congrArg (fun values : List Token => values[1]?) physicalEq
  have openAt := congrArg (fun values : List Token => values[2]?) physicalEq
  have countZero : 0 < Nat.min finish.val tokens.length - origin.val := by
    omega
  have countOne : 1 < Nat.min finish.val tokens.length - origin.val := by
    omega
  have countTwo : 2 < Nat.min finish.val tokens.length - origin.val := by
    omega
  simp only [PhysicalTokens, startEq, List.getElem?_take,
    countZero, countOne, countTwo, ↓reduceIte, List.getElem?_drop,
    Nat.add_zero, List.getElem?_cons_zero, List.getElem?_cons_succ]
    at dotAt nameAt openAt
  let dotCursor : TerminalCursor tokens :=
    ⟨origin.val, by omega⟩
  let nameCursor : TerminalCursor tokens :=
    ⟨origin.val + 1, by omega⟩
  let openCursor : TerminalCursor tokens :=
    ⟨origin.val + 2, by omega⟩
  have dotTerminalAt : TerminalAt file tokens dotCursor
      (.retained dotToken) dotToken.span := by
    apply TerminalAt.retained
    · dsimp only [dotCursor]
      omega
    · simpa [dotCursor] using dotAt
    · exact owned dotToken (List.mem_of_getElem? dotAt)
  have nameTerminalAt : TerminalAt file tokens nameCursor
      (.retained nameToken) nameToken.span := by
    apply TerminalAt.retained
    · dsimp only [nameCursor]
      omega
    · simpa [nameCursor] using nameAt
    · exact owned nameToken (List.mem_of_getElem? nameAt)
  have openTerminalAt : TerminalAt file tokens openCursor
      (.retained openToken) openToken.span := by
    apply TerminalAt.retained
    · dsimp only [openCursor]
      omega
    · simpa [openCursor] using openAt
    · exact owned openToken (List.mem_of_getElem? openAt)
  constructor
  · constructor
    · simpa using siteEq
    · intro index
      have indexCases : index.val = 0 ∨ index.val = 1 := by
        have bound := index.isLt
        simp only [List.length_cons, List.length_nil] at bound
        omega
      rcases indexCases with indexZero | indexOne
      · have indexEq : index = ⟨0, by decide⟩ := Fin.ext indexZero
        subst index
        refine ⟨dotCursor, dotToken, ?_, dotTerminalAt, ?_⟩
        · rfl
        · simpa [TerminalMatches] using dotPayload
      · have indexEq : index = ⟨1, by decide⟩ := Fin.ext indexOne
        subst index
        refine ⟨nameCursor, nameToken, ?_, nameTerminalAt, ?_⟩
        · rfl
        · exact ⟨name.payload.render, name.payload, namePayload,
            Identifier.parse_render name.payload⟩
  · refine ⟨openCursor, openToken, ?_, openTerminalAt, openPayload⟩
    apply Fin.ext
    dsimp only [openCursor, TerminalCursor.beforeBoundary]
    exact siteEq.symm

/-- Coherent postfix parsing excludes the one source split that the AST
visitor intentionally rejects: a leading-dot constructor without arguments
followed by a call suffix. -/
private theorem coherentPostfix_admissible
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .postfix origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .postfix origin finish context).raw)
    (owned : TokensOwnedBy file tokens)
    (atom : Expression) (parts : List PostfixPartValue)
    (sourceEvidence : TokenPlanEvidence
      (postfixFoldSourceTokenPlan? atom parts)
      (PhysicalTokens tokens origin finish))
    (coherent : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .postfix origin finish context)
      priorValues)
    (inputEq : RootAction.unpack .postfix
      (PrefixValues.fullValue
        (CanonicalCompleteRootItem tokens .postfix origin finish context)
        complete priorValues) =
      postfixSourceValue atom parts) :
    PostfixFoldAdmissible atom parts := by
  cases parts with
  | nil => trivial
  | cons part rest =>
      cases part with
      | select => trivial
      | index => trivial
      | call openParen arguments closeParen =>
          rcases atom with ⟨atomSpan, atomPayload⟩
          cases atomPayload <;> try trivial
          case dotConstructor marker name constructorArguments =>
            cases constructorArguments with
            | some values => trivial
            | none =>
                obtain ⟨dotToken, nameToken, openToken, physicalTail,
                    physicalEq, dotPayload, namePayload, openPayload⟩ :=
                  postfixDotCall_physicalPrefix atomSpan marker name openParen
                    arguments closeParen rest sourceEvidence
                cases coherent with
                | zero item reached zero =>
                    simp [CanonicalCompleteRootItem] at zero
                | scan before after cursor priorValues witness edge prior =>
                    rcases witness.advance with
                      ⟨productionEq, dotEq, originEq, currentEq⟩
                    simp [CanonicalCompleteRootItem] at productionEq dotEq
                    have lookup0 :
                        before.raw.production.rhs[0]? =
                          some (.terminal witness.terminal) := by
                      have beforeDot : before.raw.dot.val = 0 :=
                        congrArg Fin.val dotEq
                      simpa only [beforeDot] using witness.next.2
                    have rootLookup :
                        (ProductionId.root .postfix).rhs[0]? =
                          some (.terminal witness.terminal) :=
                      (congrArg (fun production : ProductionId =>
                        production.rhs[0]?) productionEq).trans lookup0
                    simp at rootLookup
                | complete waiting finished after shared priorValues childValue
                    witness edge prior child =>
                    rcases witness.advance with
                      ⟨productionEq, dotEq, originEq, currentEq⟩
                    simp [CanonicalCompleteRootItem] at productionEq dotEq
                    cases prior with
                    | zero item reached zero =>
                        have waitingProduction :
                            waiting.raw.production = .root .postfix :=
                          productionEq.symm
                        have waitingDot : waiting.raw.dot.val = 0 :=
                          congrArg Fin.val dotEq
                        have finishedLhs : finished.raw.production.lhs =
                            .aux (GrammarSite.root .postfix) := by
                          let index : Nat := waiting.raw.dot.val
                          have selected :
                              some (GrammarSymbol.nonterminal
                                  (.aux (GrammarSite.root .postfix))) =
                                some (GrammarSymbol.nonterminal
                                  finished.raw.production.lhs) := by
                            calc
                              _ = (ProductionId.root .postfix).rhs[index]? := by
                                simp [index, waitingDot]
                              _ = waiting.raw.production.rhs[index]? :=
                                congrArg (fun production : ProductionId =>
                                  production.rhs[index]?)
                                  waitingProduction.symm
                              _ = waiting.raw.production.rhs[
                                  waiting.raw.dot.val]? := rfl
                              _ = _ := witness.next.2
                          exact (GrammarSymbol.nonterminal.inj
                            (Option.some.inj selected)).symm
                        obtain ⟨sequenceSite, sequenceProduction⟩ :=
                          postfixRootChild_isSequence
                            finished.raw.production finishedLhs
                        cases child with
                        | reduce sequenceItem sequencePrior sequenceOutput
                            sequenceReached sequenceComplete sequencePrefix
                            sequenceAction =>
                            have sequenceSiteRoot : sequenceSite.site =
                                GrammarSite.root .postfix := by
                              rw [sequenceProduction] at finishedLhs
                              exact NonterminalSymbol.aux.inj finishedLhs
                            rcases finished with
                              ⟨⟨sequenceProductionId, sequenceDot,
                                sequenceOrigin, sequenceCurrent⟩,
                                sequenceContext⟩
                            simp only at sequenceProduction
                            subst sequenceProductionId
                            cases sequenceAction
                            have childrenExpressions :=
                              SequenceSite.children_expression sequenceSite
                            rw [sequenceSiteRoot,
                              GrammarSite.root_expression] at childrenExpressions
                            simp only [EbnfExpr.children] at childrenExpressions
                            change sequenceSite.children.map
                                GrammarSite.expression =
                              postfixSourceChildren at childrenExpressions
                            have childrenLength :
                                sequenceSite.children.length = 2 := by
                              have exactLength :=
                                congrArg List.length childrenExpressions
                              simpa [postfixSourceChildren] using exactLength
                            cases sequencePrefix with
                            | zero item reached zero =>
                                unfold CompleteItem at sequenceComplete
                                have zeroValue : sequenceDot.val = 0 := zero
                                simp [ProductionId.rhs_seq, childrenLength]
                                  at sequenceComplete
                                omega
                            | scan before after cursor priorValues scanWitness
                                scanEdge scanPrior =>
                                have beforeMember : GrammarSymbol.terminal
                                    scanWitness.terminal ∈
                                    before.raw.production.rhs :=
                                  List.mem_of_getElem? scanWitness.next.2
                                have member : GrammarSymbol.terminal
                                    scanWitness.terminal ∈
                                    (ProductionId.seq sequenceSite).rhs := by
                                  have rhsEq := congrArg ProductionId.rhs
                                    scanWitness.advance.1
                                  rw [rhsEq]
                                  exact beforeMember
                                simp [ProductionId.rhs_seq] at member
                            | complete starWaiting starFinished starAfter
                                starShared starPrior starValue starWitness
                                starEdge starPrefix starChild =>
                                obtain ⟨firstSite, secondSite, childrenEq⟩ :=
                                  list_eq_pair_of_length_two
                                    sequenceSite.children childrenLength
                                have childExpressions :
                                    firstSite.expression =
                                        .atom (.nonterminal .atom) ∧
                                      secondSite.expression =
                                        .star (.atom
                                          (.nonterminal .postfixPart)) := by
                                  simpa [postfixSourceChildren, childrenEq]
                                    using childrenExpressions
                                have sequenceDotValue :
                                    sequenceDot.val = 2 := by
                                  unfold CompleteItem at sequenceComplete
                                  simpa [ProductionId.rhs_seq,
                                    childrenLength] using sequenceComplete
                                have starWaitingProduction :
                                    starWaiting.raw.production =
                                      .seq sequenceSite :=
                                  starWitness.advance.1.symm
                                have starWaitingDot :
                                    starWaiting.raw.dot.val = 1 := by
                                  have advanced := starWitness.advance.2.1
                                  change sequenceDot.val =
                                    starWaiting.raw.dot.val + 1 at advanced
                                  omega
                                have starFinishedLhs :
                                    starFinished.raw.production.lhs =
                                      .aux secondSite := by
                                  have nextLookup :
                                      starWaiting.raw.production.rhs[
                                          starWaiting.raw.dot.val]? =
                                        some (.nonterminal
                                          starFinished.raw.production.lhs) :=
                                    starWitness.next.2
                                  have canonicalLookup :
                                      (ProductionId.seq sequenceSite).rhs[1]? =
                                        some (.nonterminal
                                          starFinished.raw.production.lhs) := by
                                    calc
                                      _ = starWaiting.raw.production.rhs[1]? :=
                                        congrArg (fun production : ProductionId =>
                                          production.rhs[1]?)
                                          starWaitingProduction.symm
                                      _ = starWaiting.raw.production.rhs[
                                          starWaiting.raw.dot.val]? := by
                                        rw [starWaitingDot]
                                      _ = _ := nextLookup
                                  simp [ProductionId.rhs_seq, childrenEq]
                                    at canonicalLookup
                                  exact canonicalLookup.symm
                                cases starPrefix with
                                | zero item reached zero =>
                                    have zeroValue :
                                        starWaiting.raw.dot.val = 0 := zero
                                    omega
                                | scan before after cursor scanPriorValues
                                    scanWitness scanEdge scanPrior =>
                                    rcases scanWitness.advance with
                                      ⟨scanProduction, scanDot, scanOrigin,
                                        scanCurrent⟩
                                    have beforeMember :
                                        GrammarSymbol.terminal
                                            scanWitness.terminal ∈
                                          before.raw.production.rhs :=
                                      List.mem_of_getElem?
                                        scanWitness.next.2
                                    have rhsEq :
                                        (ProductionId.seq sequenceSite).rhs =
                                          before.raw.production.rhs :=
                                      (congrArg ProductionId.rhs
                                        starWaitingProduction).symm.trans
                                        (congrArg ProductionId.rhs
                                          scanProduction)
                                    have member :
                                        GrammarSymbol.terminal
                                            scanWitness.terminal ∈
                                          (ProductionId.seq
                                            sequenceSite).rhs := by
                                      rw [rhsEq]
                                      exact beforeMember
                                    simp [ProductionId.rhs_seq] at member
                                | complete atomWaiting atomFinished atomAfter
                                    atomShared atomPrior atomValue atomWitness
                                    atomEdge atomPrefix atomChild =>
                                    have atomWaitingProduction :
                                        atomWaiting.raw.production =
                                          .seq sequenceSite := by
                                      calc
                                        _ = starWaiting.raw.production :=
                                          atomWitness.advance.1.symm
                                        _ = _ := starWaitingProduction
                                    have atomWaitingDot :
                                        atomWaiting.raw.dot.val = 0 := by
                                      have advanced :=
                                        atomWitness.advance.2.1
                                      change starWaiting.raw.dot.val =
                                        atomWaiting.raw.dot.val + 1 at advanced
                                      omega
                                    have atomFinishedLhs :
                                        atomFinished.raw.production.lhs =
                                          .aux firstSite := by
                                      have nextLookup :
                                          atomWaiting.raw.production.rhs[
                                              atomWaiting.raw.dot.val]? =
                                            some (.nonterminal
                                              atomFinished.raw.production.lhs) :=
                                        atomWitness.next.2
                                      have canonicalLookup :
                                          (ProductionId.seq sequenceSite).rhs[0]? =
                                            some (.nonterminal
                                              atomFinished.raw.production.lhs) := by
                                        calc
                                          _ = atomWaiting.raw.production.rhs[0]? :=
                                            congrArg
                                              (fun production : ProductionId =>
                                                production.rhs[0]?)
                                              atomWaitingProduction.symm
                                          _ = atomWaiting.raw.production.rhs[
                                              atomWaiting.raw.dot.val]? := by
                                            rw [atomWaitingDot]
                                          _ = _ := nextLookup
                                      simp [ProductionId.rhs_seq, childrenEq]
                                        at canonicalLookup
                                      exact canonicalLookup.symm
                                    cases atomPrefix with
                                    | zero item atomReached atomZero =>
                                        have firstKind :
                                            firstSite.expression.kind =
                                              .atom := by
                                          rw [childExpressions.1]
                                          rfl
                                        obtain ⟨atomSite, atomProduction,
                                            atomSiteEq⟩ :=
                                          auxiliaryAtomProduction
                                            atomFinished.raw.production
                                            firstSite atomFinishedLhs firstKind
                                        cases atomChild with
                                        | reduce atomItem atomValues atomOutput
                                            atomItemReached atomItemComplete
                                            atomCoherent atomAction =>
                                          rcases atomFinished with
                                            ⟨⟨atomProductionId, atomDot,
                                              atomOrigin, atomCurrent⟩,
                                              atomContext⟩
                                          simp only at atomProduction atomFinishedLhs inputEq ⊢
                                          subst atomProductionId
                                          cases atomAction
                                          have atomSiteAtom :
                                              atomSite.atom =
                                                .nonterminal .atom := by
                                            have sameExpression :
                                                atomSite.site.expression =
                                                  .atom
                                                    (.nonterminal .atom) := by
                                              rw [atomSiteEq,
                                                childExpressions.1]
                                            exact EbnfExpr.atom.inj
                                              (atomSite.expression_eq_atom.symm.trans
                                                sameExpression)
                                          cases atomCoherent with
                                          | zero item itemReached itemZero =>
                                              unfold CompleteItem at atomItemComplete
                                              have itemZeroValue :
                                                  atomDot.val = 0 := itemZero
                                              simp [ProductionId.rhs_atom] at atomItemComplete
                                              omega
                                          | scan before after cursor priorValues
                                              scanWitness scanEdge scanPrior =>
                                              have beforeMember :
                                                  GrammarSymbol.terminal
                                                      scanWitness.terminal ∈
                                                    before.raw.production.rhs :=
                                                List.mem_of_getElem?
                                                  scanWitness.next.2
                                              have rhsEq :
                                                  (ProductionId.atom
                                                      atomSite).rhs =
                                                    before.raw.production.rhs :=
                                                congrArg ProductionId.rhs
                                                  scanWitness.advance.1
                                              have member :
                                                  GrammarSymbol.terminal
                                                      scanWitness.terminal ∈
                                                    (ProductionId.atom
                                                      atomSite).rhs := by
                                                rw [rhsEq]
                                                exact beforeMember
                                              have impossible :
                                                  GrammarSymbol.terminal
                                                      scanWitness.terminal =
                                                    .nonterminal (.rule .atom) := by
                                                calc
                                                  _ = atomSite.symbol := by
                                                    simpa [ProductionId.rhs_atom]
                                                      using member
                                                  _ = _ := by
                                                    rw [atomSite.symbol_eq,
                                                      atomSiteAtom]
                                                    rfl
                                              cases impossible
                                          | complete sourceWaiting
                                              sourceFinished sourceAfter
                                              sourceShared sourcePrior
                                              sourceValue sourceWitness
                                              sourceEdge sourcePrefix
                                              sourceChild =>
                                              have sourceWaitingDot :
                                                  sourceWaiting.raw.dot.val =
                                                    0 := by
                                                have advanced :=
                                                  sourceWitness.advance.2.1
                                                unfold CompleteItem at atomItemComplete
                                                simp [ProductionId.rhs_atom] at atomItemComplete
                                                change atomDot.val =
                                                  sourceWaiting.raw.dot.val + 1
                                                  at advanced
                                                omega
                                              have sourceFinishedLhs :
                                                  sourceFinished.raw.production.lhs =
                                                    .rule .atom := by
                                                have nextLookup :=
                                                  sourceWitness.next.2
                                                have waitingProduction :
                                                    sourceWaiting.raw.production =
                                                      .atom atomSite :=
                                                  sourceWitness.advance.1.symm
                                                have canonicalLookup :
                                                    (ProductionId.atom
                                                        atomSite).rhs[0]? =
                                                      some (.nonterminal
                                                        sourceFinished.raw.production.lhs) := by
                                                  calc
                                                    _ = sourceWaiting.raw.production.rhs[0]? :=
                                                      congrArg
                                                        (fun production :
                                                            ProductionId =>
                                                          production.rhs[0]?)
                                                        waitingProduction.symm
                                                    _ = sourceWaiting.raw.production.rhs[
                                                        sourceWaiting.raw.dot.val]? := by
                                                      rw [sourceWaitingDot]
                                                    _ = _ := nextLookup
                                                simp [ProductionId.rhs_atom]
                                                  at canonicalLookup
                                                have symbolEq :
                                                    atomSite.symbol =
                                                      GrammarSymbol.nonterminal
                                                        (NonterminalSymbol.rule
                                                          .atom) := by
                                                  rw [atomSite.symbol_eq,
                                                    atomSiteAtom]
                                                  rfl
                                                have nonterminalEq :
                                                    GrammarSymbol.nonterminal
                                                        sourceFinished.raw.production.lhs =
                                                      GrammarSymbol.nonterminal
                                                        (NonterminalSymbol.rule
                                                          .atom) :=
                                                  canonicalLookup.symm.trans
                                                    symbolEq
                                                exact
                                                  GrammarSymbol.nonterminal.inj
                                                    nonterminalEq
                                              have sourceProduction :=
                                                production_of_rule_lhs
                                                  sourceFinished.raw.production
                                                  .atom sourceFinishedLhs
                                              cases sourceChild with
                                              | reduce sourceItem sourceValues
                                                  sourceOutput sourceReached
                                                  sourceComplete
                                                  sourceCoherent sourceAction =>
                                                  rcases sourceFinished with
                                                    ⟨⟨sourceProductionId,
                                                      sourceDot,
                                                      sourceOrigin,
                                                      sourceCurrent⟩,
                                                      sourceContext⟩
                                                  simp only at sourceProduction sourceFinishedLhs inputEq ⊢
                                                  subst sourceProductionId
                                                  cases sourceAction with
                                                  | root rule _ _ _ _
                                                      sourceReduction =>
                                                      cases sourcePrefix with
                                                      | zero sourceWaiting
                                                          sourceWaitingReached
                                                          sourceWaitingZero =>
                                                          rcases waiting with
                                                            ⟨⟨rootWaitingProductionId,
                                                              rootWaitingDotFin,
                                                              rootWaitingOrigin,
                                                              rootWaitingCurrent⟩,
                                                              rootWaitingContext⟩
                                                          simp only at waitingProduction waitingDot inputEq ⊢
                                                          subst rootWaitingProductionId
                                                          let exactRootDot : Fin
                                                              ((ProductionId.root .postfix).rhs.length + 1) :=
                                                            ⟨0, by simp⟩
                                                          have rootWaitingDotEq :
                                                              rootWaitingDotFin =
                                                                exactRootDot :=
                                                            Fin.ext waitingDot
                                                          subst rootWaitingDotFin
                                                          rcases atomWaiting with
                                                            ⟨⟨atomWaitingProductionId,
                                                              atomWaitingDotFin,
                                                              atomWaitingOrigin,
                                                              atomWaitingCurrent⟩,
                                                              atomWaitingContext⟩
                                                          simp only at atomWaitingProduction atomWaitingDot atomZero inputEq ⊢
                                                          subst atomWaitingProductionId
                                                          rcases atomWaitingDotFin with
                                                            ⟨atomWaitingDotValue,
                                                              atomWaitingDotBound⟩
                                                          simp only at atomWaitingDot atomZero
                                                          subst atomWaitingDotValue
                                                          rcases starWaiting with
                                                            ⟨⟨starWaitingProductionId,
                                                              starWaitingDotFin,
                                                              starWaitingOrigin,
                                                              starWaitingCurrent⟩,
                                                              starWaitingContext⟩
                                                          simp only at starWaitingProduction starWaitingDot inputEq ⊢
                                                          subst starWaitingProductionId
                                                          rcases starWaitingDotFin with
                                                            ⟨starWaitingDotValue,
                                                              starWaitingDotBound⟩
                                                          simp only at starWaitingDot
                                                          subst starWaitingDotValue
                                                          let atomBefore :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.seq sequenceSite,
                                                              ⟨0,
                                                                atomWaitingDotBound⟩,
                                                              atomWaitingOrigin,
                                                              atomWaitingCurrent⟩,
                                                              atomWaitingContext⟩
                                                          let starBefore :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.seq sequenceSite,
                                                              ⟨1,
                                                                starWaitingDotBound⟩,
                                                              starWaitingOrigin,
                                                              starWaitingCurrent⟩,
                                                              starWaitingContext⟩
                                                          let atomItem :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.atom atomSite,
                                                              atomDot, atomOrigin,
                                                              atomCurrent⟩,
                                                              atomContext⟩
                                                          let atomPacked :=
                                                            AtomSite.pack atomSite
                                                              (PrefixValues.fullValue
                                                                atomItem
                                                                atomItemComplete
                                                                (PrefixValues.completeValue
                                                                  sourceWaiting
                                                                  { raw := {
                                                                      production :=
                                                                        .root .atom
                                                                      dot := sourceDot
                                                                      origin :=
                                                                        sourceOrigin
                                                                      current :=
                                                                        sourceCurrent }
                                                                    context :=
                                                                      sourceContext }
                                                                  atomItem
                                                                  sourceWitness.next
                                                                  sourceWitness.advance
                                                                  (PrefixValues.zeroValue
                                                                    sourceWaiting
                                                                    sourceWaitingZero)
                                                                  sourceValue))
                                                          have sequencePriorLayout :
                                                              (ProductionId.seq
                                                                  sequenceSite).rhs.take 1 =
                                                                [GrammarSymbol.nonterminal
                                                                  (.aux firstSite)] := by
                                                            simp [ProductionId.rhs_seq,
                                                              childrenEq]
                                                          have atomEmpty :
                                                              PrefixValues.zeroValue
                                                                  (file := file)
                                                                  atomBefore atomZero =
                                                                (show Unit from ()) := by
                                                            dsimp only [atomBefore]
                                                            unfold PrefixValues.zeroValue
                                                              GrammarSymbolValues.transport
                                                            simp
                                                          have atomSymbolLayout :
                                                              GrammarSymbol.nonterminal
                                                                  (ProductionId.atom
                                                                    atomSite).lhs =
                                                                GrammarSymbol.nonterminal
                                                                  (.aux firstSite) :=
                                                            congrArg
                                                              GrammarSymbol.nonterminal
                                                              atomFinishedLhs
                                                          have sequencePriorTupleEq :
                                                              GrammarSymbolValues.transport
                                                                  sequencePriorLayout
                                                                  (PrefixValues.completeValue
                                                                    atomBefore atomItem
                                                                    starBefore
                                                                    atomWitness.next
                                                                    atomWitness.advance
                                                                    (PrefixValues.zeroValue
                                                                      atomBefore atomZero)
                                                                    atomPacked) =
                                                                (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      atomSymbolLayout)
                                                                    atomPacked,
                                                                  ()) := by
                                                            unfold PrefixValues.completeValue
                                                            rw [atomEmpty]
                                                            exact
                                                              GrammarSymbolValues.transport_append_single_to
                                                                _ _ atomSymbolLayout
                                                                atomPacked
                                                          have sequencePriorRecover :
                                                              GrammarSymbolValues.transport
                                                                  sequencePriorLayout.symm
                                                                  (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        atomSymbolLayout)
                                                                      atomPacked,
                                                                    ()) =
                                                                PrefixValues.completeValue
                                                                  atomBefore atomItem
                                                                  starBefore
                                                                  atomWitness.next
                                                                  atomWitness.advance
                                                                  (PrefixValues.zeroValue
                                                                    atomBefore atomZero)
                                                                  atomPacked := by
                                                            have transported := congrArg
                                                              (GrammarSymbolValues.transport
                                                                sequencePriorLayout.symm)
                                                              sequencePriorTupleEq
                                                            have recovered :
                                                                GrammarSymbolValues.transport
                                                                    sequencePriorLayout.symm
                                                                    (GrammarSymbolValues.transport
                                                                      sequencePriorLayout
                                                                      (PrefixValues.completeValue
                                                                        atomBefore atomItem
                                                                        starBefore
                                                                        atomWitness.next
                                                                        atomWitness.advance
                                                                        (PrefixValues.zeroValue
                                                                          atomBefore atomZero)
                                                                        atomPacked)) =
                                                                  PrefixValues.completeValue
                                                                    atomBefore atomItem
                                                                    starBefore
                                                                    atomWitness.next
                                                                    atomWitness.advance
                                                                    (PrefixValues.zeroValue
                                                                      atomBefore atomZero)
                                                                    atomPacked := by
                                                              rw [GrammarSymbolValues.transport_trans]
                                                              exact
                                                                GrammarSymbolValues.transport_self
                                                                  _ _
                                                            exact transported.symm.trans
                                                              recovered
                                                          dsimp only [atomBefore, starBefore, atomItem, atomPacked] at sequencePriorRecover
                                                          rw [← sequencePriorRecover] at inputEq
                                                          rw [PrefixValues.fullValue_completeValue_eq] at inputEq
                                                          rw [PrefixValues.fullValue_completeValue_eq] at inputEq
                                                          let sequenceAfter :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.seq sequenceSite,
                                                              sequenceDot,
                                                              sequenceOrigin,
                                                              sequenceCurrent⟩,
                                                              sequenceContext⟩
                                                          have sequenceTargetLayout :
                                                              sequenceSite.children.map
                                                                  (fun child =>
                                                                    GrammarSymbol.nonterminal
                                                                      (.aux child)) =
                                                                [GrammarSymbol.nonterminal
                                                                    (.aux firstSite),
                                                                  GrammarSymbol.nonterminal
                                                                    starFinished.raw.production.lhs] := by
                                                            rw [childrenEq,
                                                              starFinishedLhs]
                                                            rfl
                                                          have sequenceTupleEq :
                                                              GrammarSymbolValues.view
                                                                  (ProductionId.rhs_seq
                                                                    sequenceSite)
                                                                  (GrammarSymbolValues.transport
                                                                    ((prefix_complete_layout
                                                                      starBefore.raw
                                                                      starFinished.raw
                                                                      sequenceAfter.raw
                                                                      starWitness.next
                                                                      starWitness.advance).trans
                                                                      (prefix_full_layout
                                                                        sequenceAfter.raw
                                                                        sequenceComplete))
                                                                    (GrammarSymbolValues.append
                                                                      (GrammarSymbolValues.transport
                                                                        sequencePriorLayout.symm
                                                                        (Eq.mp
                                                                            (congrArg
                                                                              (GrammarSymbolValue
                                                                                file tokens)
                                                                              atomSymbolLayout)
                                                                            atomPacked,
                                                                          ()))
                                                                      (starValue, ()))) =
                                                                GrammarSymbolValues.transport
                                                                  sequenceTargetLayout.symm
                                                                  (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        atomSymbolLayout)
                                                                      atomPacked,
                                                                    (starValue, ())) := by
                                                            exact
                                                              GrammarSymbolValues.transport_append_pair_to
                                                                sequencePriorLayout _ _
                                                                sequenceTargetLayout _ _
                                                          dsimp only [starBefore, sequenceAfter, atomPacked] at sequenceTupleEq
                                                          simp only [RootAction.unpack,
                                                            SequenceSite.pack] at inputEq
                                                          conv at inputEq in
                                                              (EbnfValues.ofAuxiliaries _
                                                                (GrammarSymbolValues.view _ _)) =>
                                                            rw [sequenceTupleEq]
                                                          let rootBefore :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.root .postfix,
                                                              exactRootDot,
                                                              rootWaitingOrigin,
                                                              rootWaitingCurrent⟩,
                                                              rootWaitingContext⟩
                                                          have rootEmpty :
                                                              PrefixValues.zeroValue
                                                                  (file := file)
                                                                  rootBefore zero =
                                                                (show Unit from ()) := by
                                                            dsimp only [rootBefore,
                                                              exactRootDot]
                                                            unfold PrefixValues.zeroValue
                                                              GrammarSymbolValues.transport
                                                            simp
                                                          rw [rootEmpty] at inputEq
                                                          dsimp only at inputEq
                                                          let sequencePacked :=
                                                            EbnfValue.ofShape
                                                              sequenceSite.expression_eq_sequence
                                                              (EbnfValue.sequence
                                                                (sequenceSite.children.map
                                                                  GrammarSite.expression)
                                                                (EbnfValues.ofAuxiliaries
                                                                  sequenceSite.children
                                                                  (GrammarSymbolValues.transport
                                                                    sequenceTargetLayout.symm
                                                                    (Eq.mp
                                                                        (congrArg
                                                                          (GrammarSymbolValue
                                                                            file tokens)
                                                                          atomSymbolLayout)
                                                                        atomPacked,
                                                                      (starValue, ())))))
                                                          have rootSymbolLayout :
                                                              GrammarSymbol.nonterminal
                                                                  (ProductionId.seq
                                                                    sequenceSite).lhs =
                                                                GrammarSymbol.nonterminal
                                                                  (.aux
                                                                    (GrammarSite.root
                                                                      .postfix)) :=
                                                            congrArg
                                                              GrammarSymbol.nonterminal
                                                              finishedLhs
                                                          have rootTupleEq :
                                                              GrammarSymbolValues.view
                                                                  (ProductionId.rhs_root
                                                                    .postfix)
                                                                  (GrammarSymbolValues.transport
                                                                    ((prefix_complete_layout
                                                                      rootBefore.raw
                                                                      sequenceAfter.raw
                                                                      (CanonicalCompleteRootItem
                                                                        tokens .postfix
                                                                        origin finish
                                                                        context).raw
                                                                      witness.next
                                                                      witness.advance).trans
                                                                      (prefix_full_layout
                                                                        (CanonicalCompleteRootItem
                                                                          tokens .postfix
                                                                          origin finish
                                                                          context).raw
                                                                        complete))
                                                                    (GrammarSymbolValues.append
                                                                      (left := []) ()
                                                                      (sequencePacked, ()))) =
                                                                (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      rootSymbolLayout)
                                                                    sequencePacked,
                                                                  ()) := by
                                                            exact
                                                              GrammarSymbolValues.transport_append_single_to
                                                                _ _ rootSymbolLayout
                                                                sequencePacked
                                                          dsimp only [rootBefore, sequenceAfter, sequencePacked, atomPacked] at rootTupleEq
                                                          generalize rootValuesEq :
                                                              GrammarSymbolValues.view
                                                                (ProductionId.rhs_root
                                                                  .postfix) _ =
                                                                rootValues at inputEq
                                                          have rootValuesCanonical :=
                                                            rootValuesEq.symm.trans
                                                              rootTupleEq
                                                          rw [rootValuesCanonical] at inputEq
                                                          let rawSequenceValue :=
                                                            EbnfValue.sequence
                                                              (sequenceSite.children.map
                                                                GrammarSite.expression)
                                                              (EbnfValues.ofAuxiliaries
                                                                sequenceSite.children
                                                                (GrammarSymbolValues.transport
                                                                  sequenceTargetLayout.symm
                                                                  (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        atomSymbolLayout)
                                                                      atomPacked,
                                                                    (starValue, ()))))
                                                          change
                                                            EbnfValue.atShape
                                                                (GrammarSite.root_expression
                                                                  .postfix)
                                                                (Eq.mp
                                                                  (congrArg
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    rootSymbolLayout)
                                                                  (EbnfValue.ofShape
                                                                    sequenceSite.expression_eq_sequence
                                                                    rawSequenceValue)) =
                                                              postfixSourceValue
                                                                { span := atomSpan
                                                                  payload :=
                                                                    .dotConstructor
                                                                      marker name none }
                                                                (.call openParen
                                                                    arguments
                                                                    closeParen :: rest)
                                                            at inputEq
                                                          have expectedRootSymbolLayout :=
                                                            congrArg
                                                              (fun child =>
                                                                GrammarSymbol.nonterminal
                                                                  (.aux child))
                                                              sequenceSiteRoot
                                                          have rootProofEq :
                                                              congrArg
                                                                  (GrammarSymbolValue
                                                                    file tokens)
                                                                  rootSymbolLayout =
                                                                congrArg
                                                                  (GrammarSymbolValue
                                                                    file tokens)
                                                                  expectedRootSymbolLayout :=
                                                            Subsingleton.elim _ _
                                                          have packedEq :
                                                              Eq.mp
                                                                  (congrArg
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    rootSymbolLayout)
                                                                  (EbnfValue.ofShape
                                                                    sequenceSite.expression_eq_sequence
                                                                    rawSequenceValue) =
                                                                Eq.mp
                                                                  (congrArg
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    expectedRootSymbolLayout)
                                                                  (EbnfValue.ofShape
                                                                    sequenceSite.expression_eq_sequence
                                                                    rawSequenceValue) :=
                                                            congrArg
                                                              (fun equality =>
                                                                Eq.mp equality
                                                                  (EbnfValue.ofShape
                                                                    sequenceSite.expression_eq_sequence
                                                                    rawSequenceValue))
                                                              rootProofEq
                                                          have alignedInputEq :
                                                              EbnfValue.atShape
                                                                  (GrammarSite.root_expression
                                                                    .postfix)
                                                                  (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      expectedRootSymbolLayout)
                                                                    (EbnfValue.ofShape
                                                                      sequenceSite.expression_eq_sequence
                                                                      rawSequenceValue)) =
                                                                postfixSourceValue
                                                                  { span := atomSpan
                                                                    payload :=
                                                                      .dotConstructor
                                                                        marker name none }
                                                                  (.call openParen
                                                                      arguments
                                                                      closeParen :: rest) := by
                                                            have alignedLeftEq := congrArg
                                                              (EbnfValue.atShape
                                                                (GrammarSite.root_expression
                                                                  .postfix))
                                                              packedEq
                                                            exact alignedLeftEq.symm.trans
                                                              inputEq
                                                          have rootLayout :
                                                              EbnfExpr.sequence
                                                                  (sequenceSite.children.map
                                                                    GrammarSite.expression) =
                                                                m2cV1.rhs .postfix := by
                                                            change EbnfExpr.sequence
                                                                (sequenceSite.children.map
                                                                  GrammarSite.expression) =
                                                              EbnfExpr.sequence
                                                                postfixSourceChildren
                                                            exact congrArg
                                                              EbnfExpr.sequence
                                                              childrenExpressions
                                                          have normalizedInputEq :
                                                              EbnfValue.transport rootLayout
                                                                  rawSequenceValue =
                                                                postfixSourceValue
                                                                  { span := atomSpan
                                                                    payload :=
                                                                      .dotConstructor
                                                                        marker name none }
                                                                  (.call openParen
                                                                      arguments
                                                                      closeParen :: rest) := by
                                                            rw [← postfixRoot_sequenceTransport_eq
                                                              sequenceSite sequenceSiteRoot
                                                              rootLayout rawSequenceValue]
                                                            exact alignedInputEq
                                                          have rootLayoutEq : rootLayout =
                                                              congrArg EbnfExpr.sequence
                                                                childrenExpressions :=
                                                            Subsingleton.elim _ _
                                                          rw [rootLayoutEq]
                                                            at normalizedInputEq
                                                          have viewEq := congrArg
                                                            (EbnfValue.sequence2View
                                                              (.atom
                                                                (.nonterminal .atom))
                                                              (.star (.atom
                                                                (.nonterminal
                                                                  .postfixPart))))
                                                            normalizedInputEq
                                                          have pairViewEq :=
                                                            sequencePairView_ofAuxiliaries
                                                              childrenEq
                                                              childExpressions.1
                                                              childExpressions.2
                                                              (congrArg
                                                                GrammarSymbol.nonterminal
                                                                starFinishedLhs)
                                                              sequenceTargetLayout
                                                              childrenExpressions
                                                              (Eq.mp
                                                                (congrArg
                                                                  (GrammarSymbolValue
                                                                    file tokens)
                                                                  atomSymbolLayout)
                                                                atomPacked)
                                                              starValue
                                                          have outputViewEq :=
                                                            pairViewEq.symm.trans
                                                              viewEq
                                                          have actualPairEq :=
                                                            outputViewEq.trans
                                                              (postfixSourceValue_sequence2View
                                                                { span := atomSpan
                                                                  payload :=
                                                                    .dotConstructor
                                                                      marker name none }
                                                                (.call openParen
                                                                    arguments
                                                                    closeParen :: rest))
                                                          have actualAtomEq := congrArg
                                                            Prod.fst actualPairEq
                                                          have atomTransportEq :
                                                              EbnfValue.transport
                                                                  childExpressions.1
                                                                  (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      atomSymbolLayout)
                                                                    atomPacked) =
                                                                AtomSite.packAtAtom atomSite
                                                                  (.nonterminal .atom)
                                                                  atomSiteAtom
                                                                  (PrefixValues.fullValue
                                                                    atomItem
                                                                    atomItemComplete
                                                                    (PrefixValues.completeValue
                                                                      sourceWaiting
                                                                      { raw := {
                                                                          production :=
                                                                            .root .atom
                                                                          dot := sourceDot
                                                                          origin :=
                                                                            sourceOrigin
                                                                          current :=
                                                                            sourceCurrent }
                                                                        context :=
                                                                          sourceContext }
                                                                      atomItem
                                                                      sourceWitness.next
                                                                      sourceWitness.advance
                                                                      (PrefixValues.zeroValue
                                                                        sourceWaiting
                                                                        sourceWaitingZero)
                                                                      sourceValue)) := by
                                                            cases atomSiteEq
                                                            have atomSymbolRefl :
                                                                atomSymbolLayout = rfl :=
                                                              Subsingleton.elim _ _
                                                            rw [atomSymbolRefl]
                                                            unfold AtomSite.packAtAtom
                                                              EbnfValue.atShape
                                                            rw [EbnfValue.transport_trans]
                                                            dsimp only [atomPacked]
                                                            congr 1
                                                          have atomOutputExternal :
                                                              AtomSite.packAtAtom atomSite
                                                                  (.nonterminal .atom)
                                                                  atomSiteAtom
                                                                  (PrefixValues.fullValue
                                                                    atomItem
                                                                    atomItemComplete
                                                                    (PrefixValues.completeValue
                                                                      sourceWaiting
                                                                      { raw := {
                                                                          production :=
                                                                            .root .atom
                                                                          dot := sourceDot
                                                                          origin :=
                                                                            sourceOrigin
                                                                          current :=
                                                                            sourceCurrent }
                                                                        context :=
                                                                          sourceContext }
                                                                      atomItem
                                                                      sourceWitness.next
                                                                      sourceWitness.advance
                                                                      (PrefixValues.zeroValue
                                                                        sourceWaiting
                                                                        sourceWaitingZero)
                                                                      sourceValue)) =
                                                                EbnfValue.ruleAtom .atom
                                                                  { span := atomSpan
                                                                    payload :=
                                                                      .dotConstructor
                                                                        marker name none } :=
                                                            atomTransportEq.symm.trans
                                                              actualAtomEq
                                                          have sourceWaitingProduction :
                                                              sourceWaiting.raw.production =
                                                                .atom atomSite :=
                                                            sourceWitness.advance.1.symm
                                                          rcases sourceWaiting with
                                                            ⟨⟨sourceWaitingProductionId,
                                                              sourceWaitingDotFin,
                                                              sourceWaitingOrigin,
                                                              sourceWaitingCurrent⟩,
                                                              sourceWaitingContext⟩
                                                          simp only at sourceWaitingProduction sourceWaitingDot sourceWaitingZero atomOutputExternal ⊢
                                                          subst sourceWaitingProductionId
                                                          rcases sourceWaitingDotFin with
                                                            ⟨sourceWaitingDotValue,
                                                              sourceWaitingDotBound⟩
                                                          simp only at sourceWaitingDot
                                                          subst sourceWaitingDotValue
                                                          let sourceBefore :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.atom atomSite,
                                                              ⟨0,
                                                                sourceWaitingDotBound⟩,
                                                              sourceWaitingOrigin,
                                                              sourceWaitingCurrent⟩,
                                                              sourceWaitingContext⟩
                                                          let sourceFinishedItem :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.root .atom, sourceDot,
                                                              sourceOrigin,
                                                              sourceCurrent⟩,
                                                              sourceContext⟩
                                                          have sourceEmpty :
                                                              PrefixValues.zeroValue
                                                                  (file := file)
                                                                  sourceBefore
                                                                  sourceWaitingZero =
                                                                (show Unit from ()) := by
                                                            dsimp only [sourceBefore]
                                                            unfold PrefixValues.zeroValue
                                                              GrammarSymbolValues.transport
                                                            simp
                                                          have sourceSymbolLayout :
                                                              GrammarSymbol.nonterminal
                                                                  (ProductionId.root .atom).lhs =
                                                                atomSite.symbol := by
                                                            rw [atomSite.symbol_eq,
                                                              atomSiteAtom]
                                                            rfl
                                                          have atomTupleEq :
                                                              GrammarSymbolValues.view
                                                                  (ProductionId.rhs_atom
                                                                    atomSite)
                                                                  (GrammarSymbolValues.transport
                                                                    ((prefix_complete_layout
                                                                      sourceBefore.raw
                                                                      sourceFinishedItem.raw
                                                                      atomItem.raw
                                                                      sourceWitness.next
                                                                      sourceWitness.advance).trans
                                                                      (prefix_full_layout
                                                                        atomItem.raw
                                                                        atomItemComplete))
                                                                    (GrammarSymbolValues.append
                                                                      (left := []) ()
                                                                      (sourceValue, ()))) =
                                                                (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      sourceSymbolLayout)
                                                                    sourceValue,
                                                                  ()) := by
                                                            exact
                                                              GrammarSymbolValues.transport_append_single_to
                                                                _ _ sourceSymbolLayout
                                                                sourceValue
                                                          dsimp only [sourceBefore,
                                                            sourceFinishedItem] at sourceEmpty atomTupleEq
                                                          rw [PrefixValues.fullValue_completeValue_eq]
                                                            at atomOutputExternal
                                                          rw [sourceEmpty] at atomOutputExternal
                                                          rw [AtomSite.pack_rule_eq]
                                                            at atomOutputExternal
                                                          generalize atomValuesEq :
                                                              GrammarSymbolValues.view
                                                                (ProductionId.rhs_atom
                                                                  atomSite) _ = atomValues
                                                            at atomOutputExternal
                                                          have atomValuesCanonical :
                                                              atomValues =
                                                                (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      sourceSymbolLayout)
                                                                    sourceValue,
                                                                  ()) :=
                                                            atomValuesEq.symm.trans
                                                              atomTupleEq
                                                          rw [atomValuesCanonical]
                                                            at atomOutputExternal
                                                          let combinedSourceSymbolLayout :=
                                                            (sourceSymbolLayout.trans
                                                              atomSite.symbol_eq).trans
                                                              (congrArg
                                                                EbnfAtom.grammarSymbol
                                                                atomSiteAtom)
                                                          have atomEncodedValueEq :
                                                              Eq.mp
                                                                  (congrArg
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    (congrArg
                                                                      EbnfAtom.grammarSymbol
                                                                      atomSiteAtom))
                                                                  (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      atomSite.symbol_eq)
                                                                    (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        sourceSymbolLayout)
                                                                      sourceValue)) =
                                                                sourceValue := by
                                                            calc
                                                              _ = Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      (congrArg
                                                                        EbnfAtom.grammarSymbol
                                                                        atomSiteAtom))
                                                                    (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        (sourceSymbolLayout.trans
                                                                          atomSite.symbol_eq))
                                                                      sourceValue) :=
                                                                congrArg _
                                                                  (eqMp_congrArg_trans
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    sourceSymbolLayout
                                                                    atomSite.symbol_eq
                                                                    sourceValue)
                                                              _ = Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      combinedSourceSymbolLayout)
                                                                    sourceValue :=
                                                                eqMp_congrArg_trans
                                                                  (GrammarSymbolValue
                                                                    file tokens)
                                                                  (sourceSymbolLayout.trans
                                                                    atomSite.symbol_eq)
                                                                  (congrArg
                                                                    EbnfAtom.grammarSymbol
                                                                    atomSiteAtom)
                                                                  sourceValue
                                                              _ = sourceValue := by
                                                                have combinedRefl :
                                                                    combinedSourceSymbolLayout =
                                                                      rfl :=
                                                                  Subsingleton.elim _ _
                                                                rw [combinedRefl]
                                                                rfl
                                                          have sourceValueExternal :
                                                              sourceValue =
                                                                { span := atomSpan
                                                                  payload :=
                                                                    .dotConstructor
                                                                      marker name none } :=
                                                            atomEncodedValueEq.symm.trans
                                                              (EbnfValue.ruleAtom_injective
                                                                .atom atomOutputExternal)
                                                          subst sourceValue
                                                          generalize sourceInputEq :
                                                              RootAction.unpack .atom
                                                                (PrefixValues.fullValue
                                                                  { raw := {
                                                                      production :=
                                                                        .root .atom
                                                                      dot := sourceDot
                                                                      origin :=
                                                                        sourceOrigin
                                                                      current :=
                                                                        sourceCurrent }
                                                                    context :=
                                                                      sourceContext }
                                                                  sourceComplete
                                                                  sourceValues) =
                                                                sourceInput
                                                            at sourceReduction
                                                          cases sourceCoherent with
                                                          | zero _ _ sourceZero =>
                                                              have sourceDotOne : sourceDot.val = 1 := by
                                                                change sourceDot.val =
                                                                  (ProductionId.root .atom).rhs.length
                                                                  at sourceComplete
                                                                simpa [ProductionId.rhs] using
                                                                  sourceComplete
                                                              change sourceDot.val = 0 at sourceZero
                                                              omega
                                                          | scan sourceBefore _ _ _ sourceScan _ _ =>
                                                              have beforeProduction :
                                                                  sourceBefore.raw.production =
                                                                    .root .atom :=
                                                                sourceScan.advance.1.symm
                                                              have beforeDot :
                                                                  sourceBefore.raw.dot.val = 0 := by
                                                                have advanced :=
                                                                  sourceScan.advance.2.1
                                                                have sourceDotOne : sourceDot.val = 1 := by
                                                                  change sourceDot.val =
                                                                    (ProductionId.root .atom).rhs.length
                                                                    at sourceComplete
                                                                  simpa [ProductionId.rhs] using
                                                                    sourceComplete
                                                                change sourceDot.val =
                                                                  sourceBefore.raw.dot.val + 1 at advanced
                                                                omega
                                                              have impossible :
                                                                  some (GrammarSymbol.terminal
                                                                      sourceScan.terminal) =
                                                                    some (GrammarSymbol.nonterminal
                                                                      (NonterminalSymbol.aux
                                                                        (GrammarSite.root
                                                                          .atom))) := by
                                                                calc
                                                                  _ = sourceBefore.raw.production.rhs[
                                                                      sourceBefore.raw.dot.val]? :=
                                                                    sourceScan.next.2.symm
                                                                  _ = (ProductionId.root .atom).rhs[0]? := by
                                                                    let index :=
                                                                      sourceBefore.raw.dot.val
                                                                    have indexZero : index = 0 :=
                                                                      beforeDot
                                                                    change sourceBefore.raw.production.rhs[index]? =
                                                                      (ProductionId.root .atom).rhs[0]?
                                                                    calc
                                                                      _ = (ProductionId.root .atom).rhs[index]? :=
                                                                        congrArg
                                                                          (fun production : ProductionId =>
                                                                            production.rhs[index]?)
                                                                          beforeProduction
                                                                      _ = _ := by
                                                                        rw [indexZero]
                                                                  _ = _ := by
                                                                    simp [ProductionId.rhs_root]
                                                              exact GrammarSymbol.noConfusion
                                                                (Option.some.inj impossible)
                                                          | complete sourceRootWaiting
                                                              sourceChoiceFinished
                                                              sourceRootAfter sourceRootShared
                                                              sourceRootPriorValues
                                                              sourceChoiceValue
                                                              sourceRootWitness
                                                              sourceRootEdge sourceRootPrefix
                                                              sourceChoiceReduction =>
                                                              have sourceRootWaitingProduction :
                                                                  sourceRootWaiting.raw.production =
                                                                    .root .atom :=
                                                                sourceRootWitness.advance.1.symm
                                                              have sourceRootWaitingDot :
                                                                  sourceRootWaiting.raw.dot.val = 0 := by
                                                                have advanced :=
                                                                  sourceRootWitness.advance.2.1
                                                                have sourceDotOne : sourceDot.val = 1 := by
                                                                  change sourceDot.val =
                                                                    (ProductionId.root .atom).rhs.length
                                                                    at sourceComplete
                                                                  simpa [ProductionId.rhs] using
                                                                    sourceComplete
                                                                change sourceDot.val =
                                                                  sourceRootWaiting.raw.dot.val + 1
                                                                  at advanced
                                                                omega
                                                              have sourceChoiceLhs :
                                                                  sourceChoiceFinished.raw.production.lhs =
                                                                    NonterminalSymbol.aux
                                                                      (GrammarSite.root .atom) := by
                                                                have selected :
                                                                    some (GrammarSymbol.nonterminal
                                                                      sourceChoiceFinished.raw.production.lhs) =
                                                                      some (GrammarSymbol.nonterminal
                                                                        (NonterminalSymbol.aux
                                                                          (GrammarSite.root .atom))) := by
                                                                  calc
                                                                    _ = sourceRootWaiting.raw.production.rhs[
                                                                        sourceRootWaiting.raw.dot.val]? :=
                                                                      sourceRootWitness.next.2.symm
                                                                    _ = (ProductionId.root .atom).rhs[0]? := by
                                                                      let index :=
                                                                        sourceRootWaiting.raw.dot.val
                                                                      have indexZero : index = 0 :=
                                                                        sourceRootWaitingDot
                                                                      change sourceRootWaiting.raw.production.rhs[index]? =
                                                                        (ProductionId.root .atom).rhs[0]?
                                                                      calc
                                                                        _ = (ProductionId.root .atom).rhs[index]? :=
                                                                          congrArg
                                                                            (fun production : ProductionId =>
                                                                              production.rhs[index]?)
                                                                            sourceRootWaitingProduction
                                                                        _ = _ := by
                                                                          rw [indexZero]
                                                                    _ = _ := by
                                                                      simp [ProductionId.rhs_root]
                                                                exact GrammarSymbol.nonterminal.inj
                                                                  (Option.some.inj selected)
                                                              have atomRootKind :
                                                                  (GrammarSite.root .atom).expression.kind =
                                                                    .choice := by
                                                                rw [GrammarSite.root_expression]
                                                                rfl
                                                              obtain ⟨sourceChoiceSite,
                                                                  sourceChoiceBranch,
                                                                  sourceChoiceProduction,
                                                                  sourceChoiceSiteRoot⟩ :=
                                                                auxiliaryChoiceProduction
                                                                  sourceChoiceFinished.raw.production
                                                                  (GrammarSite.root .atom)
                                                                  sourceChoiceLhs atomRootKind
                                                              rcases sourceChoiceFinished with
                                                                ⟨⟨sourceChoiceProductionId,
                                                                  sourceChoiceDot,
                                                                  sourceChoiceOrigin,
                                                                  sourceChoiceCurrent⟩,
                                                                  sourceChoiceContext⟩
                                                              simp only at sourceChoiceProduction sourceChoiceLhs sourceInputEq ⊢
                                                              subst sourceChoiceProductionId
                                                              cases sourceChoiceReduction with
                                                              | reduce sourceChoiceItem
                                                                  sourceChoiceValues
                                                                  sourceChoiceOutput
                                                                  sourceChoiceReached
                                                                  sourceChoiceComplete
                                                                  sourceChoiceCoherent
                                                                  sourceChoiceAction =>
                                                                  have sourceChoicePackedEq :=
                                                                    actionReduces_eleven_shapes_exact.mp
                                                                      sourceChoiceAction
                                                                  change sourceChoiceValue =
                                                                    ChoiceSite.pack
                                                                      sourceChoiceSite
                                                                      sourceChoiceBranch
                                                                      (PrefixValues.fullValue
                                                                        { raw := {
                                                                            production :=
                                                                              .choice
                                                                                sourceChoiceSite
                                                                                sourceChoiceBranch
                                                                            dot := sourceChoiceDot
                                                                            origin := sourceChoiceOrigin
                                                                            current := sourceChoiceCurrent }
                                                                          context := sourceChoiceContext }
                                                                        sourceChoiceComplete
                                                                        sourceChoiceValues)
                                                                    at sourceChoicePackedEq
                                                                  cases sourceRootPrefix with
                                                                  | zero sourceRootWaiting
                                                                      sourceRootWaitingReached
                                                                      sourceRootWaitingZero =>
                                                                      have sourceRootPriorLayout :
                                                                          sourceRootWaiting.raw.production.rhs.take
                                                                              sourceRootWaiting.raw.dot.val =
                                                                            [] := by
                                                                        rw [sourceRootWaitingZero]
                                                                        rfl
                                                                      rw [PrefixValues.fullValue_completeValue_eq]
                                                                        at sourceInputEq
                                                                      have sourceRootSymbolLayout :
                                                                          GrammarSymbol.nonterminal
                                                                              (ProductionId.choice
                                                                                sourceChoiceSite
                                                                                sourceChoiceBranch).lhs =
                                                                            GrammarSymbol.nonterminal
                                                                              (.aux
                                                                                (GrammarSite.root
                                                                                  .atom)) :=
                                                                        congrArg
                                                                          GrammarSymbol.nonterminal
                                                                          sourceChoiceLhs
                                                                      have sourceRootTupleEq :
                                                                          GrammarSymbolValues.view
                                                                              (ProductionId.rhs_root
                                                                                .atom)
                                                                              (GrammarSymbolValues.transport
                                                                                ((prefix_complete_layout
                                                                                  sourceRootWaiting.raw
                                                                                  { production :=
                                                                                      .choice
                                                                                        sourceChoiceSite
                                                                                        sourceChoiceBranch
                                                                                    dot := sourceChoiceDot
                                                                                    origin := sourceChoiceOrigin
                                                                                    current := sourceChoiceCurrent }
                                                                                  { production :=
                                                                                      .root .atom
                                                                                    dot := sourceDot
                                                                                    origin := sourceOrigin
                                                                                    current := sourceCurrent }
                                                                                  sourceRootWitness.next
                                                                                  sourceRootWitness.advance).trans
                                                                                  (prefix_full_layout
                                                                                    { production :=
                                                                                        .root .atom
                                                                                      dot := sourceDot
                                                                                      origin := sourceOrigin
                                                                                      current := sourceCurrent }
                                                                                    sourceComplete))
                                                                                (GrammarSymbolValues.append
                                                                                  (PrefixValues.zeroValue
                                                                                    sourceRootWaiting
                                                                                    sourceRootWaitingZero)
                                                                                  (sourceChoiceValue,
                                                                                    ()))) =
                                                                            (Eq.mp
                                                                                (congrArg
                                                                                  (GrammarSymbolValue
                                                                                    file tokens)
                                                                                  sourceRootSymbolLayout)
                                                                                sourceChoiceValue,
                                                                              ()) := by
                                                                        exact
                                                                          transport_append_empty_single_to
                                                                            sourceRootPriorLayout _ _
                                                                            sourceRootSymbolLayout
                                                                            (PrefixValues.zeroValue
                                                                              sourceRootWaiting
                                                                              sourceRootWaitingZero)
                                                                            sourceChoiceValue
                                                                      rw [RootAction.unpack_eq]
                                                                        at sourceInputEq
                                                                      generalize sourceRootValuesEq :
                                                                          GrammarSymbolValues.view
                                                                            (ProductionId.rhs_root
                                                                              .atom) _ =
                                                                            sourceRootValues
                                                                        at sourceInputEq
                                                                      have sourceRootValuesCanonical :=
                                                                        sourceRootValuesEq.symm.trans
                                                                          sourceRootTupleEq
                                                                      rw [sourceRootValuesCanonical]
                                                                        at sourceInputEq
                                                                      rw [sourceChoicePackedEq]
                                                                        at sourceInputEq
                                                                      have sourceRootCastLayoutEq :
                                                                          congrArg
                                                                              (GrammarSymbolValue file tokens)
                                                                              sourceRootSymbolLayout =
                                                                            congrArg
                                                                              (GrammarSymbolValue file tokens)
                                                                              (congrArg
                                                                                (fun child =>
                                                                                  GrammarSymbol.nonterminal
                                                                                    (.aux child))
                                                                                sourceChoiceSiteRoot) :=
                                                                        Subsingleton.elim _ _
                                                                      have sourceChoiceLayout :
                                                                          EbnfExpr.choice
                                                                              sourceChoiceSite.branchExpressions.toList =
                                                                            m2cV1.rhs .atom :=
                                                                        sourceChoiceSite.expression_eq_choice.symm.trans
                                                                          ((congrArg GrammarSite.expression
                                                                            sourceChoiceSiteRoot).trans
                                                                            (GrammarSite.root_expression .atom))
                                                                      let sourceChoiceChildValue :=
                                                                        EbnfValue.transport
                                                                          ((sourceChoiceSite.branch_expression
                                                                            sourceChoiceBranch).trans
                                                                            (sourceChoiceSite.branch_get_toList
                                                                              sourceChoiceBranch).symm)
                                                                          (GrammarSymbolValues.view
                                                                            (ProductionId.rhs_choice
                                                                              sourceChoiceSite
                                                                              sourceChoiceBranch)
                                                                            (PrefixValues.fullValue
                                                                              { raw := {
                                                                                  production :=
                                                                                    .choice sourceChoiceSite
                                                                                      sourceChoiceBranch
                                                                                  dot := sourceChoiceDot
                                                                                  origin := sourceChoiceOrigin
                                                                                  current := sourceChoiceCurrent }
                                                                                context := sourceChoiceContext }
                                                                              sourceChoiceComplete
                                                                              sourceChoiceValues)).1
                                                                      have sourcePackedRightEq :
                                                                          EbnfValue.atShape
                                                                              (GrammarSite.root_expression .atom)
                                                                              (Eq.mp
                                                                                (congrArg
                                                                                  (GrammarSymbolValue file tokens)
                                                                                  sourceRootSymbolLayout)
                                                                                (ChoiceSite.pack
                                                                                  sourceChoiceSite
                                                                                  sourceChoiceBranch
                                                                                  (PrefixValues.fullValue
                                                                                    { raw := {
                                                                                        production :=
                                                                                          .choice
                                                                                            sourceChoiceSite
                                                                                            sourceChoiceBranch
                                                                                        dot := sourceChoiceDot
                                                                                        origin := sourceChoiceOrigin
                                                                                        current := sourceChoiceCurrent }
                                                                                      context :=
                                                                                        sourceChoiceContext }
                                                                                    sourceChoiceComplete
                                                                                    sourceChoiceValues))) =
                                                                            EbnfValue.transport
                                                                              sourceChoiceLayout
                                                                              (EbnfValue.choice
                                                                                sourceChoiceSite.branchExpressions.toList
                                                                                ⟨sourceChoiceSite.branchListIndex
                                                                                    sourceChoiceBranch,
                                                                                  sourceChoiceChildValue⟩) := by
                                                                        rw [sourceRootCastLayoutEq]
                                                                        unfold ChoiceSite.pack
                                                                        exact rootChoice_transport_eq .atom
                                                                          sourceChoiceSite sourceChoiceSiteRoot
                                                                          sourceChoiceLayout _
                                                                      have sourceInputNormalizedEq :
                                                                          EbnfValue.transport
                                                                              sourceChoiceLayout
                                                                              (EbnfValue.choice
                                                                                sourceChoiceSite.branchExpressions.toList
                                                                                ⟨sourceChoiceSite.branchListIndex
                                                                                    sourceChoiceBranch,
                                                                                  sourceChoiceChildValue⟩) =
                                                                            sourceInput :=
                                                                        sourcePackedRightEq.symm.trans
                                                                          sourceInputEq
                                                                      have sourcePackedBranchTag :
                                                                          (EbnfValue.choiceView
                                                                              (EbnfExpr.children
                                                                                (m2cV1.rhs .atom))
                                                                              (EbnfValue.transport
                                                                                sourceChoiceLayout
                                                                                (EbnfValue.choice
                                                                                  sourceChoiceSite.branchExpressions.toList
                                                                                  ⟨sourceChoiceSite.branchListIndex
                                                                                      sourceChoiceBranch,
                                                                                    sourceChoiceChildValue⟩))).1.val =
                                                                            sourceChoiceBranch.val :=
                                                                        choiceView_transport_branch_val
                                                                          sourceChoiceLayout
                                                                          (sourceChoiceSite.branchListIndex
                                                                            sourceChoiceBranch)
                                                                          sourceChoiceChildValue
                                                                      have sourceBranchTagEq :
                                                                          sourceChoiceBranch.val =
                                                                            (EbnfValue.choiceView
                                                                              (EbnfExpr.children
                                                                                (m2cV1.rhs .atom))
                                                                              sourceInput).1.val :=
                                                                        sourcePackedBranchTag.symm.trans
                                                                          (congrArg
                                                                            (fun value =>
                                                                              (EbnfValue.choiceView
                                                                                (EbnfExpr.children
                                                                                  (m2cV1.rhs .atom))
                                                                                value).1.val)
                                                                            sourceInputNormalizedEq)
                                                                      cases sourceChoiceCoherent with
                                                                      | zero _ _ sourceChoiceZero =>
                                                                          have sourceChoiceDotOne :
                                                                              sourceChoiceDot.val = 1 := by
                                                                            change sourceChoiceDot.val =
                                                                              (ProductionId.choice
                                                                                sourceChoiceSite
                                                                                sourceChoiceBranch).rhs.length
                                                                              at sourceChoiceComplete
                                                                            simpa [ProductionId.rhs_choice] using
                                                                              sourceChoiceComplete
                                                                          change sourceChoiceDot.val = 0
                                                                            at sourceChoiceZero
                                                                          omega
                                                                      | scan sourceChoiceBefore _ _ _
                                                                          sourceChoiceScan _ _ =>
                                                                          have sourceChoiceBeforeProduction :
                                                                              sourceChoiceBefore.raw.production =
                                                                                .choice sourceChoiceSite
                                                                                  sourceChoiceBranch :=
                                                                            sourceChoiceScan.advance.1.symm
                                                                          have sourceChoiceBeforeDot :
                                                                              sourceChoiceBefore.raw.dot.val = 0 := by
                                                                            have advanced :=
                                                                              sourceChoiceScan.advance.2.1
                                                                            have sourceChoiceDotOne :
                                                                                sourceChoiceDot.val = 1 := by
                                                                              change sourceChoiceDot.val =
                                                                                (ProductionId.choice
                                                                                  sourceChoiceSite
                                                                                  sourceChoiceBranch).rhs.length
                                                                                at sourceChoiceComplete
                                                                              simpa [ProductionId.rhs_choice] using
                                                                                sourceChoiceComplete
                                                                            change sourceChoiceDot.val =
                                                                              sourceChoiceBefore.raw.dot.val + 1
                                                                              at advanced
                                                                            omega
                                                                          have impossible :
                                                                              some (GrammarSymbol.terminal
                                                                                sourceChoiceScan.terminal) =
                                                                                some (GrammarSymbol.nonterminal
                                                                                  (.aux
                                                                                    (sourceChoiceSite.branch
                                                                                      sourceChoiceBranch))) := by
                                                                            let index :=
                                                                              sourceChoiceBefore.raw.dot.val
                                                                            have indexZero : index = 0 :=
                                                                              sourceChoiceBeforeDot
                                                                            calc
                                                                              _ = sourceChoiceBefore.raw.production.rhs[index]? :=
                                                                                sourceChoiceScan.next.2.symm
                                                                              _ = (ProductionId.choice
                                                                                  sourceChoiceSite
                                                                                  sourceChoiceBranch).rhs[index]? :=
                                                                                congrArg
                                                                                  (fun production : ProductionId =>
                                                                                    production.rhs[index]?)
                                                                                  sourceChoiceBeforeProduction
                                                                              _ = (ProductionId.choice
                                                                                  sourceChoiceSite
                                                                                  sourceChoiceBranch).rhs[0]? := by
                                                                                rw [indexZero]
                                                                              _ = _ := by
                                                                                simp [ProductionId.rhs_choice]
                                                                          exact GrammarSymbol.noConfusion
                                                                            (Option.some.inj impossible)
                                                                      | complete sourceChoiceWaiting
                                                                          sourceBranchFinished sourceChoiceAfter
                                                                          sourceChoiceShared sourceChoicePriorValues
                                                                          sourceBranchValue sourceBranchWitness
                                                                          sourceBranchEdge sourceChoicePrefix
                                                                          sourceGrandchild =>
                                                                          have sourceChoiceWaitingProduction :
                                                                              sourceChoiceWaiting.raw.production =
                                                                                .choice sourceChoiceSite
                                                                                  sourceChoiceBranch :=
                                                                            sourceBranchWitness.advance.1.symm
                                                                          have sourceChoiceWaitingDot :
                                                                              sourceChoiceWaiting.raw.dot.val = 0 := by
                                                                            have advanced :=
                                                                              sourceBranchWitness.advance.2.1
                                                                            have sourceChoiceDotOne :
                                                                                sourceChoiceDot.val = 1 := by
                                                                              change sourceChoiceDot.val =
                                                                                (ProductionId.choice
                                                                                  sourceChoiceSite
                                                                                  sourceChoiceBranch).rhs.length
                                                                                at sourceChoiceComplete
                                                                              simpa [ProductionId.rhs_choice] using
                                                                                sourceChoiceComplete
                                                                            change sourceChoiceDot.val =
                                                                              sourceChoiceWaiting.raw.dot.val + 1
                                                                              at advanced
                                                                            omega
                                                                          have sourceBranchLhs :
                                                                              sourceBranchFinished.raw.production.lhs =
                                                                                .aux (sourceChoiceSite.branch
                                                                                  sourceChoiceBranch) := by
                                                                            have selected :
                                                                                some (GrammarSymbol.nonterminal
                                                                                  sourceBranchFinished.raw.production.lhs) =
                                                                                  some (GrammarSymbol.nonterminal
                                                                                    (.aux
                                                                                      (sourceChoiceSite.branch
                                                                                        sourceChoiceBranch))) := by
                                                                              let index :=
                                                                                sourceChoiceWaiting.raw.dot.val
                                                                              have indexZero : index = 0 :=
                                                                                sourceChoiceWaitingDot
                                                                              calc
                                                                                _ = sourceChoiceWaiting.raw.production.rhs[index]? :=
                                                                                  sourceBranchWitness.next.2.symm
                                                                                _ = (ProductionId.choice
                                                                                    sourceChoiceSite
                                                                                    sourceChoiceBranch).rhs[index]? :=
                                                                                  congrArg
                                                                                    (fun production : ProductionId =>
                                                                                      production.rhs[index]?)
                                                                                    sourceChoiceWaitingProduction
                                                                                _ = (ProductionId.choice
                                                                                    sourceChoiceSite
                                                                                    sourceChoiceBranch).rhs[0]? := by
                                                                                  rw [indexZero]
                                                                                _ = _ := by
                                                                                  simp [ProductionId.rhs_choice]
                                                                            exact GrammarSymbol.nonterminal.inj
                                                                              (Option.some.inj selected)
                                                                          have sourceChoiceWaitingOriginCurrent :
                                                                              sourceChoiceWaiting.raw.origin =
                                                                                sourceChoiceWaiting.raw.current :=
                                                                            contextualReach_zero_origin_eq_current
                                                                              sourceBranchEdge.2.1
                                                                              sourceChoiceWaitingDot
                                                                          have sourceChoicePriorEq :=
                                                                            prefixValues_eq_zeroValue
                                                                              sourceChoiceWaiting
                                                                              sourceChoicePriorValues
                                                                              sourceChoiceWaitingDot
                                                                          subst sourceChoicePriorValues
                                                                          have sourceChoicePriorLayout :
                                                                              sourceChoiceWaiting.raw.production.rhs.take
                                                                                  sourceChoiceWaiting.raw.dot.val =
                                                                                [] := by
                                                                            rw [sourceChoiceWaitingDot]
                                                                            rfl
                                                                          have sourceChoiceSymbolLayout :
                                                                              GrammarSymbol.nonterminal
                                                                                  sourceBranchFinished.raw.production.lhs =
                                                                                GrammarSymbol.nonterminal
                                                                                  (.aux
                                                                                    (sourceChoiceSite.branch
                                                                                      sourceChoiceBranch)) :=
                                                                            congrArg GrammarSymbol.nonterminal
                                                                              sourceBranchLhs
                                                                          have sourceChoiceViewEq :
                                                                              GrammarSymbolValues.view
                                                                                  (ProductionId.rhs_choice
                                                                                    sourceChoiceSite
                                                                                    sourceChoiceBranch)
                                                                                  (PrefixValues.fullValue
                                                                                    { raw := {
                                                                                        production :=
                                                                                          .choice sourceChoiceSite
                                                                                            sourceChoiceBranch
                                                                                        dot := sourceChoiceDot
                                                                                        origin := sourceChoiceOrigin
                                                                                        current := sourceChoiceCurrent }
                                                                                      context := sourceChoiceContext }
                                                                                    sourceChoiceComplete
                                                                                    (PrefixValues.completeValue
                                                                                      sourceChoiceWaiting
                                                                                      sourceBranchFinished
                                                                                      { raw := {
                                                                                          production :=
                                                                                            .choice sourceChoiceSite
                                                                                              sourceChoiceBranch
                                                                                          dot := sourceChoiceDot
                                                                                          origin := sourceChoiceOrigin
                                                                                          current := sourceChoiceCurrent }
                                                                                        context := sourceChoiceContext }
                                                                                      sourceBranchWitness.next
                                                                                      sourceBranchWitness.advance
                                                                                      (PrefixValues.zeroValue
                                                                                        sourceChoiceWaiting
                                                                                        sourceChoiceWaitingDot)
                                                                                      sourceBranchValue)) =
                                                                                (Eq.mp
                                                                                    (congrArg
                                                                                      (GrammarSymbolValue file tokens)
                                                                                      sourceChoiceSymbolLayout)
                                                                                    sourceBranchValue,
                                                                                  ()) := by
                                                                            rw [PrefixValues.fullValue_completeValue_eq]
                                                                            exact
                                                                              transport_append_empty_single_to
                                                                                sourceChoicePriorLayout _ _
                                                                                sourceChoiceSymbolLayout
                                                                                (PrefixValues.zeroValue
                                                                                  sourceChoiceWaiting
                                                                                  sourceChoiceWaitingDot)
                                                                                sourceBranchValue
                                                                          have sourceChoiceViewHeadEq :=
                                                                            congrArg Prod.fst sourceChoiceViewEq
                                                                          have sourceChoiceChildValueHEq :
                                                                              HEq sourceChoiceChildValue
                                                                                sourceBranchValue := by
                                                                            dsimp only [sourceChoiceChildValue]
                                                                            rw [sourceChoiceViewHeadEq]
                                                                            let branchLayout :=
                                                                              (atomRootChoiceSite.branch_expression
                                                                                atomDotChoiceBranch).trans
                                                                                (atomRootChoiceSite.branch_get_toList
                                                                                  atomDotChoiceBranch).symm
                                                                            have outerCast :=
                                                                              cast_heq
                                                                                (congrArg
                                                                                  (EbnfValue file tokens)
                                                                                  ((sourceChoiceSite.branch_expression
                                                                                    sourceChoiceBranch).trans
                                                                                    (sourceChoiceSite.branch_get_toList
                                                                                      sourceChoiceBranch).symm))
                                                                                (Eq.mp
                                                                                  (congrArg
                                                                                    (GrammarSymbolValue file tokens)
                                                                                    sourceChoiceSymbolLayout)
                                                                                  sourceBranchValue)
                                                                            have innerCast :=
                                                                              cast_heq
                                                                                (congrArg
                                                                                  (GrammarSymbolValue file tokens)
                                                                                  sourceChoiceSymbolLayout)
                                                                                sourceBranchValue
                                                                            exact outerCast.trans innerCast
                                                                          have sourceBranchOrigin :
                                                                              sourceBranchFinished.raw.origin =
                                                                                sourceChoiceOrigin := by
                                                                            calc
                                                                              _ = sourceChoiceShared :=
                                                                                sourceBranchWitness.finishedAtShared
                                                                              _ = sourceChoiceWaiting.raw.current :=
                                                                                sourceBranchWitness.waitingAtShared.symm
                                                                              _ = sourceChoiceWaiting.raw.origin :=
                                                                                sourceChoiceWaitingOriginCurrent.symm
                                                                              _ = sourceChoiceOrigin :=
                                                                                sourceBranchWitness.advance.2.2.1.symm
                                                                          cases sourceReduction with
                                                                          | atomDotConstructorWithoutArguments
                                                                              directOrigin directFinish
                                                                              directDot directName directSpelling
                                                                              directParsed directProjects
                                                                              directWitness =>
                                                                              have sourceBranchTwo :
                                                                                  sourceChoiceBranch.val = 2 := by
                                                                                exact sourceBranchTagEq.trans
                                                                                  (atomDotWithoutArgumentsInput_branchTag
                                                                                    directDot directName)
                                                                              have sourceChoiceSiteEq :
                                                                                  sourceChoiceSite = atomRootChoiceSite := by
                                                                                cases sourceChoiceSite
                                                                                simp only [atomRootChoiceSite]
                                                                                  at sourceChoiceSiteRoot ⊢
                                                                                subst_vars
                                                                                rfl
                                                                              subst sourceChoiceSite
                                                                              have sourceChoiceBranchEq :
                                                                                  sourceChoiceBranch =
                                                                                    atomDotChoiceBranch := by
                                                                                apply Fin.ext
                                                                                exact sourceBranchTwo
                                                                              subst sourceChoiceBranch
                                                                              have sourceChoiceBranchesEq :
                                                                                  atomRootChoiceSite.branchExpressions.toList =
                                                                                    EbnfExpr.children
                                                                                      (m2cV1.rhs .atom) :=
                                                                                EbnfExpr.choice.inj
                                                                                  sourceChoiceLayout
                                                                              have sourceChoiceLayoutProofEq :
                                                                                  sourceChoiceLayout =
                                                                                    congrArg EbnfExpr.choice
                                                                                      sourceChoiceBranchesEq :=
                                                                                Subsingleton.elim _ _
                                                                              have sourceChoiceInputEq :=
                                                                                sourceInputNormalizedEq
                                                                              rw [sourceChoiceLayoutProofEq]
                                                                                at sourceChoiceInputEq
                                                                              have sourceChoicePairEq :=
                                                                                choice_transport_pair_heq
                                                                                  sourceChoiceBranchesEq
                                                                                  (atomRootChoiceSite.branchListIndex
                                                                                    atomDotChoiceBranch)
                                                                                  sourceChoiceChildValue
                                                                                  atomDotRootBranch
                                                                                  (atomDotWithoutArgumentsChild
                                                                                    directDot directName)
                                                                                  sourceChoiceInputEq
                                                                              have sourceChoiceChildSemanticHEq :
                                                                                  HEq sourceChoiceChildValue
                                                                                    (atomDotWithoutArgumentsChild
                                                                                      directDot directName) :=
                                                                                sourceChoicePairEq.2
                                                                              rw [atomDotChoiceBranch_site]
                                                                                at sourceBranchLhs
                                                                              obtain ⟨sourceSequenceSite,
                                                                                  sourceBranchProduction,
                                                                                  sourceSequenceSiteEq⟩ :=
                                                                                auxiliarySequenceProduction
                                                                                  sourceBranchFinished.raw.production
                                                                                  atomDotSequenceSite.site
                                                                                  sourceBranchLhs
                                                                                  atomDotSequenceSite.hasKind
                                                                              have sourceSequenceSiteCanonical :
                                                                                  sourceSequenceSite =
                                                                                    atomDotSequenceSite := by
                                                                                cases sourceSequenceSite
                                                                                simp only [atomDotSequenceSite]
                                                                                  at sourceSequenceSiteEq ⊢
                                                                                subst_vars
                                                                                rfl
                                                                              subst sourceSequenceSite
                                                                              rcases sourceBranchFinished with
                                                                                ⟨⟨sourceBranchProductionId,
                                                                                  sourceBranchDot,
                                                                                  sourceBranchOriginBoundary,
                                                                                  sourceBranchCurrent⟩,
                                                                                  sourceBranchContext⟩
                                                                              simp only at sourceBranchProduction
                                                                              simp only at sourceBranchLhs
                                                                              simp only at sourceBranchOrigin
                                                                              subst sourceBranchProductionId
                                                                              cases sourceGrandchild with
                                                                              | reduce sourceSequenceItem
                                                                                  sourceSequenceValues
                                                                                  sourceSequenceOutput
                                                                                  sourceSequenceReached
                                                                                  sourceSequenceComplete
                                                                                  sourceSequenceCoherent
                                                                                  sourceSequenceAction =>
                                                                                  have sourceSequencePackedEq :=
                                                                                    actionReduces_eleven_shapes_exact.mp
                                                                                      sourceSequenceAction
                                                                                  change sourceBranchValue =
                                                                                    SequenceSite.pack
                                                                                      atomDotSequenceSite
                                                                                      (PrefixValues.fullValue
                                                                                        { raw := {
                                                                                            production :=
                                                                                              .seq atomDotSequenceSite
                                                                                            dot := sourceBranchDot
                                                                                            origin :=
                                                                                              sourceBranchOriginBoundary
                                                                                            current :=
                                                                                              sourceBranchCurrent }
                                                                                          context :=
                                                                                            sourceBranchContext }
                                                                                        sourceSequenceComplete
                                                                                        sourceSequenceValues)
                                                                                    at sourceSequencePackedEq
                                                                                  have sourceBranchSemanticHEq :
                                                                                      HEq sourceBranchValue
                                                                                        (atomDotWithoutArgumentsChild
                                                                                          directDot directName) :=
                                                                                    sourceChoiceChildValueHEq.symm.trans
                                                                                      sourceChoiceChildSemanticHEq
                                                                                  have sourceSequenceSemanticHEq :
                                                                                      HEq
                                                                                        (EbnfValue.atShape
                                                                                          atomDotSequenceSite.expression_eq_sequence
                                                                                          sourceBranchValue)
                                                                                        (EbnfValue.transport
                                                                                          atomDotDirectChild_shape
                                                                                          (atomDotWithoutArgumentsChild
                                                                                            directDot directName)) :=
                                                                                    ((cast_heq
                                                                                        (congrArg
                                                                                          (EbnfValue file tokens)
                                                                                          atomDotSequenceSite.expression_eq_sequence)
                                                                                        sourceBranchValue).trans
                                                                                      sourceBranchSemanticHEq).trans
                                                                                      (cast_heq
                                                                                        (congrArg
                                                                                          (EbnfValue file tokens)
                                                                                          atomDotDirectChild_shape)
                                                                                        (atomDotWithoutArgumentsChild
                                                                                          directDot directName)).symm
                                                                                  have sourceSequenceSemanticEq :=
                                                                                    eq_of_heq sourceSequenceSemanticHEq
                                                                                  rw [sourceSequencePackedEq,
                                                                                    SequenceSite.pack_eq]
                                                                                    at sourceSequenceSemanticEq
                                                                                  rw [atomDotWithoutArgumentsChild_shape_eq]
                                                                                    at sourceSequenceSemanticEq
                                                                                  have sourceSequenceValuesEq :=
                                                                                    EbnfValue.sequence_injective
                                                                                      (atomDotSequenceSite.children.map
                                                                                        GrammarSite.expression)
                                                                                      sourceSequenceSemanticEq
                                                                                  have sourceOptionalSemanticEq :=
                                                                                    congrArg atomDotOptionalValue
                                                                                      sourceSequenceValuesEq
                                                                                  rw [atomDotOptionalValue_withoutArguments]
                                                                                    at sourceOptionalSemanticEq
                                                                                  cases sourceSequenceCoherent with
                                                                                  | zero _ _ sourceSequenceZero =>
                                                                                      have sourceSequenceDotThree :
                                                                                          sourceBranchDot.val = 3 := by
                                                                                        change sourceBranchDot.val =
                                                                                          (ProductionId.seq
                                                                                            atomDotSequenceSite).rhs.length
                                                                                          at sourceSequenceComplete
                                                                                        simpa [ProductionId.rhs_seq,
                                                                                          atomDotSequenceSite_children]
                                                                                          using sourceSequenceComplete
                                                                                      change sourceBranchDot.val = 0
                                                                                        at sourceSequenceZero
                                                                                      omega
                                                                                  | scan sourceOptionalWaiting _ _ _
                                                                                      sourceOptionalScan _ _ =>
                                                                                      have sourceOptionalWaitingProduction :
                                                                                          sourceOptionalWaiting.raw.production =
                                                                                            .seq atomDotSequenceSite :=
                                                                                        sourceOptionalScan.advance.1.symm
                                                                                      have sourceSequenceDotThree :
                                                                                          sourceBranchDot.val = 3 := by
                                                                                        change sourceBranchDot.val =
                                                                                          (ProductionId.seq
                                                                                            atomDotSequenceSite).rhs.length
                                                                                          at sourceSequenceComplete
                                                                                        simpa [ProductionId.rhs_seq,
                                                                                          atomDotSequenceSite_children]
                                                                                          using sourceSequenceComplete
                                                                                      have sourceOptionalWaitingDot :
                                                                                          sourceOptionalWaiting.raw.dot.val =
                                                                                            2 := by
                                                                                        have advanced :=
                                                                                          sourceOptionalScan.advance.2.1
                                                                                        change sourceBranchDot.val =
                                                                                          sourceOptionalWaiting.raw.dot.val + 1
                                                                                          at advanced
                                                                                        omega
                                                                                      have impossible :
                                                                                          some (GrammarSymbol.terminal
                                                                                            sourceOptionalScan.terminal) =
                                                                                            some (GrammarSymbol.nonterminal
                                                                                              (.aux atomDotOptionalSite.site)) := by
                                                                                        let sourceOptionalIndex : Nat :=
                                                                                          sourceOptionalWaiting.raw.dot.val
                                                                                        have sourceOptionalIndexTwo :
                                                                                            sourceOptionalIndex = 2 :=
                                                                                          sourceOptionalWaitingDot
                                                                                        calc
                                                                                          _ = sourceOptionalWaiting.raw.production.rhs[
                                                                                                sourceOptionalWaiting.raw.dot.val]? :=
                                                                                            sourceOptionalScan.next.2.symm
                                                                                          _ = sourceOptionalWaiting.raw.production.rhs[
                                                                                                sourceOptionalIndex]? := rfl
                                                                                          _ = (ProductionId.seq
                                                                                                atomDotSequenceSite).rhs[
                                                                                                  sourceOptionalIndex]? :=
                                                                                            congrArg
                                                                                              (fun production : ProductionId =>
                                                                                                production.rhs[sourceOptionalIndex]?)
                                                                                              sourceOptionalWaitingProduction
                                                                                          _ = (ProductionId.seq
                                                                                                atomDotSequenceSite).rhs[2]? := by
                                                                                            rw [sourceOptionalIndexTwo]
                                                                                          _ = _ := by
                                                                                            simp [ProductionId.rhs_seq,
                                                                                              atomDotSequenceSite_children]
                                                                                      exact GrammarSymbol.noConfusion
                                                                                        (Option.some.inj impossible)
                                                                                  | complete sourceOptionalWaiting
                                                                                      sourceOptionalFinished
                                                                                      sourceOptionalAfter sourceOptionalShared
                                                                                      sourceSequencePriorValues
                                                                                      sourceOptionalValue sourceOptionalWitness
                                                                                      sourceOptionalEdge sourceSequencePrior
                                                                                      sourceOptionalReduction =>
                                                                                      have sourceSequenceDotThree :
                                                                                          sourceBranchDot.val = 3 := by
                                                                                        change sourceBranchDot.val =
                                                                                          (ProductionId.seq
                                                                                            atomDotSequenceSite).rhs.length
                                                                                          at sourceSequenceComplete
                                                                                        simpa [ProductionId.rhs_seq,
                                                                                          atomDotSequenceSite_children]
                                                                                          using sourceSequenceComplete
                                                                                      have sourceOptionalWaitingProduction :
                                                                                          sourceOptionalWaiting.raw.production =
                                                                                            .seq atomDotSequenceSite :=
                                                                                        sourceOptionalWitness.advance.1.symm
                                                                                      have sourceOptionalWaitingDot :
                                                                                          sourceOptionalWaiting.raw.dot.val = 2 := by
                                                                                        have advanced :=
                                                                                          sourceOptionalWitness.advance.2.1
                                                                                        change sourceBranchDot.val =
                                                                                          sourceOptionalWaiting.raw.dot.val + 1
                                                                                          at advanced
                                                                                        omega
                                                                                      have sourceOptionalFinishedLhs :
                                                                                          sourceOptionalFinished.raw.production.lhs =
                                                                                            .aux atomDotOptionalSite.site := by
                                                                                        have selected :
                                                                                            some (GrammarSymbol.nonterminal
                                                                                              sourceOptionalFinished.raw.production.lhs) =
                                                                                              some (GrammarSymbol.nonterminal
                                                                                                (.aux atomDotOptionalSite.site)) := by
                                                                                          let index : Nat :=
                                                                                            sourceOptionalWaiting.raw.dot.val
                                                                                          have indexTwo : index = 2 :=
                                                                                            sourceOptionalWaitingDot
                                                                                          calc
                                                                                            _ = sourceOptionalWaiting.raw.production.rhs[
                                                                                                  sourceOptionalWaiting.raw.dot.val]? :=
                                                                                              sourceOptionalWitness.next.2.symm
                                                                                            _ = sourceOptionalWaiting.raw.production.rhs[
                                                                                                  index]? := rfl
                                                                                            _ = (ProductionId.seq
                                                                                                  atomDotSequenceSite).rhs[index]? :=
                                                                                              congrArg
                                                                                                (fun production : ProductionId =>
                                                                                                  production.rhs[index]?)
                                                                                                sourceOptionalWaitingProduction
                                                                                            _ = (ProductionId.seq
                                                                                                  atomDotSequenceSite).rhs[2]? := by
                                                                                              rw [indexTwo]
                                                                                            _ = _ := by
                                                                                              simp [ProductionId.rhs_seq,
                                                                                                atomDotSequenceSite_children]
                                                                                        exact GrammarSymbol.nonterminal.inj
                                                                                          (Option.some.inj selected)
                                                                                      obtain ⟨sourceOptionalSite,
                                                                                          sourceOptionalBranch,
                                                                                          sourceOptionalProduction,
                                                                                          sourceOptionalSiteEq⟩ :=
                                                                                        auxiliaryOptionalProduction
                                                                                          sourceOptionalFinished.raw.production
                                                                                          atomDotOptionalSite.site
                                                                                          sourceOptionalFinishedLhs
                                                                                          atomDotOptionalSite.hasKind
                                                                                      have sourceOptionalSiteCanonical :
                                                                                          sourceOptionalSite =
                                                                                            atomDotOptionalSite := by
                                                                                        cases sourceOptionalSite
                                                                                        simp only [atomDotOptionalSite]
                                                                                          at sourceOptionalSiteEq ⊢
                                                                                        subst_vars
                                                                                        rfl
                                                                                      subst sourceOptionalSite
                                                                                      rcases sourceOptionalFinished with
                                                                                        ⟨⟨sourceOptionalProductionId,
                                                                                          sourceOptionalDot,
                                                                                          sourceOptionalOrigin,
                                                                                          sourceOptionalCurrent⟩,
                                                                                          sourceOptionalContext⟩
                                                                                      simp only at sourceOptionalProduction
                                                                                      subst sourceOptionalProductionId
                                                                                      cases sourceOptionalReduction with
                                                                                      | reduce sourceOptionalItem
                                                                                          sourceOptionalValues
                                                                                          sourceOptionalOutput
                                                                                          sourceOptionalReached
                                                                                          sourceOptionalComplete
                                                                                          sourceOptionalCoherent
                                                                                          sourceOptionalAction =>
                                                                                          have sourceOptionalPackedEq :=
                                                                                            actionReduces_eleven_shapes_exact.mp
                                                                                              sourceOptionalAction
                                                                                          change sourceOptionalValue =
                                                                                            OptionalSite.pack atomDotOptionalSite
                                                                                              sourceOptionalBranch
                                                                                              (PrefixValues.fullValue
                                                                                                { raw := {
                                                                                                    production :=
                                                                                                      .opt atomDotOptionalSite
                                                                                                        sourceOptionalBranch
                                                                                                    dot := sourceOptionalDot
                                                                                                    origin :=
                                                                                                      sourceOptionalOrigin
                                                                                                    current :=
                                                                                                      sourceOptionalCurrent }
                                                                                                  context :=
                                                                                                    sourceOptionalContext }
                                                                                                sourceOptionalComplete
                                                                                                sourceOptionalValues)
                                                                                            at sourceOptionalPackedEq
                                                                                          cases sourceSequencePrior with
                                                                                          | zero _ _ sourceNameZero =>
                                                                                              change
                                                                                                sourceOptionalWaiting.raw.dot.val = 0
                                                                                                at sourceNameZero
                                                                                              omega
                                                                                          | scan sourceNameWaiting _ _ _
                                                                                              sourceNameScan _ _ =>
                                                                                              have sourceNameWaitingProduction :
                                                                                                  sourceNameWaiting.raw.production =
                                                                                                    .seq atomDotSequenceSite := by
                                                                                                calc
                                                                                                  _ = sourceOptionalWaiting.raw.production :=
                                                                                                    sourceNameScan.advance.1.symm
                                                                                                  _ = _ := sourceOptionalWaitingProduction
                                                                                              have sourceNameWaitingDot :
                                                                                                  sourceNameWaiting.raw.dot.val = 1 := by
                                                                                                have advanced :=
                                                                                                  sourceNameScan.advance.2.1
                                                                                                change
                                                                                                  sourceOptionalWaiting.raw.dot.val =
                                                                                                    sourceNameWaiting.raw.dot.val + 1
                                                                                                  at advanced
                                                                                                omega
                                                                                              have impossible :
                                                                                                  some (GrammarSymbol.terminal
                                                                                                    sourceNameScan.terminal) =
                                                                                                    some (GrammarSymbol.nonterminal
                                                                                                      (.aux atomDotNameSite.site)) := by
                                                                                                let index : Nat :=
                                                                                                  sourceNameWaiting.raw.dot.val
                                                                                                have indexOne : index = 1 :=
                                                                                                  sourceNameWaitingDot
                                                                                                calc
                                                                                                  _ = sourceNameWaiting.raw.production.rhs[
                                                                                                        sourceNameWaiting.raw.dot.val]? :=
                                                                                                    sourceNameScan.next.2.symm
                                                                                                  _ = sourceNameWaiting.raw.production.rhs[
                                                                                                        index]? := rfl
                                                                                                  _ = (ProductionId.seq
                                                                                                        atomDotSequenceSite).rhs[index]? :=
                                                                                                    congrArg
                                                                                                      (fun production : ProductionId =>
                                                                                                        production.rhs[index]?)
                                                                                                      sourceNameWaitingProduction
                                                                                                  _ = (ProductionId.seq
                                                                                                        atomDotSequenceSite).rhs[1]? := by
                                                                                                    rw [indexOne]
                                                                                                  _ = _ := by
                                                                                                    simp [ProductionId.rhs_seq,
                                                                                                      atomDotSequenceSite_children]
                                                                                              exact GrammarSymbol.noConfusion
                                                                                                (Option.some.inj impossible)
                                                                                          | complete sourceNameWaiting
                                                                                              sourceNameFinished _
                                                                                              sourceNameShared
                                                                                              sourceNamePriorValues
                                                                                              sourceNameValue sourceNameWitness
                                                                                              sourceNameEdge sourceNamePrior
                                                                                              sourceNameReduction =>
                                                                                              have sourceNameWaitingProduction :
                                                                                                  sourceNameWaiting.raw.production =
                                                                                                    .seq atomDotSequenceSite := by
                                                                                                calc
                                                                                                  _ = sourceOptionalWaiting.raw.production :=
                                                                                                    sourceNameWitness.advance.1.symm
                                                                                                  _ = _ := sourceOptionalWaitingProduction
                                                                                              have sourceNameWaitingDot :
                                                                                                  sourceNameWaiting.raw.dot.val = 1 := by
                                                                                                have advanced :=
                                                                                                  sourceNameWitness.advance.2.1
                                                                                                change
                                                                                                  sourceOptionalWaiting.raw.dot.val =
                                                                                                    sourceNameWaiting.raw.dot.val + 1
                                                                                                  at advanced
                                                                                                omega
                                                                                              have sourceNameFinishedLhs :
                                                                                                  sourceNameFinished.raw.production.lhs =
                                                                                                    .aux atomDotNameSite.site := by
                                                                                                have selected :
                                                                                                    some (GrammarSymbol.nonterminal
                                                                                                      sourceNameFinished.raw.production.lhs) =
                                                                                                      some (GrammarSymbol.nonterminal
                                                                                                        (.aux atomDotNameSite.site)) := by
                                                                                                  let index : Nat :=
                                                                                                    sourceNameWaiting.raw.dot.val
                                                                                                  have indexOne : index = 1 :=
                                                                                                    sourceNameWaitingDot
                                                                                                  calc
                                                                                                    _ = sourceNameWaiting.raw.production.rhs[
                                                                                                          sourceNameWaiting.raw.dot.val]? :=
                                                                                                      sourceNameWitness.next.2.symm
                                                                                                    _ = sourceNameWaiting.raw.production.rhs[
                                                                                                          index]? := rfl
                                                                                                    _ = (ProductionId.seq
                                                                                                          atomDotSequenceSite).rhs[index]? :=
                                                                                                      congrArg
                                                                                                        (fun production : ProductionId =>
                                                                                                          production.rhs[index]?)
                                                                                                        sourceNameWaitingProduction
                                                                                                    _ = (ProductionId.seq
                                                                                                          atomDotSequenceSite).rhs[1]? := by
                                                                                                      rw [indexOne]
                                                                                                    _ = _ := by
                                                                                                      simp [ProductionId.rhs_seq,
                                                                                                        atomDotSequenceSite_children]
                                                                                                exact GrammarSymbol.nonterminal.inj
                                                                                                  (Option.some.inj selected)
                                                                                              obtain ⟨sourceNameAtomSite,
                                                                                                  sourceNameProduction,
                                                                                                  sourceNameAtomSiteEq⟩ :=
                                                                                                auxiliaryAtomProduction
                                                                                                  sourceNameFinished.raw.production
                                                                                                  atomDotNameSite.site
                                                                                                  sourceNameFinishedLhs
                                                                                                  atomDotNameSite.hasKind
                                                                                              have sourceNameAtomSiteCanonical :
                                                                                                  sourceNameAtomSite =
                                                                                                    atomDotNameSite := by
                                                                                                cases sourceNameAtomSite
                                                                                                simp only [atomDotNameSite]
                                                                                                  at sourceNameAtomSiteEq ⊢
                                                                                                subst_vars
                                                                                                rfl
                                                                                              subst sourceNameAtomSite
                                                                                              rcases sourceNameFinished with
                                                                                                ⟨⟨sourceNameProductionId,
                                                                                                  sourceNameDot,
                                                                                                  sourceNameOrigin,
                                                                                                  sourceNameCurrent⟩,
                                                                                                  sourceNameContext⟩
                                                                                              simp only at sourceNameProduction
                                                                                              subst sourceNameProductionId
                                                                                              cases sourceNameReduction with
                                                                                              | reduce sourceNameItem
                                                                                                  sourceNameValues
                                                                                                  sourceNameOutput
                                                                                                  sourceNameReached
                                                                                                  sourceNameComplete
                                                                                                  sourceNameCoherent
                                                                                                  sourceNameAction =>
                                                                                                  have sourceNamePriorLayout :
                                                                                                      sourceNameWaiting.raw.production.rhs.take
                                                                                                        sourceNameWaiting.raw.dot.val = [
                                                                                                          .nonterminal
                                                                                                            (.aux atomDotTokenSite.site)] := by
                                                                                                    let index : Nat :=
                                                                                                      sourceNameWaiting.raw.dot.val
                                                                                                    have indexOne : index = 1 :=
                                                                                                      sourceNameWaitingDot
                                                                                                    calc
                                                                                                      _ = (ProductionId.seq
                                                                                                            atomDotSequenceSite).rhs.take
                                                                                                              index :=
                                                                                                        congrArg
                                                                                                          (fun production : ProductionId =>
                                                                                                            production.rhs.take index)
                                                                                                          sourceNameWaitingProduction
                                                                                                      _ = (ProductionId.seq
                                                                                                            atomDotSequenceSite).rhs.take 1 := by
                                                                                                        rw [indexOne]
                                                                                                      _ = _ := by
                                                                                                        simp [ProductionId.rhs_seq,
                                                                                                          atomDotSequenceSite_children]
                                                                                                  generalize sourceNameCanonicalEq :
                                                                                                      GrammarSymbolValues.transport
                                                                                                        sourceNamePriorLayout
                                                                                                        sourceNamePriorValues =
                                                                                                        sourceNameCanonical
                                                                                                  rcases sourceNameCanonical with
                                                                                                    ⟨sourceDotCanonicalValue, ⟨⟩⟩
                                                                                                  cases sourceNamePrior with
                                                                                                  | zero _ _ sourceDotZero =>
                                                                                                      change
                                                                                                        sourceNameWaiting.raw.dot.val = 0
                                                                                                        at sourceDotZero
                                                                                                      omega
                                                                                                  | scan sourceDotWaiting _ _ _
                                                                                                      sourceDotScan _ _ =>
                                                                                                      have sourceDotWaitingProduction :
                                                                                                          sourceDotWaiting.raw.production =
                                                                                                            .seq atomDotSequenceSite := by
                                                                                                        calc
                                                                                                          _ = sourceNameWaiting.raw.production :=
                                                                                                            sourceDotScan.advance.1.symm
                                                                                                          _ = _ := sourceNameWaitingProduction
                                                                                                      have sourceDotWaitingDot :
                                                                                                          sourceDotWaiting.raw.dot.val = 0 := by
                                                                                                        have advanced :=
                                                                                                          sourceDotScan.advance.2.1
                                                                                                        change
                                                                                                          sourceNameWaiting.raw.dot.val =
                                                                                                            sourceDotWaiting.raw.dot.val + 1
                                                                                                          at advanced
                                                                                                        omega
                                                                                                      have impossible :
                                                                                                          some (GrammarSymbol.terminal
                                                                                                            sourceDotScan.terminal) =
                                                                                                            some (GrammarSymbol.nonterminal
                                                                                                              (.aux atomDotTokenSite.site)) := by
                                                                                                        let index : Nat :=
                                                                                                          sourceDotWaiting.raw.dot.val
                                                                                                        have indexZero : index = 0 :=
                                                                                                          sourceDotWaitingDot
                                                                                                        calc
                                                                                                          _ = sourceDotWaiting.raw.production.rhs[
                                                                                                                sourceDotWaiting.raw.dot.val]? :=
                                                                                                            sourceDotScan.next.2.symm
                                                                                                          _ = sourceDotWaiting.raw.production.rhs[
                                                                                                                index]? := rfl
                                                                                                          _ = (ProductionId.seq
                                                                                                                atomDotSequenceSite).rhs[index]? :=
                                                                                                            congrArg
                                                                                                              (fun production : ProductionId =>
                                                                                                                production.rhs[index]?)
                                                                                                              sourceDotWaitingProduction
                                                                                                          _ = (ProductionId.seq
                                                                                                                atomDotSequenceSite).rhs[0]? := by
                                                                                                            rw [indexZero]
                                                                                                          _ = _ := by
                                                                                                            simp [ProductionId.rhs_seq,
                                                                                                              atomDotSequenceSite_children]
                                                                                                      exact GrammarSymbol.noConfusion
                                                                                                        (Option.some.inj impossible)
                                                                                                  | complete sourceDotWaiting
                                                                                                      sourceDotFinished _
                                                                                                      sourceDotShared
                                                                                                      sourceDotPriorValues
                                                                                                      sourceDotValue sourceDotWitness
                                                                                                      sourceDotEdge sourceDotPrior
                                                                                                      sourceDotReduction =>
                                                                                                      have sourceDotWaitingProduction :
                                                                                                          sourceDotWaiting.raw.production =
                                                                                                            .seq atomDotSequenceSite := by
                                                                                                        calc
                                                                                                          _ = sourceNameWaiting.raw.production :=
                                                                                                            sourceDotWitness.advance.1.symm
                                                                                                          _ = _ := sourceNameWaitingProduction
                                                                                                      have sourceDotWaitingDot :
                                                                                                          sourceDotWaiting.raw.dot.val = 0 := by
                                                                                                        have advanced :=
                                                                                                          sourceDotWitness.advance.2.1
                                                                                                        change
                                                                                                          sourceNameWaiting.raw.dot.val =
                                                                                                            sourceDotWaiting.raw.dot.val + 1
                                                                                                          at advanced
                                                                                                        omega
                                                                                                      have sourceDotFinishedLhs :
                                                                                                          sourceDotFinished.raw.production.lhs =
                                                                                                            .aux atomDotTokenSite.site := by
                                                                                                        have selected :
                                                                                                            some (GrammarSymbol.nonterminal
                                                                                                              sourceDotFinished.raw.production.lhs) =
                                                                                                              some (GrammarSymbol.nonterminal
                                                                                                                (.aux atomDotTokenSite.site)) := by
                                                                                                          let index : Nat :=
                                                                                                            sourceDotWaiting.raw.dot.val
                                                                                                          have indexZero : index = 0 :=
                                                                                                            sourceDotWaitingDot
                                                                                                          calc
                                                                                                            _ = sourceDotWaiting.raw.production.rhs[
                                                                                                                  sourceDotWaiting.raw.dot.val]? :=
                                                                                                              sourceDotWitness.next.2.symm
                                                                                                            _ = sourceDotWaiting.raw.production.rhs[
                                                                                                                  index]? := rfl
                                                                                                            _ = (ProductionId.seq
                                                                                                                  atomDotSequenceSite).rhs[index]? :=
                                                                                                              congrArg
                                                                                                                (fun production : ProductionId =>
                                                                                                                  production.rhs[index]?)
                                                                                                                sourceDotWaitingProduction
                                                                                                            _ = (ProductionId.seq
                                                                                                                  atomDotSequenceSite).rhs[0]? := by
                                                                                                              rw [indexZero]
                                                                                                            _ = _ := by
                                                                                                              simp [ProductionId.rhs_seq,
                                                                                                                atomDotSequenceSite_children]
                                                                                                        exact GrammarSymbol.nonterminal.inj
                                                                                                          (Option.some.inj selected)
                                                                                                      obtain ⟨sourceDotAtomSite,
                                                                                                          sourceDotProduction,
                                                                                                          sourceDotAtomSiteEq⟩ :=
                                                                                                        auxiliaryAtomProduction
                                                                                                          sourceDotFinished.raw.production
                                                                                                          atomDotTokenSite.site
                                                                                                          sourceDotFinishedLhs
                                                                                                          atomDotTokenSite.hasKind
                                                                                                      have sourceDotAtomSiteCanonical :
                                                                                                          sourceDotAtomSite =
                                                                                                            atomDotTokenSite := by
                                                                                                        cases sourceDotAtomSite
                                                                                                        simp only [atomDotTokenSite]
                                                                                                          at sourceDotAtomSiteEq ⊢
                                                                                                        subst_vars
                                                                                                        rfl
                                                                                                      subst sourceDotAtomSite
                                                                                                      rcases sourceDotFinished with
                                                                                                        ⟨⟨sourceDotProductionId,
                                                                                                          sourceDotDot,
                                                                                                          sourceDotOrigin,
                                                                                                          sourceDotCurrent⟩,
                                                                                                          sourceDotContext⟩
                                                                                                      simp only at sourceDotProduction
                                                                                                      subst sourceDotProductionId
                                                                                                      cases sourceDotReduction with
                                                                                                      | reduce sourceDotItem
                                                                                                          sourceDotValues
                                                                                                          sourceDotOutput
                                                                                                          sourceDotReached
                                                                                                          sourceDotComplete
                                                                                                          sourceDotCoherent
                                                                                                          sourceDotAction =>
                                                                                                          cases sourceDotPrior with
                                                                                                          | zero _ sourceDotWaitingReached
                                                                                                              sourceDotWaitingZero =>
                                                                                                              have sourceNamePriorRecover :
                                                                                                                  GrammarSymbolValues.transport
                                                                                                                      sourceNamePriorLayout.symm
                                                                                                                      (sourceDotCanonicalValue,
                                                                                                                        ()) =
                                                                                                                    PrefixValues.completeValue
                                                                                                                      sourceDotWaiting
                                                                                                                      { raw := {
                                                                                                                          production :=
                                                                                                                            .atom atomDotTokenSite
                                                                                                                          dot := sourceDotDot
                                                                                                                          origin :=
                                                                                                                            sourceDotOrigin
                                                                                                                          current :=
                                                                                                                            sourceDotCurrent }
                                                                                                                        context :=
                                                                                                                          sourceDotContext }
                                                                                                                      sourceNameWaiting
                                                                                                                      sourceDotWitness.next
                                                                                                                      sourceDotWitness.advance
                                                                                                                      (PrefixValues.zeroValue
                                                                                                                        sourceDotWaiting
                                                                                                                        sourceDotWaitingZero)
                                                                                                                      sourceDotValue := by
                                                                                                                rw [← sourceNameCanonicalEq,
                                                                                                                  GrammarSymbolValues.transport_trans]
                                                                                                                exact
                                                                                                                  GrammarSymbolValues.transport_self
                                                                                                                    _ _
                                                                                                              have sourceSequenceSymbolLayout :
                                                                                                                  atomDotSequenceSite.children.map
                                                                                                                      (fun child =>
                                                                                                                        GrammarSymbol.nonterminal
                                                                                                                          (.aux child)) = [
                                                                                                                    .nonterminal
                                                                                                                      (.aux atomDotTokenSite.site),
                                                                                                                    .nonterminal
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotNameSite).lhs,
                                                                                                                    .nonterminal
                                                                                                                      (ProductionId.opt
                                                                                                                        atomDotOptionalSite
                                                                                                                        sourceOptionalBranch).lhs] := by
                                                                                                                rw [atomDotSequenceSite_children]
                                                                                                                simp [ProductionId.lhs]
                                                                                                              have sourceSequenceTargetLayout :
                                                                                                                  (ProductionId.seq
                                                                                                                      atomDotSequenceSite).rhs = [
                                                                                                                    .nonterminal
                                                                                                                      (.aux atomDotTokenSite.site),
                                                                                                                    .nonterminal
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotNameSite).lhs,
                                                                                                                    .nonterminal
                                                                                                                      (ProductionId.opt
                                                                                                                        atomDotOptionalSite
                                                                                                                        sourceOptionalBranch).lhs] :=
                                                                                                                (ProductionId.rhs_seq
                                                                                                                  atomDotSequenceSite).trans
                                                                                                                  sourceSequenceSymbolLayout
                                                                                                              have sourceSequenceFullTupleEq :=
                                                                                                                GrammarSymbolValues.transport_append_three_direct
                                                                                                                  sourceNamePriorLayout
                                                                                                                  (prefix_complete_layout
                                                                                                                    sourceNameWaiting.raw
                                                                                                                    { production :=
                                                                                                                        .atom atomDotNameSite
                                                                                                                      dot := sourceNameDot
                                                                                                                      origin := sourceNameOrigin
                                                                                                                      current := sourceNameCurrent }
                                                                                                                    sourceOptionalWaiting.raw
                                                                                                                    sourceNameWitness.next
                                                                                                                    sourceNameWitness.advance)
                                                                                                                  ((prefix_complete_layout
                                                                                                                    sourceOptionalWaiting.raw
                                                                                                                    { production :=
                                                                                                                        .opt atomDotOptionalSite
                                                                                                                          sourceOptionalBranch
                                                                                                                      dot := sourceOptionalDot
                                                                                                                      origin :=
                                                                                                                        sourceOptionalOrigin
                                                                                                                      current :=
                                                                                                                        sourceOptionalCurrent }
                                                                                                                    { production :=
                                                                                                                        .seq atomDotSequenceSite
                                                                                                                      dot := sourceBranchDot
                                                                                                                      origin :=
                                                                                                                        sourceBranchOriginBoundary
                                                                                                                      current :=
                                                                                                                        sourceBranchCurrent }
                                                                                                                    sourceOptionalWitness.next
                                                                                                                    sourceOptionalWitness.advance).trans
                                                                                                                    (prefix_full_layout
                                                                                                                      { production :=
                                                                                                                          .seq atomDotSequenceSite
                                                                                                                        dot := sourceBranchDot
                                                                                                                        origin :=
                                                                                                                          sourceBranchOriginBoundary
                                                                                                                        current :=
                                                                                                                          sourceBranchCurrent }
                                                                                                                      sourceSequenceComplete))
                                                                                                                  sourceSequenceTargetLayout
                                                                                                                  sourceDotCanonicalValue
                                                                                                                  sourceNameValue
                                                                                                                  sourceOptionalValue
                                                                                                              rw [PrefixValues.fullValue_completeValue_eq]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              rw [← sourceNamePriorRecover]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              unfold PrefixValues.completeValue
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              rw [sourceSequenceFullTupleEq]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              unfold GrammarSymbolValues.view
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              rw [GrammarSymbolValues.transport_trans]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              have sourceSequenceTransportProof :
                                                                                                                  sourceSequenceTargetLayout.symm.trans
                                                                                                                      (ProductionId.rhs_seq
                                                                                                                        atomDotSequenceSite) =
                                                                                                                    sourceSequenceSymbolLayout.symm :=
                                                                                                                Subsingleton.elim _ _
                                                                                                              rw [sourceSequenceTransportProof]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              rw [atomDotOptionalValue_auxiliaryTuple_of_lhs
                                                                                                                sourceNameFinishedLhs
                                                                                                                sourceOptionalFinishedLhs
                                                                                                                sourceSequenceSymbolLayout
                                                                                                                sourceDotCanonicalValue
                                                                                                                sourceNameValue
                                                                                                                sourceOptionalValue]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              have sourceOptionalFinishedLhsProof :
                                                                                                                  sourceOptionalFinishedLhs = rfl :=
                                                                                                                Subsingleton.elim _ _
                                                                                                              rw [sourceOptionalFinishedLhsProof]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              rw [sourceOptionalPackedEq]
                                                                                                                at sourceOptionalSemanticEq
                                                                                                              cases sourceOptionalBranch with
                                                                                                              | none =>
                                                                                                                  have sourceDotDotOne :
                                                                                                                      sourceDotDot.val = 1 := by
                                                                                                                    change sourceDotDot.val =
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotTokenSite).rhs.length
                                                                                                                      at sourceDotComplete
                                                                                                                    simpa [ProductionId.rhs_atom]
                                                                                                                      using sourceDotComplete
                                                                                                                  have sourceDotSelected :
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotTokenSite).rhs[0]? =
                                                                                                                        some (.terminal
                                                                                                                          (.symbol .dot)) := by
                                                                                                                    run_tac
                                                                                                                      Lean.Meta.withTransparency .all do
                                                                                                                        (← Lean.Elab.Tactic.getMainGoal).refl
                                                                                                                  obtain ⟨sourceDotMatched,
                                                                                                                      sourceDotMatchedOrigin,
                                                                                                                      sourceDotMatchedCurrent⟩ :=
                                                                                                                    contextualReach_one_terminal
                                                                                                                      sourceDotReached
                                                                                                                      sourceDotDotOne
                                                                                                                      sourceDotSelected
                                                                                                                  have sourceNameDotOne :
                                                                                                                      sourceNameDot.val = 1 := by
                                                                                                                    change sourceNameDot.val =
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotNameSite).rhs.length
                                                                                                                      at sourceNameComplete
                                                                                                                    simpa [ProductionId.rhs_atom]
                                                                                                                      using sourceNameComplete
                                                                                                                  have sourceNameSelected :
                                                                                                                      (ProductionId.atom
                                                                                                                        atomDotNameSite).rhs[0]? =
                                                                                                                        some (.terminal
                                                                                                                          (.category .identifier)) := by
                                                                                                                    run_tac
                                                                                                                      Lean.Meta.withTransparency .all do
                                                                                                                        (← Lean.Elab.Tactic.getMainGoal).refl
                                                                                                                  obtain ⟨sourceNameMatched,
                                                                                                                      sourceNameMatchedOrigin,
                                                                                                                      sourceNameMatchedCurrent⟩ :=
                                                                                                                    contextualReach_one_terminal
                                                                                                                      sourceNameReached
                                                                                                                      sourceNameDotOne
                                                                                                                      sourceNameSelected
                                                                                                                  have sourceDotCurrentVal :
                                                                                                                      sourceDotCurrent.val =
                                                                                                                        sourceDotOrigin.val + 1 := by
                                                                                                                    have originVal :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceDotMatchedOrigin
                                                                                                                    have currentVal :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceDotMatchedCurrent
                                                                                                                    change sourceDotMatched.cursor.val =
                                                                                                                      sourceDotOrigin.val at originVal
                                                                                                                    change sourceDotMatched.cursor.val + 1 =
                                                                                                                      sourceDotCurrent.val at currentVal
                                                                                                                    omega
                                                                                                                  have sourceNameCurrentVal :
                                                                                                                      sourceNameCurrent.val =
                                                                                                                        sourceNameOrigin.val + 1 := by
                                                                                                                    have originVal :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceNameMatchedOrigin
                                                                                                                    have currentVal :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceNameMatchedCurrent
                                                                                                                    change sourceNameMatched.cursor.val =
                                                                                                                      sourceNameOrigin.val at originVal
                                                                                                                    change sourceNameMatched.cursor.val + 1 =
                                                                                                                      sourceNameCurrent.val at currentVal
                                                                                                                    omega
                                                                                                                  have sourceDotWaitingOriginCurrent :
                                                                                                                      sourceDotWaiting.raw.origin =
                                                                                                                        sourceDotWaiting.raw.current :=
                                                                                                                    contextualReach_zero_origin_eq_current
                                                                                                                      sourceDotWaitingReached
                                                                                                                      sourceDotWaitingZero
                                                                                                                  have sourceDotOriginAtBranch :
                                                                                                                      sourceDotOrigin =
                                                                                                                        sourceBranchOriginBoundary := by
                                                                                                                    calc
                                                                                                                      sourceDotOrigin =
                                                                                                                          sourceDotShared :=
                                                                                                                        sourceDotWitness.finishedAtShared
                                                                                                                      _ = sourceDotWaiting.raw.current :=
                                                                                                                        sourceDotWitness.waitingAtShared.symm
                                                                                                                      _ = sourceDotWaiting.raw.origin :=
                                                                                                                        sourceDotWaitingOriginCurrent.symm
                                                                                                                      _ = sourceNameWaiting.raw.origin :=
                                                                                                                        sourceDotWitness.advance.2.2.1.symm
                                                                                                                      _ = sourceOptionalWaiting.raw.origin :=
                                                                                                                        sourceNameWitness.advance.2.2.1.symm
                                                                                                                      _ = sourceBranchOriginBoundary :=
                                                                                                                        sourceOptionalWitness.advance.2.2.1.symm
                                                                                                                  have sourceNameOriginAtDotCurrent :
                                                                                                                      sourceNameOrigin =
                                                                                                                        sourceDotCurrent := by
                                                                                                                    calc
                                                                                                                      sourceNameOrigin =
                                                                                                                          sourceNameShared :=
                                                                                                                        sourceNameWitness.finishedAtShared
                                                                                                                      _ = sourceNameWaiting.raw.current :=
                                                                                                                        sourceNameWitness.waitingAtShared.symm
                                                                                                                      _ = sourceDotCurrent :=
                                                                                                                        sourceDotWitness.advance.2.2.2
                                                                                                                  have sourceOptionalOriginAtNameCurrent :
                                                                                                                      sourceOptionalOrigin =
                                                                                                                        sourceNameCurrent := by
                                                                                                                    calc
                                                                                                                      sourceOptionalOrigin =
                                                                                                                          sourceOptionalShared :=
                                                                                                                        sourceOptionalWitness.finishedAtShared
                                                                                                                      _ = sourceOptionalWaiting.raw.current :=
                                                                                                                        sourceOptionalWitness.waitingAtShared.symm
                                                                                                                      _ = sourceNameCurrent :=
                                                                                                                        sourceNameWitness.advance.2.2.2
                                                                                                                  have sourceOptionalOriginVal :
                                                                                                                      sourceOptionalOrigin.val =
                                                                                                                        sourceBranchOriginBoundary.val + 2 := by
                                                                                                                    have optionalAtName :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceOptionalOriginAtNameCurrent
                                                                                                                    have nameAtDot :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceNameOriginAtDotCurrent
                                                                                                                    have dotAtBranch :=
                                                                                                                      congrArg Fin.val
                                                                                                                        sourceDotOriginAtBranch
                                                                                                                    omega
                                                                                                                  have sourceRootWaitingOriginCurrent :
                                                                                                                      sourceRootWaiting.raw.origin =
                                                                                                                        sourceRootWaiting.raw.current :=
                                                                                                                    contextualReach_zero_origin_eq_current
                                                                                                                      sourceRootWaitingReached
                                                                                                                      sourceRootWaitingZero
                                                                                                                  have sourceWaitingOriginCurrent :
                                                                                                                      sourceWaitingOrigin =
                                                                                                                        sourceWaitingCurrent :=
                                                                                                                    contextualReach_zero_origin_eq_current
                                                                                                                      sourceWaitingReached
                                                                                                                      sourceWaitingZero
                                                                                                                  have atomWaitingOriginCurrent :
                                                                                                                      atomWaitingOrigin =
                                                                                                                        atomWaitingCurrent :=
                                                                                                                    contextualReach_zero_origin_eq_current
                                                                                                                      atomReached atomZero
                                                                                                                  have rootWaitingOriginCurrent :
                                                                                                                      rootWaitingOrigin =
                                                                                                                        rootWaitingCurrent :=
                                                                                                                    contextualReach_zero_origin_eq_current
                                                                                                                      reached zero
                                                                                                                  have sourceChoiceOriginAtOrigin :
                                                                                                                      sourceChoiceOrigin = origin := by
                                                                                                                    calc
                                                                                                                      sourceChoiceOrigin =
                                                                                                                          sourceRootShared :=
                                                                                                                        sourceRootWitness.finishedAtShared
                                                                                                                      _ = sourceRootWaiting.raw.current :=
                                                                                                                        sourceRootWitness.waitingAtShared.symm
                                                                                                                      _ = sourceRootWaiting.raw.origin :=
                                                                                                                        sourceRootWaitingOriginCurrent.symm
                                                                                                                      _ = sourceOrigin :=
                                                                                                                        sourceRootWitness.advance.2.2.1.symm
                                                                                                                      _ = sourceShared :=
                                                                                                                        sourceWitness.finishedAtShared
                                                                                                                      _ = sourceWaitingCurrent :=
                                                                                                                        sourceWitness.waitingAtShared.symm
                                                                                                                      _ = sourceWaitingOrigin :=
                                                                                                                        sourceWaitingOriginCurrent.symm
                                                                                                                      _ = atomOrigin :=
                                                                                                                        sourceWitness.advance.2.2.1.symm
                                                                                                                      _ = atomShared :=
                                                                                                                        atomWitness.finishedAtShared
                                                                                                                      _ = atomWaitingCurrent :=
                                                                                                                        atomWitness.waitingAtShared.symm
                                                                                                                      _ = atomWaitingOrigin :=
                                                                                                                        atomWaitingOriginCurrent.symm
                                                                                                                      _ = starWaitingOrigin :=
                                                                                                                        atomWitness.advance.2.2.1.symm
                                                                                                                      _ = sequenceOrigin :=
                                                                                                                        starWitness.advance.2.2.1.symm
                                                                                                                      _ = shared :=
                                                                                                                        witness.finishedAtShared
                                                                                                                      _ = rootWaitingCurrent :=
                                                                                                                        witness.waitingAtShared.symm
                                                                                                                      _ = rootWaitingOrigin :=
                                                                                                                        rootWaitingOriginCurrent.symm
                                                                                                                      _ = origin :=
                                                                                                                        witness.advance.2.2.1.symm
                                                                                                                  have sourceOptionalOriginAtOrigin :
                                                                                                                      sourceOptionalOrigin.val =
                                                                                                                        origin.val + 2 := by
                                                                                                                    rw [sourceOptionalOriginVal,
                                                                                                                      sourceBranchOrigin,
                                                                                                                      sourceChoiceOriginAtOrigin]
                                                                                                                  have sequenceRule :
                                                                                                                      (ProductionId.seq
                                                                                                                        sequenceSite).sourceRule =
                                                                                                                        .postfix := by
                                                                                                                    change
                                                                                                                      sequenceSite.site.val.rule =
                                                                                                                        .postfix
                                                                                                                    rw [sequenceSiteRoot]
                                                                                                                    rfl
                                                                                                                  have firstSiteMember :
                                                                                                                      firstSite ∈
                                                                                                                        sequenceSite.children := by
                                                                                                                    rw [childrenEq]
                                                                                                                    simp
                                                                                                                  have firstSiteRule :
                                                                                                                      firstSite.val.rule =
                                                                                                                        .postfix := by
                                                                                                                    calc
                                                                                                                      firstSite.val.rule =
                                                                                                                          sequenceSite.site.val.rule :=
                                                                                                                        SequenceSite.child_rule
                                                                                                                          sequenceSite firstSite
                                                                                                                          firstSiteMember
                                                                                                                      _ = .postfix := by
                                                                                                                        rw [sequenceSiteRoot]
                                                                                                                        rfl
                                                                                                                  have atomSiteRule :
                                                                                                                      (ProductionId.atom
                                                                                                                        atomSite).sourceRule =
                                                                                                                        .postfix := by
                                                                                                                    change atomSite.site.val.rule =
                                                                                                                      .postfix
                                                                                                                    rw [atomSiteEq]
                                                                                                                    exact firstSiteRule
                                                                                                                  have sequenceContextEq :
                                                                                                                      sequenceContext = context :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      edge
                                                                                                                      (Or.inl sequenceRule)
                                                                                                                      (by simp)
                                                                                                                  have atomContextEq :
                                                                                                                      atomContext =
                                                                                                                        starWaitingContext :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      atomEdge
                                                                                                                      (Or.inl atomSiteRule)
                                                                                                                      (by simp)
                                                                                                                  have starWaitingContextEq :
                                                                                                                      starWaitingContext =
                                                                                                                        sequenceContext :=
                                                                                                                    starEdge.1.2.2.symm
                                                                                                                  have sourceContextEq :
                                                                                                                      sourceContext =
                                                                                                                        atomContext :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      sourceEdge
                                                                                                                      (Or.inr rfl)
                                                                                                                      (by simp)
                                                                                                                  have sourceChoiceContextEq :
                                                                                                                      sourceChoiceContext =
                                                                                                                        sourceContext :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      sourceRootEdge
                                                                                                                      (Or.inr rfl)
                                                                                                                      (by simp)
                                                                                                                  have sourceBranchContextEq :
                                                                                                                      sourceBranchContext =
                                                                                                                        sourceChoiceContext :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      sourceBranchEdge
                                                                                                                      (Or.inr rfl)
                                                                                                                      (by simp)
                                                                                                                  have sourceOptionalContextEq :
                                                                                                                      sourceOptionalContext =
                                                                                                                        sourceBranchContext :=
                                                                                                                    completedEdge_sameContext_of_postfixRegion
                                                                                                                      sourceOptionalEdge
                                                                                                                      (Or.inr rfl)
                                                                                                                      (by simp)
                                                                                                                  have rootContextEq :
                                                                                                                      context =
                                                                                                                        .postfixInvocation origin :=
                                                                                                                    contextualReach_rootPostfix_context
                                                                                                                      edge.2.2.2 rfl
                                                                                                                  have sourceOptionalContextAtOrigin :
                                                                                                                      sourceOptionalContext =
                                                                                                                        .postfixInvocation origin := by
                                                                                                                    calc
                                                                                                                      sourceOptionalContext =
                                                                                                                          sourceBranchContext :=
                                                                                                                        sourceOptionalContextEq
                                                                                                                      _ = sourceChoiceContext :=
                                                                                                                        sourceBranchContextEq
                                                                                                                      _ = sourceContext :=
                                                                                                                        sourceChoiceContextEq
                                                                                                                      _ = atomContext :=
                                                                                                                        sourceContextEq
                                                                                                                      _ = starWaitingContext :=
                                                                                                                        atomContextEq
                                                                                                                      _ = sequenceContext :=
                                                                                                                        starWaitingContextEq
                                                                                                                      _ = context :=
                                                                                                                        sequenceContextEq
                                                                                                                      _ = .postfixInvocation origin :=
                                                                                                                        rootContextEq
                                                                                                                  have leadingEvidence :=
                                                                                                                    leadingDotArguments_of_physicalPrefix
                                                                                                                      (RuleReduction.terminalLoc
                                                                                                                        directName directParsed)
                                                                                                                      owned
                                                                                                                      sourceOptionalOriginAtOrigin
                                                                                                                      physicalEq dotPayload
                                                                                                                      namePayload openPayload
                                                                                                                  have g07Member :
                                                                                                                      (.G07_leadingDotArguments,
                                                                                                                        .negative) ∈
                                                                                                                        guardOf
                                                                                                                          (.opt
                                                                                                                            atomDotOptionalSite
                                                                                                                            .none) := by
                                                                                                                    simp [guardOf,
                                                                                                                      atomDotOptionalSite,
                                                                                                                      GrammarSite.isAt]
                                                                                                                  have enabled :=
                                                                                                                    sourceOptionalReached.enabledProductionInstance
                                                                                                                  have noLeading :=
                                                                                                                    enabledG07Negative_notLeadingDotArguments
                                                                                                                      ({
                                                                                                                        production :=
                                                                                                                          .opt
                                                                                                                            atomDotOptionalSite
                                                                                                                            .none
                                                                                                                        origin :=
                                                                                                                          sourceOptionalOrigin
                                                                                                                        context :=
                                                                                                                          sourceOptionalContext
                                                                                                                      } :
                                                                                                                        ProductionInstanceKey
                                                                                                                          tokens)
                                                                                                                      origin
                                                                                                                      sourceOptionalOrigin
                                                                                                                      sourceOptionalContextAtOrigin
                                                                                                                      rfl enabled g07Member
                                                                                                                  exact noLeading leadingEvidence
                                                                                                              | some =>
                                                                                                                  change
                                                                                                                    EbnfValue.atShape
                                                                                                                        atomDotOptionalSite_expression
                                                                                                                        (OptionalSite.pack
                                                                                                                          atomDotOptionalSite
                                                                                                                          .some
                                                                                                                          (PrefixValues.fullValue
                                                                                                                            { raw := {
                                                                                                                                production :=
                                                                                                                                  .opt
                                                                                                                                    atomDotOptionalSite
                                                                                                                                    .some
                                                                                                                                dot :=
                                                                                                                                  sourceOptionalDot
                                                                                                                                origin :=
                                                                                                                                  sourceOptionalOrigin
                                                                                                                                current :=
                                                                                                                                  sourceOptionalCurrent }
                                                                                                                              context :=
                                                                                                                                sourceOptionalContext }
                                                                                                                            sourceOptionalComplete
                                                                                                                            sourceOptionalValues)) =
                                                                                                                      EbnfValue.optional
                                                                                                                        atomDotArgumentsExpression
                                                                                                                        none
                                                                                                                    at sourceOptionalSemanticEq
                                                                                                                  obtain ⟨presentValue,
                                                                                                                      present⟩ :=
                                                                                                                    optionalView_atShape_pack_some_present
                                                                                                                      atomDotOptionalSite
                                                                                                                      atomDotOptionalSite_expression
                                                                                                                      (PrefixValues.fullValue
                                                                                                                        { raw := {
                                                                                                                            production :=
                                                                                                                              .opt
                                                                                                                                atomDotOptionalSite
                                                                                                                                .some
                                                                                                                            dot :=
                                                                                                                              sourceOptionalDot
                                                                                                                            origin :=
                                                                                                                              sourceOptionalOrigin
                                                                                                                            current :=
                                                                                                                              sourceOptionalCurrent }
                                                                                                                          context :=
                                                                                                                            sourceOptionalContext }
                                                                                                                        sourceOptionalComplete
                                                                                                                        sourceOptionalValues)
                                                                                                                  have viewed :=
                                                                                                                    congrArg
                                                                                                                      (EbnfValue.optionalView
                                                                                                                        atomDotArgumentsExpression)
                                                                                                                      sourceOptionalSemanticEq
                                                                                                                  rw [present] at viewed
                                                                                                                  simp [EbnfValue.optionalView,
                                                                                                                    EbnfValue.optional] at viewed
                                                                                                          | scan sourceBefore _ _ _
                                                                                                              sourceScan _ _ =>
                                                                                                              have advanced :=
                                                                                                                sourceScan.advance.2.1
                                                                                                              change
                                                                                                                sourceDotWaiting.raw.dot.val =
                                                                                                                  sourceBefore.raw.dot.val + 1
                                                                                                                at advanced
                                                                                                              omega
                                                                                                          | complete sourceChildWaiting
                                                                                                              _ _ _ _ _
                                                                                                              sourceChildWitness _ _ _ =>
                                                                                                              have advanced :=
                                                                                                                sourceChildWitness.advance.2.1
                                                                                                              change
                                                                                                                sourceDotWaiting.raw.dot.val =
                                                                                                                  sourceChildWaiting.raw.dot.val + 1
                                                                                                                at advanced
                                                                                                              omega
                                                                          | atomLambda lambdaOrigin lambdaFinish
                                                                              sourceLambda =>
                                                                              have sourceBranchFour :
                                                                                  sourceChoiceBranch.val = 4 := by
                                                                                exact sourceBranchTagEq.trans
                                                                                  (atomLambdaInput_branchTag
                                                                                    { span := atomSpan
                                                                                      payload :=
                                                                                        .dotConstructor marker name
                                                                                          none })
                                                                              have sourceChoiceSiteEq :
                                                                                  sourceChoiceSite = atomRootChoiceSite := by
                                                                                cases sourceChoiceSite
                                                                                simp only [atomRootChoiceSite]
                                                                                  at sourceChoiceSiteRoot ⊢
                                                                                subst_vars
                                                                                rfl
                                                                              subst sourceChoiceSite
                                                                              have sourceChoiceBranchEq :
                                                                                  sourceChoiceBranch =
                                                                                    atomLambdaChoiceBranch := by
                                                                                apply Fin.ext
                                                                                exact sourceBranchFour
                                                                              subst sourceChoiceBranch
                                                                              have sourceChoiceBranchesEq :
                                                                                  atomRootChoiceSite.branchExpressions.toList =
                                                                                    EbnfExpr.children
                                                                                      (m2cV1.rhs .atom) :=
                                                                                EbnfExpr.choice.inj
                                                                                  sourceChoiceLayout
                                                                              have sourceChoiceLayoutProofEq :
                                                                                  sourceChoiceLayout =
                                                                                    congrArg EbnfExpr.choice
                                                                                      sourceChoiceBranchesEq :=
                                                                                Subsingleton.elim _ _
                                                                              have sourceChoiceInputEq :=
                                                                                sourceInputNormalizedEq
                                                                              rw [sourceChoiceLayoutProofEq]
                                                                                at sourceChoiceInputEq
                                                                              have sourceChoicePairEq :=
                                                                                choice_transport_pair_heq
                                                                                  sourceChoiceBranchesEq
                                                                                  (atomRootChoiceSite.branchListIndex
                                                                                    atomLambdaChoiceBranch)
                                                                                  sourceChoiceChildValue
                                                                                  atomLambdaRootBranch
                                                                                  (EbnfValue.ruleAtom .lambda
                                                                                    { span := atomSpan
                                                                                      payload :=
                                                                                        .dotConstructor marker name
                                                                                          none })
                                                                                  sourceChoiceInputEq
                                                                              have sourceChoiceChildSemanticHEq :
                                                                                  HEq sourceChoiceChildValue
                                                                                    (EbnfValue.ruleAtom .lambda
                                                                                      { span := atomSpan
                                                                                        payload :=
                                                                                          .dotConstructor marker name
                                                                                            none }) :=
                                                                                sourceChoicePairEq.2
                                                                              rw [atomLambdaChoiceBranch_site]
                                                                                at sourceBranchLhs
                                                                              obtain ⟨sourceLambdaAtomSite,
                                                                                  sourceBranchProduction,
                                                                                  sourceLambdaAtomSiteEq⟩ :=
                                                                                auxiliaryAtomProduction
                                                                                  sourceBranchFinished.raw.production
                                                                                  atomLambdaAtomSite.site
                                                                                  sourceBranchLhs
                                                                                  atomLambdaAtomSite.hasKind
                                                                              have sourceLambdaAtomSiteCanonical :
                                                                                  sourceLambdaAtomSite =
                                                                                    atomLambdaAtomSite := by
                                                                                cases sourceLambdaAtomSite
                                                                                simp only [atomLambdaAtomSite]
                                                                                  at sourceLambdaAtomSiteEq ⊢
                                                                                subst_vars
                                                                                rfl
                                                                              subst sourceLambdaAtomSite
                                                                              rcases sourceBranchFinished with
                                                                                ⟨⟨sourceBranchProductionId,
                                                                                  sourceBranchDot,
                                                                                  sourceBranchOriginBoundary,
                                                                                  sourceBranchCurrent⟩,
                                                                                  sourceBranchContext⟩
                                                                              simp only at sourceBranchProduction
                                                                              simp only at sourceBranchLhs
                                                                              simp only at sourceBranchOrigin
                                                                              subst sourceBranchProductionId
                                                                              cases sourceGrandchild with
                                                                              | reduce sourceLambdaAtomItem
                                                                                  sourceLambdaAtomValues
                                                                                  sourceLambdaAtomOutput
                                                                                  sourceLambdaAtomReached
                                                                                  sourceLambdaAtomComplete
                                                                                  sourceLambdaAtomCoherent
                                                                                  sourceLambdaAtomAction =>
                                                                                  have sourceLambdaAtomPackedEq :=
                                                                                    actionReduces_eleven_shapes_exact.mp
                                                                                      sourceLambdaAtomAction
                                                                                  change sourceBranchValue =
                                                                                    AtomSite.pack atomLambdaAtomSite
                                                                                      (PrefixValues.fullValue
                                                                                        { raw := {
                                                                                            production :=
                                                                                              .atom atomLambdaAtomSite
                                                                                            dot := sourceBranchDot
                                                                                            origin :=
                                                                                              sourceBranchOriginBoundary
                                                                                            current :=
                                                                                              sourceBranchCurrent }
                                                                                          context :=
                                                                                            sourceBranchContext }
                                                                                        sourceLambdaAtomComplete
                                                                                        sourceLambdaAtomValues)
                                                                                    at sourceLambdaAtomPackedEq
                                                                                  have sourceBranchSemanticHEq :
                                                                                      HEq sourceBranchValue
                                                                                        (EbnfValue.ruleAtom .lambda
                                                                                          { span := atomSpan
                                                                                            payload :=
                                                                                              .dotConstructor marker
                                                                                                name none }) :=
                                                                                    sourceChoiceChildValueHEq.symm.trans
                                                                                      sourceChoiceChildSemanticHEq
                                                                                  have sourceLambdaAtomShape :
                                                                                      atomLambdaAtomSite.atom =
                                                                                        .nonterminal .lambda := by
                                                                                    run_tac
                                                                                      Lean.Meta.withTransparency .all do
                                                                                        (← Lean.Elab.Tactic.getMainGoal).refl
                                                                                  have sourceLambdaOutputView :
                                                                                      EbnfValue.transport
                                                                                          (congrArg EbnfExpr.atom
                                                                                            sourceLambdaAtomShape)
                                                                                          (EbnfValue.atShape
                                                                                            atomLambdaAtomSite.expression_eq_atom
                                                                                            sourceBranchValue) =
                                                                                        EbnfValue.ruleAtom .lambda
                                                                                          { span := atomSpan
                                                                                            payload :=
                                                                                              .dotConstructor marker
                                                                                                name none } := by
                                                                                    calc
                                                                                      _ = EbnfValue.transport
                                                                                            (atomLambdaAtomSite.expression_eq_atom.trans
                                                                                              (congrArg EbnfExpr.atom
                                                                                                sourceLambdaAtomShape))
                                                                                            sourceBranchValue :=
                                                                                        EbnfValue.transport_trans _ _ _
                                                                                      _ = _ := eq_of_heq
                                                                                        ((cast_heq
                                                                                          (congrArg
                                                                                            (EbnfValue file tokens)
                                                                                            (atomLambdaAtomSite.expression_eq_atom.trans
                                                                                              (congrArg EbnfExpr.atom
                                                                                                sourceLambdaAtomShape)))
                                                                                          sourceBranchValue).trans
                                                                                          sourceBranchSemanticHEq)
                                                                                  let sourceLambdaAtomReduction :
                                                                                      CoherentReduction file tokens memo
                                                                                        correct final
                                                                                        { raw := {
                                                                                            production :=
                                                                                              .atom atomLambdaAtomSite
                                                                                            dot := sourceBranchDot
                                                                                            origin :=
                                                                                              sourceBranchOriginBoundary
                                                                                            current :=
                                                                                              sourceBranchCurrent }
                                                                                          context :=
                                                                                            sourceBranchContext }
                                                                                        sourceBranchValue :=
                                                                                    .reduce _ sourceLambdaAtomValues
                                                                                      sourceBranchValue
                                                                                      sourceLambdaAtomReached
                                                                                      sourceLambdaAtomComplete
                                                                                      sourceLambdaAtomCoherent
                                                                                      sourceLambdaAtomAction
                                                                                  have sourceLambdaRootCoherent :=
                                                                                    coherentAtomRule_child
                                                                                      sourceBranchDot
                                                                                      sourceBranchOriginBoundary
                                                                                      sourceBranchCurrent
                                                                                      sourceBranchContext
                                                                                      sourceLambdaAtomShape
                                                                                      (by decide)
                                                                                      sourceLambdaOutputView
                                                                                      sourceLambdaAtomReduction
                                                                                  cases sourceLambdaRootCoherent with
                                                                                  | reduce _ _ _ _ _ _ sourceLambdaAction =>
                                                                                      cases sourceLambdaAction with
                                                                                      | root _ _ _ _ _ sourceLambdaReduces =>
                                                                                          generalize sourceLambdaInputEq :
                                                                                              RootAction.unpack .lambda _ =
                                                                                                sourceLambdaInputValue
                                                                                            at sourceLambdaReduces
                                                                                          generalize sourceLambdaOutputEq :
                                                                                              ({ span := atomSpan,
                                                                                                  payload :=
                                                                                                    .dotConstructor marker
                                                                                                      name none } :
                                                                                                Expression) =
                                                                                                sourceLambdaOutput
                                                                                            at sourceLambdaReduces
                                                                                          cases sourceLambdaReduces
                                                                                          have payloadEq := congrArg
                                                                                            (fun value : Expression =>
                                                                                              value.payload)
                                                                                            sourceLambdaOutputEq
                                                                                          cases payloadEq
                                                                  | scan sourceRootBefore _ _ _
                                                                      sourceRootScan _ _ =>
                                                                      have advanced :=
                                                                        sourceRootScan.advance.2.1
                                                                      change sourceRootWaiting.raw.dot.val =
                                                                        sourceRootBefore.raw.dot.val + 1
                                                                        at advanced
                                                                      omega
                                                                  | complete sourceRootChildWaiting
                                                                      _ _ _ _ _
                                                                      sourceRootChildWitness _ _ _ =>
                                                                      have advanced :=
                                                                        sourceRootChildWitness.advance.2.1
                                                                      change sourceRootWaiting.raw.dot.val =
                                                                        sourceRootChildWaiting.raw.dot.val + 1
                                                                        at advanced
                                                                      omega
                                                      | scan sourceBefore
                                                          sourceAfter sourceCursor
                                                          sourcePriorValues
                                                          sourceScanWitness
                                                          sourceScanEdge
                                                          sourceScanPrior =>
                                                          have advanced :=
                                                            sourceScanWitness.advance.2.1
                                                          change
                                                            sourceWaiting.raw.dot.val =
                                                              sourceBefore.raw.dot.val + 1
                                                            at advanced
                                                          omega
                                                      | complete sourceChildWaiting
                                                          sourceChildFinished
                                                          sourceChildAfter
                                                          sourceChildShared
                                                          sourceChildPrior
                                                          sourceChildValue
                                                          sourceChildWitness
                                                          sourceChildEdge
                                                          sourceChildPrefix
                                                          sourceGrandchild =>
                                                          have advanced :=
                                                            sourceChildWitness.advance.2.1
                                                          change
                                                            sourceWaiting.raw.dot.val =
                                                              sourceChildWaiting.raw.dot.val + 1
                                                            at advanced
                                                          omega
                                    | scan before after cursor priorValues
                                        scanWitness scanEdge scanPrior =>
                                        have advanced :=
                                          scanWitness.advance.2.1
                                        change atomWaiting.raw.dot.val =
                                          before.raw.dot.val + 1 at advanced
                                        omega
                                    | complete childWaiting childFinished
                                        childAfter childShared childPrior
                                        childValue childWitness childEdge
                                        childPrefix childReduction =>
                                        have advanced :=
                                          childWitness.advance.2.1
                                        change atomWaiting.raw.dot.val =
                                          childWaiting.raw.dot.val + 1
                                          at advanced
                                        omega
                    | scan before after cursor priorValues witness edge prior =>
                        rcases witness.advance with
                          ⟨priorProduction, priorDot, priorOrigin,
                            priorCurrent⟩
                        have waitingDot : waiting.raw.dot.val = 0 := by
                          exact congrArg Fin.val dotEq
                        omega
                    | complete atomWaiting atomFinished atomAfter atomShared
                        atomPrior atomValue atomWitness atomEdge atomPrefix
                        atomChild =>
                        have waitingDot : waiting.raw.dot.val = 0 := by
                          exact congrArg Fin.val dotEq
                        rcases atomWitness.advance with
                          ⟨atomProduction, atomDot, atomOrigin,
                            atomCurrent⟩
                        omega

/-- Coherent postfix folding preserves every retained token. -/
theorem postfix_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout .postfix := by
  intro file tokens memo correct final origin finish context priorValues output
    complete owned _lexical coherent reduces inputEvidence
  generalize inputEq : RootAction.unpack .postfix
    (PrefixValues.fullValue
      (CanonicalCompleteRootItem tokens .postfix origin finish context)
      complete priorValues) = input at reduces
  cases reduces with
  | «postfix» origin finish atom parts =>
      have sourceEvidence : TokenPlanEvidence
          (postfixFoldSourceTokenPlan? atom parts)
          (PhysicalTokens tokens origin finish) := by
        apply inputEvidence.candidate_eq
        calc
          PrefixValues.tokenPlan? sourceRuleTokenPlanLayout
              (CanonicalCompleteRootItem tokens .postfix
                origin finish context) priorValues =
              (RootAction.unpack .postfix
                (PrefixValues.fullValue
                  (CanonicalCompleteRootItem tokens .postfix
                    origin finish context) complete priorValues)).tokenPlan?
                  sourceRuleTokenPlanLayout := by
                    symm
                    rw [RootAction.unpack_tokenPlan?]
                    exact PrefixValues.tokenPlan?_fullValue
                      sourceRuleTokenPlanLayout _ complete priorValues
          _ = (postfixSourceValue atom parts).tokenPlan?
                sourceRuleTokenPlanLayout :=
              congrArg (EbnfValue.tokenPlan?
                sourceRuleTokenPlanLayout) inputEq
          _ = postfixFoldSourceTokenPlan? atom parts :=
              postfixSourceValue_tokenPlan? atom parts
      have admissible := coherentPostfix_admissible complete owned atom parts
        sourceEvidence coherent inputEq
      simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
        postfixFold_tokenPlanEvidence atom parts admissible owned sourceEvidence

end Solcore.Surface.Multi
