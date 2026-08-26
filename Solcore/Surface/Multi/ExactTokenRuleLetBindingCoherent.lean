import Solcore.Surface.Multi.AuxiliaryInversion
import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenReachability
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Lean.Elab.Tactic

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSimpArgs false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

universe u

local macro "solve_let_binding_site" : tactic => `(tactic|
  simp [GrammarSiteKey.valid, GrammarSite.expression, m2cV1, m2cV1Rhs,
    EbnfExpr.nodeAt?, EbnfExpr.children, EbnfExpr.kind,
    Grammar.terminal, Grammar.hardKeyword, Grammar.contextualKeyword,
    Grammar.pragmaName, Grammar.symbol, Grammar.category,
    Grammar.nonterminal, Grammar.sequence, Grammar.choice, Grammar.group,
    Grammar.optional, Grammar.star, Grammar.plus, Grammar.list0,
    Grammar.list1, Grammar.identifier, Grammar.pathComponent])

private theorem matchedIdentifier_physicalTokenPlan_local
    {file : WorkspaceFile} {tokens : List Token}
    (matched : MatchedTerminal file tokens (.category .identifier))
    (spelling : String) (parsed : Identifier)
    (projects : IdentifierProjects matched spelling parsed) :
    matched.physicalTokenPlan =
      identifierPlan (RuleReduction.terminalLoc matched parsed) := by
  rcases projects with ⟨token, valueEq, payloadEq, parseEq⟩
  have spellingEq : spelling = parsed.render := by
    unfold Identifier.parse at parseEq
    split at parseEq
    · have parsedEq := Option.some.inj parseEq
      rw [← parsedEq]
      rfl
    · contradiction
  simp [MatchedTerminal.physicalTokenPlan, identifierPlan,
    RuleReduction.terminalLoc, valueEq, payloadEq, spellingEq]

private theorem matchedContextualKeyword_physicalTokenPlan_local
    {file : WorkspaceFile} {tokens : List Token}
    (keyword : ContextualKeyword)
    (matched : MatchedTerminal file tokens (.contextualKeyword keyword)) :
    matched.physicalTokenPlan =
      TokenPlan.exact (.identifier keyword.spelling) matched.span := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, matchedEvidence⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      simp [MatchedTerminal.physicalTokenPlan, TerminalMatches]
        at matchedEvidence ⊢
      rw [matchedEvidence]
  | endOfFile atEnd =>
      simp [TerminalMatches] at matchedEvidence

private def letRootSequenceSite : SequenceSite := {
  site := GrammarSite.root .letBinding
  hasKind := by
    rw [GrammarSite.root_expression]
    rfl
}

private def letTypeOptionalSite : OptionalSite := {
  site := ⟨{ rule := .letBinding, path := [2] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letTypeSequenceSite : SequenceSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letComptimeOptionalSite : OptionalSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0, 1] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letTypeAtomSite : AtomSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0, 2] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letKeywordAtomSite : AtomSite := {
  site := ⟨{ rule := .letBinding, path := [0] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letNameAtomSite : AtomSite := {
  site := ⟨{ rule := .letBinding, path := [1] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letInitializerOptionalSite : OptionalSite := {
  site := ⟨{ rule := .letBinding, path := [3] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letColonAtomSite : AtomSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0, 0] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def letComptimeAtomSite : AtomSite := {
  site := ⟨{ rule := .letBinding, path := [2, 0, 1, 0] },
    by solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def typeRootChoiceSite : ChoiceSite := {
  site := GrammarSite.root .type
  hasKind := by
    rw [GrammarSite.root_expression]
    rfl
}

private def typePlainChoiceBranch : Fin typeRootChoiceSite.branchCount :=
  ⟨1, by
    unfold typeRootChoiceSite ChoiceSite.branchCount
    rw [GrammarSite.root_expression]
    change 1 < 2
    omega⟩

private def typePlainSequenceSite : SequenceSite := {
  site := ⟨{ rule := .type, path := [1] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def typePlainTypeAtomSite : AtomSite := {
  site := ⟨{ rule := .type, path := [1, 0] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private def typePlainArrowOptionalSite : OptionalSite := {
  site := ⟨{ rule := .type, path := [1, 1] }, by
    solve_let_binding_site⟩
  hasKind := by solve_let_binding_site
}

private theorem typePlainChoiceBranch_site :
    typeRootChoiceSite.branch typePlainChoiceBranch =
      typePlainSequenceSite.site := by
  rfl

private theorem typePlainSequenceSite_children :
    typePlainSequenceSite.children = [
      typePlainTypeAtomSite.site,
      typePlainArrowOptionalSite.site] := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem letRootSequenceSite_children :
    letRootSequenceSite.children = [
      letKeywordAtomSite.site,
      letNameAtomSite.site,
      letTypeOptionalSite.site,
      letInitializerOptionalSite.site] := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem letTypeSequenceSite_children :
    letTypeSequenceSite.children = [
      letColonAtomSite.site,
      letComptimeOptionalSite.site,
      letTypeAtomSite.site] := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem letTypeOptionalSite_child :
    letTypeOptionalSite.child = letTypeSequenceSite.site := by
  rfl

private theorem production_eq_sequence_of_lhs
    (site : SequenceSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    production = .seq site := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | sequence refined same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact exact

private theorem production_eq_atom_of_lhs_local
    (site : AtomSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    production = .atom site := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | atom refined same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact exact

private theorem production_eq_root_of_lhs_local
    (rule : GrammarRuleId) (production : ProductionId)
    (lhs : production.lhs = .rule rule) :
    production = .root rule := by
  cases production with
  | root other =>
      have same := NonterminalSymbol.rule.inj lhs
      subst other
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

private theorem production_optional_of_lhs
    (site : OptionalSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    ∃ branch, production = .opt site branch := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | optional refined branch same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact ⟨branch, exact⟩

private theorem production_choice_of_lhs_local
    (site : ChoiceSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    ∃ branch, production = .choice site branch := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | choice refined branch same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact ⟨branch, exact⟩

private theorem GrammarSymbolValues.transport_append_four_to
    {file : WorkspaceFile} {tokens : List Token}
    {prior middle full target : List GrammarSymbol}
    {first second third fourth : GrammarSymbol}
    (priorLayout : prior = [first, second])
    (middleLayout : prior ++ [third] = middle)
    (fullLayout : middle ++ [fourth] = full)
    (viewLayout : full = target)
    (targetLayout : target = [first, second, third, fourth])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second)
    (thirdValue : GrammarSymbolValue file tokens third)
    (fourthValue : GrammarSymbolValue file tokens fourth) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport middleLayout
              (GrammarSymbolValues.append
                (GrammarSymbolValues.transport priorLayout.symm
                  (firstValue, (secondValue, ())))
                (thirdValue, ())))
            (fourthValue, ()))) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, (thirdValue, (fourthValue, ())))) := by
  subst prior
  subst middle
  subst full
  subst target
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem GrammarSymbolValues.transport_append_three_to
    {file : WorkspaceFile} {tokens : List Token}
    {prior middle full target : List GrammarSymbol}
    {first second third : GrammarSymbol}
    (priorLayout : prior = [first])
    (middleLayout : prior ++ [second] = middle)
    (fullLayout : middle ++ [third] = full)
    (viewLayout : full = target)
    (targetLayout : target = [first, second, third])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second)
    (thirdValue : GrammarSymbolValue file tokens third) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport middleLayout
              (GrammarSymbolValues.append
                (GrammarSymbolValues.transport priorLayout.symm
                  (firstValue, ()))
                (secondValue, ())))
            (thirdValue, ()))) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, (thirdValue, ()))) := by
  subst prior
  subst middle
  subst full
  subst target
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem GrammarSymbolValues.transport_append_two_from_empty_to
    {file : WorkspaceFile} {tokens : List Token}
    {prior middle full target : List GrammarSymbol}
    {first second : GrammarSymbol}
    (priorLayout : prior = [])
    (middleLayout : prior ++ [first] = middle)
    (fullLayout : middle ++ [second] = full)
    (viewLayout : full = target)
    (targetLayout : target = [first, second])
    (empty : GrammarSymbolValues file tokens [])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport middleLayout
              (GrammarSymbolValues.append
                (GrammarSymbolValues.transport priorLayout.symm empty)
                (firstValue, ())))
            (secondValue, ()))) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, ())) := by
  subst prior
  subst middle
  subst full
  subst target
  rcases empty with ⟨⟩
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem GrammarSymbolValues.transport_append_empty_single_to_local
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol}
    (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full)
    (viewLayout : full = [target]) (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens [])
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport priorLayout.symm empty)
            (value, ()))) =
      (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout)
        value, ()) := by
  cases priorLayout
  cases symbolLayout
  cases viewLayout
  rcases empty with ⟨⟩
  have fullProof : fullLayout = rfl := Subsingleton.elim _ _
  rw [fullProof]
  rfl

private theorem root_sequenceTransport_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (site : SequenceSite)
    (siteRoot : site.site = GrammarSite.root rule)
    (layout : EbnfExpr.sequence
        (site.children.map GrammarSite.expression) = m2cV1.rhs rule)
    (value : EbnfValue file tokens
      (.sequence (site.children.map GrammarSite.expression))) :
    EbnfValue.atShape (GrammarSite.root_expression rule)
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg (fun child =>
              GrammarSymbol.nonterminal (.aux child)) siteRoot))
          (EbnfValue.ofShape site.expression_eq_sequence value)) =
      EbnfValue.transport layout value := by
  let packed := EbnfValue.ofShape site.expression_eq_sequence value
  have outerAligned :
      EbnfValue.atShape (GrammarSite.root_expression rule)
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
              (congrArg (fun child =>
                GrammarSymbol.nonterminal (.aux child)) siteRoot)) packed) =
        EbnfValue.atShape (GrammarSite.root_expression rule)
          (EbnfValue.transport
            (congrArg GrammarSite.expression siteRoot) packed) :=
    congrArg (EbnfValue.atShape
      (GrammarSite.root_expression rule))
      (auxiliaryValue_transport_eq siteRoot packed)
  rw [outerAligned]
  unfold EbnfValue.atShape packed EbnfValue.ofShape
  rw [EbnfValue.transport_trans, EbnfValue.transport_trans]

private theorem root_choiceTransport_eq_local
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
    congrArg (EbnfValue.atShape
      (GrammarSite.root_expression rule))
      (auxiliaryValue_transport_eq siteRoot packed)
  rw [outerAligned]
  unfold EbnfValue.atShape packed EbnfValue.ofShape
  rw [EbnfValue.transport_trans, EbnfValue.transport_trans]

private abbrev letKeywordExpr : EbnfExpr :=
  Grammar.hardKeyword .letKw

private abbrev letNameExpr : EbnfExpr :=
  Grammar.identifier

private abbrev letColonExpr : EbnfExpr :=
  Grammar.symbol .colon

private abbrev letComptimeExpr : EbnfExpr :=
  Grammar.contextualKeyword .comptimeKw

private abbrev letTypeExpr : EbnfExpr :=
  Grammar.nonterminal .type

private abbrev typeComptimeBranchExpr : EbnfExpr :=
  Grammar.sequence [Grammar.contextualKeyword .comptimeKw,
    Grammar.nonterminal .type]

private abbrev typePlainBranchExpr : EbnfExpr :=
  Grammar.sequence [Grammar.nonterminal .typeAtom,
    Grammar.optional (Grammar.sequence [Grammar.symbol .arrow,
      Grammar.nonterminal .type])]

private theorem typePlainSequenceSite_shape :
    typePlainSequenceSite.site.expression = typePlainBranchExpr := by
  simp [typePlainSequenceSite, GrammarSite.expression,
    GrammarSiteKey.valid, m2cV1, m2cV1Rhs, EbnfExpr.nodeAt?,
    EbnfExpr.children, Grammar.choice]

private def typeRootBranchTag
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .type)) : Nat :=
  (EbnfValue.choiceView [typeComptimeBranchExpr, typePlainBranchExpr]
    (EbnfValue.transport (by rfl) input)).1.val

private theorem choiceView_transport_branch_val_local
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

private theorem typeRootBranchTag_zero_local
    {file : WorkspaceFile} {tokens : List Token}
    (value : EbnfValue file tokens typeComptimeBranchExpr) :
    typeRootBranchTag
      (EbnfValue.transport (by rfl)
        (EbnfValue.choice
          [typeComptimeBranchExpr, typePlainBranchExpr]
          ⟨0, value⟩)) = 0 := by
  simp [typeRootBranchTag, EbnfValue.choiceView, EbnfValue.choice,
    EbnfValue.transport, cast_cast]

private theorem typeRootBranchTag_one_local
    {file : WorkspaceFile} {tokens : List Token}
    (value : EbnfValue file tokens typePlainBranchExpr) :
    typeRootBranchTag
      (EbnfValue.transport (by rfl)
        (EbnfValue.choice
          [typeComptimeBranchExpr, typePlainBranchExpr]
          ⟨1, value⟩)) = 1 := by
  simp [typeRootBranchTag, EbnfValue.choiceView, EbnfValue.choice,
    EbnfValue.transport, cast_cast]

private theorem typeRootChoiceLayout_local :
    EbnfExpr.choice typeRootChoiceSite.branchExpressions.toList =
      m2cV1.rhs .type :=
  typeRootChoiceSite.expression_eq_choice.symm.trans
    (GrammarSite.root_expression .type)

private theorem choice_transport_pair_heq_local
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

private abbrev letTypeSequenceExpr : EbnfExpr :=
  Grammar.sequence [letColonExpr, Grammar.optional letComptimeExpr,
    letTypeExpr]

private abbrev letEqualExpr : EbnfExpr :=
  Grammar.symbol .equal

private abbrev letInitializerExpressionExpr : EbnfExpr :=
  Grammar.nonterminal .expression

private abbrev letInitializerSequenceExpr : EbnfExpr :=
  Grammar.sequence [letEqualExpr, letInitializerExpressionExpr]

private abbrev letBindingChildren : List EbnfExpr := [
  letKeywordExpr,
  letNameExpr,
  .optional letTypeSequenceExpr,
  .optional letInitializerSequenceExpr]

private theorem letBindingRootLayout :
    EbnfExpr.sequence [
      Grammar.hardKeyword .letKw, Grammar.identifier,
      Grammar.optional (Grammar.sequence [Grammar.symbol .colon,
        Grammar.optional (Grammar.contextualKeyword .comptimeKw),
        Grammar.nonterminal .type]),
      Grammar.optional (Grammar.sequence [Grammar.symbol .equal,
        Grammar.nonterminal .expression])] =
      m2cV1.rhs .letBinding := by
  rfl

private def letBindingInitializerValue
    {file : WorkspaceFile} {tokens : List Token}
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression)) :
    EbnfValue file tokens (.optional letInitializerSequenceExpr) :=
  EbnfValue.optional letInitializerSequenceExpr <|
    initializer.map fun value =>
      EbnfValue.sequence [letEqualExpr, letInitializerExpressionExpr] <|
        EbnfValues.cons _ _
          (EbnfValue.terminalAtom (.symbol .equal) value.1) <|
        EbnfValues.cons _ _
          (EbnfValue.ruleAtom .expression value.2) <|
        EbnfValues.nil

private def letBindingUntypedInput
    {file : WorkspaceFile} {tokens : List Token}
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression)) :
    EbnfValue file tokens (m2cV1.rhs .letBinding) :=
  EbnfValue.transport letBindingRootLayout <|
    EbnfValue.sequence letBindingChildren <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.category .identifier) name) <|
      EbnfValues.cons _ _
        (EbnfValue.optional letTypeSequenceExpr none) <|
      EbnfValues.cons _ _
        (letBindingInitializerValue initializer) <|
      EbnfValues.nil

private def letBindingTypedInput
    {file : WorkspaceFile} {tokens : List Token}
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression)) :
    EbnfValue file tokens (m2cV1.rhs .letBinding) :=
  EbnfValue.transport letBindingRootLayout <|
    EbnfValue.sequence letBindingChildren <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.category .identifier) name) <|
      EbnfValues.cons _ _
        (EbnfValue.optional letTypeSequenceExpr <| some <|
          EbnfValue.sequence
            [letColonExpr, .optional letComptimeExpr, letTypeExpr] <|
            EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .colon) colon) <|
            EbnfValues.cons _ _
              (EbnfValue.optional letComptimeExpr none) <|
            EbnfValues.cons _ _
              (EbnfValue.ruleAtom .type typeValue) <|
            EbnfValues.nil) <|
      EbnfValues.cons _ _
        (letBindingInitializerValue initializer) <|
      EbnfValues.nil

private def letBindingComptimeInput
    {file : WorkspaceFile} {tokens : List Token}
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (comptime : MatchedTerminal file tokens
      (.contextualKeyword .comptimeKw))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression)) :
    EbnfValue file tokens (m2cV1.rhs .letBinding) :=
  EbnfValue.transport letBindingRootLayout <|
    EbnfValue.sequence letBindingChildren <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.hardKeyword .letKw) letKeyword) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.category .identifier) name) <|
      EbnfValues.cons _ _
        (EbnfValue.optional letTypeSequenceExpr <| some <|
          EbnfValue.sequence
            [letColonExpr, .optional letComptimeExpr, letTypeExpr] <|
            EbnfValues.cons _ _
              (EbnfValue.terminalAtom (.symbol .colon) colon) <|
            EbnfValues.cons _ _
              (EbnfValue.optional letComptimeExpr <| some <|
                EbnfValue.terminalAtom (.contextualKeyword .comptimeKw)
                  comptime) <|
            EbnfValues.cons _ _
              (EbnfValue.ruleAtom .type typeValue) <|
            EbnfValues.nil) <|
      EbnfValues.cons _ _
        (letBindingInitializerValue initializer) <|
      EbnfValues.nil

private def letBindingTypeField
    {file : WorkspaceFile} {tokens : List Token}
    (input : EbnfValue file tokens (m2cV1.rhs .letBinding)) :
    EbnfValue file tokens (Grammar.optional (Grammar.sequence [
      Grammar.symbol .colon,
      Grammar.optional (Grammar.contextualKeyword .comptimeKw),
      Grammar.nonterminal .type])) :=
  (EbnfValue.sequence4View (Grammar.hardKeyword .letKw)
    Grammar.identifier
    (Grammar.optional (Grammar.sequence [Grammar.symbol .colon,
      Grammar.optional (Grammar.contextualKeyword .comptimeKw),
      Grammar.nonterminal .type]))
    (Grammar.optional (Grammar.sequence [Grammar.symbol .equal,
      Grammar.nonterminal .expression]))
    (EbnfValue.transport letBindingRootLayout.symm input)).2.2.1

private theorem sequence4View_transport_four_eq
    {file : WorkspaceFile} {tokens : List Token}
    {firstSource secondSource thirdSource fourthSource : EbnfExpr}
    {firstTarget secondTarget thirdTarget fourthTarget : EbnfExpr}
    (firstEq : firstSource = firstTarget)
    (secondEq : secondSource = secondTarget)
    (thirdEq : thirdSource = thirdTarget)
    (fourthEq : fourthSource = fourthTarget)
    (layout : [firstSource, secondSource, thirdSource, fourthSource] =
      [firstTarget, secondTarget, thirdTarget, fourthTarget])
    (values : EbnfValues file tokens
      [firstSource, secondSource, thirdSource, fourthSource]) :
    EbnfValue.sequence4View firstTarget secondTarget thirdTarget fourthTarget
        (EbnfValue.transport (congrArg EbnfExpr.sequence layout)
          (EbnfValue.sequence
            [firstSource, secondSource, thirdSource, fourthSource] values)) =
      (EbnfValue.transport firstEq
          (EbnfValues.consView firstSource
            [secondSource, thirdSource, fourthSource] values).1,
        EbnfValue.transport secondEq
          (EbnfValues.consView secondSource [thirdSource, fourthSource]
            (EbnfValues.consView firstSource
              [secondSource, thirdSource, fourthSource] values).2).1,
        EbnfValue.transport thirdEq
          (EbnfValues.consView thirdSource [fourthSource]
            (EbnfValues.consView secondSource [thirdSource, fourthSource]
              (EbnfValues.consView firstSource
                [secondSource, thirdSource, fourthSource] values).2).2).1,
        EbnfValue.transport fourthEq
          (EbnfValues.consView fourthSource []
            (EbnfValues.consView thirdSource [fourthSource]
              (EbnfValues.consView secondSource [thirdSource, fourthSource]
                (EbnfValues.consView firstSource
                  [secondSource, thirdSource, fourthSource] values).2).2).2).1) := by
  cases firstEq
  cases secondEq
  cases thirdEq
  cases fourthEq
  have exactLayout : layout = rfl := Subsingleton.elim _ _
  rw [exactLayout]
  simp [EbnfValue.sequence4View, EbnfValue.sequenceView,
    EbnfValue.sequence, EbnfValue.transport_self]

private theorem sequence3View_transport_three_eq
    {file : WorkspaceFile} {tokens : List Token}
    {firstSource secondSource thirdSource : EbnfExpr}
    {firstTarget secondTarget thirdTarget : EbnfExpr}
    (firstEq : firstSource = firstTarget)
    (secondEq : secondSource = secondTarget)
    (thirdEq : thirdSource = thirdTarget)
    (layout : [firstSource, secondSource, thirdSource] =
      [firstTarget, secondTarget, thirdTarget])
    (values : EbnfValues file tokens
      [firstSource, secondSource, thirdSource]) :
    EbnfValue.sequence3View firstTarget secondTarget thirdTarget
        (EbnfValue.transport (congrArg EbnfExpr.sequence layout)
          (EbnfValue.sequence [firstSource, secondSource, thirdSource]
            values)) =
      (EbnfValue.transport firstEq
          (EbnfValues.consView firstSource
            [secondSource, thirdSource] values).1,
        EbnfValue.transport secondEq
          (EbnfValues.consView secondSource [thirdSource]
            (EbnfValues.consView firstSource
              [secondSource, thirdSource] values).2).1,
        EbnfValue.transport thirdEq
          (EbnfValues.consView thirdSource []
            (EbnfValues.consView secondSource [thirdSource]
              (EbnfValues.consView firstSource
                [secondSource, thirdSource] values).2).2).1) := by
  cases firstEq
  cases secondEq
  cases thirdEq
  have exactLayout : layout = rfl := Subsingleton.elim _ _
  rw [exactLayout]
  simp [EbnfValue.sequence3View, EbnfValue.sequenceView,
    EbnfValue.sequence, EbnfValue.transport_self]

private theorem sequence3View_three_second_third
    {file : WorkspaceFile} {tokens : List Token}
    (first second third : EbnfExpr)
    (firstValue : EbnfValue file tokens first)
    (secondValue : EbnfValue file tokens second)
    (thirdValue : EbnfValue file tokens third) :
    (EbnfValue.sequence3View first second third
      (EbnfValue.sequence [first, second, third]
        (EbnfValues.cons first [second, third] firstValue
          (EbnfValues.cons second [third] secondValue
            (EbnfValues.cons third [] thirdValue
              EbnfValues.nil))))).2 =
      (secondValue, thirdValue) := by
  have rebuilt := EbnfValue.sequence3_of_view first second third
    (EbnfValue.sequence [first, second, third]
      (EbnfValues.cons first [second, third] firstValue
        (EbnfValues.cons second [third] secondValue
          (EbnfValues.cons third [] thirdValue EbnfValues.nil))))
  have valuesEq := EbnfValue.sequence_injective _ rebuilt
  have tailEq := (EbnfValues.cons_injective _ _ valuesEq).2
  apply Prod.ext
  · exact (EbnfValues.cons_injective _ _ tailEq).1
  · exact (EbnfValues.cons_injective _ _
      (EbnfValues.cons_injective _ _ tailEq).2).1

private theorem sequence2View_pair_first_local
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (firstValue : EbnfValue file tokens first)
    (secondValue : EbnfValue file tokens second) :
    (EbnfValue.sequence2View first second
      (EbnfValue.sequence [first, second]
        (EbnfValues.cons first [second] firstValue
          (EbnfValues.cons second [] secondValue
            EbnfValues.nil)))).1 = firstValue := by
  have rebuilt := EbnfValue.sequence2_of_view first second
    (EbnfValue.sequence [first, second]
      (EbnfValues.cons first [second] firstValue
        (EbnfValues.cons second [] secondValue EbnfValues.nil)))
  have valuesEq := EbnfValue.sequence_injective _ rebuilt
  exact (EbnfValues.cons_injective _ _ valuesEq).1

private theorem typePlainSequenceFirst_auxiliary_two_eq
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite}
    {firstLhs secondLhs : NonterminalSymbol}
    (childrenEq : children = [typePlainTypeAtomSite.site,
      typePlainArrowOptionalSite.site])
    (firstEq : typePlainTypeAtomSite.site.expression =
      Grammar.nonterminal .typeAtom)
    (secondEq : typePlainArrowOptionalSite.site.expression =
      Grammar.optional (Grammar.sequence [Grammar.symbol .arrow,
        Grammar.nonterminal .type]))
    (firstLhsEq : firstLhs = .aux typePlainTypeAtomSite.site)
    (secondLhsEq : secondLhs = .aux typePlainArrowOptionalSite.site)
    (symbolLayout : children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal firstLhs, .nonterminal secondLhs])
    (expressionLayout : children.map GrammarSite.expression = [
      Grammar.nonterminal .typeAtom,
      Grammar.optional (Grammar.sequence [Grammar.symbol .arrow,
        Grammar.nonterminal .type])])
    (firstValue : GrammarSymbolValue file tokens (.nonterminal firstLhs))
    (secondValue : GrammarSymbolValue file tokens (.nonterminal secondLhs)) :
    (EbnfValue.sequence2View (Grammar.nonterminal .typeAtom)
      (Grammar.optional (Grammar.sequence [Grammar.symbol .arrow,
        Grammar.nonterminal .type]))
      (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
        (EbnfValue.sequence (children.map GrammarSite.expression)
          (EbnfValues.ofAuxiliaries children
            (GrammarSymbolValues.transport symbolLayout.symm
              (firstValue, (secondValue, ()))))))).1 =
      EbnfValue.atShape firstEq
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
          (congrArg GrammarSymbol.nonterminal firstLhsEq)) firstValue) := by
  subst children
  subst firstLhs
  subst secondLhs
  simp only [List.map] at expressionLayout ⊢
  have canonicalExpressionLayout : [
      typePlainTypeAtomSite.site.expression,
      typePlainArrowOptionalSite.site.expression] = [
        Grammar.nonterminal .typeAtom,
        Grammar.optional (Grammar.sequence [Grammar.symbol .arrow,
          Grammar.nonterminal .type])] := by
    simpa using expressionLayout
  have expressionProof : expressionLayout = canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProof]
  have symbolProof : symbolLayout = rfl := Subsingleton.elim _ _
  rw [symbolProof]
  simp only [GrammarSymbolValues.transport_self]
  rw [sequence2View_transport_pair_eq firstEq secondEq
    canonicalExpressionLayout]
  simp [EbnfValues.consView, EbnfValues.ofAuxiliaries,
    EbnfValue.atShape]
  apply congrArg (EbnfValue.transport firstEq)
  symm
  exact cast_eq _ _

private theorem sequence4View_four_third
    {file : WorkspaceFile} {tokens : List Token}
    (first second third fourth : EbnfExpr)
    (firstValue : EbnfValue file tokens first)
    (secondValue : EbnfValue file tokens second)
    (thirdValue : EbnfValue file tokens third)
    (fourthValue : EbnfValue file tokens fourth) :
    (EbnfValue.sequence4View first second third fourth
      (EbnfValue.sequence [first, second, third, fourth]
        (EbnfValues.cons first [second, third, fourth] firstValue
          (EbnfValues.cons second [third, fourth] secondValue
            (EbnfValues.cons third [fourth] thirdValue
              (EbnfValues.cons fourth [] fourthValue
                EbnfValues.nil)))))).2.2.1 = thirdValue := by
  have rebuilt := EbnfValue.sequence4_of_view first second third fourth
    (EbnfValue.sequence [first, second, third, fourth]
      (EbnfValues.cons first [second, third, fourth] firstValue
        (EbnfValues.cons second [third, fourth] secondValue
          (EbnfValues.cons third [fourth] thirdValue
            (EbnfValues.cons fourth [] fourthValue EbnfValues.nil)))))
  have valuesEq := EbnfValue.sequence_injective _ rebuilt
  have tailEq := (EbnfValues.cons_injective _ _ valuesEq).2
  have secondTailEq := (EbnfValues.cons_injective _ _ tailEq).2
  exact (EbnfValues.cons_injective _ _ secondTailEq).1

private theorem letBindingTypeField_auxiliary_four_eq
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite}
    {thirdLhs fourthLhs : NonterminalSymbol}
    (childrenEq : children = [letKeywordAtomSite.site,
      letNameAtomSite.site, letTypeOptionalSite.site,
      letInitializerOptionalSite.site])
    (firstEq : letKeywordAtomSite.site.expression =
      Grammar.hardKeyword .letKw)
    (secondEq : letNameAtomSite.site.expression = Grammar.identifier)
    (thirdEq : letTypeOptionalSite.site.expression =
      Grammar.optional (Grammar.sequence [Grammar.symbol .colon,
        Grammar.optional (Grammar.contextualKeyword .comptimeKw),
        Grammar.nonterminal .type]))
    (fourthEq : letInitializerOptionalSite.site.expression =
      Grammar.optional (Grammar.sequence [Grammar.symbol .equal,
        Grammar.nonterminal .expression]))
    (thirdLhsEq : thirdLhs = .aux letTypeOptionalSite.site)
    (fourthLhsEq : fourthLhs = .aux letInitializerOptionalSite.site)
    (symbolLayout : children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal (.aux letKeywordAtomSite.site),
      .nonterminal (.aux letNameAtomSite.site),
      .nonterminal thirdLhs, .nonterminal fourthLhs])
    (expressionLayout : children.map GrammarSite.expression = [
      Grammar.hardKeyword .letKw, Grammar.identifier,
      Grammar.optional (Grammar.sequence [Grammar.symbol .colon,
        Grammar.optional (Grammar.contextualKeyword .comptimeKw),
        Grammar.nonterminal .type]),
      Grammar.optional (Grammar.sequence [Grammar.symbol .equal,
        Grammar.nonterminal .expression])])
    (layout : EbnfExpr.sequence (children.map GrammarSite.expression) =
      m2cV1.rhs .letBinding)
    (firstValue : GrammarSymbolValue file tokens
      (.nonterminal (.aux letKeywordAtomSite.site)))
    (secondValue : GrammarSymbolValue file tokens
      (.nonterminal (.aux letNameAtomSite.site)))
    (thirdValue : GrammarSymbolValue file tokens (.nonterminal thirdLhs))
    (fourthValue : GrammarSymbolValue file tokens (.nonterminal fourthLhs)) :
    letBindingTypeField
        (EbnfValue.transport layout
          (EbnfValue.sequence (children.map GrammarSite.expression)
            (EbnfValues.ofAuxiliaries children
              (GrammarSymbolValues.transport symbolLayout.symm
                (firstValue, (secondValue,
                  (thirdValue, (fourthValue, ())))))))) =
      EbnfValue.atShape thirdEq
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
          (congrArg GrammarSymbol.nonterminal thirdLhsEq)) thirdValue) := by
  subst children
  subst thirdLhs
  subst fourthLhs
  simp only [List.map] at expressionLayout layout ⊢
  unfold letBindingTypeField
  rw [EbnfValue.transport_trans]
  have layoutProof : layout.trans letBindingRootLayout.symm =
      congrArg EbnfExpr.sequence expressionLayout :=
    Subsingleton.elim _ _
  rw [layoutProof]
  have symbolProof : symbolLayout = rfl := Subsingleton.elim _ _
  rw [symbolProof]
  simp only [GrammarSymbolValues.transport_self]
  have canonicalExpressionLayout : [
      letKeywordAtomSite.site.expression,
      letNameAtomSite.site.expression,
      letTypeOptionalSite.site.expression,
      letInitializerOptionalSite.site.expression] =
        [Grammar.hardKeyword .letKw, Grammar.identifier,
          Grammar.optional (Grammar.sequence [Grammar.symbol .colon,
            Grammar.optional (Grammar.contextualKeyword .comptimeKw),
            Grammar.nonterminal .type]),
          Grammar.optional (Grammar.sequence [Grammar.symbol .equal,
            Grammar.nonterminal .expression])] := by
    simpa using expressionLayout
  have expressionProof : expressionLayout = canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProof]
  rw [sequence4View_transport_four_eq firstEq secondEq thirdEq fourthEq
    canonicalExpressionLayout]
  simp [EbnfValues.consView, EbnfValues.ofAuxiliaries,
    EbnfValue.atShape]
  apply congrArg (EbnfValue.transport thirdEq)
  symm
  exact cast_eq _ _

private theorem letTypeSequenceFields_auxiliary_three_eq
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite}
    {secondLhs thirdLhs : NonterminalSymbol}
    (childrenEq : children = [letColonAtomSite.site,
      letComptimeOptionalSite.site, letTypeAtomSite.site])
    (firstEq : letColonAtomSite.site.expression = letColonExpr)
    (secondEq : letComptimeOptionalSite.site.expression =
      Grammar.optional letComptimeExpr)
    (thirdEq : letTypeAtomSite.site.expression = letTypeExpr)
    (secondLhsEq : secondLhs = .aux letComptimeOptionalSite.site)
    (thirdLhsEq : thirdLhs = .aux letTypeAtomSite.site)
    (symbolLayout : children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal (.aux letColonAtomSite.site),
      .nonterminal secondLhs, .nonterminal thirdLhs])
    (expressionLayout : children.map GrammarSite.expression = [
      letColonExpr, Grammar.optional letComptimeExpr, letTypeExpr])
    (firstValue : GrammarSymbolValue file tokens
      (.nonterminal (.aux letColonAtomSite.site)))
    (secondValue : GrammarSymbolValue file tokens (.nonterminal secondLhs))
    (thirdValue : GrammarSymbolValue file tokens (.nonterminal thirdLhs)) :
    (EbnfValue.sequence3View letColonExpr
      (Grammar.optional letComptimeExpr) letTypeExpr
      (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
        (EbnfValue.sequence (children.map GrammarSite.expression)
          (EbnfValues.ofAuxiliaries children
            (GrammarSymbolValues.transport symbolLayout.symm
              (firstValue, (secondValue, (thirdValue, ())))))))).2 =
      (EbnfValue.atShape secondEq
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg GrammarSymbol.nonterminal secondLhsEq)) secondValue),
        EbnfValue.atShape thirdEq
          (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg GrammarSymbol.nonterminal thirdLhsEq)) thirdValue)) := by
  subst children
  subst secondLhs
  subst thirdLhs
  simp only [List.map] at expressionLayout ⊢
  have canonicalExpressionLayout : [
      letColonAtomSite.site.expression,
      letComptimeOptionalSite.site.expression,
      letTypeAtomSite.site.expression] = [letColonExpr,
        Grammar.optional letComptimeExpr, letTypeExpr] := by
    simpa using expressionLayout
  have expressionProof : expressionLayout = canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProof]
  have symbolProof : symbolLayout = rfl := Subsingleton.elim _ _
  rw [symbolProof]
  simp only [GrammarSymbolValues.transport_self]
  rw [sequence3View_transport_three_eq firstEq secondEq thirdEq
    canonicalExpressionLayout]
  simp [EbnfValues.consView, EbnfValues.ofAuxiliaries,
    EbnfValue.atShape]
  constructor <;> apply congrArg _ <;> symm <;> exact cast_eq _ _

private theorem letBindingTypeField_typedInput_eq
    {file : WorkspaceFile} {tokens : List Token}
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeValue : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression)) :
    letBindingTypeField
        (letBindingTypedInput letKeyword name colon typeValue initializer) =
      EbnfValue.optional letTypeSequenceExpr (some <|
        EbnfValue.sequence
          [letColonExpr, .optional letComptimeExpr, letTypeExpr] <|
          EbnfValues.cons _ _
            (EbnfValue.terminalAtom (.symbol .colon) colon) <|
          EbnfValues.cons _ _
            (EbnfValue.optional letComptimeExpr none) <|
          EbnfValues.cons _ _
            (EbnfValue.ruleAtom .type typeValue) <|
          EbnfValues.nil) := by
  unfold letBindingTypeField letBindingTypedInput
  rw [EbnfValue.transport_trans]
  have proofEq : letBindingRootLayout.trans
      letBindingRootLayout.symm = rfl := Subsingleton.elim _ _
  rw [proofEq]
  simp only [EbnfValue.transport_self]
  exact sequence4View_four_third _ _ _ _ _ _ _ _

private theorem EbnfValue.transport_optional_none_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {source target : EbnfExpr} (shape : source = target) :
    EbnfValue.transport (file := file) (tokens := tokens)
        (congrArg EbnfExpr.optional shape)
        (EbnfValue.optional source none) =
      EbnfValue.optional target none := by
  cases shape
  simp only [EbnfValue.transport_self]

private theorem optionalView_atShape_pack_none_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite) {target : EbnfExpr}
    (shape : site.site.expression = .optional target)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .none).rhs) :
    EbnfValue.optionalView target
        (EbnfValue.atShape shape
          (OptionalSite.pack site .none values)) = none := by
  have childShape : site.child.expression = target :=
    EbnfExpr.optional.inj
      (site.expression_eq_optional.symm.trans shape)
  have shapeEq : shape = site.expression_eq_optional.trans
      (congrArg EbnfExpr.optional childShape) :=
    Subsingleton.elim _ _
  rw [shapeEq]
  change EbnfValue.optionalView target
    (EbnfValue.transport
      (site.expression_eq_optional.trans
        (congrArg EbnfExpr.optional childShape))
      (OptionalSite.pack site .none values)) = none
  rw [← EbnfValue.transport_trans]
  change EbnfValue.optionalView target
    (EbnfValue.transport (congrArg EbnfExpr.optional childShape)
      (EbnfValue.atShape site.expression_eq_optional
        (OptionalSite.pack site .none values))) = none
  rw [OptionalSite.pack_none_eq,
    EbnfValue.transport_optional_none_eq_local]
  simp [EbnfValue.optionalView, EbnfValue.optional]
  exact childShape

private theorem optionalView_atShape_pack_some_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    (site : OptionalSite) {target : EbnfExpr}
    (shape : site.site.expression = .optional target)
    (childShape : site.child.expression = target)
    (values : GrammarSymbolValues file tokens
      (ProductionId.opt site .some).rhs) :
    EbnfValue.optionalView target
        (EbnfValue.atShape shape
          (OptionalSite.pack site .some values)) =
      some (EbnfValue.transport childShape
        (GrammarSymbolValues.view
          (ProductionId.rhs_opt_some site) values).1) := by
  have shapeEq : shape = site.expression_eq_optional.trans
      (congrArg EbnfExpr.optional childShape) :=
    Subsingleton.elim _ _
  rw [shapeEq]
  change EbnfValue.optionalView target
    (EbnfValue.transport
      (site.expression_eq_optional.trans
        (congrArg EbnfExpr.optional childShape))
      (OptionalSite.pack site .some values)) = _
  rw [← EbnfValue.transport_trans]
  change EbnfValue.optionalView target
    (EbnfValue.transport (congrArg EbnfExpr.optional childShape)
      (EbnfValue.atShape site.expression_eq_optional
        (OptionalSite.pack site .some values))) = _
  rw [OptionalSite.pack_some_eq, transport_optional_some_eq]
  simp [EbnfValue.optionalView, EbnfValue.optional]
  exact childShape

private theorem EbnfValue.optionalView_optional_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    (child : EbnfExpr)
    (value : Option (EbnfValue file tokens child)) :
    EbnfValue.optionalView child (EbnfValue.optional child value) = value := by
  apply EbnfValue.optional_injective child
  exact EbnfValue.optional_of_view child (EbnfValue.optional child value)

private theorem EbnfValue.atShape_trans_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {site : GrammarSite} {middle expression : EbnfExpr}
    (first : site.expression = middle) (second : middle = expression)
    (value : EbnfValue file tokens site.expression) :
    EbnfValue.atShape (first.trans second) value =
      EbnfValue.transport second (EbnfValue.atShape first value) := by
  unfold EbnfValue.atShape EbnfValue.transport
  change cast _ value = cast _ (cast _ value)
  rw [cast_cast]

private theorem Eq.mp_three_cycle_local
    {α β γ : Sort u} (first : α = β) (second : β = γ)
    (third : γ = α) (value : α) :
    Eq.mp third (Eq.mp second (Eq.mp first value)) = value := by
  cases first
  cases second
  exact cast_eq third value

private theorem coherentTypeRoot_branchTag_eq
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .type origin finish context)}
    (coherent : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .type origin finish context)
      priorValues) :
    ∃ (branch : Fin typeRootChoiceSite.branchCount)
        (choiceItem : ContextualItemKey tokens)
        (choiceProduction : choiceItem.raw.production =
          .choice typeRootChoiceSite branch)
        (choiceValue : NonterminalValue file tokens
          choiceItem.raw.production.lhs)
        (choiceChildValue : EbnfValue file tokens
          (typeRootChoiceSite.branchExpressions.toList.get
            (typeRootChoiceSite.branchListIndex branch)))
        (choiceValues : PrefixValues file tokens choiceItem)
        (choiceComplete : CompleteItem choiceItem.raw),
      CoherentReduction file tokens memo correct final choiceItem
          choiceValue ∧
        CoherentPrefix file tokens memo correct final choiceItem
          choiceValues ∧
        ContextualReach file tokens memo correct final choiceItem ∧
        choiceChildValue =
          EbnfValue.transport
            ((typeRootChoiceSite.branch_expression branch).trans
              (typeRootChoiceSite.branch_get_toList branch).symm)
            (GrammarSymbolValues.view
              (ProductionId.rhs_choice typeRootChoiceSite branch)
              (GrammarSymbolValues.transport
                (congrArg ProductionId.rhs choiceProduction)
                (PrefixValues.fullValue choiceItem choiceComplete
                  choiceValues))).1 ∧
        choiceItem.raw.origin = origin ∧
        typeRootBranchTag
          (RootAction.unpack .type
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens .type origin finish context)
              (canonicalCompleteRootItem_complete .type origin finish context)
              priorValues)) = branch.val ∧
        RootAction.unpack .type
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens .type origin finish context)
              (canonicalCompleteRootItem_complete .type origin finish context)
              priorValues) =
          EbnfValue.transport typeRootChoiceLayout_local
            (EbnfValue.choice
              typeRootChoiceSite.branchExpressions.toList
              ⟨typeRootChoiceSite.branchListIndex branch,
                choiceChildValue⟩) := by
  cases coherent with
  | zero _ _ zero =>
      change 1 = 0 at zero
      omega
  | scan before _ _ _ witness _ _ =>
      have beforeProduction : before.raw.production = .root .type :=
        witness.advance.1.symm
      have beforeDot : before.raw.dot.val = 0 := by
        have advanced := witness.advance.2.1
        change 1 = before.raw.dot.val + 1 at advanced
        omega
      have impossible :
          some (GrammarSymbol.terminal witness.terminal) =
            some (GrammarSymbol.nonterminal
              (.aux (GrammarSite.root .type))) := by
        let index := before.raw.dot.val
        calc
          _ = before.raw.production.rhs[index]? := witness.next.2.symm
          _ = (ProductionId.root .type).rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) beforeProduction
          _ = (ProductionId.root .type).rhs[0]? := by
            have indexZero : index = 0 := beforeDot
            rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting choiceItem _ rootShared rootPriorValues choiceValue
      rootWitness rootEdge _ choiceReduction =>
      have rootWaitingProduction :
          rootWaiting.raw.production = .root .type :=
        rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1
        change 1 = rootWaiting.raw.dot.val + 1 at advanced
        omega
      have rootWaitingOriginCurrent :
          rootWaiting.raw.origin = rootWaiting.raw.current :=
        contextualReach_zero_origin_eq_current rootEdge.2.1
          rootWaitingDot
      have choiceOriginEq : choiceItem.raw.origin = origin := by
        calc
          choiceItem.raw.origin = rootShared :=
            rootWitness.finishedAtShared
          _ = rootWaiting.raw.current := rootWitness.waitingAtShared.symm
          _ = rootWaiting.raw.origin := rootWaitingOriginCurrent.symm
          _ = origin := rootWitness.advance.2.2.1.symm
      have choiceLhs : choiceItem.raw.production.lhs =
          .aux (GrammarSite.root .type) := by
        have selected :
            some (GrammarSymbol.nonterminal choiceItem.raw.production.lhs) =
              some (GrammarSymbol.nonterminal
                (.aux (GrammarSite.root .type))) := by
          let index := rootWaiting.raw.dot.val
          calc
            _ = rootWaiting.raw.production.rhs[index]? :=
              rootWitness.next.2.symm
            _ = (ProductionId.root .type).rhs[index]? :=
              congrArg (fun production : ProductionId =>
                production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root .type).rhs[0]? := by
              have indexZero : index = 0 := rootWaitingDot
              rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      obtain ⟨branch, choiceProduction⟩ :=
        production_choice_of_lhs_local typeRootChoiceSite
          choiceItem.raw.production (by
            simpa [typeRootChoiceSite] using choiceLhs)
      rcases choiceItem with
        ⟨⟨choiceProductionId, choiceDot, choiceOrigin, choiceCurrent⟩,
          choiceContext⟩
      simp only at choiceProduction
      subst choiceProductionId
      let choiceItem : ContextualItemKey tokens :=
        ⟨⟨.choice typeRootChoiceSite branch, choiceDot,
          choiceOrigin, choiceCurrent⟩, choiceContext⟩
      change CoherentReduction file tokens memo correct final
        choiceItem choiceValue at choiceReduction
      cases choiceReduction with
      | reduce _ choiceValues _ choiceReached choiceComplete choiceCoherent
          choiceAction =>
          have choicePackedEq :
              choiceValue = ChoiceSite.pack typeRootChoiceSite branch
                (PrefixValues.fullValue choiceItem choiceComplete
                  choiceValues) := by
            have exact := actionReduces_eleven_shapes_exact.mp choiceAction
            simpa [choiceItem] using exact
          have rootPriorLayout :
              rootWaiting.raw.production.rhs.take
                rootWaiting.raw.dot.val = [] := by
            rw [rootWaitingDot]
            simp
          let rootEmpty : GrammarSymbolValues file tokens [] :=
            GrammarSymbolValues.transport rootPriorLayout rootPriorValues
          have rootPriorRecover :
              GrammarSymbolValues.transport rootPriorLayout.symm rootEmpty =
                rootPriorValues := by
            rw [← show GrammarSymbolValues.transport rootPriorLayout
                rootPriorValues = rootEmpty from rfl,
              GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have rootSymbolLayout :
              GrammarSymbol.nonterminal choiceItem.raw.production.lhs =
                GrammarSymbol.nonterminal
                  (.aux (GrammarSite.root .type)) :=
            congrArg GrammarSymbol.nonterminal choiceLhs
          have rootTupleEq :=
            GrammarSymbolValues.transport_append_empty_single_to_local
              rootPriorLayout
              ((prefix_complete_layout rootWaiting.raw choiceItem.raw
                (CanonicalCompleteRootItem tokens .type origin finish
                  context).raw rootWitness.next rootWitness.advance).trans
                (prefix_full_layout
                  (CanonicalCompleteRootItem tokens .type origin finish
                    context).raw
                  (canonicalCompleteRootItem_complete .type origin finish
                    context)))
              (ProductionId.rhs_root .type)
              rootSymbolLayout rootEmpty choiceValue
          have rootUnpackEq :
              RootAction.unpack .type
                  (PrefixValues.fullValue
                    (CanonicalCompleteRootItem tokens .type origin finish
                      context)
                    (canonicalCompleteRootItem_complete .type origin finish
                      context)
                    (PrefixValues.completeValue rootWaiting choiceItem
                      (CanonicalCompleteRootItem tokens .type origin finish
                        context)
                      rootWitness.next rootWitness.advance rootPriorValues
                      choiceValue)) =
                EbnfValue.atShape (GrammarSite.root_expression .type)
                  (Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      rootSymbolLayout)
                    choiceValue) := by
            rw [← rootPriorRecover]
            rw [PrefixValues.fullValue_completeValue_eq]
            rw [RootAction.unpack_eq]
            unfold GrammarSymbolValues.view
            exact congrArg
              (EbnfValue.atShape (GrammarSite.root_expression .type))
              (congrArg Prod.fst rootTupleEq)
          have rootUnpackPackedEq :
              RootAction.unpack .type
                  (PrefixValues.fullValue
                    (CanonicalCompleteRootItem tokens .type origin finish
                      context)
                    (canonicalCompleteRootItem_complete .type origin finish
                      context)
                    (PrefixValues.completeValue rootWaiting choiceItem
                      (CanonicalCompleteRootItem tokens .type origin finish
                        context)
                      rootWitness.next rootWitness.advance rootPriorValues
                      choiceValue)) =
                EbnfValue.atShape (GrammarSite.root_expression .type)
                  (Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      rootSymbolLayout)
                    (ChoiceSite.pack typeRootChoiceSite branch
                      (PrefixValues.fullValue choiceItem choiceComplete
                        choiceValues))) :=
            rootUnpackEq.trans (congrArg
              (fun value =>
                EbnfValue.atShape (GrammarSite.root_expression .type)
                  (Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      rootSymbolLayout) value))
              choicePackedEq)
          have siteRoot : typeRootChoiceSite.site =
              GrammarSite.root .type := rfl
          have rootCastLayoutEq :
              congrArg (GrammarSymbolValue file tokens) rootSymbolLayout =
                congrArg (GrammarSymbolValue file tokens)
                  (congrArg (fun child =>
                    GrammarSymbol.nonterminal (.aux child)) siteRoot) :=
            Subsingleton.elim _ _
          have choiceLayout :
              EbnfExpr.choice
                  typeRootChoiceSite.branchExpressions.toList =
                m2cV1.rhs .type :=
            typeRootChoiceSite.expression_eq_choice.symm.trans
              ((congrArg GrammarSite.expression siteRoot).trans
                (GrammarSite.root_expression .type))
          let choiceChildValue :=
            EbnfValue.transport
              ((typeRootChoiceSite.branch_expression branch).trans
                (typeRootChoiceSite.branch_get_toList branch).symm)
              (GrammarSymbolValues.view
                (ProductionId.rhs_choice typeRootChoiceSite branch)
                (PrefixValues.fullValue choiceItem choiceComplete
                  choiceValues)).1
          have packedRightEq :
              EbnfValue.atShape (GrammarSite.root_expression .type)
                  (Eq.mp
                    (congrArg (GrammarSymbolValue file tokens)
                      rootSymbolLayout)
                    (ChoiceSite.pack typeRootChoiceSite branch
                      (PrefixValues.fullValue choiceItem choiceComplete
                        choiceValues))) =
                EbnfValue.transport choiceLayout
                  (EbnfValue.choice
                    typeRootChoiceSite.branchExpressions.toList
                    ⟨typeRootChoiceSite.branchListIndex branch,
                      choiceChildValue⟩) := by
            rw [rootCastLayoutEq]
            unfold ChoiceSite.pack
            exact root_choiceTransport_eq_local .type typeRootChoiceSite
              siteRoot choiceLayout _
          have rootUnpackNormalizedEq :=
            rootUnpackPackedEq.trans packedRightEq
          have rootTagEq :=
            congrArg typeRootBranchTag rootUnpackNormalizedEq
          have packedTagEq :
              typeRootBranchTag
                  (EbnfValue.transport choiceLayout
                    (EbnfValue.choice
                      typeRootChoiceSite.branchExpressions.toList
                      ⟨typeRootChoiceSite.branchListIndex branch,
                        choiceChildValue⟩)) = branch.val := by
            unfold typeRootBranchTag
            rw [EbnfValue.transport_trans]
            exact choiceView_transport_branch_val_local _ _ _
          have choiceReduction' :
              CoherentReduction file tokens memo correct final choiceItem
                choiceValue :=
            .reduce choiceItem choiceValues choiceValue choiceReached
              choiceComplete choiceCoherent choiceAction
          have choiceLayoutEq :
              choiceLayout = typeRootChoiceLayout_local :=
            Subsingleton.elim _ _
          rw [choiceLayoutEq] at rootUnpackNormalizedEq
          exact ⟨branch, choiceItem, rfl, choiceValue, choiceChildValue,
            choiceValues, choiceComplete, choiceReduction',
            choiceCoherent, choiceReached, rfl, choiceOriginEq,
            rootTagEq.trans packedTagEq, rootUnpackNormalizedEq⟩

private theorem coherentLetBinding_typedComptime_impossible
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .letBinding origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .letBinding
        origin finish context).raw)
    (coherent : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .letBinding origin finish context)
      priorValues)
    (letKeyword : MatchedTerminal file tokens (.hardKeyword .letKw))
    (name : MatchedTerminal file tokens (.category .identifier))
    (colon : MatchedTerminal file tokens (.symbol .colon))
    (typeSpan : SourceSpan) (typeMarker : Marker) (inner : TypeExpr)
    (initializer : Option
      (MatchedTerminal file tokens (.symbol .equal) × Expression))
    (inputEq : RootAction.unpack .letBinding
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .letBinding
            origin finish context) complete priorValues) =
      letBindingTypedInput letKeyword name colon
        ⟨typeSpan, .comptime typeMarker inner⟩ initializer) :
    False := by
  cases coherent with
  | zero item reached zero =>
      change 1 = 0 at zero
      omega
  | scan before after cursor priorValues witness edge prior =>
      have beforeProduction : before.raw.production = .root .letBinding :=
        witness.advance.1.symm
      have beforeDot : before.raw.dot.val = 0 := by
        have advanced := witness.advance.2.1
        change 1 = before.raw.dot.val + 1 at advanced
        omega
      have impossible : some (GrammarSymbol.terminal witness.terminal) =
          some (GrammarSymbol.nonterminal
            (.aux (GrammarSite.root .letBinding))) := by
        let index := before.raw.dot.val
        calc
          _ = before.raw.production.rhs[index]? :=
            witness.next.2.symm
          _ = (ProductionId.root .letBinding).rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) beforeProduction
          _ = (ProductionId.root .letBinding).rhs[0]? := by
            have indexZero : index = 0 := beforeDot
            rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting sequence after rootShared rootPriorValues
      sequenceValue rootWitness rootEdge rootPrior sequenceReduction =>
      have rootWaitingProduction :
          rootWaiting.raw.production = .root .letBinding :=
        rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1
        change 1 = rootWaiting.raw.dot.val + 1 at advanced
        omega
      have sequenceLhs : sequence.raw.production.lhs =
          .aux (GrammarSite.root .letBinding) := by
        have selected : some (GrammarSymbol.nonterminal
              sequence.raw.production.lhs) =
            some (GrammarSymbol.nonterminal
              (.aux (GrammarSite.root .letBinding))) := by
          let index := rootWaiting.raw.dot.val
          calc
            _ = rootWaiting.raw.production.rhs[index]? :=
              rootWitness.next.2.symm
            _ = (ProductionId.root .letBinding).rhs[index]? :=
              congrArg (fun production : ProductionId =>
                production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root .letBinding).rhs[0]? := by
              have indexZero : index = 0 := rootWaitingDot
              rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      have sequenceProduction : sequence.raw.production =
          .seq letRootSequenceSite :=
        production_eq_sequence_of_lhs letRootSequenceSite
          sequence.raw.production (by
            simpa [letRootSequenceSite] using sequenceLhs)
      rcases sequence with
        ⟨⟨sequenceProductionId, sequenceDot, sequenceOrigin,
          sequenceCurrent⟩, sequenceContext⟩
      simp only at sequenceProduction
      subst sequenceProductionId
      let sequence : ContextualItemKey tokens :=
        ⟨⟨.seq letRootSequenceSite, sequenceDot, sequenceOrigin,
          sequenceCurrent⟩, sequenceContext⟩
      have sequenceProduction : sequence.raw.production =
          .seq letRootSequenceSite := rfl
      change CoherentReduction file tokens memo correct final
        sequence sequenceValue at sequenceReduction
      have rootPriorLayout :
          rootWaiting.raw.production.rhs.take rootWaiting.raw.dot.val = [] := by
        let index := rootWaiting.raw.dot.val
        have dotZero : index = 0 := rootWaitingDot
        calc
          _ = (ProductionId.root .letBinding).rhs.take index :=
            congrArg (fun production : ProductionId =>
              production.rhs.take index) rootWaitingProduction
          _ = (ProductionId.root .letBinding).rhs.take 0 := by rw [dotZero]
          _ = [] := by simp
      let rootEmpty := GrammarSymbolValues.transport
        rootPriorLayout rootPriorValues
      have rootPriorRecover : GrammarSymbolValues.transport
          rootPriorLayout.symm rootEmpty = rootPriorValues := by
        dsimp only [rootEmpty]
        rw [GrammarSymbolValues.transport_trans]
        exact GrammarSymbolValues.transport_self _ _
      rw [← rootPriorRecover] at inputEq
      rw [PrefixValues.fullValue_completeValue_eq] at inputEq
      have rootSymbolLayout :
          GrammarSymbol.nonterminal sequence.raw.production.lhs =
            GrammarSymbol.nonterminal
              (.aux (GrammarSite.root .letBinding)) :=
        congrArg GrammarSymbol.nonterminal sequenceLhs
      have rootTupleEq :=
        GrammarSymbolValues.transport_append_empty_single_to_local
          rootPriorLayout
          ((prefix_complete_layout rootWaiting.raw sequence.raw
            (CanonicalCompleteRootItem tokens .letBinding
              origin finish context).raw rootWitness.next
              rootWitness.advance).trans
            (prefix_full_layout
              (CanonicalCompleteRootItem tokens .letBinding
                origin finish context).raw complete))
          (ProductionId.rhs_root .letBinding)
          rootSymbolLayout rootEmpty sequenceValue
      rw [RootAction.unpack_eq] at inputEq
      unfold GrammarSymbolValues.view at inputEq
      have rootHeadEq := congrArg Prod.fst rootTupleEq
      have rootHeadAtEq := congrArg
        (EbnfValue.atShape (GrammarSite.root_expression .letBinding))
        rootHeadEq
      have rootInputEq := rootHeadAtEq.symm.trans inputEq
      cases sequenceReduction with
      | reduce _ sequenceValues sequenceOutput sequenceReached
          sequenceComplete sequenceCoherent sequenceAction =>
          have sequenceItemProduction : sequence.raw.production =
              .seq letRootSequenceSite := sequenceProduction
          cases sequenceCoherent with
          | zero item reached zero =>
              have dotFour : sequence.raw.dot.val = 4 := by
                calc
                  _ = sequence.raw.production.rhs.length := sequenceComplete
                  _ = 4 := by
                    rw [sequenceItemProduction]
                    simp [ProductionId.rhs_seq,
                      letRootSequenceSite_children]
              omega
          | scan before after cursor priorValues witness edge prior =>
              have beforeProduction : before.raw.production =
                  .seq letRootSequenceSite :=
                witness.advance.1.symm.trans sequenceItemProduction
              have beforeDot : before.raw.dot.val = 3 := by
                have advanced := witness.advance.2.1
                have itemDot : sequence.raw.dot.val = 4 := by
                  calc
                    _ = sequence.raw.production.rhs.length := sequenceComplete
                    _ = 4 := by
                      rw [sequenceItemProduction]
                      simp [ProductionId.rhs_seq,
                        letRootSequenceSite_children]
                omega
              have impossible : some (GrammarSymbol.terminal witness.terminal) =
                  some (GrammarSymbol.nonterminal
                    (.aux (letRootSequenceSite.children.get ⟨3, by
                      rw [letRootSequenceSite_children]
                      decide⟩))) := by
                let index := before.raw.dot.val
                calc
                  _ = before.raw.production.rhs[index]? :=
                    witness.next.2.symm
                  _ = (ProductionId.seq letRootSequenceSite).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = (ProductionId.seq letRootSequenceSite).rhs[3]? := by
                    have indexThree : index = 3 := beforeDot
                    rw [indexThree]
                  _ = _ := by
                    simp [ProductionId.rhs_seq,
                      letRootSequenceSite_children]
              exact GrammarSymbol.noConfusion (Option.some.inj impossible)
          | complete sequenceWaiting initializerItem sequenceAfter shared
              sequencePriorValues initializerValue sequenceWitness
              sequenceEdge sequencePrior initializerReduction =>
              have sequenceAfterDot : sequence.raw.dot.val = 4 := by
                calc
                  _ = sequence.raw.production.rhs.length :=
                    sequenceComplete
                  _ = 4 := by
                    rw [sequenceItemProduction]
                    simp [ProductionId.rhs_seq,
                      letRootSequenceSite_children]
              have sequenceWaitingDot : sequenceWaiting.raw.dot.val = 3 := by
                have advanced := sequenceWitness.advance.2.1
                omega
              cases sequencePrior with
              | zero item reached zero => omega
              | scan before after cursor priorValues witness edge prior =>
                  have beforeDot : before.raw.dot.val = 2 := by
                    have advanced := witness.advance.2.1
                    omega
                  have beforeProduction : before.raw.production =
                      .seq letRootSequenceSite := by
                    exact witness.advance.1.symm.trans
                      (sequenceWitness.advance.1.symm.trans
                        sequenceItemProduction)
                  have impossible :
                      some (GrammarSymbol.terminal witness.terminal) =
                        some (GrammarSymbol.nonterminal
                          (.aux letTypeOptionalSite.site)) := by
                    let index := before.raw.dot.val
                    calc
                      _ = before.raw.production.rhs[index]? :=
                        witness.next.2.symm
                      _ = (ProductionId.seq letRootSequenceSite).rhs[index]? :=
                        congrArg (fun production : ProductionId =>
                          production.rhs[index]?) beforeProduction
                      _ = (ProductionId.seq letRootSequenceSite).rhs[2]? := by
                        have indexTwo : index = 2 := beforeDot
                        rw [indexTwo]
                      _ = _ := by
                        simp [ProductionId.rhs_seq,
                          letRootSequenceSite_children]
                  exact GrammarSymbol.noConfusion (Option.some.inj impossible)
              | complete typeWaiting typeOptionalItem typeAfter typeShared
                  typePriorValues typeOptionalValue typeWitness typeEdge
                  typePrior typeOptionalReduction =>
                  have typeOptionalLhs :
                      typeOptionalItem.raw.production.lhs =
                        .aux letTypeOptionalSite.site := by
                    have beforeProduction : typeWaiting.raw.production =
                        .seq letRootSequenceSite := by
                      exact typeWitness.advance.1.symm.trans
                        (sequenceWitness.advance.1.symm.trans
                          sequenceItemProduction)
                    have beforeDot : typeWaiting.raw.dot.val = 2 := by
                      have advanced := typeWitness.advance.2.1
                      omega
                    have selected : some (GrammarSymbol.nonterminal
                          typeOptionalItem.raw.production.lhs) =
                        some (GrammarSymbol.nonterminal
                          (.aux letTypeOptionalSite.site)) := by
                      let index := typeWaiting.raw.dot.val
                      calc
                        _ = typeWaiting.raw.production.rhs[index]? :=
                          typeWitness.next.2.symm
                        _ = (ProductionId.seq letRootSequenceSite).rhs[index]? :=
                          congrArg (fun production : ProductionId =>
                            production.rhs[index]?) beforeProduction
                        _ = (ProductionId.seq letRootSequenceSite).rhs[2]? := by
                          have indexTwo : index = 2 := beforeDot
                          rw [indexTwo]
                        _ = _ := by
                          simp [ProductionId.rhs_seq,
                            letRootSequenceSite_children]
                    exact GrammarSymbol.nonterminal.inj
                      (Option.some.inj selected)
                  rcases production_optional_of_lhs letTypeOptionalSite
                      typeOptionalItem.raw.production typeOptionalLhs with
                    ⟨typeBranch, typeOptionalProduction⟩
                  have sequencePackedEq :=
                    actionReduces_eleven_shapes_exact.mp sequenceAction
                  dsimp only [sequence] at sequencePackedEq
                  rw [PrefixValues.fullValue_completeValue_eq] at sequencePackedEq
                  simp only [PrefixValues.completeValue] at sequencePackedEq
                  have typeWaitingProduction :
                      typeWaiting.raw.production =
                        .seq letRootSequenceSite := by
                    exact typeWitness.advance.1.symm.trans
                      (sequenceWitness.advance.1.symm.trans
                        sequenceItemProduction)
                  have typeWaitingDot : typeWaiting.raw.dot.val = 2 := by
                    have advanced := typeWitness.advance.2.1
                    omega
                  have typePriorLayout :
                      typeWaiting.raw.production.rhs.take
                          typeWaiting.raw.dot.val = [
                        .nonterminal (.aux letKeywordAtomSite.site),
                        .nonterminal (.aux letNameAtomSite.site)] := by
                    let index := typeWaiting.raw.dot.val
                    have indexTwo : index = 2 := typeWaitingDot
                    calc
                      _ = (ProductionId.seq letRootSequenceSite).rhs.take
                          index := congrArg (fun production : ProductionId =>
                            production.rhs.take index)
                          typeWaitingProduction
                      _ = (ProductionId.seq letRootSequenceSite).rhs.take
                          2 := by rw [indexTwo]
                      _ = _ := by
                        simp [ProductionId.rhs_seq,
                          letRootSequenceSite_children]
                  generalize canonicalEq :
                      GrammarSymbolValues.transport typePriorLayout
                        typePriorValues = canonicalPrior
                  rcases canonicalPrior with
                    ⟨keywordValue, nameValue, ⟨⟩⟩
                  have typePriorRecover : GrammarSymbolValues.transport
                      typePriorLayout.symm (keywordValue, (nameValue, ())) =
                        typePriorValues := by
                    rw [← canonicalEq,
                      GrammarSymbolValues.transport_trans]
                    exact GrammarSymbolValues.transport_self _ _
                  rw [← typePriorRecover] at sequencePackedEq
                  have initializerLhs :
                      initializerItem.raw.production.lhs =
                        .aux letInitializerOptionalSite.site := by
                    have waitingProduction :
                        sequenceWaiting.raw.production =
                          .seq letRootSequenceSite :=
                      sequenceWitness.advance.1.symm.trans
                        sequenceItemProduction
                    have selected : some (GrammarSymbol.nonterminal
                          initializerItem.raw.production.lhs) =
                        some (GrammarSymbol.nonterminal
                          (.aux letInitializerOptionalSite.site)) := by
                      let index := sequenceWaiting.raw.dot.val
                      calc
                        _ = sequenceWaiting.raw.production.rhs[index]? :=
                          sequenceWitness.next.2.symm
                        _ = (ProductionId.seq letRootSequenceSite).rhs[index]? :=
                          congrArg (fun production : ProductionId =>
                            production.rhs[index]?) waitingProduction
                        _ = (ProductionId.seq letRootSequenceSite).rhs[3]? := by
                          have indexThree : index = 3 := sequenceWaitingDot
                          rw [indexThree]
                        _ = _ := by
                          simp [ProductionId.rhs_seq,
                            letRootSequenceSite_children]
                    exact GrammarSymbol.nonterminal.inj
                      (Option.some.inj selected)
                  have sequenceTargetLayout :
                      letRootSequenceSite.children.map
                          (fun child => GrammarSymbol.nonterminal (.aux child)) = [
                        .nonterminal (.aux letKeywordAtomSite.site),
                        .nonterminal (.aux letNameAtomSite.site),
                        .nonterminal typeOptionalItem.raw.production.lhs,
                        .nonterminal initializerItem.raw.production.lhs] := by
                    rw [letRootSequenceSite_children]
                    simp only [List.map]
                    rw [typeOptionalLhs, initializerLhs]
                  have sequenceTupleEq :=
                    GrammarSymbolValues.transport_append_four_to
                      typePriorLayout
                      (prefix_complete_layout typeWaiting.raw
                        typeOptionalItem.raw sequenceWaiting.raw
                        typeWitness.next typeWitness.advance)
                      ((prefix_complete_layout sequenceWaiting.raw
                        initializerItem.raw sequence.raw
                        sequenceWitness.next sequenceWitness.advance).trans
                        (prefix_full_layout sequence.raw sequenceComplete))
                      (ProductionId.rhs_seq letRootSequenceSite)
                      sequenceTargetLayout keywordValue nameValue
                      typeOptionalValue initializerValue
                  simp only [SequenceSite.pack,
                    GrammarSymbolValues.view] at sequencePackedEq
                  conv at sequencePackedEq in
                      (GrammarSymbolValues.transport _ _) =>
                    rw [sequenceTupleEq]
                  rw [sequencePackedEq] at rootInputEq
                  have rootSymbolLayoutEq : rootSymbolLayout = rfl :=
                    Subsingleton.elim _ _
                  rw [rootSymbolLayoutEq] at rootInputEq
                  have rootSiteEq : letRootSequenceSite.site =
                      GrammarSite.root .letBinding := by rfl
                  have rootExpressionLayout :
                      EbnfExpr.sequence
                          (letRootSequenceSite.children.map
                            GrammarSite.expression) =
                        m2cV1.rhs .letBinding := by
                    exact letRootSequenceSite.expression_eq_sequence.symm.trans
                      ((congrArg GrammarSite.expression rootSiteEq).trans
                        (GrammarSite.root_expression .letBinding))
                  let rawSequenceValue := EbnfValue.sequence
                    (letRootSequenceSite.children.map GrammarSite.expression)
                    (EbnfValues.ofAuxiliaries letRootSequenceSite.children
                      (GrammarSymbolValues.transport
                        sequenceTargetLayout.symm
                        (keywordValue, (nameValue,
                          (typeOptionalValue, (initializerValue, ()))))))
                  have rootCanonicalEq := root_sequenceTransport_eq_local
                    .letBinding letRootSequenceSite rootSiteEq
                      rootExpressionLayout rawSequenceValue
                  have parsedInputEq : EbnfValue.transport rootExpressionLayout
                        rawSequenceValue =
                      letBindingTypedInput letKeyword name colon
                        ⟨typeSpan, .comptime typeMarker inner⟩ initializer :=
                    rootCanonicalEq.symm.trans rootInputEq
                  have childrenExpressionLayout :
                      letRootSequenceSite.children.map
                          GrammarSite.expression = [
                        Grammar.hardKeyword .letKw, Grammar.identifier,
                        Grammar.optional (Grammar.sequence [
                          Grammar.symbol .colon,
                          Grammar.optional
                            (Grammar.contextualKeyword .comptimeKw),
                          Grammar.nonterminal .type]),
                        Grammar.optional (Grammar.sequence [
                          Grammar.symbol .equal,
                          Grammar.nonterminal .expression])] :=
                    EbnfExpr.sequence.inj
                      (rootExpressionLayout.trans letBindingRootLayout.symm)
                  have expressionListEq : [
                        letKeywordAtomSite.site.expression,
                        letNameAtomSite.site.expression,
                        letTypeOptionalSite.site.expression,
                        letInitializerOptionalSite.site.expression] = [
                        Grammar.hardKeyword .letKw, Grammar.identifier,
                        Grammar.optional (Grammar.sequence [
                          Grammar.symbol .colon,
                          Grammar.optional
                            (Grammar.contextualKeyword .comptimeKw),
                          Grammar.nonterminal .type]),
                        Grammar.optional (Grammar.sequence [
                          Grammar.symbol .equal,
                          Grammar.nonterminal .expression])] := by
                    simpa only [letRootSequenceSite_children, List.map] using
                      childrenExpressionLayout
                  have firstShape : letKeywordAtomSite.site.expression =
                      Grammar.hardKeyword .letKw :=
                    (List.cons.inj expressionListEq).1
                  have expressionTail1 := (List.cons.inj expressionListEq).2
                  have secondShape : letNameAtomSite.site.expression =
                      Grammar.identifier :=
                    (List.cons.inj expressionTail1).1
                  have expressionTail2 := (List.cons.inj expressionTail1).2
                  have thirdShape : letTypeOptionalSite.site.expression =
                      Grammar.optional (Grammar.sequence [
                        Grammar.symbol .colon,
                        Grammar.optional
                          (Grammar.contextualKeyword .comptimeKw),
                        Grammar.nonterminal .type]) :=
                    (List.cons.inj expressionTail2).1
                  have expressionTail3 := (List.cons.inj expressionTail2).2
                  have fourthShape :
                      letInitializerOptionalSite.site.expression =
                        Grammar.optional (Grammar.sequence [
                          Grammar.symbol .equal,
                          Grammar.nonterminal .expression]) :=
                    (List.cons.inj expressionTail3).1
                  have parsedFieldEq :=
                    letBindingTypeField_auxiliary_four_eq
                      letRootSequenceSite_children firstShape secondShape
                      thirdShape fourthShape typeOptionalLhs initializerLhs
                      sequenceTargetLayout childrenExpressionLayout
                      rootExpressionLayout keywordValue nameValue
                      typeOptionalValue initializerValue
                  have typeFieldEq := congrArg letBindingTypeField parsedInputEq
                  rw [parsedFieldEq,
                    letBindingTypeField_typedInput_eq] at typeFieldEq
                  rcases typeOptionalItem with
                    ⟨⟨typeOptionalProductionId, typeOptionalDot,
                      typeOptionalOrigin, typeOptionalCurrent⟩,
                      typeOptionalContext⟩
                  simp only at typeOptionalProduction
                  subst typeOptionalProductionId
                  let typeOptionalItem : ContextualItemKey tokens :=
                    ⟨⟨.opt letTypeOptionalSite typeBranch,
                      typeOptionalDot, typeOptionalOrigin,
                      typeOptionalCurrent⟩, typeOptionalContext⟩
                  change CoherentReduction file tokens memo correct final
                    typeOptionalItem typeOptionalValue at typeOptionalReduction
                  cases typeOptionalReduction with
                  | reduce _ typeOptionalValues _ typeOptionalReached
                      typeOptionalComplete typeOptionalCoherent
                      typeOptionalAction =>
                      have typeOptionalPackedEq :
                          typeOptionalValue =
                            OptionalSite.pack letTypeOptionalSite typeBranch
                              (PrefixValues.fullValue typeOptionalItem
                                typeOptionalComplete typeOptionalValues) := by
                        have exact :=
                          actionReduces_eleven_shapes_exact.mp
                            typeOptionalAction
                        simpa [typeOptionalItem] using exact
                      have parsedFieldEqCanonical :=
                        letBindingTypeField_auxiliary_four_eq
                          letRootSequenceSite_children firstShape secondShape
                          thirdShape fourthShape (by rfl) initializerLhs
                          sequenceTargetLayout childrenExpressionLayout
                          rootExpressionLayout keywordValue nameValue
                          typeOptionalValue initializerValue
                      have canonicalTypeFieldEq :=
                        congrArg letBindingTypeField parsedInputEq
                      rw [parsedFieldEqCanonical,
                        letBindingTypeField_typedInput_eq] at canonicalTypeFieldEq
                      have canonicalTypeFieldEqNoCast :
                          EbnfValue.atShape thirdShape typeOptionalValue =
                            EbnfValue.optional letTypeSequenceExpr (some <|
                              EbnfValue.sequence [letColonExpr,
                                .optional letComptimeExpr, letTypeExpr] <|
                                EbnfValues.cons _ _
                                  (EbnfValue.terminalAtom (.symbol .colon)
                                    colon) <|
                                EbnfValues.cons _ _
                                  (EbnfValue.optional letComptimeExpr none) <|
                                EbnfValues.cons _ _
                                  (EbnfValue.ruleAtom .type
                                    ⟨typeSpan,
                                      .comptime typeMarker inner⟩) <|
                                EbnfValues.nil) := by
                        exact canonicalTypeFieldEq
                      cases typeBranch with
                      | none =>
                          have absent :=
                            optionalView_atShape_pack_none_eq_local
                              letTypeOptionalSite thirdShape
                              (PrefixValues.fullValue typeOptionalItem
                                typeOptionalComplete typeOptionalValues)
                          have absent' :
                              EbnfValue.optionalView letTypeSequenceExpr
                                (EbnfValue.atShape thirdShape
                                  (OptionalSite.pack letTypeOptionalSite
                                    .none
                                    (PrefixValues.fullValue typeOptionalItem
                                      typeOptionalComplete
                                      typeOptionalValues))) = none := absent
                          have viewed := congrArg
                            (EbnfValue.optionalView letTypeSequenceExpr)
                            canonicalTypeFieldEqNoCast
                          have packedViewed := congrArg
                            (fun value =>
                              EbnfValue.optionalView letTypeSequenceExpr
                                (EbnfValue.atShape thirdShape value))
                            typeOptionalPackedEq
                          have rightAbsent :=
                            viewed.symm.trans (packedViewed.trans absent')
                          simp [EbnfValue.optionalView,
                            EbnfValue.optional] at rightAbsent
                      | some =>
                          cases typeOptionalCoherent with
                          | zero _ _ zero =>
                              have dotOne : typeOptionalItem.raw.dot.val = 1 := by
                                calc
                                  _ = typeOptionalItem.raw.production.rhs.length :=
                                    typeOptionalComplete
                                  _ = 1 := by
                                    simp [typeOptionalItem, ProductionId.rhs]
                              omega
                          | scan optionalBefore _ _ _ optionalScan _ _ =>
                              have beforeProduction :
                                  optionalBefore.raw.production =
                                    .opt letTypeOptionalSite .some :=
                                optionalScan.advance.1.symm
                              have afterDot : typeOptionalItem.raw.dot.val = 1 := by
                                calc
                                  _ = typeOptionalItem.raw.production.rhs.length :=
                                    typeOptionalComplete
                                  _ = 1 := by
                                    simp [typeOptionalItem, ProductionId.rhs]
                              have beforeDot :
                                  optionalBefore.raw.dot.val = 0 := by
                                have advanced := optionalScan.advance.2.1
                                omega
                              have impossible :
                                  some (GrammarSymbol.terminal
                                    optionalScan.terminal) =
                                    some (GrammarSymbol.nonterminal
                                      (.aux letTypeOptionalSite.child)) := by
                                let index := optionalBefore.raw.dot.val
                                calc
                                  _ = optionalBefore.raw.production.rhs[index]? :=
                                    optionalScan.next.2.symm
                                  _ = (ProductionId.opt letTypeOptionalSite
                                      .some).rhs[index]? :=
                                    congrArg (fun production : ProductionId =>
                                      production.rhs[index]?) beforeProduction
                                  _ = (ProductionId.opt letTypeOptionalSite
                                      .some).rhs[0]? := by
                                    have indexZero : index = 0 := beforeDot
                                    rw [indexZero]
                                  _ = _ := by
                                    simp [ProductionId.rhs]
                              exact GrammarSymbol.noConfusion
                                (Option.some.inj impossible)
                          | complete optionalWaiting typeSequenceItem _
                              optionalShared optionalPriorValues
                              typeSequenceValue optionalWitness optionalEdge
                              optionalPrior typeSequenceReduction =>
                              have optionalWaitingProduction :
                                  optionalWaiting.raw.production =
                                    .opt letTypeOptionalSite .some :=
                                optionalWitness.advance.1.symm
                              have optionalWaitingDot :
                                  optionalWaiting.raw.dot.val = 0 := by
                                have advanced := optionalWitness.advance.2.1
                                have afterDot :
                                    typeOptionalItem.raw.dot.val = 1 := by
                                  calc
                                    _ = typeOptionalItem.raw.production.rhs.length :=
                                      typeOptionalComplete
                                    _ = 1 := by
                                      simp [typeOptionalItem,
                                        ProductionId.rhs]
                                omega
                              have typeSequenceLhs :
                                  typeSequenceItem.raw.production.lhs =
                                    .aux letTypeSequenceSite.site := by
                                have selected :
                                    some (GrammarSymbol.nonterminal
                                      typeSequenceItem.raw.production.lhs) =
                                      some (GrammarSymbol.nonterminal
                                        (.aux letTypeOptionalSite.child)) := by
                                  let index := optionalWaiting.raw.dot.val
                                  calc
                                    _ = optionalWaiting.raw.production.rhs[index]? :=
                                      optionalWitness.next.2.symm
                                    _ = (ProductionId.opt letTypeOptionalSite
                                        .some).rhs[index]? :=
                                      congrArg (fun production : ProductionId =>
                                        production.rhs[index]?)
                                        optionalWaitingProduction
                                    _ = (ProductionId.opt letTypeOptionalSite
                                        .some).rhs[0]? := by
                                      have indexZero : index = 0 :=
                                        optionalWaitingDot
                                      rw [indexZero]
                                    _ = _ := by
                                      simp [ProductionId.rhs]
                                have childLhs := GrammarSymbol.nonterminal.inj
                                  (Option.some.inj selected)
                                simpa [letTypeOptionalSite_child] using childLhs
                              have typeSequenceProduction :
                                  typeSequenceItem.raw.production =
                                    .seq letTypeSequenceSite :=
                                production_eq_sequence_of_lhs
                                  letTypeSequenceSite
                                  typeSequenceItem.raw.production
                                  typeSequenceLhs
                              rcases typeSequenceItem with
                                ⟨⟨typeSequenceProductionId,
                                  typeSequenceDot, typeSequenceOrigin,
                                  typeSequenceCurrent⟩,
                                  typeSequenceContext⟩
                              simp only at typeSequenceProduction
                              subst typeSequenceProductionId
                              let typeSequenceItem : ContextualItemKey tokens :=
                                ⟨⟨.seq letTypeSequenceSite,
                                  typeSequenceDot, typeSequenceOrigin,
                                  typeSequenceCurrent⟩,
                                  typeSequenceContext⟩
                              change CoherentReduction file tokens memo
                                correct final typeSequenceItem
                                typeSequenceValue at typeSequenceReduction
                              have optionalPriorLayout :
                                  optionalWaiting.raw.production.rhs.take
                                      optionalWaiting.raw.dot.val = [] := by
                                let index := optionalWaiting.raw.dot.val
                                calc
                                  _ = (ProductionId.opt letTypeOptionalSite
                                      .some).rhs.take index :=
                                    congrArg (fun production : ProductionId =>
                                      production.rhs.take index)
                                      optionalWaitingProduction
                                  _ = (ProductionId.opt letTypeOptionalSite
                                      .some).rhs.take 0 := by
                                    have indexZero : index = 0 :=
                                      optionalWaitingDot
                                    rw [indexZero]
                                  _ = [] := by simp
                              let optionalEmpty :=
                                GrammarSymbolValues.transport
                                  optionalPriorLayout optionalPriorValues
                              have optionalPriorRecover :
                                  GrammarSymbolValues.transport
                                    optionalPriorLayout.symm optionalEmpty =
                                      optionalPriorValues := by
                                dsimp only [optionalEmpty]
                                rw [GrammarSymbolValues.transport_trans]
                                exact GrammarSymbolValues.transport_self _ _
                              have typeSequenceSiteEq :
                                  letTypeSequenceSite.site =
                                    letTypeOptionalSite.child :=
                                letTypeOptionalSite_child.symm
                              have optionalFullTupleEq :
                                  GrammarSymbolValues.view
                                      (ProductionId.rhs_opt_some
                                        letTypeOptionalSite)
                                      (PrefixValues.fullValue
                                        typeOptionalItem typeOptionalComplete
                                        (PrefixValues.completeValue
                                          optionalWaiting typeSequenceItem
                                          typeOptionalItem optionalWitness.next
                                          optionalWitness.advance
                                          optionalPriorValues
                                          typeSequenceValue)) =
                                    (EbnfValue.transport
                                      (congrArg GrammarSite.expression
                                        typeSequenceSiteEq)
                                      typeSequenceValue, ()) := by
                                rw [← optionalPriorRecover]
                                rw [PrefixValues.fullValue_completeValue_eq]
                                exact
                                  (GrammarSymbolValues.transport_append_empty_single_to_local
                                    optionalPriorLayout
                                    ((prefix_complete_layout
                                      optionalWaiting.raw typeSequenceItem.raw
                                      typeOptionalItem.raw
                                      optionalWitness.next
                                      optionalWitness.advance).trans
                                      (prefix_full_layout typeOptionalItem.raw
                                        typeOptionalComplete))
                                    (ProductionId.rhs_opt_some
                                      letTypeOptionalSite)
                                    (congrArg (fun site =>
                                      GrammarSymbol.nonterminal (.aux site))
                                      typeSequenceSiteEq)
                                    optionalEmpty typeSequenceValue).trans
                                  (congrArg (fun value => (value, ()))
                                    (auxiliaryValue_transport_eq
                                      typeSequenceSiteEq typeSequenceValue))
                              have optionalChildShape :
                                  letTypeOptionalSite.child.expression =
                                    letTypeSequenceExpr :=
                                EbnfExpr.optional.inj
                                  (letTypeOptionalSite.expression_eq_optional.symm.trans
                                    thirdShape)
                              have typeSequenceShape :
                                  letTypeSequenceSite.site.expression =
                                    letTypeSequenceExpr :=
                                (congrArg GrammarSite.expression
                                  typeSequenceSiteEq).trans optionalChildShape
                              have semanticViewed := congrArg
                                (EbnfValue.optionalView letTypeSequenceExpr)
                                canonicalTypeFieldEqNoCast
                              have semanticViewed' := semanticViewed.trans
                                (EbnfValue.optionalView_optional_eq_local
                                  letTypeSequenceExpr _)
                              have packedViewed := congrArg
                                (fun value =>
                                  EbnfValue.optionalView letTypeSequenceExpr
                                    (EbnfValue.atShape thirdShape value))
                                typeOptionalPackedEq
                              have packView :=
                                optionalView_atShape_pack_some_eq_local
                                  letTypeOptionalSite thirdShape
                                  optionalChildShape
                                  (PrefixValues.fullValue typeOptionalItem
                                    typeOptionalComplete
                                    (PrefixValues.completeValue
                                      optionalWaiting typeSequenceItem
                                      typeOptionalItem optionalWitness.next
                                      optionalWitness.advance
                                      optionalPriorValues typeSequenceValue))
                              have optionalChildSemanticEq := Option.some.inj
                                (packView.symm.trans
                                  (packedViewed.symm.trans semanticViewed'))
                              have optionalFullHeadEq :=
                                congrArg Prod.fst optionalFullTupleEq
                              have transportedHeadEq := congrArg
                                (EbnfValue.transport optionalChildShape)
                                optionalFullHeadEq
                              have normalizedChildEq :
                                  EbnfValue.transport optionalChildShape
                                      (EbnfValue.transport
                                        (congrArg GrammarSite.expression
                                          typeSequenceSiteEq)
                                        typeSequenceValue) =
                                    EbnfValue.transport
                                      typeSequenceShape
                                      typeSequenceValue := by
                                rw [EbnfValue.transport_trans]
                              have typeSequenceSemanticEq :
                                  EbnfValue.transport
                                      typeSequenceShape
                                      typeSequenceValue =
                                    EbnfValue.sequence [letColonExpr,
                                      .optional letComptimeExpr,
                                      letTypeExpr] (EbnfValues.cons _ _
                                        (EbnfValue.terminalAtom
                                          (.symbol .colon) colon) <|
                                      EbnfValues.cons _ _
                                        (EbnfValue.optional letComptimeExpr
                                          none) <|
                                      EbnfValues.cons _ _
                                        (EbnfValue.ruleAtom .type
                                          ⟨typeSpan,
                                            .comptime typeMarker inner⟩) <|
                                      EbnfValues.nil) :=
                                normalizedChildEq.symm.trans
                                  (transportedHeadEq.symm.trans
                                    optionalChildSemanticEq)
                              cases typeSequenceReduction with
                              | reduce _ typeSequenceValues _
                                  typeSequenceReached typeSequenceComplete
                                  typeSequenceCoherent typeSequenceAction =>
                                  have typeSequencePackedEq :
                                      typeSequenceValue =
                                        SequenceSite.pack letTypeSequenceSite
                                          (PrefixValues.fullValue
                                            typeSequenceItem
                                            typeSequenceComplete
                                            typeSequenceValues) := by
                                    have exact :=
                                      actionReduces_eleven_shapes_exact.mp
                                        typeSequenceAction
                                    simpa [typeSequenceItem] using exact
                                  cases typeSequenceCoherent with
                                  | zero _ _ zero =>
                                      have dotThree :
                                          typeSequenceItem.raw.dot.val = 3 := by
                                        calc
                                          _ = typeSequenceItem.raw.production.rhs.length :=
                                            typeSequenceComplete
                                          _ = 3 := by
                                            simp [typeSequenceItem,
                                              ProductionId.rhs_seq,
                                              letTypeSequenceSite_children]
                                      omega
                                  | scan sequenceBefore _ _ _ sequenceScan _ _ =>
                                      have beforeProduction :
                                          sequenceBefore.raw.production =
                                            .seq letTypeSequenceSite :=
                                        sequenceScan.advance.1.symm
                                      have afterDot :
                                          typeSequenceItem.raw.dot.val = 3 := by
                                        calc
                                          _ = typeSequenceItem.raw.production.rhs.length :=
                                            typeSequenceComplete
                                          _ = 3 := by
                                            simp [typeSequenceItem,
                                              ProductionId.rhs_seq,
                                              letTypeSequenceSite_children]
                                      have beforeDot :
                                          sequenceBefore.raw.dot.val = 2 := by
                                        have advanced := sequenceScan.advance.2.1
                                        omega
                                      have impossible :
                                          some (GrammarSymbol.terminal
                                            sequenceScan.terminal) =
                                            some (GrammarSymbol.nonterminal
                                              (.aux letTypeAtomSite.site)) := by
                                        let index := sequenceBefore.raw.dot.val
                                        calc
                                          _ = sequenceBefore.raw.production.rhs[index]? :=
                                            sequenceScan.next.2.symm
                                          _ = (ProductionId.seq
                                              letTypeSequenceSite).rhs[index]? :=
                                            congrArg (fun production :
                                              ProductionId =>
                                              production.rhs[index]?)
                                              beforeProduction
                                          _ = (ProductionId.seq
                                              letTypeSequenceSite).rhs[2]? := by
                                            have indexTwo : index = 2 :=
                                              beforeDot
                                            rw [indexTwo]
                                          _ = _ := by
                                            simp [ProductionId.rhs_seq,
                                              letTypeSequenceSite_children]
                                      exact GrammarSymbol.noConfusion
                                        (Option.some.inj impossible)
                                  | complete typeSequenceWaiting typeAtomItem _
                                      typeAtomShared typeSequencePriorValues
                                      typeAtomValue typeAtomWitness typeAtomEdge
                                      typeSequencePrior typeAtomReduction =>
                                      have typeSequenceWaitingProduction :
                                          typeSequenceWaiting.raw.production =
                                            .seq letTypeSequenceSite :=
                                        typeAtomWitness.advance.1.symm
                                      have typeSequenceWaitingDot :
                                          typeSequenceWaiting.raw.dot.val = 2 := by
                                        have advanced :=
                                          typeAtomWitness.advance.2.1
                                        have afterDot :
                                            typeSequenceItem.raw.dot.val = 3 := by
                                          calc
                                            _ = typeSequenceItem.raw.production.rhs.length :=
                                              typeSequenceComplete
                                            _ = 3 := by
                                              simp [typeSequenceItem,
                                                ProductionId.rhs_seq,
                                                letTypeSequenceSite_children]
                                        omega
                                      have typeAtomLhs :
                                          typeAtomItem.raw.production.lhs =
                                            .aux letTypeAtomSite.site := by
                                        have selected :
                                            some (GrammarSymbol.nonterminal
                                              typeAtomItem.raw.production.lhs) =
                                              some (GrammarSymbol.nonterminal
                                                (.aux letTypeAtomSite.site)) := by
                                          let index :=
                                            typeSequenceWaiting.raw.dot.val
                                          calc
                                            _ = typeSequenceWaiting.raw.production.rhs[index]? :=
                                              typeAtomWitness.next.2.symm
                                            _ = (ProductionId.seq
                                                letTypeSequenceSite).rhs[index]? :=
                                              congrArg (fun production :
                                                ProductionId =>
                                                production.rhs[index]?)
                                                typeSequenceWaitingProduction
                                            _ = (ProductionId.seq
                                                letTypeSequenceSite).rhs[2]? := by
                                              have indexTwo : index = 2 :=
                                                typeSequenceWaitingDot
                                              rw [indexTwo]
                                            _ = _ := by
                                              simp [ProductionId.rhs_seq,
                                                letTypeSequenceSite_children]
                                        exact GrammarSymbol.nonterminal.inj
                                          (Option.some.inj selected)
                                      have typeAtomProduction :
                                          typeAtomItem.raw.production =
                                            .atom letTypeAtomSite :=
                                        production_eq_atom_of_lhs_local
                                          letTypeAtomSite
                                          typeAtomItem.raw.production
                                          typeAtomLhs
                                      cases typeSequencePrior with
                                      | zero _ _ zero =>
                                          omega
                                      | scan priorBefore _ _ _ priorScan _ _ =>
                                          have beforeProduction :
                                              priorBefore.raw.production =
                                                .seq letTypeSequenceSite :=
                                            priorScan.advance.1.symm.trans
                                              typeSequenceWaitingProduction
                                          have beforeDot :
                                              priorBefore.raw.dot.val = 1 := by
                                            have advanced :=
                                              priorScan.advance.2.1
                                            omega
                                          have impossible :
                                              some (GrammarSymbol.terminal
                                                priorScan.terminal) =
                                                some (GrammarSymbol.nonterminal
                                                  (.aux
                                                    letComptimeOptionalSite.site)) := by
                                            let index := priorBefore.raw.dot.val
                                            calc
                                              _ = priorBefore.raw.production.rhs[index]? :=
                                                priorScan.next.2.symm
                                              _ = (ProductionId.seq
                                                  letTypeSequenceSite).rhs[index]? :=
                                                congrArg (fun production :
                                                  ProductionId =>
                                                  production.rhs[index]?)
                                                  beforeProduction
                                              _ = (ProductionId.seq
                                                  letTypeSequenceSite).rhs[1]? := by
                                                have indexOne : index = 1 :=
                                                  beforeDot
                                                rw [indexOne]
                                              _ = _ := by
                                                simp [ProductionId.rhs_seq,
                                                  letTypeSequenceSite_children]
                                          exact GrammarSymbol.noConfusion
                                            (Option.some.inj impossible)
                                      | complete comptimeWaiting
                                          comptimeOptionalItem _ comptimeShared
                                          comptimePriorValues
                                          comptimeOptionalValue comptimeWitness
                                          comptimeEdge comptimePrior
                                          comptimeOptionalReduction =>
                                          have comptimeWaitingProduction :
                                              comptimeWaiting.raw.production =
                                                .seq letTypeSequenceSite :=
                                            comptimeWitness.advance.1.symm.trans
                                              typeSequenceWaitingProduction
                                          have comptimeWaitingDot :
                                              comptimeWaiting.raw.dot.val = 1 := by
                                            have advanced :=
                                              comptimeWitness.advance.2.1
                                            omega
                                          have comptimeOptionalLhs :
                                              comptimeOptionalItem.raw.production.lhs =
                                                .aux
                                                  letComptimeOptionalSite.site := by
                                            have selected :
                                                some (GrammarSymbol.nonterminal
                                                  comptimeOptionalItem.raw.production.lhs) =
                                                  some (GrammarSymbol.nonterminal
                                                    (.aux
                                                      letComptimeOptionalSite.site)) := by
                                              let index :=
                                                comptimeWaiting.raw.dot.val
                                              calc
                                                _ = comptimeWaiting.raw.production.rhs[index]? :=
                                                  comptimeWitness.next.2.symm
                                                _ = (ProductionId.seq
                                                    letTypeSequenceSite).rhs[index]? :=
                                                  congrArg (fun production :
                                                    ProductionId =>
                                                    production.rhs[index]?)
                                                    comptimeWaitingProduction
                                                _ = (ProductionId.seq
                                                    letTypeSequenceSite).rhs[1]? := by
                                                  have indexOne : index = 1 :=
                                                    comptimeWaitingDot
                                                  rw [indexOne]
                                                _ = _ := by
                                                  simp [ProductionId.rhs_seq,
                                                    letTypeSequenceSite_children]
                                            exact GrammarSymbol.nonterminal.inj
                                              (Option.some.inj selected)
                                          obtain ⟨comptimeBranch,
                                              comptimeOptionalProduction⟩ :=
                                            production_optional_of_lhs
                                              letComptimeOptionalSite
                                              comptimeOptionalItem.raw.production
                                              comptimeOptionalLhs
                                          rcases comptimeOptionalItem with
                                            ⟨⟨comptimeProductionId,
                                              comptimeDot, comptimeOrigin,
                                              comptimeCurrent⟩,
                                              comptimeContext⟩
                                          simp only at comptimeOptionalProduction
                                          subst comptimeProductionId
                                          let comptimeOptionalItem :
                                              ContextualItemKey tokens :=
                                            ⟨⟨.opt letComptimeOptionalSite
                                              comptimeBranch, comptimeDot,
                                              comptimeOrigin,
                                              comptimeCurrent⟩,
                                              comptimeContext⟩
                                          change CoherentReduction file tokens
                                            memo correct final
                                            comptimeOptionalItem
                                            comptimeOptionalValue at comptimeOptionalReduction
                                          rcases typeAtomItem with
                                            ⟨⟨typeAtomProductionId,
                                              typeAtomDot, typeAtomOrigin,
                                              typeAtomCurrent⟩,
                                              typeAtomContext⟩
                                          simp only at typeAtomProduction
                                          subst typeAtomProductionId
                                          let typeAtomItem :
                                              ContextualItemKey tokens :=
                                            ⟨⟨.atom letTypeAtomSite,
                                              typeAtomDot, typeAtomOrigin,
                                              typeAtomCurrent⟩,
                                              typeAtomContext⟩
                                          change CoherentReduction file tokens
                                            memo correct final typeAtomItem
                                            typeAtomValue at typeAtomReduction
                                          have typeChildrenExpressionLayout :
                                              letTypeSequenceSite.children.map
                                                  GrammarSite.expression = [
                                                letColonExpr,
                                                Grammar.optional
                                                  letComptimeExpr,
                                                letTypeExpr] :=
                                            EbnfExpr.sequence.inj
                                              (letTypeSequenceSite.expression_eq_sequence.symm.trans
                                                typeSequenceShape)
                                          have typeExpressionListEq : [
                                                letColonAtomSite.site.expression,
                                                letComptimeOptionalSite.site.expression,
                                                letTypeAtomSite.site.expression] = [
                                                letColonExpr,
                                                Grammar.optional
                                                  letComptimeExpr,
                                                letTypeExpr] := by
                                            simpa only [
                                              letTypeSequenceSite_children,
                                              List.map] using
                                              typeChildrenExpressionLayout
                                          have colonShape :
                                              letColonAtomSite.site.expression =
                                                letColonExpr :=
                                            (List.cons.inj
                                              typeExpressionListEq).1
                                          have typeExpressionTail1 :=
                                            (List.cons.inj
                                              typeExpressionListEq).2
                                          have comptimeShape :
                                              letComptimeOptionalSite.site.expression =
                                                Grammar.optional
                                                  letComptimeExpr :=
                                            (List.cons.inj
                                              typeExpressionTail1).1
                                          have typeExpressionTail2 :=
                                            (List.cons.inj
                                              typeExpressionTail1).2
                                          have typeAtomShape :
                                              letTypeAtomSite.site.expression =
                                                letTypeExpr :=
                                            (List.cons.inj
                                              typeExpressionTail2).1
                                          have comptimePriorLayout :
                                              comptimeWaiting.raw.production.rhs.take
                                                  comptimeWaiting.raw.dot.val = [
                                                GrammarSymbol.nonterminal
                                                  (.aux
                                                    letColonAtomSite.site)] := by
                                            let index :=
                                              comptimeWaiting.raw.dot.val
                                            calc
                                              _ = (ProductionId.seq
                                                  letTypeSequenceSite).rhs.take
                                                    index :=
                                                congrArg (fun production :
                                                  ProductionId =>
                                                  production.rhs.take index)
                                                  comptimeWaitingProduction
                                              _ = (ProductionId.seq
                                                  letTypeSequenceSite).rhs.take
                                                    1 := by
                                                have indexOne : index = 1 :=
                                                  comptimeWaitingDot
                                                rw [indexOne]
                                              _ = _ := by
                                                simp [ProductionId.rhs_seq,
                                                  letTypeSequenceSite_children]
                                          generalize comptimePriorCanonicalEq :
                                              GrammarSymbolValues.transport
                                                comptimePriorLayout
                                                comptimePriorValues =
                                              comptimePriorCanonical
                                          rcases comptimePriorCanonical with
                                            ⟨colonValue, comptimePriorTail⟩
                                          rcases comptimePriorTail with ⟨⟩
                                          have comptimePriorRecover :
                                              GrammarSymbolValues.transport
                                                comptimePriorLayout.symm
                                                (colonValue, ()) =
                                                  comptimePriorValues := by
                                            rw [← comptimePriorCanonicalEq,
                                              GrammarSymbolValues.transport_trans]
                                            exact
                                              GrammarSymbolValues.transport_self
                                                _ _
                                          have typeSequenceTargetLayout :
                                              letTypeSequenceSite.children.map
                                                  (fun child =>
                                                    GrammarSymbol.nonterminal
                                                      (.aux child)) = [
                                                .nonterminal
                                                  (.aux letColonAtomSite.site),
                                                .nonterminal
                                                  comptimeOptionalItem.raw.production.lhs,
                                                .nonterminal
                                                  typeAtomItem.raw.production.lhs] := by
                                            rw [letTypeSequenceSite_children]
                                            rfl
                                          have typeSequenceTupleEq :=
                                            GrammarSymbolValues.transport_append_three_to
                                              comptimePriorLayout
                                              (prefix_complete_layout
                                                comptimeWaiting.raw
                                                comptimeOptionalItem.raw
                                                typeSequenceWaiting.raw
                                                comptimeWitness.next
                                                comptimeWitness.advance)
                                              ((prefix_complete_layout
                                                typeSequenceWaiting.raw
                                                typeAtomItem.raw
                                                typeSequenceItem.raw
                                                typeAtomWitness.next
                                                typeAtomWitness.advance).trans
                                                (prefix_full_layout
                                                  typeSequenceItem.raw
                                                  typeSequenceComplete))
                                              (ProductionId.rhs_seq
                                                letTypeSequenceSite)
                                              typeSequenceTargetLayout
                                              colonValue comptimeOptionalValue
                                              typeAtomValue
                                          rw [← comptimePriorRecover] at typeSequencePackedEq
                                          rw [PrefixValues.fullValue_completeValue_eq]
                                            at typeSequencePackedEq
                                          unfold PrefixValues.completeValue at typeSequencePackedEq
                                          simp only [SequenceSite.pack,
                                            GrammarSymbolValues.view] at typeSequencePackedEq
                                          conv at typeSequencePackedEq in
                                              (GrammarSymbolValues.transport _ _) =>
                                            rw [typeSequenceTupleEq]
                                          let rawTypeSequenceValue :=
                                            EbnfValue.sequence
                                              (letTypeSequenceSite.children.map
                                                GrammarSite.expression)
                                              (EbnfValues.ofAuxiliaries
                                                letTypeSequenceSite.children
                                                (GrammarSymbolValues.transport
                                                  typeSequenceTargetLayout.symm
                                                  (colonValue,
                                                    (comptimeOptionalValue,
                                                      (typeAtomValue, ())))))
                                          rw [typeSequencePackedEq] at typeSequenceSemanticEq
                                          change EbnfValue.transport
                                              typeSequenceShape
                                              (EbnfValue.ofShape
                                                letTypeSequenceSite.expression_eq_sequence
                                                rawTypeSequenceValue) = _ at typeSequenceSemanticEq
                                          unfold EbnfValue.ofShape at typeSequenceSemanticEq
                                          rw [EbnfValue.transport_trans] at typeSequenceSemanticEq
                                          have typeSequenceTransportProof :
                                              letTypeSequenceSite.expression_eq_sequence.symm.trans
                                                  typeSequenceShape =
                                                congrArg EbnfExpr.sequence
                                                  typeChildrenExpressionLayout :=
                                            Subsingleton.elim _ _
                                          rw [typeSequenceTransportProof] at typeSequenceSemanticEq
                                          have canonicalTypeSequenceSemanticEq :
                                              EbnfValue.transport
                                                (congrArg EbnfExpr.sequence
                                                  typeChildrenExpressionLayout)
                                                (EbnfValue.sequence
                                                  (letTypeSequenceSite.children.map
                                                    GrammarSite.expression)
                                                  (EbnfValues.ofAuxiliaries
                                                    letTypeSequenceSite.children
                                                    (GrammarSymbolValues.transport
                                                      typeSequenceTargetLayout.symm
                                                      (colonValue,
                                                        (comptimeOptionalValue,
                                                          (typeAtomValue, ())))))) =
                                                EbnfValue.sequence [letColonExpr,
                                                  Grammar.optional
                                                    letComptimeExpr,
                                                  letTypeExpr]
                                                  (EbnfValues.cons _ _
                                                    (EbnfValue.terminalAtom
                                                      (.symbol .colon) colon) <|
                                                  EbnfValues.cons _ _
                                                    (EbnfValue.optional
                                                      letComptimeExpr none) <|
                                                  EbnfValues.cons _ _
                                                    (EbnfValue.ruleAtom .type
                                                      ⟨typeSpan,
                                                        .comptime typeMarker
                                                          inner⟩) <|
                                                  EbnfValues.nil) := by
                                            exact typeSequenceSemanticEq
                                          have typeFieldsEq := congrArg
                                            (fun value =>
                                              (EbnfValue.sequence3View
                                                letColonExpr
                                                (Grammar.optional
                                                  letComptimeExpr)
                                                letTypeExpr value).2)
                                            canonicalTypeSequenceSemanticEq
                                          have parsedTypeFields :=
                                            letTypeSequenceFields_auxiliary_three_eq
                                              letTypeSequenceSite_children
                                              colonShape comptimeShape
                                              typeAtomShape (by rfl) (by rfl)
                                              typeSequenceTargetLayout
                                              typeChildrenExpressionLayout
                                              colonValue comptimeOptionalValue
                                              typeAtomValue
                                          have expectedTypeFields :=
                                            sequence3View_three_second_third
                                              letColonExpr
                                              (Grammar.optional letComptimeExpr)
                                              letTypeExpr
                                              (EbnfValue.terminalAtom
                                                (.symbol .colon) colon)
                                              (EbnfValue.optional
                                                letComptimeExpr none)
                                              (EbnfValue.ruleAtom .type
                                                ⟨typeSpan,
                                                  .comptime typeMarker inner⟩)
                                          rw [parsedTypeFields,
                                            expectedTypeFields] at typeFieldsEq
                                          have comptimeFieldEq :=
                                            congrArg Prod.fst typeFieldsEq
                                          have typeAtomFieldEq :=
                                            congrArg Prod.snd typeFieldsEq
                                          have comptimeFieldEqNoCast :
                                              EbnfValue.atShape comptimeShape
                                                  comptimeOptionalValue =
                                                EbnfValue.optional
                                                  letComptimeExpr none := by
                                            exact comptimeFieldEq
                                          have typeAtomFieldEqNoCast :
                                              EbnfValue.atShape typeAtomShape
                                                  typeAtomValue =
                                                EbnfValue.ruleAtom .type
                                                  ⟨typeSpan,
                                                    .comptime typeMarker
                                                      inner⟩ := by
                                            exact typeAtomFieldEq
                                          cases comptimeOptionalReduction with
                                          | reduce _ comptimeValues _
                                              comptimeReached comptimeComplete
                                              comptimeCoherent comptimeAction =>
                                              have comptimePackedEq :
                                                  comptimeOptionalValue =
                                                    OptionalSite.pack
                                                      letComptimeOptionalSite
                                                      comptimeBranch
                                                      (PrefixValues.fullValue
                                                        comptimeOptionalItem
                                                        comptimeComplete
                                                        comptimeValues) := by
                                                have exact :=
                                                  actionReduces_eleven_shapes_exact.mp
                                                    comptimeAction
                                                simpa [comptimeOptionalItem]
                                                  using exact
                                              cases comptimeBranch with
                                              | some =>
                                                  have comptimeChildShape :
                                                      letComptimeOptionalSite.child.expression =
                                                        letComptimeExpr :=
                                                    EbnfExpr.optional.inj
                                                      (letComptimeOptionalSite.expression_eq_optional.symm.trans
                                                        comptimeShape)
                                                  have semanticComptimeView :=
                                                    congrArg
                                                      (EbnfValue.optionalView
                                                        letComptimeExpr)
                                                      comptimeFieldEqNoCast
                                                  have semanticComptimeView' :=
                                                    semanticComptimeView.trans
                                                      (EbnfValue.optionalView_optional_eq_local
                                                        letComptimeExpr _)
                                                  have packedComptimeView :=
                                                    congrArg
                                                      (fun value =>
                                                        EbnfValue.optionalView
                                                          letComptimeExpr
                                                          (EbnfValue.atShape
                                                            comptimeShape
                                                            value))
                                                      comptimePackedEq
                                                  have presentComptimeView :=
                                                    optionalView_atShape_pack_some_eq_local
                                                      letComptimeOptionalSite
                                                      comptimeShape
                                                      comptimeChildShape
                                                      (PrefixValues.fullValue
                                                        comptimeOptionalItem
                                                        comptimeComplete
                                                        comptimeValues)
                                                  have impossible :=
                                                    presentComptimeView.symm.trans
                                                      (packedComptimeView.symm.trans
                                                        semanticComptimeView')
                                                  cases impossible
                                              | none =>
                                                  have g04Member :
                                                      (.G04_letComptime,
                                                        .negative) ∈
                                                        guardOf
                                                          (.opt
                                                            letComptimeOptionalSite
                                                            .none) := by
                                                    have notParameter :
                                                        letComptimeOptionalSite.site.isAt
                                                            .parameter [0] = false := by
                                                      run_tac
                                                        Lean.Meta.withTransparency .all do
                                                          (← Lean.Elab.Tactic.getMainGoal).refl
                                                    have atLetComptime :
                                                        letComptimeOptionalSite.site.isAt
                                                            .letBinding [2, 0, 1] = true := by
                                                      run_tac
                                                        Lean.Meta.withTransparency .all do
                                                          (← Lean.Elab.Tactic.getMainGoal).refl
                                                    simp [guardOf,
                                                      notParameter,
                                                      atLetComptime]
                                                  have comptimeEnabled :=
                                                    comptimeReached.enabledProductionInstance
                                                  rcases comptimeEnabled
                                                      .G04_letComptime .negative
                                                      g04Member with
                                                    ⟨g04Key,
                                                      g04ProductionEq,
                                                      g04GuardEq,
                                                      g04PolarityEq,
                                                      g04Witness⟩
                                                  have g04Anchor :=
                                                    g04Key.property.2
                                                  have g04SiteOrigin :
                                                      g04Key.guardInstance.siteCursor =
                                                        comptimeOptionalItem.raw.origin := by
                                                    have anchor :
                                                        GuardAnchor
                                                          g04Key.productionInstance
                                                          (g04Key.guardInstance.guard,
                                                            g04Key.polarity)
                                                          g04Key.guardInstance :=
                                                      g04Anchor
                                                    rw [g04ProductionEq,
                                                      g04GuardEq,
                                                      g04PolarityEq] at anchor
                                                    exact anchor.2.2.1
                                                  rcases g04Witness with
                                                    ⟨g04Decision, g04Memo,
                                                      g04Evidence,
                                                      g04Allows⟩
                                                  have g04DecisionEq :
                                                      g04Decision = .negative := by
                                                    rw [g04PolarityEq] at g04Allows
                                                    cases g04Decision with
                                                    | positive =>
                                                        unfold GuardDecision.allows
                                                          Polarity.accepts at g04Allows
                                                        cases g04Allows
                                                    | negative => rfl
                                                    | neutral =>
                                                        unfold GuardEvidence at g04Evidence
                                                        rw [g04GuardEq] at g04Evidence
                                                        exact False.elim g04Evidence.2
                                                  subst g04Decision
                                                  have g04NoComptime :
                                                      ¬ ∃ matched :
                                                          MatchedTerminal file tokens
                                                            (.contextualKeyword
                                                              .comptimeKw),
                                                        matched.cursor.beforeBoundary =
                                                          g04Key.guardInstance.siteCursor := by
                                                    unfold GuardEvidence at g04Evidence
                                                    rw [g04GuardEq] at g04Evidence
                                                    exact g04Evidence.2
                                                  cases typeAtomReduction with
                                                  | reduce _ typeAtomValues _
                                                      typeAtomReached
                                                      typeAtomComplete
                                                      typeAtomCoherent
                                                      typeAtomAction =>
                                                      have typeAtomPackedEq :
                                                          typeAtomValue =
                                                            AtomSite.pack
                                                              letTypeAtomSite
                                                              (PrefixValues.fullValue
                                                                typeAtomItem
                                                                typeAtomComplete
                                                                typeAtomValues) := by
                                                        have exact :=
                                                          actionReduces_eleven_shapes_exact.mp
                                                            typeAtomAction
                                                        simpa [typeAtomItem]
                                                          using exact
                                                      cases typeAtomCoherent with
                                                      | zero _ _ zero =>
                                                          have dotOne :
                                                              typeAtomItem.raw.dot.val =
                                                                1 := by
                                                            calc
                                                              _ = typeAtomItem.raw.production.rhs.length :=
                                                                typeAtomComplete
                                                              _ = 1 := by
                                                                simp [typeAtomItem,
                                                                  ProductionId.rhs]
                                                          omega
                                                      | scan atomBefore _ _ _
                                                          atomScan _ _ =>
                                                          have beforeProduction :
                                                              atomBefore.raw.production =
                                                                .atom
                                                                  letTypeAtomSite :=
                                                            atomScan.advance.1.symm
                                                          have beforeDot :
                                                              atomBefore.raw.dot.val =
                                                                0 := by
                                                            have advanced :=
                                                              atomScan.advance.2.1
                                                            have afterDot :
                                                                typeAtomItem.raw.dot.val =
                                                                  1 := by
                                                              calc
                                                                _ = typeAtomItem.raw.production.rhs.length :=
                                                                  typeAtomComplete
                                                                _ = 1 := by
                                                                  simp [typeAtomItem,
                                                                    ProductionId.rhs]
                                                            omega
                                                          have impossible :
                                                              some
                                                                  (GrammarSymbol.terminal
                                                                    atomScan.terminal) =
                                                                some
                                                                  (GrammarSymbol.nonterminal
                                                                    (.rule .type)) := by
                                                            let index :=
                                                              atomBefore.raw.dot.val
                                                            calc
                                                              _ = atomBefore.raw.production.rhs[index]? :=
                                                                atomScan.next.2.symm
                                                              _ = (ProductionId.atom
                                                                  letTypeAtomSite).rhs[index]? :=
                                                                congrArg
                                                                  (fun production :
                                                                    ProductionId =>
                                                                    production.rhs[index]?)
                                                                  beforeProduction
                                                              _ = (ProductionId.atom
                                                                  letTypeAtomSite).rhs[0]? := by
                                                                have indexZero :
                                                                    index = 0 :=
                                                                  beforeDot
                                                                rw [indexZero]
                                                              _ = _ := by
                                                                have atomEq :
                                                                    letTypeAtomSite.atom =
                                                                      .nonterminal .type :=
                                                                  EbnfExpr.atom.inj
                                                                    (letTypeAtomSite.expression_eq_atom.symm.trans
                                                                      typeAtomShape)
                                                                simp [ProductionId.rhs,
                                                                  letTypeAtomSite.symbol_eq,
                                                                  atomEq,
                                                                  EbnfAtom.grammarSymbol]
                                                          exact
                                                            GrammarSymbol.noConfusion
                                                              (Option.some.inj
                                                                impossible)
                                                      | complete atomWaiting
                                                          typeRootItem _
                                                          typeRootShared
                                                          atomPriorValues
                                                          typeRootValue
                                                          atomWitness atomEdge
                                                          atomPrior
                                                          typeRootReduction =>
                                                          have atomWaitingProduction :
                                                              atomWaiting.raw.production =
                                                                .atom
                                                                  letTypeAtomSite :=
                                                            atomWitness.advance.1.symm
                                                          have atomWaitingDot :
                                                              atomWaiting.raw.dot.val =
                                                                0 := by
                                                            have advanced :=
                                                              atomWitness.advance.2.1
                                                            have afterDot :
                                                                typeAtomItem.raw.dot.val =
                                                                  1 := by
                                                              calc
                                                                _ = typeAtomItem.raw.production.rhs.length :=
                                                                  typeAtomComplete
                                                                _ = 1 := by
                                                                  simp [typeAtomItem,
                                                                    ProductionId.rhs]
                                                            omega
                                                          have typeRootLhs :
                                                              typeRootItem.raw.production.lhs =
                                                                .rule .type := by
                                                            have selected :
                                                                some
                                                                    (GrammarSymbol.nonterminal
                                                                      typeRootItem.raw.production.lhs) =
                                                                  some
                                                                    (GrammarSymbol.nonterminal
                                                                      (.rule .type)) := by
                                                              let index :=
                                                                atomWaiting.raw.dot.val
                                                              calc
                                                                _ = atomWaiting.raw.production.rhs[index]? :=
                                                                  atomWitness.next.2.symm
                                                                _ = (ProductionId.atom
                                                                    letTypeAtomSite).rhs[index]? :=
                                                                  congrArg
                                                                    (fun production :
                                                                      ProductionId =>
                                                                      production.rhs[index]?)
                                                                    atomWaitingProduction
                                                                _ = (ProductionId.atom
                                                                    letTypeAtomSite).rhs[0]? := by
                                                                  have indexZero :
                                                                      index = 0 :=
                                                                    atomWaitingDot
                                                                  rw [indexZero]
                                                                _ = _ := by
                                                                  have atomEq :
                                                                      letTypeAtomSite.atom =
                                                                        .nonterminal .type :=
                                                                    EbnfExpr.atom.inj
                                                                      (letTypeAtomSite.expression_eq_atom.symm.trans
                                                                        typeAtomShape)
                                                                  simp [ProductionId.rhs,
                                                                    letTypeAtomSite.symbol_eq,
                                                                    atomEq,
                                                                    EbnfAtom.grammarSymbol]
                                                            exact
                                                              GrammarSymbol.nonterminal.inj
                                                                (Option.some.inj
                                                                  selected)
                                                          have typeRootProduction :
                                                              typeRootItem.raw.production =
                                                                .root .type :=
                                                            production_eq_root_of_lhs_local
                                                              .type
                                                              typeRootItem.raw.production
                                                              typeRootLhs
                                                          rcases typeRootItem with
                                                            ⟨⟨typeRootProductionId,
                                                              typeRootDot,
                                                              typeRootOrigin,
                                                              typeRootCurrent⟩,
                                                              typeRootContext⟩
                                                          simp only at typeRootProduction
                                                          subst typeRootProductionId
                                                          let typeRootItem :
                                                              ContextualItemKey tokens :=
                                                            ⟨⟨.root .type,
                                                              typeRootDot,
                                                              typeRootOrigin,
                                                              typeRootCurrent⟩,
                                                              typeRootContext⟩
                                                          change CoherentReduction
                                                            file tokens memo correct final
                                                            typeRootItem typeRootValue at typeRootReduction
                                                          have atomPriorLayout :
                                                              atomWaiting.raw.production.rhs.take
                                                                  atomWaiting.raw.dot.val = [] := by
                                                            rw [atomWaitingDot]
                                                            simp
                                                          let atomEmpty :
                                                              GrammarSymbolValues file tokens [] :=
                                                            GrammarSymbolValues.transport
                                                              atomPriorLayout
                                                              atomPriorValues
                                                          have atomPriorRecover :
                                                              GrammarSymbolValues.transport
                                                                  atomPriorLayout.symm
                                                                  atomEmpty =
                                                                atomPriorValues := by
                                                            rw [← show
                                                                GrammarSymbolValues.transport
                                                                    atomPriorLayout
                                                                    atomPriorValues = atomEmpty
                                                                  from rfl,
                                                              GrammarSymbolValues.transport_trans]
                                                            exact
                                                              GrammarSymbolValues.transport_self
                                                                _ _
                                                          have atomEq :
                                                              letTypeAtomSite.atom =
                                                                .nonterminal .type :=
                                                            EbnfExpr.atom.inj
                                                              (letTypeAtomSite.expression_eq_atom.symm.trans
                                                                typeAtomShape)
                                                          have siteSymbolEq :
                                                              letTypeAtomSite.symbol =
                                                                .nonterminal (.rule .type) :=
                                                            letTypeAtomSite.symbol_eq.trans
                                                              (congrArg
                                                                EbnfAtom.grammarSymbol atomEq)
                                                          have atomSymbolLayout :
                                                              .nonterminal
                                                                  typeRootItem.raw.production.lhs =
                                                                letTypeAtomSite.symbol := by
                                                            exact siteSymbolEq.symm
                                                          have atomFullTupleEq :=
                                                            GrammarSymbolValues.transport_append_empty_single_to_local
                                                              atomPriorLayout
                                                              ((prefix_complete_layout
                                                                  atomWaiting.raw
                                                                  typeRootItem.raw
                                                                  typeAtomItem.raw
                                                                  atomWitness.next
                                                                  atomWitness.advance).trans
                                                                (prefix_full_layout
                                                                  typeAtomItem.raw
                                                                  typeAtomComplete))
                                                              (ProductionId.rhs_atom
                                                                letTypeAtomSite)
                                                              atomSymbolLayout
                                                              atomEmpty
                                                              typeRootValue
                                                          rw [← atomPriorRecover] at typeAtomPackedEq
                                                          rw [PrefixValues.fullValue_completeValue_eq]
                                                            at typeAtomPackedEq
                                                          have typeAtomFieldPackedEq :=
                                                            typeAtomFieldEqNoCast
                                                          rw [typeAtomPackedEq] at typeAtomFieldPackedEq
                                                          have shapeEq :
                                                              typeAtomShape =
                                                                letTypeAtomSite.expression_eq_atom.trans
                                                                  (congrArg EbnfExpr.atom
                                                                    atomEq) :=
                                                            Subsingleton.elim _ _
                                                          rw [shapeEq,
                                                            EbnfValue.atShape_trans_eq_local]
                                                            at typeAtomFieldPackedEq
                                                          change AtomSite.packAtAtom
                                                              letTypeAtomSite
                                                              (.nonterminal .type)
                                                              atomEq _ = _ at typeAtomFieldPackedEq
                                                          rw [AtomSite.pack_rule_eq] at typeAtomFieldPackedEq
                                                          have packedHeadEq :=
                                                            EbnfValue.ruleAtom_injective .type
                                                              typeAtomFieldPackedEq
                                                          have atomFullHeadEq :=
                                                            congrArg Prod.fst atomFullTupleEq
                                                          unfold GrammarSymbolValues.view at packedHeadEq
                                                          rw [atomFullHeadEq] at packedHeadEq
                                                          have packedHeadNormal :
                                                              Eq.mp
                                                                  (congrArg
                                                                    (GrammarSymbolValue
                                                                      file tokens)
                                                                    (congrArg
                                                                      EbnfAtom.grammarSymbol
                                                                      atomEq))
                                                                  (Eq.mp
                                                                    (congrArg
                                                                      (GrammarSymbolValue
                                                                        file tokens)
                                                                      letTypeAtomSite.symbol_eq)
                                                                    (Eq.mp
                                                                      (congrArg
                                                                        (GrammarSymbolValue
                                                                          file tokens)
                                                                        atomSymbolLayout)
                                                                      typeRootValue)) =
                                                                typeRootValue :=
                                                            Eq.mp_three_cycle_local
                                                              (congrArg
                                                                (GrammarSymbolValue file tokens)
                                                                atomSymbolLayout)
                                                              (congrArg
                                                                (GrammarSymbolValue file tokens)
                                                                letTypeAtomSite.symbol_eq)
                                                              (congrArg
                                                                (GrammarSymbolValue file tokens)
                                                                (congrArg
                                                                  EbnfAtom.grammarSymbol
                                                                  atomEq))
                                                              typeRootValue
                                                          have typeRootSemanticEq :
                                                              typeRootValue =
                                                                ⟨typeSpan,
                                                                  .comptime typeMarker
                                                                    inner⟩ := by
                                                            calc
                                                              typeRootValue = _ :=
                                                                packedHeadNormal.symm
                                                              _ = _ := packedHeadEq
                                                          cases typeRootReduction with
                                                          | reduce _ typeRootValues _
                                                              typeRootReached
                                                              typeRootComplete
                                                              typeRootCoherent
                                                              typeRootAction =>
                                                              have typeReduction :
                                                                  RuleReduction file tokens
                                                                    .type
                                                                    typeRootItem.raw.origin
                                                                    typeRootItem.raw.current
                                                                    (RootAction.unpack .type
                                                                      (PrefixValues.fullValue
                                                                        typeRootItem
                                                                        typeRootComplete
                                                                        typeRootValues))
                                                                    typeRootValue := by
                                                                have exact :=
                                                                  actionReduces_eleven_shapes_exact.mp
                                                                    typeRootAction
                                                                simpa [typeRootItem] using exact
                                                              have typeRootDotEq :
                                                                  typeRootDot =
                                                                    (CanonicalCompleteRootItem
                                                                      tokens .type
                                                                      typeRootOrigin
                                                                      typeRootCurrent
                                                                      typeRootContext).raw.dot := by
                                                                apply Fin.ext
                                                                exact typeRootComplete
                                                              subst typeRootDot
                                                              change CoherentPrefix file tokens
                                                                memo correct final
                                                                (CanonicalCompleteRootItem
                                                                  tokens .type
                                                                  typeRootOrigin
                                                                  typeRootCurrent
                                                                  typeRootContext)
                                                                typeRootValues at typeRootCoherent
                                                              obtain ⟨choiceBranch,
                                                                  choiceItem,
                                                                  choiceProduction,
                                                                  choiceValue,
                                                                  choiceChildValue,
                                                                  choiceValues,
                                                                  choiceComplete,
                                                                  choiceReduction,
                                                                  choiceCoherent,
                                                                  choiceReached,
                                                                  choiceChildEq,
                                                                  choiceOriginEq,
                                                                  branchTagEq,
                                                                  rootChoiceInputEq⟩ :=
                                                                coherentTypeRoot_branchTag_eq
                                                                  typeRootCoherent
                                                              generalize typeInputEq :
                                                                  (RootAction.unpack .type
                                                                    (PrefixValues.fullValue
                                                                      typeRootItem
                                                                      typeRootComplete
                                                                      typeRootValues)) =
                                                                    typeInput at typeReduction
                                                              cases typeReduction with
                                                              | typeComptime _ _ comptimeToken
                                                                  parsedInner comptimeProjects
                                                                  typeWitness =>
                                                                  have semanticTagEq :=
                                                                    congrArg
                                                                      typeRootBranchTag
                                                                      typeInputEq
                                                                  have semanticTagZero :
                                                                      typeRootBranchTag
                                                                          (RootAction.unpack .type
                                                                            (PrefixValues.fullValue
                                                                              typeRootItem
                                                                              typeRootComplete
                                                                              typeRootValues)) = 0 := by
                                                                    exact semanticTagEq.trans
                                                                      (typeRootBranchTag_zero_local _)
                                                                  have semanticTagZeroCanonical :
                                                                      typeRootBranchTag
                                                                          (RootAction.unpack .type
                                                                            (PrefixValues.fullValue
                                                                              (CanonicalCompleteRootItem
                                                                                tokens .type
                                                                                typeRootOrigin
                                                                                typeRootCurrent
                                                                                typeRootContext)
                                                                              (canonicalCompleteRootItem_complete
                                                                                .type typeRootOrigin
                                                                                typeRootCurrent
                                                                                typeRootContext)
                                                                              typeRootValues)) = 0 := by
                                                                    change typeRootBranchTag
                                                                      (RootAction.unpack .type
                                                                        (PrefixValues.fullValue
                                                                          (CanonicalCompleteRootItem
                                                                            tokens .type
                                                                            typeRootOrigin
                                                                            typeRootCurrent
                                                                            typeRootContext)
                                                                          typeRootComplete
                                                                          typeRootValues)) = 0 at semanticTagZero
                                                                    have completeEq :
                                                                        typeRootComplete =
                                                                          canonicalCompleteRootItem_complete
                                                                            .type typeRootOrigin
                                                                            typeRootCurrent
                                                                            typeRootContext :=
                                                                      Subsingleton.elim _ _
                                                                    rw [completeEq] at semanticTagZero
                                                                    exact semanticTagZero
                                                                  have branchZero :
                                                                      choiceBranch.val = 0 := by
                                                                    exact branchTagEq.symm.trans
                                                                      semanticTagZeroCanonical
                                                                  have notStatement :
                                                                      typeRootChoiceSite.site.isAt
                                                                          .statement [] = false := by
                                                                    run_tac
                                                                      Lean.Meta.withTransparency .all do
                                                                        (← Lean.Elab.Tactic.getMainGoal).refl
                                                                  have atType :
                                                                      typeRootChoiceSite.site.isAt
                                                                          .type [] = true := by
                                                                    run_tac
                                                                      Lean.Meta.withTransparency .all do
                                                                        (← Lean.Elab.Tactic.getMainGoal).refl
                                                                  have g05Member :
                                                                      (.G05_typeComptime,
                                                                        .positive) ∈
                                                                        guardOf
                                                                          choiceItem.raw.production := by
                                                                    rw [choiceProduction]
                                                                    simp [guardOf,
                                                                      notStatement, atType,
                                                                      branchZero]
                                                                  have choiceEnabled :=
                                                                    choiceReached.enabledProductionInstance
                                                                  rcases choiceEnabled
                                                                      .G05_typeComptime .positive
                                                                      g05Member with
                                                                    ⟨g05Key,
                                                                      g05ProductionEq,
                                                                      g05GuardEq,
                                                                      g05PolarityEq,
                                                                      g05Witness⟩
                                                                  have g05Anchor :=
                                                                    g05Key.property.2
                                                                  have g05SiteOrigin :
                                                                      g05Key.guardInstance.siteCursor =
                                                                        choiceItem.raw.origin := by
                                                                    have anchor :
                                                                        GuardAnchor
                                                                          g05Key.productionInstance
                                                                          (g05Key.guardInstance.guard,
                                                                            g05Key.polarity)
                                                                          g05Key.guardInstance :=
                                                                      g05Anchor
                                                                    rw [g05ProductionEq,
                                                                      g05GuardEq,
                                                                      g05PolarityEq] at anchor
                                                                    exact anchor.2.2.1
                                                                  rcases g05Witness with
                                                                    ⟨g05Decision, g05Memo,
                                                                      g05Evidence,
                                                                      g05Allows⟩
                                                                  have g05DecisionEq :
                                                                      g05Decision = .positive := by
                                                                    rw [g05PolarityEq] at g05Allows
                                                                    cases g05Decision with
                                                                    | positive => rfl
                                                                    | negative =>
                                                                        unfold GuardDecision.allows
                                                                          Polarity.accepts at g05Allows
                                                                        cases g05Allows
                                                                    | neutral =>
                                                                        unfold GuardEvidence at g05Evidence
                                                                        rw [g05GuardEq] at g05Evidence
                                                                        exact False.elim g05Evidence.2
                                                                  subst g05Decision
                                                                  have g05Comptime :
                                                                      ∃ matched :
                                                                          MatchedTerminal file tokens
                                                                            (.contextualKeyword
                                                                              .comptimeKw),
                                                                        matched.cursor.beforeBoundary =
                                                                          g05Key.guardInstance.siteCursor := by
                                                                    unfold GuardEvidence at g05Evidence
                                                                    rw [g05GuardEq] at g05Evidence
                                                                    exact g05Evidence.2
                                                                  rcases g05Comptime with
                                                                    ⟨g05Matched, g05MatchedAt⟩
                                                                  have atomWaitingOriginCurrent :
                                                                      atomWaiting.raw.origin =
                                                                        atomWaiting.raw.current :=
                                                                    contextualReach_zero_origin_eq_current
                                                                      atomEdge.2.1 atomWaitingDot
                                                                  have comptimeDotZero :
                                                                      comptimeOptionalItem.raw.dot.val = 0 := by
                                                                    calc
                                                                      _ = comptimeOptionalItem.raw.production.rhs.length :=
                                                                        comptimeComplete
                                                                      _ = 0 := by
                                                                        simp [comptimeOptionalItem,
                                                                          ProductionId.rhs]
                                                                  have comptimeOriginCurrent :
                                                                      comptimeOptionalItem.raw.origin =
                                                                        comptimeOptionalItem.raw.current :=
                                                                    contextualReach_zero_origin_eq_current
                                                                      comptimeReached comptimeDotZero
                                                                  have typeRootOriginEqComptimeOrigin :
                                                                      typeRootOrigin =
                                                                        comptimeOptionalItem.raw.origin := by
                                                                    calc
                                                                      typeRootOrigin = typeRootShared :=
                                                                        atomWitness.finishedAtShared
                                                                      _ = atomWaiting.raw.current :=
                                                                        atomWitness.waitingAtShared.symm
                                                                      _ = atomWaiting.raw.origin :=
                                                                        atomWaitingOriginCurrent.symm
                                                                      _ = typeAtomItem.raw.origin :=
                                                                        atomWitness.advance.2.2.1.symm
                                                                      _ = typeAtomShared :=
                                                                        typeAtomWitness.finishedAtShared
                                                                      _ = typeSequenceWaiting.raw.current :=
                                                                        typeAtomWitness.waitingAtShared.symm
                                                                      _ = comptimeOptionalItem.raw.current :=
                                                                        comptimeWitness.advance.2.2.2
                                                                      _ = comptimeOptionalItem.raw.origin :=
                                                                        comptimeOriginCurrent.symm
                                                                  apply g04NoComptime
                                                                  refine ⟨g05Matched, ?_⟩
                                                                  exact g05MatchedAt.trans
                                                                    (g05SiteOrigin.trans
                                                                      (choiceOriginEq.trans
                                                                        (typeRootOriginEqComptimeOrigin.trans
                                                                          g04SiteOrigin.symm)))
                                                              | typeAtomOnly _ _ parsedAtom =>
                                                                  have semanticTagEq :=
                                                                    congrArg
                                                                      typeRootBranchTag
                                                                      typeInputEq
                                                                  have semanticTagOne :
                                                                      typeRootBranchTag
                                                                          (RootAction.unpack .type
                                                                            (PrefixValues.fullValue
                                                                              typeRootItem
                                                                              typeRootComplete
                                                                              typeRootValues)) = 1 := by
                                                                    exact semanticTagEq.trans
                                                                      (typeRootBranchTag_one_local _)
                                                                  change typeRootBranchTag
                                                                    (RootAction.unpack .type
                                                                      (PrefixValues.fullValue
                                                                        (CanonicalCompleteRootItem
                                                                          tokens .type
                                                                          typeRootOrigin
                                                                          typeRootCurrent
                                                                          typeRootContext)
                                                                        typeRootComplete
                                                                        typeRootValues)) = 1 at semanticTagOne
                                                                  have completeEq :
                                                                      typeRootComplete =
                                                                        canonicalCompleteRootItem_complete
                                                                          .type typeRootOrigin
                                                                          typeRootCurrent
                                                                          typeRootContext :=
                                                                    Subsingleton.elim _ _
                                                                  rw [completeEq] at semanticTagOne
                                                                  have branchOne :
                                                                      choiceBranch.val = 1 :=
                                                                    branchTagEq.symm.trans
                                                                      semanticTagOne
                                                                  have choiceBranchEq :
                                                                      choiceBranch =
                                                                        typePlainChoiceBranch :=
                                                                    Fin.ext branchOne
                                                                  have typeInputEqCanonical :=
                                                                    typeInputEq
                                                                  change RootAction.unpack .type
                                                                    (PrefixValues.fullValue
                                                                      (CanonicalCompleteRootItem
                                                                        tokens .type
                                                                        typeRootOrigin
                                                                        typeRootCurrent
                                                                      typeRootContext)
                                                                      typeRootComplete
                                                                      typeRootValues) = _ at typeInputEqCanonical
                                                                  rw [completeEq] at typeInputEqCanonical
                                                                  have packedInputEq :=
                                                                    rootChoiceInputEq.symm.trans
                                                                      typeInputEqCanonical
                                                                  have branchesEq :
                                                                      typeRootChoiceSite.branchExpressions.toList =
                                                                        [typeComptimeBranchExpr,
                                                                          typePlainBranchExpr] :=
                                                                    EbnfExpr.choice.inj
                                                                      typeRootChoiceLayout_local
                                                                  have choiceLayoutProofEq :
                                                                      typeRootChoiceLayout_local =
                                                                        congrArg EbnfExpr.choice
                                                                          branchesEq :=
                                                                    Subsingleton.elim _ _
                                                                  rw [choiceLayoutProofEq] at packedInputEq
                                                                  let plainValue :
                                                                      EbnfValue file tokens
                                                                        typePlainBranchExpr :=
                                                                    EbnfValue.sequence
                                                                      [Grammar.nonterminal .typeAtom,
                                                                        Grammar.optional
                                                                          (Grammar.sequence
                                                                            [Grammar.symbol .arrow,
                                                                              Grammar.nonterminal .type])]
                                                                      (EbnfValues.cons _ _
                                                                        (EbnfValue.ruleAtom
                                                                          .typeAtom typeRootValue)
                                                                        (EbnfValues.cons _ _
                                                                          (EbnfValue.optional
                                                                            (Grammar.sequence
                                                                              [Grammar.symbol .arrow,
                                                                                Grammar.nonterminal .type])
                                                                            none)
                                                                          EbnfValues.nil))
                                                                  change EbnfValue.transport
                                                                      (congrArg EbnfExpr.choice branchesEq)
                                                                      (EbnfValue.choice
                                                                        typeRootChoiceSite.branchExpressions.toList
                                                                        ⟨typeRootChoiceSite.branchListIndex
                                                                            choiceBranch,
                                                                          choiceChildValue⟩) =
                                                                    EbnfValue.transport (Eq.refl _)
                                                                      (EbnfValue.choice
                                                                        [typeComptimeBranchExpr,
                                                                          typePlainBranchExpr]
                                                                        ⟨1, plainValue⟩) at packedInputEq
                                                                  simp [EbnfValue.transport] at packedInputEq
                                                                  have choicePairEq :=
                                                                    choice_transport_pair_heq_local
                                                                      branchesEq
                                                                      (typeRootChoiceSite.branchListIndex
                                                                        choiceBranch)
                                                                      choiceChildValue
                                                                      ⟨1, by decide⟩
                                                                      plainValue
                                                                      packedInputEq
                                                                  have plainChildHEq :
                                                                      HEq choiceChildValue plainValue :=
                                                                    choicePairEq.2
                                                                  have plainBranchExprEq :
                                                                      typeRootChoiceSite.branchExpressions.get
                                                                          typePlainChoiceBranch =
                                                                        typePlainBranchExpr := by
                                                                    calc
                                                                      _ = (typeRootChoiceSite.branch
                                                                          typePlainChoiceBranch).expression :=
                                                                        (typeRootChoiceSite.branch_expression
                                                                          typePlainChoiceBranch).symm
                                                                      _ = typePlainSequenceSite.site.expression :=
                                                                        congrArg GrammarSite.expression
                                                                          typePlainChoiceBranch_site
                                                                      _ = _ := typePlainSequenceSite_shape
                                                                  have childExpressionEq :
                                                                      typeRootChoiceSite.branchExpressions.toList.get
                                                                          (typeRootChoiceSite.branchListIndex
                                                                            choiceBranch) =
                                                                        typePlainBranchExpr := by
                                                                    calc
                                                                      _ = typeRootChoiceSite.branchExpressions.get
                                                                          choiceBranch :=
                                                                        typeRootChoiceSite.branch_get_toList
                                                                          choiceBranch
                                                                      _ = typeRootChoiceSite.branchExpressions.get
                                                                          typePlainChoiceBranch := by
                                                                        rw [choiceBranchEq]
                                                                      _ = _ := plainBranchExprEq
                                                                  have transportedChildHEq :
                                                                      HEq
                                                                        (EbnfValue.transport
                                                                          childExpressionEq
                                                                          choiceChildValue)
                                                                        plainValue :=
                                                                    (cast_heq
                                                                      (congrArg
                                                                        (EbnfValue file tokens)
                                                                        childExpressionEq)
                                                                      choiceChildValue).trans
                                                                        plainChildHEq
                                                                  have transportedChildEq :
                                                                      EbnfValue.transport
                                                                          childExpressionEq
                                                                          choiceChildValue =
                                                                        plainValue :=
                                                                    eq_of_heq transportedChildHEq
                                                                  have choiceProductionPlain :
                                                                      choiceItem.raw.production =
                                                                        .choice typeRootChoiceSite
                                                                          typePlainChoiceBranch :=
                                                                    choiceProduction.trans
                                                                      (congrArg
                                                                        (ProductionId.choice
                                                                          typeRootChoiceSite)
                                                                        choiceBranchEq)
                                                                  cases choiceCoherent with
                                                                  | zero _ _ zero =>
                                                                      have dotOne :
                                                                          choiceItem.raw.dot.val = 1 := by
                                                                        calc
                                                                          _ = choiceItem.raw.production.rhs.length :=
                                                                            choiceComplete
                                                                          _ = 1 := by
                                                                            rw [choiceProductionPlain]
                                                                            simp [ProductionId.rhs]
                                                                      omega
                                                                  | scan choiceBefore _ _ _ choiceScan _ _ =>
                                                                      have beforeProduction :
                                                                          choiceBefore.raw.production =
                                                                            .choice typeRootChoiceSite
                                                                              typePlainChoiceBranch :=
                                                                        choiceScan.advance.1.symm.trans
                                                                          choiceProductionPlain
                                                                      have beforeDot :
                                                                          choiceBefore.raw.dot.val = 0 := by
                                                                        have advanced :=
                                                                          choiceScan.advance.2.1
                                                                        have afterDot :
                                                                            choiceItem.raw.dot.val = 1 := by
                                                                          calc
                                                                            _ = choiceItem.raw.production.rhs.length :=
                                                                              choiceComplete
                                                                            _ = 1 := by
                                                                              rw [choiceProductionPlain]
                                                                              simp [ProductionId.rhs]
                                                                        omega
                                                                      have impossible :
                                                                          some (GrammarSymbol.terminal
                                                                            choiceScan.terminal) =
                                                                            some (GrammarSymbol.nonterminal
                                                                              (.aux
                                                                                typePlainSequenceSite.site)) := by
                                                                        let index :=
                                                                          choiceBefore.raw.dot.val
                                                                        calc
                                                                          _ = choiceBefore.raw.production.rhs[index]? :=
                                                                            choiceScan.next.2.symm
                                                                          _ = (ProductionId.choice
                                                                              typeRootChoiceSite
                                                                              typePlainChoiceBranch).rhs[index]? :=
                                                                            congrArg
                                                                              (fun production : ProductionId =>
                                                                                production.rhs[index]?)
                                                                              beforeProduction
                                                                          _ = (ProductionId.choice
                                                                              typeRootChoiceSite
                                                                              typePlainChoiceBranch).rhs[0]? := by
                                                                            have indexZero : index = 0 :=
                                                                              beforeDot
                                                                            rw [indexZero]
                                                                          _ = _ := by
                                                                            simp [ProductionId.rhs,
                                                                              typePlainChoiceBranch_site]
                                                                      exact GrammarSymbol.noConfusion
                                                                        (Option.some.inj impossible)
                                                                  | complete choiceWaiting plainSequenceItem _
                                                                      plainShared choicePriorValues
                                                                      plainSequenceValue plainWitness
                                                                      plainEdge choicePrior
                                                                      plainSequenceReduction =>
                                                                      have choiceWaitingProduction :
                                                                          choiceWaiting.raw.production =
                                                                            .choice typeRootChoiceSite
                                                                              typePlainChoiceBranch :=
                                                                        plainWitness.advance.1.symm.trans
                                                                          choiceProductionPlain
                                                                      have choiceWaitingDot :
                                                                          choiceWaiting.raw.dot.val = 0 := by
                                                                        have advanced :=
                                                                          plainWitness.advance.2.1
                                                                        have afterDot :
                                                                            choiceItem.raw.dot.val = 1 := by
                                                                          calc
                                                                            _ = choiceItem.raw.production.rhs.length :=
                                                                              choiceComplete
                                                                            _ = 1 := by
                                                                              rw [choiceProductionPlain]
                                                                              simp [ProductionId.rhs]
                                                                        omega
                                                                      have plainSequenceLhs :
                                                                          plainSequenceItem.raw.production.lhs =
                                                                            .aux typePlainSequenceSite.site := by
                                                                        have selected :
                                                                            some (GrammarSymbol.nonterminal
                                                                              plainSequenceItem.raw.production.lhs) =
                                                                              some (GrammarSymbol.nonterminal
                                                                                (.aux
                                                                                  typePlainSequenceSite.site)) := by
                                                                          let index :=
                                                                            choiceWaiting.raw.dot.val
                                                                          calc
                                                                            _ = choiceWaiting.raw.production.rhs[index]? :=
                                                                              plainWitness.next.2.symm
                                                                            _ = (ProductionId.choice
                                                                                typeRootChoiceSite
                                                                                typePlainChoiceBranch).rhs[index]? :=
                                                                              congrArg
                                                                                (fun production : ProductionId =>
                                                                                  production.rhs[index]?)
                                                                                choiceWaitingProduction
                                                                            _ = (ProductionId.choice
                                                                                typeRootChoiceSite
                                                                                typePlainChoiceBranch).rhs[0]? := by
                                                                              have indexZero : index = 0 :=
                                                                                choiceWaitingDot
                                                                              rw [indexZero]
                                                                            _ = _ := by
                                                                              simp [ProductionId.rhs,
                                                                                typePlainChoiceBranch_site]
                                                                        exact GrammarSymbol.nonterminal.inj
                                                                          (Option.some.inj selected)
                                                                      have plainSequenceProduction :
                                                                          plainSequenceItem.raw.production =
                                                                            .seq typePlainSequenceSite :=
                                                                        production_eq_sequence_of_lhs
                                                                          typePlainSequenceSite
                                                                          plainSequenceItem.raw.production
                                                                          plainSequenceLhs
                                                                      rcases plainSequenceItem with
                                                                        ⟨⟨plainProductionId,
                                                                          plainDot, plainOrigin,
                                                                          plainCurrent⟩,
                                                                          plainContext⟩
                                                                      simp only at plainSequenceProduction
                                                                      subst plainProductionId
                                                                      let plainSequenceItem :
                                                                          ContextualItemKey tokens :=
                                                                        ⟨⟨.seq typePlainSequenceSite,
                                                                          plainDot, plainOrigin,
                                                                          plainCurrent⟩,
                                                                          plainContext⟩
                                                                      change CoherentReduction file tokens
                                                                        memo correct final
                                                                        plainSequenceItem
                                                                        plainSequenceValue at plainSequenceReduction
                                                                      have choicePriorLayout :
                                                                          choiceWaiting.raw.production.rhs.take
                                                                              choiceWaiting.raw.dot.val = [] := by
                                                                        rw [choiceWaitingDot]
                                                                        simp
                                                                      let choiceEmpty :
                                                                          GrammarSymbolValues file tokens [] :=
                                                                        GrammarSymbolValues.transport
                                                                          choicePriorLayout
                                                                          choicePriorValues
                                                                      have choicePriorRecover :
                                                                          GrammarSymbolValues.transport
                                                                              choicePriorLayout.symm
                                                                              choiceEmpty =
                                                                            choicePriorValues := by
                                                                        rw [← show
                                                                            GrammarSymbolValues.transport
                                                                                choicePriorLayout
                                                                                choicePriorValues = choiceEmpty
                                                                              from rfl,
                                                                          GrammarSymbolValues.transport_trans]
                                                                        exact
                                                                          GrammarSymbolValues.transport_self
                                                                            _ _
                                                                      have plainSiteEq :
                                                                          typePlainSequenceSite.site =
                                                                            typeRootChoiceSite.branch
                                                                              choiceBranch := by
                                                                        calc
                                                                          _ = typeRootChoiceSite.branch
                                                                              typePlainChoiceBranch :=
                                                                            typePlainChoiceBranch_site.symm
                                                                          _ = _ := by rw [choiceBranchEq]
                                                                      have choiceSymbolLayout :
                                                                          GrammarSymbol.nonterminal
                                                                              plainSequenceItem.raw.production.lhs =
                                                                            GrammarSymbol.nonterminal
                                                                              (.aux
                                                                                (typeRootChoiceSite.branch
                                                                                  choiceBranch)) := by
                                                                        exact congrArg
                                                                          GrammarSymbol.nonterminal
                                                                          (congrArg NonterminalSymbol.aux
                                                                            plainSiteEq)
                                                                      have choiceFullTupleEq :=
                                                                        GrammarSymbolValues.transport_append_empty_single_to_local
                                                                          choicePriorLayout
                                                                          ((prefix_complete_layout
                                                                              choiceWaiting.raw
                                                                              plainSequenceItem.raw
                                                                              choiceItem.raw
                                                                              plainWitness.next
                                                                              plainWitness.advance).trans
                                                                            (prefix_full_layout
                                                                              choiceItem.raw
                                                                              choiceComplete))
                                                                          ((congrArg ProductionId.rhs
                                                                              choiceProduction).trans
                                                                            (ProductionId.rhs_choice
                                                                              typeRootChoiceSite
                                                                              choiceBranch))
                                                                          choiceSymbolLayout
                                                                          choiceEmpty
                                                                          plainSequenceValue
                                                                      rw [← choicePriorRecover] at choiceChildEq
                                                                      rw [PrefixValues.fullValue_completeValue_eq]
                                                                        at choiceChildEq
                                                                      unfold GrammarSymbolValues.view at choiceChildEq
                                                                      rw [GrammarSymbolValues.transport_trans]
                                                                        at choiceChildEq
                                                                      conv at choiceChildEq in
                                                                          (GrammarSymbolValues.transport _ _) =>
                                                                        rw [choiceFullTupleEq]
                                                                      have transportedChoiceChildEq :=
                                                                        congrArg
                                                                          (EbnfValue.transport
                                                                            childExpressionEq)
                                                                          choiceChildEq
                                                                      have choiceCastLayoutEq :
                                                                          congrArg
                                                                              (GrammarSymbolValue file tokens)
                                                                              choiceSymbolLayout =
                                                                            congrArg
                                                                              (GrammarSymbolValue file tokens)
                                                                              (congrArg
                                                                                (fun child =>
                                                                                  GrammarSymbol.nonterminal
                                                                                    (.aux child))
                                                                                plainSiteEq) :=
                                                                        Subsingleton.elim _ _
                                                                      have auxiliaryTransportEq :
                                                                          Eq.mp
                                                                              (congrArg
                                                                                (GrammarSymbolValue file tokens)
                                                                                choiceSymbolLayout)
                                                                              plainSequenceValue =
                                                                            EbnfValue.transport
                                                                              (congrArg GrammarSite.expression
                                                                                plainSiteEq)
                                                                              plainSequenceValue := by
                                                                        rw [choiceCastLayoutEq]
                                                                        simpa only [plainSequenceItem,
                                                                          ProductionId.lhs] using
                                                                          (auxiliaryValue_transport_eq
                                                                            plainSiteEq
                                                                            (show EbnfValue file tokens
                                                                                typePlainSequenceSite.site.expression
                                                                              from plainSequenceValue))
                                                                      have normalizedChoiceChild :
                                                                          EbnfValue.transport
                                                                              childExpressionEq
                                                                              (EbnfValue.transport
                                                                                ((typeRootChoiceSite.branch_expression
                                                                                    choiceBranch).trans
                                                                                  (typeRootChoiceSite.branch_get_toList
                                                                                    choiceBranch).symm)
                                                                                (Eq.mp
                                                                                  (congrArg
                                                                                    (GrammarSymbolValue file tokens)
                                                                                    choiceSymbolLayout)
                                                                                  plainSequenceValue)) =
                                                                            EbnfValue.transport
                                                                              typePlainSequenceSite_shape
                                                                              plainSequenceValue := by
                                                                        have castAligned := congrArg
                                                                          (EbnfValue.transport
                                                                            ((typeRootChoiceSite.branch_expression
                                                                                choiceBranch).trans
                                                                              (typeRootChoiceSite.branch_get_toList
                                                                                choiceBranch).symm))
                                                                          auxiliaryTransportEq
                                                                        have outerAligned := congrArg
                                                                          (EbnfValue.transport
                                                                            childExpressionEq)
                                                                          castAligned
                                                                        exact outerAligned.trans (by
                                                                          rw [EbnfValue.transport_trans,
                                                                            EbnfValue.transport_trans])
                                                                      have plainSequenceSemanticEq :
                                                                          EbnfValue.transport
                                                                              typePlainSequenceSite_shape
                                                                              plainSequenceValue =
                                                                            plainValue := by
                                                                        exact normalizedChoiceChild.symm.trans
                                                                          (transportedChoiceChildEq.symm.trans
                                                                            transportedChildEq)
                                                                      cases plainSequenceReduction with
                                                                      | reduce _ plainSequenceValues _
                                                                          plainSequenceReached
                                                                          plainSequenceComplete
                                                                          plainSequenceCoherent
                                                                          plainSequenceAction =>
                                                                          have plainSequencePackedEq :
                                                                              plainSequenceValue =
                                                                                SequenceSite.pack
                                                                                  typePlainSequenceSite
                                                                                  (PrefixValues.fullValue
                                                                                    plainSequenceItem
                                                                                    plainSequenceComplete
                                                                                    plainSequenceValues) := by
                                                                            have actionExact :=
                                                                              actionReduces_eleven_shapes_exact.mp
                                                                                plainSequenceAction
                                                                            simpa [plainSequenceItem]
                                                                              using actionExact
                                                                          cases plainSequenceCoherent with
                                                                          | zero _ _ zero =>
                                                                              have dotTwo :
                                                                                  plainSequenceItem.raw.dot.val = 2 := by
                                                                                calc
                                                                                  _ = plainSequenceItem.raw.production.rhs.length :=
                                                                                    plainSequenceComplete
                                                                                  _ = 2 := by
                                                                                    simp [plainSequenceItem,
                                                                                      ProductionId.rhs_seq,
                                                                                      typePlainSequenceSite_children]
                                                                              omega
                                                                          | scan plainBefore _ _ _ plainScan _ _ =>
                                                                              have beforeProduction :
                                                                                  plainBefore.raw.production =
                                                                                    .seq typePlainSequenceSite :=
                                                                                plainScan.advance.1.symm
                                                                              have afterDot :
                                                                                  plainSequenceItem.raw.dot.val = 2 := by
                                                                                calc
                                                                                  _ = plainSequenceItem.raw.production.rhs.length :=
                                                                                    plainSequenceComplete
                                                                                  _ = 2 := by
                                                                                    simp [plainSequenceItem,
                                                                                      ProductionId.rhs_seq,
                                                                                      typePlainSequenceSite_children]
                                                                              have beforeDot :
                                                                                  plainBefore.raw.dot.val = 1 := by
                                                                                have advanced :=
                                                                                  plainScan.advance.2.1
                                                                                omega
                                                                              have impossible :
                                                                                  some (GrammarSymbol.terminal
                                                                                    plainScan.terminal) =
                                                                                    some (GrammarSymbol.nonterminal
                                                                                      (.aux
                                                                                        typePlainArrowOptionalSite.site)) := by
                                                                                let index := plainBefore.raw.dot.val
                                                                                calc
                                                                                  _ = plainBefore.raw.production.rhs[index]? :=
                                                                                    plainScan.next.2.symm
                                                                                  _ = (ProductionId.seq
                                                                                      typePlainSequenceSite).rhs[index]? :=
                                                                                    congrArg
                                                                                      (fun production : ProductionId =>
                                                                                        production.rhs[index]?)
                                                                                      beforeProduction
                                                                                  _ = (ProductionId.seq
                                                                                      typePlainSequenceSite).rhs[1]? := by
                                                                                    have indexOne : index = 1 :=
                                                                                      beforeDot
                                                                                    rw [indexOne]
                                                                                  _ = _ := by
                                                                                    simp [ProductionId.rhs_seq,
                                                                                      typePlainSequenceSite_children]
                                                                              exact GrammarSymbol.noConfusion
                                                                                (Option.some.inj impossible)
                                                                          | complete plainWaiting arrowOptionalItem _
                                                                              arrowShared plainPriorValues
                                                                              arrowOptionalValue arrowWitness arrowEdge
                                                                              plainPrior arrowOptionalReduction =>
                                                                              have plainWaitingProduction :
                                                                                  plainWaiting.raw.production =
                                                                                    .seq typePlainSequenceSite :=
                                                                                arrowWitness.advance.1.symm
                                                                              have plainWaitingDot :
                                                                                  plainWaiting.raw.dot.val = 1 := by
                                                                                have advanced :=
                                                                                  arrowWitness.advance.2.1
                                                                                have afterDot :
                                                                                    plainSequenceItem.raw.dot.val = 2 := by
                                                                                  calc
                                                                                    _ = plainSequenceItem.raw.production.rhs.length :=
                                                                                      plainSequenceComplete
                                                                                    _ = 2 := by
                                                                                      simp [plainSequenceItem,
                                                                                        ProductionId.rhs_seq,
                                                                                        typePlainSequenceSite_children]
                                                                                omega
                                                                              have arrowOptionalLhs :
                                                                                  arrowOptionalItem.raw.production.lhs =
                                                                                    .aux typePlainArrowOptionalSite.site := by
                                                                                have selected :
                                                                                    some (GrammarSymbol.nonterminal
                                                                                      arrowOptionalItem.raw.production.lhs) =
                                                                                      some (GrammarSymbol.nonterminal
                                                                                        (.aux
                                                                                          typePlainArrowOptionalSite.site)) := by
                                                                                  let index :=
                                                                                    plainWaiting.raw.dot.val
                                                                                  calc
                                                                                    _ = plainWaiting.raw.production.rhs[index]? :=
                                                                                      arrowWitness.next.2.symm
                                                                                    _ = (ProductionId.seq
                                                                                        typePlainSequenceSite).rhs[index]? :=
                                                                                      congrArg
                                                                                        (fun production : ProductionId =>
                                                                                          production.rhs[index]?)
                                                                                        plainWaitingProduction
                                                                                    _ = (ProductionId.seq
                                                                                        typePlainSequenceSite).rhs[1]? := by
                                                                                      have indexOne : index = 1 :=
                                                                                        plainWaitingDot
                                                                                      rw [indexOne]
                                                                                    _ = _ := by
                                                                                      simp [ProductionId.rhs_seq,
                                                                                        typePlainSequenceSite_children]
                                                                                exact GrammarSymbol.nonterminal.inj
                                                                                  (Option.some.inj selected)
                                                                              cases plainPrior with
                                                                              | zero _ _ zero =>
                                                                                  omega
                                                                              | scan typeAtomBefore _ _ _ typeAtomScan _ _ =>
                                                                                  have beforeProduction :
                                                                                      typeAtomBefore.raw.production =
                                                                                        .seq typePlainSequenceSite :=
                                                                                    typeAtomScan.advance.1.symm.trans
                                                                                      plainWaitingProduction
                                                                                  have beforeDot :
                                                                                      typeAtomBefore.raw.dot.val = 0 := by
                                                                                    have advanced :=
                                                                                      typeAtomScan.advance.2.1
                                                                                    omega
                                                                                  have impossible :
                                                                                      some (GrammarSymbol.terminal
                                                                                        typeAtomScan.terminal) =
                                                                                        some (GrammarSymbol.nonterminal
                                                                                          (.aux
                                                                                            typePlainTypeAtomSite.site)) := by
                                                                                    let index :=
                                                                                      typeAtomBefore.raw.dot.val
                                                                                    calc
                                                                                      _ = typeAtomBefore.raw.production.rhs[index]? :=
                                                                                        typeAtomScan.next.2.symm
                                                                                      _ = (ProductionId.seq
                                                                                          typePlainSequenceSite).rhs[index]? :=
                                                                                        congrArg
                                                                                          (fun production : ProductionId =>
                                                                                            production.rhs[index]?)
                                                                                          beforeProduction
                                                                                      _ = (ProductionId.seq
                                                                                          typePlainSequenceSite).rhs[0]? := by
                                                                                        have indexZero : index = 0 :=
                                                                                          beforeDot
                                                                                        rw [indexZero]
                                                                                      _ = _ := by
                                                                                        simp [ProductionId.rhs_seq,
                                                                                          typePlainSequenceSite_children]
                                                                                  exact GrammarSymbol.noConfusion
                                                                                    (Option.some.inj impossible)
                                                                              | complete typeAtomWaiting typeAtomItem _
                                                                                  typeAtomShared typeAtomPriorValues
                                                                                  typeAtomValue typeAtomWitness typeAtomEdge
                                                                                  typeAtomPrior typeAtomReduction =>
                                                                                  have typeAtomWaitingProduction :
                                                                                      typeAtomWaiting.raw.production =
                                                                                        .seq typePlainSequenceSite :=
                                                                                    typeAtomWitness.advance.1.symm.trans
                                                                                      plainWaitingProduction
                                                                                  have typeAtomWaitingDot :
                                                                                      typeAtomWaiting.raw.dot.val = 0 := by
                                                                                    have advanced :=
                                                                                      typeAtomWitness.advance.2.1
                                                                                    omega
                                                                                  have typeAtomLhs :
                                                                                      typeAtomItem.raw.production.lhs =
                                                                                        .aux typePlainTypeAtomSite.site := by
                                                                                    have selected :
                                                                                        some (GrammarSymbol.nonterminal
                                                                                          typeAtomItem.raw.production.lhs) =
                                                                                          some (GrammarSymbol.nonterminal
                                                                                            (.aux
                                                                                              typePlainTypeAtomSite.site)) := by
                                                                                      let index :=
                                                                                        typeAtomWaiting.raw.dot.val
                                                                                      calc
                                                                                        _ = typeAtomWaiting.raw.production.rhs[index]? :=
                                                                                          typeAtomWitness.next.2.symm
                                                                                        _ = (ProductionId.seq
                                                                                            typePlainSequenceSite).rhs[index]? :=
                                                                                          congrArg
                                                                                            (fun production : ProductionId =>
                                                                                              production.rhs[index]?)
                                                                                            typeAtomWaitingProduction
                                                                                        _ = (ProductionId.seq
                                                                                            typePlainSequenceSite).rhs[0]? := by
                                                                                          have indexZero : index = 0 :=
                                                                                            typeAtomWaitingDot
                                                                                          rw [indexZero]
                                                                                        _ = _ := by
                                                                                          simp [ProductionId.rhs_seq,
                                                                                            typePlainSequenceSite_children]
                                                                                    exact GrammarSymbol.nonterminal.inj
                                                                                      (Option.some.inj selected)
                                                                                  have typeAtomProduction :
                                                                                      typeAtomItem.raw.production =
                                                                                        .atom typePlainTypeAtomSite :=
                                                                                    production_eq_atom_of_lhs_local
                                                                                      typePlainTypeAtomSite
                                                                                      typeAtomItem.raw.production
                                                                                      typeAtomLhs
                                                                                  rcases typeAtomItem with
                                                                                    ⟨⟨typeAtomProductionId,
                                                                                      typeAtomDot, typeAtomOrigin,
                                                                                      typeAtomCurrent⟩,
                                                                                      typeAtomContext⟩
                                                                                  simp only at typeAtomProduction
                                                                                  subst typeAtomProductionId
                                                                                  let typeAtomItem :
                                                                                      ContextualItemKey tokens :=
                                                                                    ⟨⟨.atom typePlainTypeAtomSite,
                                                                                      typeAtomDot, typeAtomOrigin,
                                                                                      typeAtomCurrent⟩,
                                                                                      typeAtomContext⟩
                                                                                  change CoherentReduction file tokens
                                                                                    memo correct final typeAtomItem
                                                                                    typeAtomValue at typeAtomReduction
                                                                                  have plainChildrenExpressionLayout :
                                                                                      typePlainSequenceSite.children.map
                                                                                          GrammarSite.expression = [
                                                                                        Grammar.nonterminal .typeAtom,
                                                                                        Grammar.optional
                                                                                          (Grammar.sequence [
                                                                                            Grammar.symbol .arrow,
                                                                                            Grammar.nonterminal .type])] :=
                                                                                    EbnfExpr.sequence.inj
                                                                                      (typePlainSequenceSite.expression_eq_sequence.symm.trans
                                                                                        typePlainSequenceSite_shape)
                                                                                  have plainExpressionListEq : [
                                                                                        typePlainTypeAtomSite.site.expression,
                                                                                        typePlainArrowOptionalSite.site.expression] = [
                                                                                        Grammar.nonterminal .typeAtom,
                                                                                        Grammar.optional
                                                                                          (Grammar.sequence [
                                                                                            Grammar.symbol .arrow,
                                                                                            Grammar.nonterminal .type])] := by
                                                                                    simpa only [
                                                                                      typePlainSequenceSite_children,
                                                                                      List.map] using
                                                                                      plainChildrenExpressionLayout
                                                                                  have typeAtomShape :
                                                                                      typePlainTypeAtomSite.site.expression =
                                                                                        Grammar.nonterminal .typeAtom :=
                                                                                    (List.cons.inj
                                                                                      plainExpressionListEq).1
                                                                                  have plainExpressionTail :=
                                                                                    (List.cons.inj
                                                                                      plainExpressionListEq).2
                                                                                  have arrowOptionalShape :
                                                                                      typePlainArrowOptionalSite.site.expression =
                                                                                        Grammar.optional
                                                                                          (Grammar.sequence [
                                                                                            Grammar.symbol .arrow,
                                                                                            Grammar.nonterminal .type]) :=
                                                                                    (List.cons.inj
                                                                                      plainExpressionTail).1
                                                                                  have typeAtomPriorLayout :
                                                                                      typeAtomWaiting.raw.production.rhs.take
                                                                                          typeAtomWaiting.raw.dot.val = [] := by
                                                                                    rw [typeAtomWaitingDot]
                                                                                    simp
                                                                                  let typeAtomEmpty :
                                                                                      GrammarSymbolValues file tokens [] :=
                                                                                    GrammarSymbolValues.transport
                                                                                      typeAtomPriorLayout
                                                                                      typeAtomPriorValues
                                                                                  have typeAtomPriorRecover :
                                                                                      GrammarSymbolValues.transport
                                                                                          typeAtomPriorLayout.symm
                                                                                          typeAtomEmpty =
                                                                                        typeAtomPriorValues := by
                                                                                    rw [← show
                                                                                        GrammarSymbolValues.transport
                                                                                            typeAtomPriorLayout
                                                                                            typeAtomPriorValues =
                                                                                          typeAtomEmpty
                                                                                      from rfl,
                                                                                      GrammarSymbolValues.transport_trans]
                                                                                    exact
                                                                                      GrammarSymbolValues.transport_self
                                                                                        _ _
                                                                                  have plainSequenceTargetLayout :
                                                                                      typePlainSequenceSite.children.map
                                                                                          (fun child =>
                                                                                            GrammarSymbol.nonterminal
                                                                                              (.aux child)) = [
                                                                                        .nonterminal
                                                                                          typeAtomItem.raw.production.lhs,
                                                                                        .nonterminal
                                                                                          arrowOptionalItem.raw.production.lhs] := by
                                                                                    rw [typePlainSequenceSite_children]
                                                                                    simp only [List.map]
                                                                                    rw [typeAtomLhs,
                                                                                      arrowOptionalLhs]
                                                                                  have plainSequenceTupleEq :=
                                                                                    GrammarSymbolValues.transport_append_two_from_empty_to
                                                                                      typeAtomPriorLayout
                                                                                      (prefix_complete_layout
                                                                                        typeAtomWaiting.raw
                                                                                        typeAtomItem.raw
                                                                                        plainWaiting.raw
                                                                                        typeAtomWitness.next
                                                                                        typeAtomWitness.advance)
                                                                                      ((prefix_complete_layout
                                                                                        plainWaiting.raw
                                                                                        arrowOptionalItem.raw
                                                                                        plainSequenceItem.raw
                                                                                        arrowWitness.next
                                                                                        arrowWitness.advance).trans
                                                                                        (prefix_full_layout
                                                                                          plainSequenceItem.raw
                                                                                          plainSequenceComplete))
                                                                                      (ProductionId.rhs_seq
                                                                                        typePlainSequenceSite)
                                                                                      plainSequenceTargetLayout
                                                                                      typeAtomEmpty
                                                                                      typeAtomValue
                                                                                      arrowOptionalValue
                                                                                  rw [← typeAtomPriorRecover]
                                                                                    at plainSequencePackedEq
                                                                                  rw [PrefixValues.fullValue_completeValue_eq]
                                                                                    at plainSequencePackedEq
                                                                                  unfold PrefixValues.completeValue
                                                                                    at plainSequencePackedEq
                                                                                  simp only [SequenceSite.pack,
                                                                                    GrammarSymbolValues.view]
                                                                                    at plainSequencePackedEq
                                                                                  conv at plainSequencePackedEq in
                                                                                      (GrammarSymbolValues.transport _ _) =>
                                                                                    rw [plainSequenceTupleEq]
                                                                                  let rawPlainSequenceValue :=
                                                                                    EbnfValue.sequence
                                                                                      (typePlainSequenceSite.children.map
                                                                                        GrammarSite.expression)
                                                                                      (EbnfValues.ofAuxiliaries
                                                                                        typePlainSequenceSite.children
                                                                                        (GrammarSymbolValues.transport
                                                                                          plainSequenceTargetLayout.symm
                                                                                          (typeAtomValue,
                                                                                            (arrowOptionalValue, ()))))
                                                                                  rw [plainSequencePackedEq]
                                                                                    at plainSequenceSemanticEq
                                                                                  change EbnfValue.transport
                                                                                      typePlainSequenceSite_shape
                                                                                      (EbnfValue.ofShape
                                                                                        typePlainSequenceSite.expression_eq_sequence
                                                                                        rawPlainSequenceValue) = _
                                                                                    at plainSequenceSemanticEq
                                                                                  unfold EbnfValue.ofShape
                                                                                    at plainSequenceSemanticEq
                                                                                  rw [EbnfValue.transport_trans]
                                                                                    at plainSequenceSemanticEq
                                                                                  have plainSequenceTransportProof :
                                                                                      typePlainSequenceSite.expression_eq_sequence.symm.trans
                                                                                          typePlainSequenceSite_shape =
                                                                                        congrArg EbnfExpr.sequence
                                                                                          plainChildrenExpressionLayout :=
                                                                                    Subsingleton.elim _ _
                                                                                  rw [plainSequenceTransportProof]
                                                                                    at plainSequenceSemanticEq
                                                                                  have canonicalPlainSequenceSemanticEq :
                                                                                      EbnfValue.transport
                                                                                        (congrArg EbnfExpr.sequence
                                                                                          plainChildrenExpressionLayout)
                                                                                        (EbnfValue.sequence
                                                                                          (typePlainSequenceSite.children.map
                                                                                            GrammarSite.expression)
                                                                                          (EbnfValues.ofAuxiliaries
                                                                                            typePlainSequenceSite.children
                                                                                            (GrammarSymbolValues.transport
                                                                                              plainSequenceTargetLayout.symm
                                                                                              (typeAtomValue,
                                                                                                (arrowOptionalValue, ()))))) =
                                                                                        EbnfValue.sequence [
                                                                                          Grammar.nonterminal .typeAtom,
                                                                                          Grammar.optional
                                                                                            (Grammar.sequence [
                                                                                              Grammar.symbol .arrow,
                                                                                              Grammar.nonterminal .type])]
                                                                                          (EbnfValues.cons _ _
                                                                                            (EbnfValue.ruleAtom
                                                                                              .typeAtom
                                                                                              typeRootValue) <|
                                                                                          EbnfValues.cons _ _
                                                                                            (EbnfValue.optional
                                                                                              (Grammar.sequence [
                                                                                                Grammar.symbol .arrow,
                                                                                                Grammar.nonterminal .type])
                                                                                              none) <|
                                                                                          EbnfValues.nil) := by
                                                                                    exact plainSequenceSemanticEq
                                                                                  have plainFirstEq := congrArg
                                                                                    (fun value =>
                                                                                      (EbnfValue.sequence2View
                                                                                        (Grammar.nonterminal .typeAtom)
                                                                                        (Grammar.optional
                                                                                          (Grammar.sequence [
                                                                                            Grammar.symbol .arrow,
                                                                                            Grammar.nonterminal .type]))
                                                                                        value).1)
                                                                                    canonicalPlainSequenceSemanticEq
                                                                                  have parsedPlainFirst :=
                                                                                    typePlainSequenceFirst_auxiliary_two_eq
                                                                                      typePlainSequenceSite_children
                                                                                      typeAtomShape
                                                                                      arrowOptionalShape
                                                                                      (by rfl)
                                                                                      arrowOptionalLhs
                                                                                      plainSequenceTargetLayout
                                                                                      plainChildrenExpressionLayout
                                                                                      typeAtomValue
                                                                                      arrowOptionalValue
                                                                                  have expectedPlainFirst :=
                                                                                    sequence2View_pair_first_local
                                                                                      (file := file)
                                                                                      (tokens := tokens)
                                                                                      (Grammar.nonterminal .typeAtom)
                                                                                      (Grammar.optional
                                                                                        (Grammar.sequence [
                                                                                          Grammar.symbol .arrow,
                                                                                          Grammar.nonterminal .type]))
                                                                                      (EbnfValue.ruleAtom
                                                                                        .typeAtom typeRootValue)
                                                                                      (EbnfValue.optional
                                                                                        (Grammar.sequence [
                                                                                          Grammar.symbol .arrow,
                                                                                          Grammar.nonterminal .type])
                                                                                        none)
                                                                                  rw [parsedPlainFirst,
                                                                                    expectedPlainFirst] at plainFirstEq
                                                                                  have typeAtomFieldEqNoCast :
                                                                                      EbnfValue.atShape typeAtomShape
                                                                                          typeAtomValue =
                                                                                        EbnfValue.ruleAtom .typeAtom
                                                                                          typeRootValue := by
                                                                                    exact plainFirstEq
                                                                                  cases typeAtomReduction with
                                                                                  | reduce _ typeAtomValues _
                                                                                      typeAtomReached
                                                                                      typeAtomComplete
                                                                                      typeAtomCoherent
                                                                                      typeAtomAction =>
                                                                                      have typeAtomPackedEq :
                                                                                          typeAtomValue =
                                                                                            AtomSite.pack
                                                                                              typePlainTypeAtomSite
                                                                                              (PrefixValues.fullValue
                                                                                                typeAtomItem
                                                                                                typeAtomComplete
                                                                                                typeAtomValues) := by
                                                                                        have actionExact :=
                                                                                          actionReduces_eleven_shapes_exact.mp
                                                                                            typeAtomAction
                                                                                        simpa [typeAtomItem]
                                                                                          using actionExact
                                                                                      cases typeAtomCoherent with
                                                                                      | zero _ _ zero =>
                                                                                          have dotOne :
                                                                                              typeAtomItem.raw.dot.val = 1 := by
                                                                                            calc
                                                                                              _ = typeAtomItem.raw.production.rhs.length :=
                                                                                                typeAtomComplete
                                                                                              _ = 1 := by
                                                                                                simp [typeAtomItem,
                                                                                                  ProductionId.rhs]
                                                                                          omega
                                                                                      | scan atomBefore _ _ _ atomScan _ _ =>
                                                                                          have beforeProduction :
                                                                                              atomBefore.raw.production =
                                                                                                .atom typePlainTypeAtomSite :=
                                                                                            atomScan.advance.1.symm
                                                                                          have beforeDot :
                                                                                              atomBefore.raw.dot.val = 0 := by
                                                                                            have advanced :=
                                                                                              atomScan.advance.2.1
                                                                                            have afterDot :
                                                                                                typeAtomItem.raw.dot.val = 1 := by
                                                                                              calc
                                                                                                _ = typeAtomItem.raw.production.rhs.length :=
                                                                                                  typeAtomComplete
                                                                                                _ = 1 := by
                                                                                                  simp [typeAtomItem,
                                                                                                    ProductionId.rhs]
                                                                                            omega
                                                                                          have impossible :
                                                                                              some (GrammarSymbol.terminal
                                                                                                atomScan.terminal) =
                                                                                                some (GrammarSymbol.nonterminal
                                                                                                  (.rule .typeAtom)) := by
                                                                                            let index :=
                                                                                              atomBefore.raw.dot.val
                                                                                            calc
                                                                                              _ = atomBefore.raw.production.rhs[index]? :=
                                                                                                atomScan.next.2.symm
                                                                                              _ = (ProductionId.atom
                                                                                                  typePlainTypeAtomSite).rhs[index]? :=
                                                                                                congrArg
                                                                                                  (fun production : ProductionId =>
                                                                                                    production.rhs[index]?)
                                                                                                  beforeProduction
                                                                                              _ = (ProductionId.atom
                                                                                                  typePlainTypeAtomSite).rhs[0]? := by
                                                                                                have indexZero : index = 0 :=
                                                                                                  beforeDot
                                                                                                rw [indexZero]
                                                                                              _ = _ := by
                                                                                                have atomEq :
                                                                                                    typePlainTypeAtomSite.atom =
                                                                                                      .nonterminal .typeAtom :=
                                                                                                  EbnfExpr.atom.inj
                                                                                                    (typePlainTypeAtomSite.expression_eq_atom.symm.trans
                                                                                                      typeAtomShape)
                                                                                                simp [ProductionId.rhs,
                                                                                                  typePlainTypeAtomSite.symbol_eq,
                                                                                                  atomEq,
                                                                                                  EbnfAtom.grammarSymbol]
                                                                                          exact GrammarSymbol.noConfusion
                                                                                            (Option.some.inj impossible)
                                                                                      | complete atomWaiting typeAtomRootItem _
                                                                                          typeAtomRootShared atomPriorValues
                                                                                          typeAtomRootValue atomWitness atomEdge
                                                                                          atomPrior typeAtomRootReduction =>
                                                                                          have atomWaitingProduction :
                                                                                              atomWaiting.raw.production =
                                                                                                .atom typePlainTypeAtomSite :=
                                                                                            atomWitness.advance.1.symm
                                                                                          have atomWaitingDot :
                                                                                              atomWaiting.raw.dot.val = 0 := by
                                                                                            have advanced :=
                                                                                              atomWitness.advance.2.1
                                                                                            have afterDot :
                                                                                                typeAtomItem.raw.dot.val = 1 := by
                                                                                              calc
                                                                                                _ = typeAtomItem.raw.production.rhs.length :=
                                                                                                  typeAtomComplete
                                                                                                _ = 1 := by
                                                                                                  simp [typeAtomItem,
                                                                                                    ProductionId.rhs]
                                                                                            omega
                                                                                          have typeAtomRootLhs :
                                                                                              typeAtomRootItem.raw.production.lhs =
                                                                                                .rule .typeAtom := by
                                                                                            have selected :
                                                                                                some (GrammarSymbol.nonterminal
                                                                                                  typeAtomRootItem.raw.production.lhs) =
                                                                                                  some (GrammarSymbol.nonterminal
                                                                                                    (.rule .typeAtom)) := by
                                                                                              let index :=
                                                                                                atomWaiting.raw.dot.val
                                                                                              calc
                                                                                                _ = atomWaiting.raw.production.rhs[index]? :=
                                                                                                  atomWitness.next.2.symm
                                                                                                _ = (ProductionId.atom
                                                                                                    typePlainTypeAtomSite).rhs[index]? :=
                                                                                                  congrArg
                                                                                                    (fun production : ProductionId =>
                                                                                                      production.rhs[index]?)
                                                                                                    atomWaitingProduction
                                                                                                _ = (ProductionId.atom
                                                                                                    typePlainTypeAtomSite).rhs[0]? := by
                                                                                                  have indexZero : index = 0 :=
                                                                                                    atomWaitingDot
                                                                                                  rw [indexZero]
                                                                                                _ = _ := by
                                                                                                  have atomEq :
                                                                                                      typePlainTypeAtomSite.atom =
                                                                                                        .nonterminal .typeAtom :=
                                                                                                    EbnfExpr.atom.inj
                                                                                                      (typePlainTypeAtomSite.expression_eq_atom.symm.trans
                                                                                                        typeAtomShape)
                                                                                                  simp [ProductionId.rhs,
                                                                                                    typePlainTypeAtomSite.symbol_eq,
                                                                                                    atomEq,
                                                                                                    EbnfAtom.grammarSymbol]
                                                                                            exact GrammarSymbol.nonterminal.inj
                                                                                              (Option.some.inj selected)
                                                                                          have typeAtomRootProduction :
                                                                                              typeAtomRootItem.raw.production =
                                                                                                .root .typeAtom :=
                                                                                            production_eq_root_of_lhs_local
                                                                                              .typeAtom
                                                                                              typeAtomRootItem.raw.production
                                                                                              typeAtomRootLhs
                                                                                          rcases typeAtomRootItem with
                                                                                            ⟨⟨typeAtomRootProductionId,
                                                                                              typeAtomRootDot,
                                                                                              typeAtomRootOrigin,
                                                                                              typeAtomRootCurrent⟩,
                                                                                              typeAtomRootContext⟩
                                                                                          simp only at typeAtomRootProduction
                                                                                          subst typeAtomRootProductionId
                                                                                          let typeAtomRootItem :
                                                                                              ContextualItemKey tokens :=
                                                                                            ⟨⟨.root .typeAtom,
                                                                                              typeAtomRootDot,
                                                                                              typeAtomRootOrigin,
                                                                                              typeAtomRootCurrent⟩,
                                                                                              typeAtomRootContext⟩
                                                                                          change CoherentReduction file tokens
                                                                                            memo correct final
                                                                                            typeAtomRootItem
                                                                                            typeAtomRootValue
                                                                                            at typeAtomRootReduction
                                                                                          have atomPriorLayout :
                                                                                              atomWaiting.raw.production.rhs.take
                                                                                                  atomWaiting.raw.dot.val = [] := by
                                                                                            rw [atomWaitingDot]
                                                                                            simp
                                                                                          let atomEmpty :
                                                                                              GrammarSymbolValues file tokens [] :=
                                                                                            GrammarSymbolValues.transport
                                                                                              atomPriorLayout
                                                                                              atomPriorValues
                                                                                          have atomPriorRecover :
                                                                                              GrammarSymbolValues.transport
                                                                                                  atomPriorLayout.symm
                                                                                                  atomEmpty =
                                                                                                atomPriorValues := by
                                                                                            rw [← show
                                                                                                GrammarSymbolValues.transport
                                                                                                    atomPriorLayout
                                                                                                    atomPriorValues =
                                                                                                  atomEmpty
                                                                                              from rfl,
                                                                                              GrammarSymbolValues.transport_trans]
                                                                                            exact
                                                                                              GrammarSymbolValues.transport_self
                                                                                                _ _
                                                                                          have atomEq :
                                                                                              typePlainTypeAtomSite.atom =
                                                                                                .nonterminal .typeAtom :=
                                                                                            EbnfExpr.atom.inj
                                                                                              (typePlainTypeAtomSite.expression_eq_atom.symm.trans
                                                                                                typeAtomShape)
                                                                                          have siteSymbolEq :
                                                                                              typePlainTypeAtomSite.symbol =
                                                                                                .nonterminal
                                                                                                  (.rule .typeAtom) :=
                                                                                            typePlainTypeAtomSite.symbol_eq.trans
                                                                                              (congrArg
                                                                                                EbnfAtom.grammarSymbol
                                                                                                atomEq)
                                                                                          have atomSymbolLayout :
                                                                                              .nonterminal
                                                                                                  typeAtomRootItem.raw.production.lhs =
                                                                                                typePlainTypeAtomSite.symbol := by
                                                                                            exact siteSymbolEq.symm
                                                                                          have atomFullTupleEq :=
                                                                                            GrammarSymbolValues.transport_append_empty_single_to_local
                                                                                              atomPriorLayout
                                                                                              ((prefix_complete_layout
                                                                                                  atomWaiting.raw
                                                                                                  typeAtomRootItem.raw
                                                                                                  typeAtomItem.raw
                                                                                                  atomWitness.next
                                                                                                  atomWitness.advance).trans
                                                                                                (prefix_full_layout
                                                                                                  typeAtomItem.raw
                                                                                                  typeAtomComplete))
                                                                                              (ProductionId.rhs_atom
                                                                                                typePlainTypeAtomSite)
                                                                                              atomSymbolLayout
                                                                                              atomEmpty
                                                                                              typeAtomRootValue
                                                                                          rw [← atomPriorRecover]
                                                                                            at typeAtomPackedEq
                                                                                          rw [PrefixValues.fullValue_completeValue_eq]
                                                                                            at typeAtomPackedEq
                                                                                          have typeAtomFieldPackedEq :=
                                                                                            typeAtomFieldEqNoCast
                                                                                          rw [typeAtomPackedEq]
                                                                                            at typeAtomFieldPackedEq
                                                                                          have atomShapeEq :
                                                                                              typeAtomShape =
                                                                                                typePlainTypeAtomSite.expression_eq_atom.trans
                                                                                                  (congrArg EbnfExpr.atom
                                                                                                    atomEq) :=
                                                                                            Subsingleton.elim _ _
                                                                                          rw [atomShapeEq,
                                                                                            EbnfValue.atShape_trans_eq_local]
                                                                                            at typeAtomFieldPackedEq
                                                                                          change AtomSite.packAtAtom
                                                                                              typePlainTypeAtomSite
                                                                                              (.nonterminal .typeAtom)
                                                                                              atomEq _ = _
                                                                                            at typeAtomFieldPackedEq
                                                                                          rw [AtomSite.pack_rule_eq]
                                                                                            at typeAtomFieldPackedEq
                                                                                          have packedHeadEq :=
                                                                                            EbnfValue.ruleAtom_injective
                                                                                              .typeAtom
                                                                                              typeAtomFieldPackedEq
                                                                                          have atomFullHeadEq :=
                                                                                            congrArg Prod.fst
                                                                                              atomFullTupleEq
                                                                                          unfold GrammarSymbolValues.view
                                                                                            at packedHeadEq
                                                                                          rw [atomFullHeadEq]
                                                                                            at packedHeadEq
                                                                                          have packedHeadNormal :
                                                                                              Eq.mp
                                                                                                  (congrArg
                                                                                                    (GrammarSymbolValue
                                                                                                      file tokens)
                                                                                                    (congrArg
                                                                                                      EbnfAtom.grammarSymbol
                                                                                                      atomEq))
                                                                                                  (Eq.mp
                                                                                                    (congrArg
                                                                                                      (GrammarSymbolValue
                                                                                                        file tokens)
                                                                                                      typePlainTypeAtomSite.symbol_eq)
                                                                                                    (Eq.mp
                                                                                                      (congrArg
                                                                                                        (GrammarSymbolValue
                                                                                                          file tokens)
                                                                                                        atomSymbolLayout)
                                                                                                      typeAtomRootValue)) =
                                                                                                typeAtomRootValue :=
                                                                                            Eq.mp_three_cycle_local
                                                                                              (congrArg
                                                                                                (GrammarSymbolValue file tokens)
                                                                                                atomSymbolLayout)
                                                                                              (congrArg
                                                                                                (GrammarSymbolValue file tokens)
                                                                                                typePlainTypeAtomSite.symbol_eq)
                                                                                              (congrArg
                                                                                                (GrammarSymbolValue file tokens)
                                                                                                (congrArg
                                                                                                  EbnfAtom.grammarSymbol
                                                                                                  atomEq))
                                                                                              typeAtomRootValue
                                                                                          have typeAtomRootSemanticEq :
                                                                                              typeAtomRootValue =
                                                                                                typeRootValue := by
                                                                                            calc
                                                                                              typeAtomRootValue = _ :=
                                                                                                packedHeadNormal.symm
                                                                                              _ = _ := packedHeadEq
                                                                                          cases typeAtomRootReduction with
                                                                                          | reduce _ typeAtomRootValues _
                                                                                              typeAtomRootReached
                                                                                              typeAtomRootComplete
                                                                                              typeAtomRootCoherent
                                                                                              typeAtomRootAction =>
                                                                                              have typeAtomRuleReduction :
                                                                                                  RuleReduction file tokens
                                                                                                    .typeAtom
                                                                                                    typeAtomRootItem.raw.origin
                                                                                                    typeAtomRootItem.raw.current
                                                                                                    (RootAction.unpack .typeAtom
                                                                                                      (PrefixValues.fullValue
                                                                                                        typeAtomRootItem
                                                                                                        typeAtomRootComplete
                                                                                                        typeAtomRootValues))
                                                                                                    typeAtomRootValue := by
                                                                                                have actionExact :=
                                                                                                  actionReduces_eleven_shapes_exact.mp
                                                                                                    typeAtomRootAction
                                                                                                simpa [typeAtomRootItem]
                                                                                                  using actionExact
                                                                                              have impossible := congrArg
                                                                                                (fun value : TypeExpr =>
                                                                                                  value.payload)
                                                                                                (typeAtomRootSemanticEq.trans
                                                                                                  typeRootSemanticEq)
                                                                                              generalize typeAtomRootInputEq :
                                                                                                  (RootAction.unpack .typeAtom
                                                                                                    (PrefixValues.fullValue
                                                                                                      typeAtomRootItem
                                                                                                      typeAtomRootComplete
                                                                                                      typeAtomRootValues)) =
                                                                                                    typeAtomRootInput
                                                                                                at typeAtomRuleReduction
                                                                                              cases typeAtomRuleReduction <;>
                                                                                                cases impossible
                                                              | typeFunction _ _ domain arrow
                                                                  codomain typeWitness =>
                                                                  have impossible := congrArg
                                                                    (fun value : TypeExpr =>
                                                                      value.payload)
                                                                    typeRootSemanticEq
                                                                  cases impossible

/-- Coherent let-binding reductions preserve every retained source token. -/
theorem letBinding_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout
      .letBinding := by
  intro file tokens memo correct final origin finish context priorValues output
    complete owned lexicalExact coherent reduces inputEvidence
  have semanticInputEvidence : TokenPlanEvidence
      ((RootAction.unpack .letBinding
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .letBinding
            origin finish context) complete priorValues)).tokenPlan?
        sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish) := by
    apply inputEvidence.candidate_eq
    symm
    rw [RootAction.unpack_tokenPlan?]
    simpa only [CanonicalCompleteRootItem] using
      (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
        (CanonicalCompleteRootItem tokens .letBinding
          origin finish context) complete priorValues)
  generalize inputEq : RootAction.unpack .letBinding
      (PrefixValues.fullValue
        (CanonicalCompleteRootItem tokens .letBinding
          origin finish context) complete priorValues) = input
    at reduces semanticInputEvidence
  cases reduces with
  | letBindingUntyped origin finish letKeyword name spelling parsed
      nameProjects initializer witness =>
      change TokenPlanEvidence
        ((letBindingUntypedInput letKeyword name initializer).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at semanticInputEvidence
      unfold letBindingUntypedInput letBindingInitializerValue
        at semanticInputEvidence
      simp only [letBindingChildren, letKeywordExpr, letNameExpr,
        letColonExpr, letComptimeExpr, letTypeExpr, letEqualExpr,
        letInitializerExpressionExpr, letTypeSequenceExpr,
        letInitializerSequenceExpr, Grammar.sequence,
        Grammar.hardKeyword, Grammar.identifier, Grammar.symbol,
        Grammar.category, Grammar.contextualKeyword, Grammar.nonterminal,
        Grammar.optional, Grammar.terminal] at semanticInputEvidence
      rw [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence] at semanticInputEvidence
      rw [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_cons,
        MatchedTerminal.physicalTokenPlan_hardKeyword,
        matchedIdentifier_physicalTokenPlan_local name spelling parsed
          nameProjects] at semanticInputEvidence
      cases initializer with
      | none =>
          simp only [Option.map, EbnfValue.tokenPlan?_optional_none,
            EbnfValues.tokenPlan?_nil] at semanticInputEvidence
          let sourceCore := TokenPlan.concat [
            TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
            identifierPlan (RuleReduction.terminalLoc name parsed)]
          rcases semanticInputEvidence with ⟨plan, planEq, relation⟩
          change some sourceCore = some plan at planEq
          injection planEq with planEq
          subst plan
          let plainCore := TokenPlan.concat [
            TokenPlan.plain (.hardKeyword .letKw),
            identifierPlan (RuleReduction.terminalLoc name parsed)]
          have plainRelation : TokenSlot.ListMatches plainCore.slots
              (PhysicalTokens tokens origin finish) := by
            have converted := TokenSlot.ListMatches.exactBetweenToPlain
              (left := TokenPlan.empty)
              (right := identifierPlan
                (RuleReduction.terminalLoc name parsed))
              (kind := .hardKeyword .letKw)
              (span := letKeyword.span)
              (by
                simpa [sourceCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using relation)
            simpa [plainCore, TokenPlan.concat_cons,
              TokenPlan.append_assoc] using converted
          have plainAnchored : plainCore.WellAnchored := by
            dsimp only [plainCore]
            simpa [TokenPlan.concat_cons] using
              TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.plain (.hardKeyword .letKw))
                (identifierPlan_wellAnchored
                  (RuleReduction.terminalLoc name parsed))
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some plainRelation)
            (fun candidate success => by
              simp only [Option.some.injEq] at success
              subst candidate
              exact plainAnchored)
            witness.consumed
          simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
            letBindingTokenPlan?, sourceLoc, plainCore,
            TokenPlan.concat_cons, TokenPlan.append_assoc]
            using enclosed
      | some initializer =>
          rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
            EbnfValue.tokenPlan?_sequence,
            EbnfValues.tokenPlan?_cons,
            EbnfValue.tokenPlan?_terminalAtom,
            EbnfValues.tokenPlan?_cons,
            EbnfValue.tokenPlan?_ruleAtom,
            EbnfValues.tokenPlan?_nil,
            MatchedTerminal.physicalTokenPlan_symbol]
            at semanticInputEvidence
          simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
            at semanticInputEvidence
          cases expressionPlanEq : expressionTokenPlan? initializer.2 with
          | none =>
              simp [expressionPlanEq, TokenPlanEvidence]
                at semanticInputEvidence
          | some expressionPlan =>
              simp only [expressionPlanEq] at semanticInputEvidence
              change expressionTokenPlanAt? .annotation initializer.2 =
                some expressionPlan at expressionPlanEq
              let sourceCore := TokenPlan.concat [
                TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.exact (.symbol .equal) initializer.1.span,
                expressionPlan]
              rcases semanticInputEvidence with ⟨plan, planEq, relation⟩
              have sourcePlanEq : some sourceCore = some plan := by
                simpa [sourceCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using planEq
              injection sourcePlanEq with planEq
              subst plan
              let keywordCore := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .letKw),
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.exact (.symbol .equal) initializer.1.span,
                expressionPlan]
              have keywordRelation : TokenSlot.ListMatches keywordCore.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted := TokenSlot.ListMatches.exactBetweenToPlain
                  (left := TokenPlan.empty)
                  (right := TokenPlan.concat [
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.exact (.symbol .equal) initializer.1.span,
                    expressionPlan])
                  (kind := .hardKeyword .letKw)
                  (span := letKeyword.span)
                  (by
                    simpa [sourceCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using relation)
                simpa [keywordCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using converted
              let plainCore := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .letKw),
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.plain (.symbol .equal),
                expressionPlan]
              have plainRelation : TokenSlot.ListMatches plainCore.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted := TokenSlot.ListMatches.exactBetweenToPlain
                  (left := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .letKw),
                    identifierPlan (RuleReduction.terminalLoc name parsed)])
                  (right := expressionPlan)
                  (kind := .symbol .equal)
                  (span := initializer.1.span)
                  (by
                    simpa [keywordCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using keywordRelation)
                simpa [plainCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using converted
              have expressionAnchored : expressionPlan.WellAnchored :=
                expressionTokenPlan?_wellAnchored initializer.2
                  expressionPlan expressionPlanEq
              have plainAnchored : plainCore.WellAnchored := by
                dsimp only [plainCore]
                simp only [TokenPlan.concat_cons,
                  TokenPlan.concat_nil, TokenPlan.append_empty]
                exact TokenPlan.WellAnchored.append
                  (TokenPlan.WellAnchored.plain (.hardKeyword .letKw))
                  (TokenPlan.WellAnchored.append
                    (identifierPlan_wellAnchored
                      (RuleReduction.terminalLoc name parsed))
                    (TokenPlan.WellAnchored.append
                      (TokenPlan.WellAnchored.plain (.symbol .equal))
                      expressionAnchored))
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some plainRelation)
                (fun candidate success => by
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact plainAnchored)
                witness.consumed
              simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
                letBindingTokenPlan?, sourceLoc, plainCore,
                expressionPlanEq, TokenPlan.concat_cons,
                TokenPlan.append_assoc] using enclosed
  | letBindingTyped origin finish letKeyword name spelling parsed nameProjects
      colon typeValue initializer witness =>
      change TokenPlanEvidence
        ((letBindingTypedInput letKeyword name colon typeValue initializer).tokenPlan?
          sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at semanticInputEvidence
      unfold letBindingTypedInput letBindingInitializerValue
        at semanticInputEvidence
      simp only [letBindingChildren, letKeywordExpr, letNameExpr,
        letColonExpr, letComptimeExpr, letTypeExpr, letEqualExpr,
        letInitializerExpressionExpr, letTypeSequenceExpr,
        letInitializerSequenceExpr, Grammar.sequence,
        Grammar.hardKeyword, Grammar.identifier, Grammar.symbol,
        Grammar.category, Grammar.contextualKeyword, Grammar.nonterminal,
        Grammar.optional, Grammar.terminal] at semanticInputEvidence
      rw [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        EbnfValues.tokenPlan?_cons,
        MatchedTerminal.physicalTokenPlan_hardKeyword,
        matchedIdentifier_physicalTokenPlan_local name spelling parsed
          nameProjects,
        MatchedTerminal.physicalTokenPlan_symbol]
        at semanticInputEvidence
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
        at semanticInputEvidence
      cases typePlanEq : typeExprPlan? typeValue with
      | none =>
          simp [typePlanEq, TokenPlanEvidence] at semanticInputEvidence
      | some typePlan =>
          simp only [typePlanEq] at semanticInputEvidence
          rcases typeValue with ⟨typeSpan, typePayload⟩
          cases typePayload
          case comptime typeMarker inner =>
              exact False.elim
                (coherentLetBinding_typedComptime_impossible complete coherent
                  letKeyword name colon typeSpan typeMarker inner initializer
                  inputEq)
          all_goals
            cases initializer with
            | none =>
                simp only [Option.map, EbnfValue.tokenPlan?_optional_none,
                  EbnfValues.tokenPlan?_nil] at semanticInputEvidence
                let sourceCore := TokenPlan.concat [
                  TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
                  identifierPlan (RuleReduction.terminalLoc name parsed),
                  TokenPlan.exact (.symbol .colon) colon.span,
                  typePlan]
                rcases semanticInputEvidence with ⟨plan, planEq, relation⟩
                have sourcePlanEq : some sourceCore = some plan := by
                  simpa [sourceCore, TokenPlan.concat_cons,
                    TokenPlan.append_assoc] using planEq
                injection sourcePlanEq with planEq
                subst plan
                let keywordCore := TokenPlan.concat [
                  TokenPlan.plain (.hardKeyword .letKw),
                  identifierPlan (RuleReduction.terminalLoc name parsed),
                  TokenPlan.exact (.symbol .colon) colon.span,
                  typePlan]
                have keywordRelation : TokenSlot.ListMatches keywordCore.slots
                    (PhysicalTokens tokens origin finish) := by
                  have converted := TokenSlot.ListMatches.exactBetweenToPlain
                    (left := TokenPlan.empty)
                    (right := TokenPlan.concat [
                      identifierPlan (RuleReduction.terminalLoc name parsed),
                      TokenPlan.exact (.symbol .colon) colon.span,
                      typePlan])
                    (kind := .hardKeyword .letKw)
                    (span := letKeyword.span)
                    (by
                      simpa [sourceCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using relation)
                  simpa [keywordCore, TokenPlan.concat_cons,
                    TokenPlan.append_assoc] using converted
                let plainCore := TokenPlan.concat [
                  TokenPlan.plain (.hardKeyword .letKw),
                  identifierPlan (RuleReduction.terminalLoc name parsed),
                  TokenPlan.plain (.symbol .colon),
                  typePlan]
                have plainRelation : TokenSlot.ListMatches plainCore.slots
                    (PhysicalTokens tokens origin finish) := by
                  have converted := TokenSlot.ListMatches.exactBetweenToPlain
                    (left := TokenPlan.concat [
                      TokenPlan.plain (.hardKeyword .letKw),
                      identifierPlan (RuleReduction.terminalLoc name parsed)])
                    (right := typePlan)
                    (kind := .symbol .colon)
                    (span := colon.span)
                    (by
                      simpa [keywordCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using keywordRelation)
                  simpa [plainCore, TokenPlan.concat_cons,
                    TokenPlan.append_assoc] using converted
                have typeAnchored : typePlan.WellAnchored :=
                  typeExprPlan?_wellAnchored _ typePlan typePlanEq
                have plainAnchored : plainCore.WellAnchored := by
                  dsimp only [plainCore]
                  simp only [TokenPlan.concat_cons,
                    TokenPlan.concat_nil, TokenPlan.append_empty]
                  exact TokenPlan.WellAnchored.append
                    (TokenPlan.WellAnchored.plain (.hardKeyword .letKw))
                    (TokenPlan.WellAnchored.append
                      (identifierPlan_wellAnchored
                        (RuleReduction.terminalLoc name parsed))
                      (TokenPlan.WellAnchored.append
                        (TokenPlan.WellAnchored.plain (.symbol .colon))
                        typeAnchored))
                have enclosed := TokenPlanEvidence.enclose
                  (TokenPlanEvidence.some plainRelation)
                  (fun candidate success => by
                    simp only [Option.some.injEq] at success
                    subst candidate
                    exact plainAnchored)
                  witness.consumed
                simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
                  letBindingTokenPlan?, sourceLoc, plainCore, typePlanEq,
                  TokenPlan.concat_cons, TokenPlan.append_assoc]
                  using enclosed
            | some initializer =>
                rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
                  EbnfValue.tokenPlan?_sequence,
                  EbnfValues.tokenPlan?_cons,
                  EbnfValue.tokenPlan?_terminalAtom,
                  EbnfValues.tokenPlan?_cons,
                  EbnfValue.tokenPlan?_ruleAtom,
                  EbnfValues.tokenPlan?_nil,
                  MatchedTerminal.physicalTokenPlan_symbol]
                  at semanticInputEvidence
                simp only [ruleTokenPlan?]
                  at semanticInputEvidence
                cases expressionPlanEq : expressionTokenPlan? initializer.2 with
                | none =>
                    simp [expressionPlanEq, TokenPlanEvidence]
                      at semanticInputEvidence
                | some expressionPlan =>
                    simp only [expressionPlanEq] at semanticInputEvidence
                    change expressionTokenPlanAt? .annotation initializer.2 =
                      some expressionPlan at expressionPlanEq
                    let sourceCore := TokenPlan.concat [
                      TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
                      identifierPlan (RuleReduction.terminalLoc name parsed),
                      TokenPlan.exact (.symbol .colon) colon.span,
                      typePlan,
                      TokenPlan.exact (.symbol .equal) initializer.1.span,
                      expressionPlan]
                    rcases semanticInputEvidence with
                      ⟨plan, planEq, relation⟩
                    have sourcePlanEq : some sourceCore = some plan := by
                      simpa [sourceCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using planEq
                    injection sourcePlanEq with planEq
                    subst plan
                    let keywordCore := TokenPlan.concat [
                      TokenPlan.plain (.hardKeyword .letKw),
                      identifierPlan (RuleReduction.terminalLoc name parsed),
                      TokenPlan.exact (.symbol .colon) colon.span,
                      typePlan,
                      TokenPlan.exact (.symbol .equal) initializer.1.span,
                      expressionPlan]
                    have keywordRelation :
                        TokenSlot.ListMatches keywordCore.slots
                          (PhysicalTokens tokens origin finish) := by
                      have converted :=
                        TokenSlot.ListMatches.exactBetweenToPlain
                          (left := TokenPlan.empty)
                          (right := TokenPlan.concat [
                            identifierPlan
                              (RuleReduction.terminalLoc name parsed),
                            TokenPlan.exact (.symbol .colon) colon.span,
                            typePlan,
                            TokenPlan.exact (.symbol .equal)
                              initializer.1.span,
                            expressionPlan])
                          (kind := .hardKeyword .letKw)
                          (span := letKeyword.span)
                          (by
                            simpa [sourceCore, TokenPlan.concat_cons,
                              TokenPlan.append_assoc] using relation)
                      simpa [keywordCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using converted
                    let colonCore := TokenPlan.concat [
                      TokenPlan.plain (.hardKeyword .letKw),
                      identifierPlan (RuleReduction.terminalLoc name parsed),
                      TokenPlan.plain (.symbol .colon),
                      typePlan,
                      TokenPlan.exact (.symbol .equal) initializer.1.span,
                      expressionPlan]
                    have colonRelation :
                        TokenSlot.ListMatches colonCore.slots
                          (PhysicalTokens tokens origin finish) := by
                      have converted :=
                        TokenSlot.ListMatches.exactBetweenToPlain
                          (left := TokenPlan.concat [
                            TokenPlan.plain (.hardKeyword .letKw),
                            identifierPlan
                              (RuleReduction.terminalLoc name parsed)])
                          (right := TokenPlan.concat [
                            typePlan,
                            TokenPlan.exact (.symbol .equal)
                              initializer.1.span,
                            expressionPlan])
                          (kind := .symbol .colon)
                          (span := colon.span)
                          (by
                            simpa [keywordCore, TokenPlan.concat_cons,
                              TokenPlan.append_assoc] using keywordRelation)
                      simpa [colonCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using converted
                    let plainCore := TokenPlan.concat [
                      TokenPlan.plain (.hardKeyword .letKw),
                      identifierPlan (RuleReduction.terminalLoc name parsed),
                      TokenPlan.plain (.symbol .colon),
                      typePlan,
                      TokenPlan.plain (.symbol .equal),
                      expressionPlan]
                    have plainRelation :
                        TokenSlot.ListMatches plainCore.slots
                          (PhysicalTokens tokens origin finish) := by
                      have converted :=
                        TokenSlot.ListMatches.exactBetweenToPlain
                          (left := TokenPlan.concat [
                            TokenPlan.plain (.hardKeyword .letKw),
                            identifierPlan
                              (RuleReduction.terminalLoc name parsed),
                            TokenPlan.plain (.symbol .colon),
                            typePlan])
                          (right := expressionPlan)
                          (kind := .symbol .equal)
                          (span := initializer.1.span)
                          (by
                            simpa [colonCore, TokenPlan.concat_cons,
                              TokenPlan.append_assoc] using colonRelation)
                      simpa [plainCore, TokenPlan.concat_cons,
                        TokenPlan.append_assoc] using converted
                    have typeAnchored : typePlan.WellAnchored :=
                      typeExprPlan?_wellAnchored _ typePlan typePlanEq
                    have expressionAnchored : expressionPlan.WellAnchored :=
                      expressionTokenPlan?_wellAnchored initializer.2
                        expressionPlan expressionPlanEq
                    have plainAnchored : plainCore.WellAnchored := by
                      dsimp only [plainCore]
                      simp only [TokenPlan.concat_cons,
                        TokenPlan.concat_nil, TokenPlan.append_empty]
                      exact TokenPlan.WellAnchored.append
                        (TokenPlan.WellAnchored.plain
                          (.hardKeyword .letKw))
                        (TokenPlan.WellAnchored.append
                          (identifierPlan_wellAnchored
                            (RuleReduction.terminalLoc name parsed))
                          (TokenPlan.WellAnchored.append
                            (TokenPlan.WellAnchored.plain (.symbol .colon))
                            (TokenPlan.WellAnchored.append typeAnchored
                              (TokenPlan.WellAnchored.append
                                (TokenPlan.WellAnchored.plain
                                  (.symbol .equal))
                                expressionAnchored))))
                    have enclosed := TokenPlanEvidence.enclose
                      (TokenPlanEvidence.some plainRelation)
                      (fun candidate success => by
                        simp only [Option.some.injEq] at success
                        subst candidate
                        exact plainAnchored)
                      witness.consumed
                    simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
                      letBindingTokenPlan?, sourceLoc, plainCore, typePlanEq,
                      expressionPlanEq, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using enclosed
  | letBindingComptime origin finish letKeyword name spelling parsed
      nameProjects colon comptime typeValue initializer witness =>
      change TokenPlanEvidence
        ((letBindingComptimeInput letKeyword name colon comptime typeValue
          initializer).tokenPlan? sourceRuleTokenPlanLayout)
        (PhysicalTokens tokens origin finish) at semanticInputEvidence
      unfold letBindingComptimeInput letBindingInitializerValue
        at semanticInputEvidence
      simp only [letBindingChildren, letKeywordExpr, letNameExpr,
        letColonExpr, letComptimeExpr, letTypeExpr, letEqualExpr,
        letInitializerExpressionExpr, letTypeSequenceExpr,
        letInitializerSequenceExpr, Grammar.sequence,
        Grammar.hardKeyword, Grammar.identifier, Grammar.symbol,
        Grammar.category, Grammar.contextualKeyword, Grammar.nonterminal,
        Grammar.optional, Grammar.terminal] at semanticInputEvidence
      rw [EbnfValue.tokenPlan?_transport,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_sequence,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_optional_some,
        EbnfValue.tokenPlan?_terminalAtom,
        EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValues.tokenPlan?_nil,
        EbnfValues.tokenPlan?_cons,
        MatchedTerminal.physicalTokenPlan_hardKeyword,
        matchedIdentifier_physicalTokenPlan_local name spelling parsed
          nameProjects,
        MatchedTerminal.physicalTokenPlan_symbol,
        matchedContextualKeyword_physicalTokenPlan_local .comptimeKw
          comptime]
        at semanticInputEvidence
      simp only [sourceRuleTokenPlanLayout, ruleTokenPlan?]
        at semanticInputEvidence
      cases typePlanEq : typeExprPlan? typeValue with
      | none =>
          simp [typePlanEq, TokenPlanEvidence] at semanticInputEvidence
      | some typePlan =>
          simp only [typePlanEq] at semanticInputEvidence
          cases initializer with
          | none =>
              simp only [Option.map, EbnfValue.tokenPlan?_optional_none,
                EbnfValues.tokenPlan?_nil] at semanticInputEvidence
              let sourceCore := TokenPlan.concat [
                TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.exact (.symbol .colon) colon.span,
                TokenPlan.exact
                  (.identifier ContextualKeyword.comptimeKw.spelling)
                  comptime.span,
                typePlan]
              rcases semanticInputEvidence with ⟨plan, planEq, relation⟩
              have sourcePlanEq : some sourceCore = some plan := by
                simpa [sourceCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using planEq
              injection sourcePlanEq with planEq
              subst plan
              let keywordCore := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .letKw),
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.exact (.symbol .colon) colon.span,
                TokenPlan.exact
                  (.identifier ContextualKeyword.comptimeKw.spelling)
                  comptime.span,
                typePlan]
              have keywordRelation : TokenSlot.ListMatches keywordCore.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted := TokenSlot.ListMatches.exactBetweenToPlain
                  (left := TokenPlan.empty)
                  (right := TokenPlan.concat [
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.exact (.symbol .colon) colon.span,
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan])
                  (kind := .hardKeyword .letKw)
                  (span := letKeyword.span)
                  (by
                    simpa [sourceCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using relation)
                simpa [keywordCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using converted
              let plainCore := TokenPlan.concat [
                TokenPlan.plain (.hardKeyword .letKw),
                identifierPlan (RuleReduction.terminalLoc name parsed),
                TokenPlan.plain (.symbol .colon),
                TokenPlan.exact
                  (.identifier ContextualKeyword.comptimeKw.spelling)
                  comptime.span,
                typePlan]
              have plainRelation : TokenSlot.ListMatches plainCore.slots
                  (PhysicalTokens tokens origin finish) := by
                have converted := TokenSlot.ListMatches.exactBetweenToPlain
                  (left := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .letKw),
                    identifierPlan (RuleReduction.terminalLoc name parsed)])
                  (right := TokenPlan.concat [
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan])
                  (kind := .symbol .colon)
                  (span := colon.span)
                  (by
                    simpa [keywordCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using keywordRelation)
                simpa [plainCore, TokenPlan.concat_cons,
                  TokenPlan.append_assoc] using converted
              have typeAnchored : typePlan.WellAnchored :=
                typeExprPlan?_wellAnchored typeValue typePlan typePlanEq
              have plainAnchored : plainCore.WellAnchored := by
                dsimp only [plainCore]
                simp only [TokenPlan.concat_cons,
                  TokenPlan.concat_nil, TokenPlan.append_empty]
                exact TokenPlan.WellAnchored.append
                  (TokenPlan.WellAnchored.plain (.hardKeyword .letKw))
                  (TokenPlan.WellAnchored.append
                    (identifierPlan_wellAnchored
                      (RuleReduction.terminalLoc name parsed))
                    (TokenPlan.WellAnchored.append
                      (TokenPlan.WellAnchored.plain (.symbol .colon))
                      (TokenPlan.WellAnchored.append
                        (TokenPlan.WellAnchored.exact
                          (.identifier ContextualKeyword.comptimeKw.spelling)
                          comptime.span)
                        typeAnchored)))
              have enclosed := TokenPlanEvidence.enclose
                (TokenPlanEvidence.some plainRelation)
                (fun candidate success => by
                  simp only [Option.some.injEq] at success
                  subst candidate
                  exact plainAnchored)
                witness.consumed
              simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
                letBindingTokenPlan?, RuleReduction.marker,
                RuleReduction.terminalLoc, sourceLoc, plainCore, typePlanEq,
                TokenPlan.concat_cons, TokenPlan.append_assoc]
                using enclosed
          | some initializer =>
              rw [Option.map_some, EbnfValue.tokenPlan?_optional_some,
                EbnfValue.tokenPlan?_sequence,
                EbnfValues.tokenPlan?_cons,
                EbnfValue.tokenPlan?_terminalAtom,
                EbnfValues.tokenPlan?_cons,
                EbnfValue.tokenPlan?_ruleAtom,
                EbnfValues.tokenPlan?_nil,
                MatchedTerminal.physicalTokenPlan_symbol]
                at semanticInputEvidence
              simp only [ruleTokenPlan?] at semanticInputEvidence
              cases expressionPlanEq : expressionTokenPlan? initializer.2 with
              | none =>
                  simp [expressionPlanEq, TokenPlanEvidence]
                    at semanticInputEvidence
              | some expressionPlan =>
                  simp only [expressionPlanEq] at semanticInputEvidence
                  change expressionTokenPlanAt? .annotation initializer.2 =
                    some expressionPlan at expressionPlanEq
                  let sourceCore := TokenPlan.concat [
                    TokenPlan.exact (.hardKeyword .letKw) letKeyword.span,
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.exact (.symbol .colon) colon.span,
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan,
                    TokenPlan.exact (.symbol .equal) initializer.1.span,
                    expressionPlan]
                  rcases semanticInputEvidence with ⟨plan, planEq, relation⟩
                  have sourcePlanEq : some sourceCore = some plan := by
                    simpa [sourceCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using planEq
                  injection sourcePlanEq with planEq
                  subst plan
                  let keywordCore := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .letKw),
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.exact (.symbol .colon) colon.span,
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan,
                    TokenPlan.exact (.symbol .equal) initializer.1.span,
                    expressionPlan]
                  have keywordRelation :
                      TokenSlot.ListMatches keywordCore.slots
                        (PhysicalTokens tokens origin finish) := by
                    have converted :=
                      TokenSlot.ListMatches.exactBetweenToPlain
                        (left := TokenPlan.empty)
                        (right := TokenPlan.concat [
                          identifierPlan
                            (RuleReduction.terminalLoc name parsed),
                          TokenPlan.exact (.symbol .colon) colon.span,
                          TokenPlan.exact
                            (.identifier
                              ContextualKeyword.comptimeKw.spelling)
                            comptime.span,
                          typePlan,
                          TokenPlan.exact (.symbol .equal)
                            initializer.1.span,
                          expressionPlan])
                        (kind := .hardKeyword .letKw)
                        (span := letKeyword.span)
                        (by
                          simpa [sourceCore, TokenPlan.concat_cons,
                            TokenPlan.append_assoc] using relation)
                    simpa [keywordCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using converted
                  let colonCore := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .letKw),
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.plain (.symbol .colon),
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan,
                    TokenPlan.exact (.symbol .equal) initializer.1.span,
                    expressionPlan]
                  have colonRelation :
                      TokenSlot.ListMatches colonCore.slots
                        (PhysicalTokens tokens origin finish) := by
                    have converted :=
                      TokenSlot.ListMatches.exactBetweenToPlain
                        (left := TokenPlan.concat [
                          TokenPlan.plain (.hardKeyword .letKw),
                          identifierPlan
                            (RuleReduction.terminalLoc name parsed)])
                        (right := TokenPlan.concat [
                          TokenPlan.exact
                            (.identifier
                              ContextualKeyword.comptimeKw.spelling)
                            comptime.span,
                          typePlan,
                          TokenPlan.exact (.symbol .equal)
                            initializer.1.span,
                          expressionPlan])
                        (kind := .symbol .colon)
                        (span := colon.span)
                        (by
                          simpa [keywordCore, TokenPlan.concat_cons,
                            TokenPlan.append_assoc] using keywordRelation)
                    simpa [colonCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using converted
                  let plainCore := TokenPlan.concat [
                    TokenPlan.plain (.hardKeyword .letKw),
                    identifierPlan (RuleReduction.terminalLoc name parsed),
                    TokenPlan.plain (.symbol .colon),
                    TokenPlan.exact
                      (.identifier ContextualKeyword.comptimeKw.spelling)
                      comptime.span,
                    typePlan,
                    TokenPlan.plain (.symbol .equal),
                    expressionPlan]
                  have plainRelation :
                      TokenSlot.ListMatches plainCore.slots
                        (PhysicalTokens tokens origin finish) := by
                    have converted :=
                      TokenSlot.ListMatches.exactBetweenToPlain
                        (left := TokenPlan.concat [
                          TokenPlan.plain (.hardKeyword .letKw),
                          identifierPlan
                            (RuleReduction.terminalLoc name parsed),
                          TokenPlan.plain (.symbol .colon),
                          TokenPlan.exact
                            (.identifier
                              ContextualKeyword.comptimeKw.spelling)
                            comptime.span,
                          typePlan])
                        (right := expressionPlan)
                        (kind := .symbol .equal)
                        (span := initializer.1.span)
                        (by
                          simpa [colonCore, TokenPlan.concat_cons,
                            TokenPlan.append_assoc] using colonRelation)
                    simpa [plainCore, TokenPlan.concat_cons,
                      TokenPlan.append_assoc] using converted
                  have typeAnchored : typePlan.WellAnchored :=
                    typeExprPlan?_wellAnchored typeValue typePlan typePlanEq
                  have expressionAnchored : expressionPlan.WellAnchored :=
                    expressionTokenPlan?_wellAnchored initializer.2
                      expressionPlan expressionPlanEq
                  have plainAnchored : plainCore.WellAnchored := by
                    dsimp only [plainCore]
                    simp only [TokenPlan.concat_cons,
                      TokenPlan.concat_nil, TokenPlan.append_empty]
                    exact TokenPlan.WellAnchored.append
                      (TokenPlan.WellAnchored.plain
                        (.hardKeyword .letKw))
                      (TokenPlan.WellAnchored.append
                        (identifierPlan_wellAnchored
                          (RuleReduction.terminalLoc name parsed))
                        (TokenPlan.WellAnchored.append
                          (TokenPlan.WellAnchored.plain (.symbol .colon))
                          (TokenPlan.WellAnchored.append
                            (TokenPlan.WellAnchored.exact
                              (.identifier
                                ContextualKeyword.comptimeKw.spelling)
                              comptime.span)
                            (TokenPlan.WellAnchored.append typeAnchored
                              (TokenPlan.WellAnchored.append
                                (TokenPlan.WellAnchored.plain
                                  (.symbol .equal))
                                expressionAnchored)))))
                  have enclosed := TokenPlanEvidence.enclose
                    (TokenPlanEvidence.some plainRelation)
                    (fun candidate success => by
                      simp only [Option.some.injEq] at success
                      subst candidate
                      exact plainAnchored)
                    witness.consumed
                  simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?,
                    letBindingTokenPlan?, RuleReduction.marker,
                    RuleReduction.terminalLoc, sourceLoc, plainCore,
                    typePlanEq, expressionPlanEq, TokenPlan.concat_cons,
                    TokenPlan.append_assoc] using enclosed

end Solcore.Surface.Multi
