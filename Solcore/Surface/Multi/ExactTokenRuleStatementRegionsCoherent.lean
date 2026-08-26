import Solcore.Surface.Multi.AuxiliaryInversion
import Solcore.Surface.Multi.CoherentAtomRuleInversion
import Solcore.Surface.Multi.CoherentStarStatementInversion
import Solcore.Surface.Multi.EbnfDelimiterSoundness
import Solcore.Surface.Multi.ExactTokenReachability
import Solcore.Surface.Multi.ExactTokenRuleExpressionFolds
import Solcore.Surface.Multi.ExactTokenRuleForHelpers
import Solcore.Surface.Multi.ExactTokenRuleMatchArmAssembly
import Solcore.Surface.Multi.ExactTokenRuleParameterBody
import Solcore.Surface.Multi.RuleCoherentStatementLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

universe u v

local macro "solve_statement_site" : tactic =>
  `(tactic| simp [GrammarSiteKey.valid, GrammarSite.expression, m2cV1,
    m2cV1Rhs, EbnfExpr.nodeAt?, EbnfExpr.children, EbnfExpr.kind,
    Grammar.terminal, Grammar.hardKeyword, Grammar.contextualKeyword,
    Grammar.pragmaName, Grammar.symbol, Grammar.category,
    Grammar.nonterminal, Grammar.sequence, Grammar.choice, Grammar.group,
    Grammar.optional, Grammar.star, Grammar.plus, Grammar.list0,
    Grammar.list1, Grammar.identifier, Grammar.pathComponent])

private def expressionStatementRootSequenceSite : SequenceSite := {
  site := GrammarSite.root .expressionStatement
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def expressionStatementExpressionAtomSite : AtomSite := {
  site := ⟨{ rule := .expressionStatement, path := [0] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def expressionStatementOptionalSite : OptionalSite := {
  site := ⟨{ rule := .expressionStatement, path := [1] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def bodyRootSequenceSite : SequenceSite := {
  site := GrammarSite.root .body
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def bodyOpenBraceAtomSite : AtomSite := {
  site := ⟨{ rule := .body, path := [0] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def bodyStatementStarSite : StarSite := {
  site := ⟨{ rule := .body, path := [1] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def bodyCloseBraceAtomSite : AtomSite := {
  site := ⟨{ rule := .body, path := [2] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def matchArmPipeAtomSite : AtomSite := {
  site := ⟨{ rule := .matchArm, path := [0] }, by solve_statement_site⟩
  hasKind := by solve_statement_site
}

private def matchArmPatternListSite : List1Site := {
  site := ⟨{ rule := .matchArm, path := [1] }, by solve_statement_site⟩
  hasKind := by solve_statement_site
}

private def matchArmFatArrowAtomSite : AtomSite := {
  site := ⟨{ rule := .matchArm, path := [2] }, by solve_statement_site⟩
  hasKind := by solve_statement_site
}

private def armStatementRootAtomSite : AtomSite := {
  site := GrammarSite.root .armStatement
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def statementRootChoiceSite : ChoiceSite := {
  site := GrammarSite.root .statement
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def statementExpressionAtomSite : AtomSite := {
  site := ⟨{ rule := .statement, path := [10] }, by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl⟩
  hasKind := by
    run_tac Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl
}

private def statementExpressionBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨10, by
    have count : statementRootChoiceSite.branchCount = 11 := by
      run_tac Lean.Meta.withTransparency .all do
        (← Lean.Elab.Tactic.getMainGoal).refl
    rw [count]
    omega⟩

private theorem statementChoiceBranchExpressions :
    statementRootChoiceSite.branchExpressions.toList = [
      .atom (.nonterminal .letStatement),
      .atom (.nonterminal .returnStatement),
      .atom (.nonterminal .matchStatement),
      .atom (.nonterminal .ifStatement),
      .atom (.nonterminal .forStatement),
      .atom (.nonterminal .assemblyStatement),
      .atom (.nonterminal .blockStatement),
      .atom (.nonterminal .breakStatement),
      .atom (.nonterminal .continueStatement),
      .atom (.nonterminal .assignmentStatement),
      .atom (.nonterminal .expressionStatement)] := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

/-- Every displayed branch of the source `statement` choice is an atom. -/
private theorem statementChoiceBranches_atoms :
    ∀ expression ∈ statementRootChoiceSite.branchExpressions.toList,
      expression.kind = .atom := by
  intro expression member
  rw [statementChoiceBranchExpressions] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl <;> rfl

/-- Every direct child of the source `statement` choice is an atom site. -/
private def statementBranchAtomSite
    (branch : Fin statementRootChoiceSite.branchCount) : AtomSite := {
  site := statementRootChoiceSite.branch branch
  hasKind := by
    rw [statementRootChoiceSite.branch_expression]
    apply statementChoiceBranches_atoms
    rw [← statementRootChoiceSite.branch_get_toList branch]
    exact List.get_mem _ _
}

private theorem statementBranchAtomSite_site
    (branch : Fin statementRootChoiceSite.branchCount) :
    statementRootChoiceSite.branch branch =
      (statementBranchAtomSite branch).site := by
  rfl

private theorem statementRootChoiceBranchCount :
    statementRootChoiceSite.branchCount = 11 := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private def statementLetBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨0, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementReturnBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨1, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementMatchBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨2, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementIfBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨3, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementForBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨4, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementAssemblyBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨5, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementBlockBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨6, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementBreakBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨7, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementContinueBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨8, by rw [statementRootChoiceBranchCount]; omega⟩
private def statementAssignmentBranch :
    Fin statementRootChoiceSite.branchCount :=
  ⟨9, by rw [statementRootChoiceBranchCount]; omega⟩

private theorem statementLetBranch_shape :
    (statementBranchAtomSite statementLetBranch).atom =
      .nonterminal .letStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementReturnBranch_shape :
    (statementBranchAtomSite statementReturnBranch).atom =
      .nonterminal .returnStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementMatchBranch_shape :
    (statementBranchAtomSite statementMatchBranch).atom =
      .nonterminal .matchStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementIfBranch_shape :
    (statementBranchAtomSite statementIfBranch).atom =
      .nonterminal .ifStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementForBranch_shape :
    (statementBranchAtomSite statementForBranch).atom =
      .nonterminal .forStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementAssemblyBranch_shape :
    (statementBranchAtomSite statementAssemblyBranch).atom =
      .nonterminal .assemblyStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementBlockBranch_shape :
    (statementBranchAtomSite statementBlockBranch).atom =
      .nonterminal .blockStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementBreakBranch_shape :
    (statementBranchAtomSite statementBreakBranch).atom =
      .nonterminal .breakStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementContinueBranch_shape :
    (statementBranchAtomSite statementContinueBranch).atom =
      .nonterminal .continueStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementAssignmentBranch_shape :
    (statementBranchAtomSite statementAssignmentBranch).atom =
      .nonterminal .assignmentStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl
private theorem statementExpressionBranch_shape :
    (statementBranchAtomSite statementExpressionBranch).atom =
      .nonterminal .expressionStatement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem statementExpressionBranch_site :
    statementRootChoiceSite.branch statementExpressionBranch =
      statementExpressionAtomSite.site := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem statementExpressionAtomSite_expression :
    statementExpressionAtomSite.site.expression =
      .atom (.nonterminal .expressionStatement) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem statementExpressionBranch_listExpression :
    statementRootChoiceSite.branchExpressions.toList.get
        (statementRootChoiceSite.branchListIndex statementExpressionBranch) =
      .atom (.nonterminal .expressionStatement) := by
  exact (statementRootChoiceSite.branch_get_toList
      statementExpressionBranch).trans
    ((statementRootChoiceSite.branch_expression
      statementExpressionBranch).symm.trans
      ((congrArg GrammarSite.expression
        statementExpressionBranch_site).trans
        statementExpressionAtomSite_expression))

private theorem statementRootChoiceLayout : EbnfExpr.choice
      statementRootChoiceSite.branchExpressions.toList =
    m2cV1.rhs .statement := by
  exact statementRootChoiceSite.expression_eq_choice.symm.trans
    (GrammarSite.root_expression .statement)

private theorem statementExpression_inputValue_eq_choice
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (value : Statement) :
    RuleReduction.inputValue
        (RuleReduction.statementExpression (file := file) (tokens := tokens)
          origin finish value) =
      EbnfValue.transport statementRootChoiceLayout
        (EbnfValue.choice (file := file) (tokens := tokens)
          statementRootChoiceSite.branchExpressions.toList
          ⟨statementRootChoiceSite.branchListIndex
              statementExpressionBranch,
            EbnfValue.transport
              statementExpressionBranch_listExpression.symm
              (EbnfValue.ruleAtom (file := file) (tokens := tokens)
                .expressionStatement value)⟩) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem statementLet_inputValue_eq_selectedChoice
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens) (value : Statement) :
    RuleReduction.inputValue
        (RuleReduction.statementLet (file := file) (tokens := tokens)
          origin finish value) =
      EbnfValue.transport statementRootChoiceLayout
        (EbnfValue.choice statementRootChoiceSite.branchExpressions.toList
          ⟨statementRootChoiceSite.branchListIndex statementLetBranch,
            EbnfValue.transport
              ((congrArg GrammarSite.expression
                  (statementBranchAtomSite_site statementLetBranch)).symm.trans
                ((statementRootChoiceSite.branch_expression
                    statementLetBranch).trans
                  (statementRootChoiceSite.branch_get_toList
                    statementLetBranch).symm))
              (EbnfValue.ofShape
                (statementBranchAtomSite statementLetBranch).expression_eq_atom
                (EbnfValue.transport
                  (congrArg EbnfExpr.atom statementLetBranch_shape).symm
                  (EbnfValue.ruleAtom .letStatement value)))⟩) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem bodyRootSequenceSite_children :
    bodyRootSequenceSite.children = [
      bodyOpenBraceAtomSite.site,
      bodyStatementStarSite.site,
      bodyCloseBraceAtomSite.site] := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem bodyStatementStarSite_child_expression :
    bodyStatementStarSite.child.expression =
      .atom (.nonterminal .statement) := by
  have outer : bodyStatementStarSite.site.expression =
      .star (.atom (.nonterminal .statement)) := by
    unfold bodyStatementStarSite GrammarSite.expression m2cV1 m2cV1Rhs
      EbnfExpr.nodeAt?
    simp [EbnfExpr.children, EbnfExpr.nodeAt?, Grammar.sequence,
      Grammar.nonterminal, Grammar.star, Grammar.symbol, Grammar.terminal]
  exact EbnfExpr.star.inj
    (bodyStatementStarSite.expression_eq_star.symm.trans outer)

private theorem bodyOpenBraceAtomSite_expression :
    bodyOpenBraceAtomSite.site.expression =
      .atom (.terminal (.symbol .leftBrace)) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

private theorem bodyStatementStarSite_expression :
    bodyStatementStarSite.site.expression =
      .star (.atom (.nonterminal .statement)) := by
  exact bodyStatementStarSite.expression_eq_star.trans
    (congrArg EbnfExpr.star bodyStatementStarSite_child_expression)

private theorem bodyCloseBraceAtomSite_expression :
    bodyCloseBraceAtomSite.site.expression =
      .atom (.terminal (.symbol .rightBrace)) := by
  run_tac
    Lean.Meta.withTransparency .all do
      (← Lean.Elab.Tactic.getMainGoal).refl

/-- A matched symbol terminal exposes the corresponding raw symbol and its
exact successor boundary. -/
private theorem MatchedTerminal.immediatelyAfterSymbol_local
    {file : WorkspaceFile} {tokens : List Token} {symbol : Symbol}
    (matched : MatchedTerminal file tokens (.symbol symbol)) :
    ImmediatelyAfterSymbol file tokens symbol
      matched.cursor.beforeBoundary matched.cursor.afterBoundary := by
  rcases matched with
    ⟨cursor, value, span, terminalAt, terminalMatches⟩
  cases terminalAt with
  | retained token inRange lookup valid =>
      refine ⟨cursor, token, rfl, rfl, ?_, ?_⟩
      · exact .retained cursor token inRange lookup valid
      · simpa [TerminalMatches] using terminalMatches
  | endOfFile atEnd =>
      exact False.elim terminalMatches

private theorem matchArmSequenceSite_children :
    matchArmSequenceSite.children = [
      matchArmPipeAtomSite.site,
      matchArmPatternListSite.site,
      matchArmFatArrowAtomSite.site,
      matchArmBodyStarSite.site] := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem matchArmPipeAtomSite_expression :
    matchArmPipeAtomSite.site.expression =
      .atom (.terminal (.symbol .pipe)) := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem matchArmPatternListSite_expression :
    matchArmPatternListSite.site.expression =
      .list1 (.atom (.nonterminal .pattern)) := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem matchArmFatArrowAtomSite_expression :
    matchArmFatArrowAtomSite.site.expression =
      .atom (.terminal (.symbol .fatArrow)) := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem matchArmBodyStarSite_child_expression :
    matchArmBodyStarSite.child.expression =
      .atom (.nonterminal .armStatement) := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem matchArmBodyStarSite_expression :
    matchArmBodyStarSite.site.expression =
      .star (.atom (.nonterminal .armStatement)) := by
  exact matchArmBodyStarSite.expression_eq_star.trans
    (congrArg EbnfExpr.star matchArmBodyStarSite_child_expression)

private theorem matchArmRootSequenceLayout : EbnfExpr.sequence
      (matchArmSequenceSite.children.map GrammarSite.expression) =
    m2cV1.rhs .matchArm := by
  exact matchArmSequenceSite.expression_eq_sequence.symm.trans
    (GrammarSite.root_expression .matchArm)

private theorem armStatementRootAtomSite_shape :
    armStatementRootAtomSite.atom = .nonterminal .statement := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem armStatementRootAtomLayout :
    EbnfExpr.atom armStatementRootAtomSite.atom =
      m2cV1.rhs .armStatement := by
  exact armStatementRootAtomSite.expression_eq_atom.symm.trans
    (GrammarSite.root_expression .armStatement)

private theorem bodyRootSequenceLayout : EbnfExpr.sequence
      (bodyRootSequenceSite.children.map GrammarSite.expression) =
    m2cV1.rhs .body := by
  exact bodyRootSequenceSite.expression_eq_sequence.symm.trans
    (GrammarSite.root_expression .body)

private theorem bodyRootSequenceSite_isAt_body :
    bodyRootSequenceSite.site.isAt .body [] = true := by
  unfold bodyRootSequenceSite GrammarSite.isAt
  simp [GrammarSite.root]

private theorem bodyStatementStarSite_isAt_body :
    bodyStatementStarSite.site.isAt .body [1] = true := by
  unfold bodyStatementStarSite GrammarSite.isAt
  simp

private theorem expressionStatementRootSequenceSite_children :
    expressionStatementRootSequenceSite.children = [
      expressionStatementExpressionAtomSite.site,
      expressionStatementOptionalSite.site] := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem expressionStatementRootSequenceSite_not_body :
    expressionStatementRootSequenceSite.site.isAt .body [] = false := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem expressionStatementRootSequenceSite_not_matchArm :
    expressionStatementRootSequenceSite.site.isAt .matchArm [] = false := by
  run_tac Lean.Meta.withTransparency .all do
    (← Lean.Elab.Tactic.getMainGoal).refl

private theorem expressionStatementExpressionAtomSite_expression :
    expressionStatementExpressionAtomSite.site.expression =
      .atom (.nonterminal .expression) := by
  unfold expressionStatementExpressionAtomSite GrammarSite.expression
    m2cV1 m2cV1Rhs EbnfExpr.nodeAt?
  simp [EbnfExpr.children, EbnfExpr.nodeAt?, Grammar.sequence,
    Grammar.nonterminal, Grammar.optional, Grammar.symbol, Grammar.terminal]

private theorem expressionStatementOptionalSite_expression :
    expressionStatementOptionalSite.site.expression =
      .optional (.atom (.terminal (.symbol .semicolon))) := by
  unfold expressionStatementOptionalSite GrammarSite.expression m2cV1
    m2cV1Rhs EbnfExpr.nodeAt?
  simp [EbnfExpr.children, EbnfExpr.nodeAt?, Grammar.sequence,
    Grammar.nonterminal, Grammar.optional, Grammar.symbol, Grammar.terminal]

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

private theorem production_star_of_lhs_local
    (site : StarSite) (production : ProductionId)
    (lhs : production.lhs = .aux site.site) :
    ∃ branch, production = .star site branch := by
  have view := auxiliaryProductionView site.site production lhs
  rw [site.hasKind] at view
  cases view with
  | star refined branch same exact =>
      have refinedEq : refined = site := by
        cases refined
        cases site
        simp only at same ⊢
        subst_vars
        rfl
      subst refined
      exact ⟨branch, exact⟩

private theorem production_atom_of_lhs_local
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

private theorem production_root_of_lhs_local
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

private theorem eqMp_congrArg_trans_local
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

private theorem eqMp_proof_irrel_local
    {first second : Sort u}
    (left right : first = second) (value : first) :
    Eq.mp left value = Eq.mp right value := by
  have same : left = right := Subsingleton.elim _ _
  cases same
  rfl

private theorem grammarSymbolValue_nonterminal_transport_local
    {file : WorkspaceFile} {tokens : List Token}
    {left right : NonterminalSymbol}
    (equality : left = right)
    (value : NonterminalValue file tokens left) :
    Eq.mp (congrArg (GrammarSymbolValue file tokens)
        (congrArg GrammarSymbol.nonterminal equality)) value =
      Eq.mp (congrArg (NonterminalValue file tokens) equality) value := by
  cases equality
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

private theorem GrammarSymbolValues.transport_append_empty_single_direct_local
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol} {source target : GrammarSymbol}
    (priorLayout : prior = [])
    (fullLayout : prior ++ [source] = full)
    (viewLayout : full = [target]) (symbolLayout : source = target)
    (empty : GrammarSymbolValues file tokens [])
    (value : GrammarSymbolValue file tokens source) :
    GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport priorLayout.symm empty)
            (value, ())) =
      GrammarSymbolValues.transport viewLayout.symm
        (Eq.mp (congrArg (GrammarSymbolValue file tokens) symbolLayout)
          value, ()) := by
  cases priorLayout
  cases symbolLayout
  cases viewLayout
  rcases empty with ⟨⟩
  have fullProof : fullLayout = rfl := Subsingleton.elim _ _
  rw [fullProof]
  rfl

private theorem GrammarSymbolValues.transport_append_pair_to_local
    {file : WorkspaceFile} {tokens : List Token}
    {prior full target : List GrammarSymbol}
    {first second : GrammarSymbol}
    (priorLayout : prior = [first])
    (fullLayout : prior ++ [second] = full)
    (viewLayout : full = target)
    (targetLayout : target = [first, second])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second) :
    GrammarSymbolValues.transport viewLayout
        (GrammarSymbolValues.transport fullLayout
          (GrammarSymbolValues.append
            (GrammarSymbolValues.transport priorLayout.symm
              (firstValue, ()))
            (secondValue, ()))) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, ())) := by
  subst prior
  subst full
  subst target
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem GrammarSymbolValues.transport_append_three_to_local
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

private theorem GrammarSymbolValues.transport_append_three_direct_local
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

private theorem GrammarSymbolValues.transport_append_four_direct_local
    {file : WorkspaceFile} {tokens : List Token}
    {prior middle full : List GrammarSymbol}
    {first second third fourth : GrammarSymbol}
    (priorLayout : prior = [first, second])
    (middleLayout : prior ++ [third] = middle)
    (fullLayout : middle ++ [fourth] = full)
    (targetLayout : full = [first, second, third, fourth])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second)
    (thirdValue : GrammarSymbolValue file tokens third)
    (fourthValue : GrammarSymbolValue file tokens fourth) :
    GrammarSymbolValues.transport fullLayout
        (GrammarSymbolValues.append
          (GrammarSymbolValues.transport middleLayout
            (GrammarSymbolValues.append
              (GrammarSymbolValues.transport priorLayout.symm
                (firstValue, (secondValue, ())))
              (thirdValue, ())))
          (fourthValue, ())) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, (thirdValue, (fourthValue, ())))) := by
  subst prior
  subst middle
  subst full
  simp only [GrammarSymbolValues.transport_self]
  rfl

private theorem GrammarSymbolValues.transport_append_three_single_direct_local
    {file : WorkspaceFile} {tokens : List Token}
    {prior full : List GrammarSymbol}
    {first second third fourth : GrammarSymbol}
    (priorLayout : prior = [first, second, third])
    (fullLayout : prior ++ [fourth] = full)
    (targetLayout : full = [first, second, third, fourth])
    (firstValue : GrammarSymbolValue file tokens first)
    (secondValue : GrammarSymbolValue file tokens second)
    (thirdValue : GrammarSymbolValue file tokens third)
    (fourthValue : GrammarSymbolValue file tokens fourth) :
    GrammarSymbolValues.transport fullLayout
        (GrammarSymbolValues.append
          (GrammarSymbolValues.transport priorLayout.symm
            (firstValue, (secondValue, (thirdValue, ()))))
          (fourthValue, ())) =
      GrammarSymbolValues.transport targetLayout.symm
        (firstValue, (secondValue, (thirdValue, (fourthValue, ())))) := by
  subst prior
  subst full
  simp only [GrammarSymbolValues.transport_self]
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

private theorem root_atomTransport_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    (rule : GrammarRuleId) (site : AtomSite)
    (siteRoot : site.site = GrammarSite.root rule)
    (layout : EbnfExpr.atom site.atom = m2cV1.rhs rule)
    (value : EbnfValue file tokens (.atom site.atom)) :
    EbnfValue.atShape (GrammarSite.root_expression rule)
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
            (congrArg (fun child =>
              GrammarSymbol.nonterminal (.aux child)) siteRoot))
          (EbnfValue.ofShape site.expression_eq_atom value)) =
      EbnfValue.transport layout value := by
  let packed := EbnfValue.ofShape site.expression_eq_atom value
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

private theorem optionalView_sequence_ofAuxiliary_pair_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite} {firstSite secondSite : GrammarSite}
    {first child : EbnfExpr}
    (childrenEq : children = [firstSite, secondSite])
    (firstEq : firstSite.expression = first)
    (secondEq : secondSite.expression = .optional child)
    (symbolLayout : children.map (fun site =>
        GrammarSymbol.nonterminal (.aux site)) = [
      GrammarSymbol.nonterminal (.aux firstSite),
      GrammarSymbol.nonterminal (.aux secondSite)])
    (expressionLayout : children.map GrammarSite.expression =
      [first, .optional child])
    (firstValue : EbnfValue file tokens firstSite.expression)
    (secondValue : EbnfValue file tokens secondSite.expression) :
    EbnfValue.optionalView child
        (EbnfValue.sequence2View first (.optional child)
          (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
            (EbnfValue.sequence (children.map GrammarSite.expression)
              (EbnfValues.ofAuxiliaries children
                (GrammarSymbolValues.transport symbolLayout.symm
                  (firstValue, (secondValue, ()))))))).2 =
      EbnfValue.optionalView child
        (EbnfValue.atShape secondEq secondValue) := by
  subst children
  have canonicalExpressionLayout :
      [firstSite.expression, secondSite.expression] =
        [first, .optional child] := by
    simpa using expressionLayout
  have expressionProofEq :
      congrArg EbnfExpr.sequence expressionLayout =
        congrArg EbnfExpr.sequence canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProofEq]
  have exactSymbolLayout : symbolLayout = rfl := Subsingleton.elim _ _
  rw [exactSymbolLayout]
  simp only [List.map, GrammarSymbolValues.transport_self]
  rw [sequence2View_transport_pair_eq firstEq secondEq
    canonicalExpressionLayout]
  have firstAuxView := EbnfValues.ofAuxiliaries_cons_eq firstSite
    [secondSite] firstValue (secondValue, ())
  have tailEq :
      (EbnfValues.consView firstSite.expression [secondSite.expression]
        (EbnfValues.ofAuxiliaries [firstSite, secondSite]
          (firstValue, (secondValue, ())))).2 =
        EbnfValues.ofAuxiliaries [secondSite] (secondValue, ()) :=
    congrArg Prod.snd firstAuxView
  change EbnfValue.optionalView child
    (EbnfValue.transport secondEq
      (EbnfValues.consView secondSite.expression []
        (EbnfValues.consView firstSite.expression [secondSite.expression]
          (EbnfValues.ofAuxiliaries [firstSite, secondSite]
            (firstValue, (secondValue, ())))).2).1) = _
  rw [tailEq]
  have secondAuxView := EbnfValues.ofAuxiliaries_cons_eq secondSite []
    secondValue ()
  have secondViewEq :
      (EbnfValues.consView secondSite.expression []
        (EbnfValues.ofAuxiliaries [secondSite]
          (secondValue, ()))).1 = secondValue :=
    congrArg Prod.fst secondAuxView
  rw [secondViewEq]
  rfl

private theorem sequence2View_pair_second_local
    {file : WorkspaceFile} {tokens : List Token}
    (first second : EbnfExpr)
    (firstValue : EbnfValue file tokens first)
    (secondValue : EbnfValue file tokens second) :
    (EbnfValue.sequence2View first second
      (EbnfValue.sequence [first, second]
        (EbnfValues.cons first [second] firstValue
          (EbnfValues.cons second [] secondValue
            EbnfValues.nil)))).2 = secondValue := by
  have rebuilt := EbnfValue.sequence2_of_view first second
    (EbnfValue.sequence [first, second]
      (EbnfValues.cons first [second] firstValue
        (EbnfValues.cons second [] secondValue EbnfValues.nil)))
  have valuesEq := EbnfValue.sequence_injective _ rebuilt
  have tailEq := (EbnfValues.cons_injective _ _ valuesEq).2
  exact (EbnfValues.cons_injective _ _ tailEq).1

private theorem sequence3View_transport_three_eq_local
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

private theorem sequence4View_transport_four_eq_local
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

private theorem bodySequenceMiddle_auxiliary_three_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite}
    {firstLhs secondLhs thirdLhs : NonterminalSymbol}
    (childrenEq : children = [bodyOpenBraceAtomSite.site,
      bodyStatementStarSite.site, bodyCloseBraceAtomSite.site])
    (firstLhsEq : firstLhs = .aux bodyOpenBraceAtomSite.site)
    (secondLhsEq : secondLhs = .aux bodyStatementStarSite.site)
    (thirdLhsEq : thirdLhs = .aux bodyCloseBraceAtomSite.site)
    (symbolLayout : children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal firstLhs, .nonterminal secondLhs,
      .nonterminal thirdLhs])
    (expressionLayout : children.map GrammarSite.expression = [
      .atom (.terminal (.symbol .leftBrace)),
      .star (.atom (.nonterminal .statement)),
      .atom (.terminal (.symbol .rightBrace))])
    (firstValue : GrammarSymbolValue file tokens (.nonterminal firstLhs))
    (secondValue : GrammarSymbolValue file tokens (.nonterminal secondLhs))
    (thirdValue : GrammarSymbolValue file tokens (.nonterminal thirdLhs)) :
    (EbnfValue.sequence3View
      (.atom (.terminal (.symbol .leftBrace)))
      (.star (.atom (.nonterminal .statement)))
      (.atom (.terminal (.symbol .rightBrace)))
      (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
        (EbnfValue.sequence (children.map GrammarSite.expression)
          (EbnfValues.ofAuxiliaries children
            (GrammarSymbolValues.transport symbolLayout.symm
              (firstValue, (secondValue, (thirdValue, ())))))))).2.1 =
      EbnfValue.atShape bodyStatementStarSite_expression
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
          (congrArg GrammarSymbol.nonterminal secondLhsEq)) secondValue) := by
  subst children
  subst firstLhs
  subst secondLhs
  subst thirdLhs
  simp only [List.map] at expressionLayout ⊢
  have canonicalExpressionLayout : [
      bodyOpenBraceAtomSite.site.expression,
      bodyStatementStarSite.site.expression,
      bodyCloseBraceAtomSite.site.expression] = [
      .atom (.terminal (.symbol .leftBrace)),
      .star (.atom (.nonterminal .statement)),
      .atom (.terminal (.symbol .rightBrace))] := by
    simpa using expressionLayout
  have expressionProof : expressionLayout = canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProof]
  have symbolProof : symbolLayout = rfl := Subsingleton.elim _ _
  rw [symbolProof]
  simp only [GrammarSymbolValues.transport_self]
  rw [sequence3View_transport_three_eq_local
    bodyOpenBraceAtomSite_expression bodyStatementStarSite_expression
    bodyCloseBraceAtomSite_expression canonicalExpressionLayout]
  simp [EbnfValues.consView, EbnfValues.ofAuxiliaries,
    EbnfValue.atShape]
  apply congrArg (EbnfValue.atShape bodyStatementStarSite_expression)
  symm
  exact cast_eq _ _

private theorem matchArmSequenceFourth_auxiliary_four_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {children : List GrammarSite}
    {firstLhs secondLhs thirdLhs fourthLhs : NonterminalSymbol}
    (childrenEq : children = [matchArmPipeAtomSite.site,
      matchArmPatternListSite.site, matchArmFatArrowAtomSite.site,
      matchArmBodyStarSite.site])
    (firstLhsEq : firstLhs = .aux matchArmPipeAtomSite.site)
    (secondLhsEq : secondLhs = .aux matchArmPatternListSite.site)
    (thirdLhsEq : thirdLhs = .aux matchArmFatArrowAtomSite.site)
    (fourthLhsEq : fourthLhs = .aux matchArmBodyStarSite.site)
    (symbolLayout : children.map (fun child =>
        GrammarSymbol.nonterminal (.aux child)) = [
      .nonterminal firstLhs, .nonterminal secondLhs,
      .nonterminal thirdLhs, .nonterminal fourthLhs])
    (expressionLayout : children.map GrammarSite.expression = [
      .atom (.terminal (.symbol .pipe)),
      .list1 (.atom (.nonterminal .pattern)),
      .atom (.terminal (.symbol .fatArrow)),
      .star (.atom (.nonterminal .armStatement))])
    (firstValue : GrammarSymbolValue file tokens (.nonterminal firstLhs))
    (secondValue : GrammarSymbolValue file tokens (.nonterminal secondLhs))
    (thirdValue : GrammarSymbolValue file tokens (.nonterminal thirdLhs))
    (fourthValue : GrammarSymbolValue file tokens (.nonterminal fourthLhs)) :
    (EbnfValue.sequence4View
      (.atom (.terminal (.symbol .pipe)))
      (.list1 (.atom (.nonterminal .pattern)))
      (.atom (.terminal (.symbol .fatArrow)))
      (.star (.atom (.nonterminal .armStatement)))
      (EbnfValue.transport (congrArg EbnfExpr.sequence expressionLayout)
        (EbnfValue.sequence (children.map GrammarSite.expression)
          (EbnfValues.ofAuxiliaries children
            (GrammarSymbolValues.transport symbolLayout.symm
              (firstValue, (secondValue,
                (thirdValue, (fourthValue, ()))))))))).2.2.2 =
      EbnfValue.atShape matchArmBodyStarSite_expression
        (Eq.mp (congrArg (GrammarSymbolValue file tokens)
          (congrArg GrammarSymbol.nonterminal fourthLhsEq)) fourthValue) := by
  subst children
  subst firstLhs
  subst secondLhs
  subst thirdLhs
  subst fourthLhs
  simp only [List.map] at expressionLayout ⊢
  have canonicalExpressionLayout : [
      matchArmPipeAtomSite.site.expression,
      matchArmPatternListSite.site.expression,
      matchArmFatArrowAtomSite.site.expression,
      matchArmBodyStarSite.site.expression] = [
      .atom (.terminal (.symbol .pipe)),
      .list1 (.atom (.nonterminal .pattern)),
      .atom (.terminal (.symbol .fatArrow)),
      .star (.atom (.nonterminal .armStatement))] := by
    simpa using expressionLayout
  have expressionProof : expressionLayout = canonicalExpressionLayout :=
    Subsingleton.elim _ _
  rw [expressionProof]
  have symbolProof : symbolLayout = rfl := Subsingleton.elim _ _
  rw [symbolProof]
  simp only [GrammarSymbolValues.transport_self]
  rw [sequence4View_transport_four_eq_local
    matchArmPipeAtomSite_expression matchArmPatternListSite_expression
    matchArmFatArrowAtomSite_expression matchArmBodyStarSite_expression
    canonicalExpressionLayout]
  simp [EbnfValues.consView, EbnfValues.ofAuxiliaries,
    EbnfValue.atShape]
  apply congrArg (EbnfValue.atShape matchArmBodyStarSite_expression)
  symm
  exact cast_eq _ _

/-- Positive G08 enablement at an inherited body context identifies the
nearest legal end of that statement region. -/
theorem enabledG08Positive_nearestStatementRegion
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (productionInstance : ProductionInstanceKey tokens)
    (regionStart : Boundary tokens)
    (context : productionInstance.context = .bracedBody regionStart ∨
      productionInstance.context = .armBody regionStart)
    (enabled : EnabledProductionInstance file tokens memo correct final
      productionInstance)
    (member : (.G08_terminalExpression, .positive) ∈
      guardOf productionInstance.production) :
    NearestStatementRegion file tokens regionStart
      productionInstance.origin := by
  rcases enabled .G08_terminalExpression .positive member with
    ⟨key, productionEq, guardEq, polarityEq, witness⟩
  change key.val.productionInstance = productionInstance at productionEq
  change key.val.guardInstance.guard = .G08_terminalExpression at guardEq
  change key.val.polarity = .positive at polarityEq
  rcases witness with ⟨decision, _stored, evidence, allowed⟩
  have anchor := key.property.2
  rw [productionEq, guardEq, polarityEq] at anchor
  have siteEq : key.guardInstance.siteCursor =
      productionInstance.origin := anchor.2.2.1
  have startEq : key.guardInstance.contextStart = regionStart := by
    rcases context with context | context
    · have selected := anchor.2.2.2
      change (match productionInstance.context with
        | .bracedBody start => some start
        | .armBody start => some start
        | _ => none) = some key.val.guardInstance.contextStart at selected
      rw [context] at selected
      exact (Option.some.inj selected).symm
    · have selected := anchor.2.2.2
      change (match productionInstance.context with
        | .bracedBody start => some start
        | .armBody start => some start
        | _ => none) = some key.val.guardInstance.contextStart at selected
      rw [context] at selected
      exact (Option.some.inj selected).symm
  cases decision with
  | positive =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      have nearest := evidence.2
      change NearestStatementRegion file tokens
        key.val.guardInstance.contextStart
        key.val.guardInstance.siteCursor at nearest
      change key.val.guardInstance.contextStart = regionStart at startEq
      change key.val.guardInstance.siteCursor = productionInstance.origin at siteEq
      rw [startEq, siteEq] at nearest
      exact nearest
  | negative =>
      have denied : false = true := by
        simpa only [GuardWitnessKey.polarity, polarityEq,
          GuardDecision.allows, Polarity.accepts] using allowed
      exact False.elim (Bool.false_ne_true denied)
  | neutral =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      exact False.elim evidence.2

/-- A recursive match-arm star cannot be enabled at a genuine same-frame arm
header: G02 selects the empty branch there. -/
theorem enabledG02Negative_excludes_armHeader
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (productionInstance : ProductionInstanceKey tokens)
    (regionStart : Boundary tokens)
    (context : productionInstance.context = .armBody regionStart)
    (enabled : EnabledProductionInstance file tokens memo correct final
      productionInstance)
    (member : (.G02_matchArmBoundary, .negative) ∈
      guardOf productionInstance.production)
    (header : ArmHeaderAt file tokens regionStart
      productionInstance.origin) : False := by
  rcases enabled .G02_matchArmBoundary .negative member with
    ⟨key, productionEq, guardEq, polarityEq, witness⟩
  change key.val.productionInstance = productionInstance at productionEq
  change key.val.guardInstance.guard = .G02_matchArmBoundary at guardEq
  change key.val.polarity = .negative at polarityEq
  rcases witness with ⟨decision, _stored, evidence, allowed⟩
  have anchor := key.property.2
  rw [productionEq, guardEq, polarityEq] at anchor
  have siteEq : key.guardInstance.siteCursor =
      productionInstance.origin := anchor.2.2.1
  have startEq : key.guardInstance.contextStart = regionStart := by
    have selected := anchor.2.2.2
    change (match productionInstance.context with
      | .armBody start => some start
      | _ => none) = some key.val.guardInstance.contextStart at selected
    rw [context] at selected
    exact (Option.some.inj selected).symm
  cases decision with
  | positive =>
      have denied : false = true := by
        simpa only [GuardWitnessKey.polarity, polarityEq,
          GuardDecision.allows, Polarity.accepts] using allowed
      exact Bool.false_ne_true denied
  | negative =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      have notHeader := evidence.2.2
      change ¬ ArmHeaderAt file tokens
        key.val.guardInstance.contextStart
        key.val.guardInstance.siteCursor at notHeader
      change key.val.guardInstance.contextStart = regionStart at startEq
      change key.val.guardInstance.siteCursor =
        productionInstance.origin at siteEq
      rw [startEq, siteEq] at notHeader
      exact notHeader header
  | neutral =>
      unfold GuardEvidence at evidence
      simp only [GuardWitnessKey.guardInstance, guardEq] at evidence
      have noPipe := evidence.2
      change ¬ SymbolAtBoundary file tokens
        key.val.guardInstance.siteCursor .pipe at noPipe
      change key.val.guardInstance.siteCursor =
        productionInstance.origin at siteEq
      rw [siteEq] at noPipe
      exact noPipe header.2.2.1

/-- A coherent semicolon-free expression statement can finish only at the
nearest braced-body or match-arm statement-region boundary selected by G08. -/
theorem expressionStatementTerminal_nearestStatementRegion
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (regionStart : Boundary tokens)
    (regionContext : context = .bracedBody regionStart ∨
      context = .armBody regionStart)
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .expressionStatement origin finish
        context)
      ⟨span, .expression expression none⟩) :
    NearestStatementRegion file tokens regionStart finish := by
  cases coherent with
  | reduce root priorValues output reached complete coherentPrefix action =>
      have actionRule : RuleReduction file tokens .expressionStatement
          origin finish
          (RootAction.unpack .expressionStatement
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens .expressionStatement
                origin finish context) complete priorValues))
          ⟨span, .expression expression none⟩ := by
        exact actionReduces_eleven_shapes_exact.mp action
      generalize inputEq : RootAction.unpack .expressionStatement
          (PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens .expressionStatement
              origin finish context) complete priorValues) = semanticInput
          at actionRule
      generalize outputEq :
          (⟨span, .expression expression none⟩ : Statement) =
            semanticOutput at actionRule
      cases actionRule with
      | expressionStatementTerminated _ _ terminatedExpression semicolon
          terminatedWitness =>
          have payloadEq := congrArg Located.payload outputEq
          simp [sourceLoc] at payloadEq
      | expressionStatementTerminal _ _ terminalExpression terminalWitness =>
          cases coherentPrefix with
          | zero _ _ zero =>
              change 1 = 0 at zero
              omega
          | scan before after cursor priorValues scanWitness edge prior =>
              have productionEq : before.raw.production =
                  .root .expressionStatement := scanWitness.advance.1.symm
              have dotEq : before.raw.dot.val = 0 := by
                have advanced := scanWitness.advance.2.1
                change 1 = before.raw.dot.val + 1 at advanced
                omega
              have impossible : some (GrammarSymbol.terminal scanWitness.terminal) =
                  some (GrammarSymbol.nonterminal
                    (.aux (GrammarSite.root .expressionStatement))) := by
                let index := before.raw.dot.val
                have indexZero : index = 0 := dotEq
                calc
                  _ = before.raw.production.rhs[index]? :=
                    scanWitness.next.2.symm
                  _ = (ProductionId.root .expressionStatement).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) productionEq
                  _ = (ProductionId.root .expressionStatement).rhs[0]? := by
                    rw [indexZero]
                  _ = _ := by simp [ProductionId.rhs]
              exact GrammarSymbol.noConfusion (Option.some.inj impossible)
          | complete rootWaiting sequence _ rootShared rootPriorValues
              sequenceValue rootWitness rootEdge rootPrior sequenceReduction =>
              have rootWaitingProduction : rootWaiting.raw.production =
                  .root .expressionStatement := rootWitness.advance.1.symm
              have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
                have advanced := rootWitness.advance.2.1
                change 1 = rootWaiting.raw.dot.val + 1 at advanced
                omega
              have sequenceLhs : sequence.raw.production.lhs =
                  .aux (GrammarSite.root .expressionStatement) := by
                have selected : some (GrammarSymbol.nonterminal
                      sequence.raw.production.lhs) =
                    some (GrammarSymbol.nonterminal
                      (.aux (GrammarSite.root .expressionStatement))) := by
                  let index := rootWaiting.raw.dot.val
                  calc
                    _ = rootWaiting.raw.production.rhs[index]? :=
                      rootWitness.next.2.symm
                    _ = (ProductionId.root .expressionStatement).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) rootWaitingProduction
                    _ = (ProductionId.root .expressionStatement).rhs[0]? := by
                      have indexZero : index = 0 := rootWaitingDot
                      rw [indexZero]
                    _ = _ := by simp [ProductionId.rhs]
                exact GrammarSymbol.nonterminal.inj
                  (Option.some.inj selected)
              have sequenceProduction : sequence.raw.production =
                  .seq expressionStatementRootSequenceSite :=
                production_eq_sequence_of_lhs
                  expressionStatementRootSequenceSite sequence.raw.production
                  (by simpa [expressionStatementRootSequenceSite] using
                    sequenceLhs)
              rcases sequence with
                ⟨⟨sequenceProductionId, sequenceDot, sequenceOrigin,
                  sequenceCurrent⟩, sequenceContext⟩
              simp only at sequenceProduction
              subst sequenceProductionId
              let sequence : ContextualItemKey tokens :=
                ⟨⟨.seq expressionStatementRootSequenceSite,
                  sequenceDot, sequenceOrigin, sequenceCurrent⟩,
                  sequenceContext⟩
              have sequenceProduction : sequence.raw.production =
                  .seq expressionStatementRootSequenceSite := rfl
              change CoherentReduction file tokens memo correct final
                sequence sequenceValue at sequenceReduction
              have rootPriorLayout :
                  rootWaiting.raw.production.rhs.take
                      rootWaiting.raw.dot.val = [] := by
                let index := rootWaiting.raw.dot.val
                have dotZero : index = 0 := rootWaitingDot
                calc
                  _ = (ProductionId.root .expressionStatement).rhs.take
                      index := congrArg (fun production : ProductionId =>
                        production.rhs.take index) rootWaitingProduction
                  _ = (ProductionId.root .expressionStatement).rhs.take 0 := by
                    rw [dotZero]
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
                      (.aux (GrammarSite.root .expressionStatement)) :=
                congrArg GrammarSymbol.nonterminal sequenceLhs
              have rootTupleEq :=
                GrammarSymbolValues.transport_append_empty_single_to_local
                  rootPriorLayout
                  ((prefix_complete_layout rootWaiting.raw sequence.raw
                    (CanonicalCompleteRootItem tokens .expressionStatement
                      origin finish context).raw rootWitness.next
                      rootWitness.advance).trans
                    (prefix_full_layout
                      (CanonicalCompleteRootItem tokens .expressionStatement
                        origin finish context).raw complete))
                  (ProductionId.rhs_root .expressionStatement)
                  rootSymbolLayout rootEmpty sequenceValue
              rw [RootAction.unpack_eq] at inputEq
              unfold GrammarSymbolValues.view at inputEq
              have rootHeadEq := congrArg Prod.fst rootTupleEq
              have rootHeadAtEq := congrArg
                (EbnfValue.atShape
                  (GrammarSite.root_expression .expressionStatement))
                rootHeadEq
              have rootInputEq := rootHeadAtEq.symm.trans inputEq
              cases sequenceReduction with
              | reduce _ sequenceValues sequenceOutput sequenceReached
                  sequenceComplete sequenceCoherent sequenceAction =>
                  cases sequenceCoherent with
                  | zero item reached zero =>
                      have dotTwo : sequence.raw.dot.val = 2 := by
                        calc
                          _ = sequence.raw.production.rhs.length :=
                            sequenceComplete
                          _ = 2 := by
                            rw [sequenceProduction]
                            simp [ProductionId.rhs_seq,
                              expressionStatementRootSequenceSite_children]
                      omega
                  | scan before after cursor priorValues scanWitness edge prior =>
                      have beforeProduction : before.raw.production =
                          .seq expressionStatementRootSequenceSite :=
                        scanWitness.advance.1.symm.trans sequenceProduction
                      have beforeDot : before.raw.dot.val = 1 := by
                        have advanced := scanWitness.advance.2.1
                        have itemDot : sequence.raw.dot.val = 2 := by
                          calc
                            _ = sequence.raw.production.rhs.length :=
                              sequenceComplete
                            _ = 2 := by
                              rw [sequenceProduction]
                              simp [ProductionId.rhs_seq,
                                expressionStatementRootSequenceSite_children]
                        omega
                      have impossible : some
                            (GrammarSymbol.terminal scanWitness.terminal) =
                          some (GrammarSymbol.nonterminal
                            (.aux expressionStatementOptionalSite.site)) := by
                        let index := before.raw.dot.val
                        calc
                          _ = before.raw.production.rhs[index]? :=
                            scanWitness.next.2.symm
                          _ = (ProductionId.seq
                              expressionStatementRootSequenceSite).rhs[index]? :=
                            congrArg (fun production : ProductionId =>
                              production.rhs[index]?) beforeProduction
                          _ = (ProductionId.seq
                              expressionStatementRootSequenceSite).rhs[1]? := by
                            have indexOne : index = 1 := beforeDot
                            rw [indexOne]
                          _ = _ := by
                            simp [ProductionId.rhs_seq,
                              expressionStatementRootSequenceSite_children]
                      exact GrammarSymbol.noConfusion
                        (Option.some.inj impossible)
                  | complete sequenceWaiting optionalItem _ optionalShared
                      sequencePriorValues optionalValue optionalWitness
                      optionalEdge sequencePrior optionalReduction =>
                      have sequenceDotValue : sequence.raw.dot.val = 2 := by
                        calc
                          _ = sequence.raw.production.rhs.length :=
                            sequenceComplete
                          _ = 2 := by
                            rw [sequenceProduction]
                            simp [ProductionId.rhs_seq,
                              expressionStatementRootSequenceSite_children]
                      have sequenceWaitingDot :
                          sequenceWaiting.raw.dot.val = 1 := by
                        have advanced := optionalWitness.advance.2.1
                        omega
                      have sequenceWaitingProduction :
                          sequenceWaiting.raw.production =
                            .seq expressionStatementRootSequenceSite :=
                        optionalWitness.advance.1.symm.trans
                          sequenceProduction
                      have optionalLhs : optionalItem.raw.production.lhs =
                          .aux expressionStatementOptionalSite.site := by
                        have selected : some (GrammarSymbol.nonterminal
                              optionalItem.raw.production.lhs) =
                            some (GrammarSymbol.nonterminal
                              (.aux expressionStatementOptionalSite.site)) := by
                          let index := sequenceWaiting.raw.dot.val
                          calc
                            _ = sequenceWaiting.raw.production.rhs[index]? :=
                              optionalWitness.next.2.symm
                            _ = (ProductionId.seq
                                expressionStatementRootSequenceSite).rhs[index]? :=
                              congrArg (fun production : ProductionId =>
                                production.rhs[index]?)
                                sequenceWaitingProduction
                            _ = (ProductionId.seq
                                expressionStatementRootSequenceSite).rhs[1]? := by
                              have indexOne : index = 1 := sequenceWaitingDot
                              rw [indexOne]
                            _ = _ := by
                              simp [ProductionId.rhs_seq,
                                expressionStatementRootSequenceSite_children]
                        exact GrammarSymbol.nonterminal.inj
                          (Option.some.inj selected)
                      rcases production_optional_of_lhs
                          expressionStatementOptionalSite
                          optionalItem.raw.production optionalLhs with
                        ⟨optionalBranch, optionalProduction⟩
                      rcases optionalItem with
                        ⟨⟨optionalProductionId, optionalDot,
                          optionalOrigin, optionalCurrent⟩, optionalContext⟩
                      simp only at optionalProduction
                      subst optionalProductionId
                      let optionalItem : ContextualItemKey tokens :=
                        ⟨⟨.opt expressionStatementOptionalSite
                            optionalBranch, optionalDot, optionalOrigin,
                            optionalCurrent⟩, optionalContext⟩
                      change CoherentReduction file tokens memo correct final
                        optionalItem optionalValue at optionalReduction
                      have sequencePackedEq :=
                        actionReduces_eleven_shapes_exact.mp sequenceAction
                      dsimp only [sequence] at sequencePackedEq
                      rw [PrefixValues.fullValue_completeValue_eq] at sequencePackedEq
                      have sequencePriorLayout :
                          sequenceWaiting.raw.production.rhs.take
                              sequenceWaiting.raw.dot.val = [
                            .nonterminal
                              (.aux expressionStatementExpressionAtomSite.site)] := by
                        let index := sequenceWaiting.raw.dot.val
                        have indexOne : index = 1 := sequenceWaitingDot
                        calc
                          _ = (ProductionId.seq
                              expressionStatementRootSequenceSite).rhs.take
                                index := congrArg
                            (fun production : ProductionId =>
                              production.rhs.take index)
                            sequenceWaitingProduction
                          _ = (ProductionId.seq
                              expressionStatementRootSequenceSite).rhs.take 1 := by
                            rw [indexOne]
                          _ = _ := by
                            simp [ProductionId.rhs_seq,
                              expressionStatementRootSequenceSite_children]
                      generalize canonicalEq : GrammarSymbolValues.transport
                          sequencePriorLayout sequencePriorValues =
                            canonicalPrior
                      rcases canonicalPrior with ⟨firstValue, ⟨⟩⟩
                      have sequencePriorRecover : GrammarSymbolValues.transport
                          sequencePriorLayout.symm (firstValue, ()) =
                            sequencePriorValues := by
                        rw [← canonicalEq,
                          GrammarSymbolValues.transport_trans]
                        exact GrammarSymbolValues.transport_self _ _
                      rw [← sequencePriorRecover] at sequencePackedEq
                      have sequenceTargetLayout :
                          expressionStatementRootSequenceSite.children.map
                              (fun child =>
                                GrammarSymbol.nonterminal (.aux child)) = [
                            .nonterminal
                              (.aux expressionStatementExpressionAtomSite.site),
                            .nonterminal optionalItem.raw.production.lhs] := by
                        rw [expressionStatementRootSequenceSite_children]
                        simp only [List.map]
                        rw [optionalLhs]
                      have sequenceTupleEq :=
                        GrammarSymbolValues.transport_append_pair_to_local
                          sequencePriorLayout
                          ((prefix_complete_layout sequenceWaiting.raw
                            optionalItem.raw sequence.raw optionalWitness.next
                            optionalWitness.advance).trans
                            (prefix_full_layout sequence.raw
                              sequenceComplete))
                          (ProductionId.rhs_seq
                            expressionStatementRootSequenceSite)
                          sequenceTargetLayout firstValue optionalValue
                      simp only [SequenceSite.pack,
                        GrammarSymbolValues.view] at sequencePackedEq
                      conv at sequencePackedEq in
                          (GrammarSymbolValues.transport _ _) =>
                        rw [sequenceTupleEq]
                      rw [sequencePackedEq] at rootInputEq
                      have rootSymbolLayoutEq : rootSymbolLayout = rfl :=
                        Subsingleton.elim _ _
                      rw [rootSymbolLayoutEq] at rootInputEq
                      have rootSiteEq :
                          expressionStatementRootSequenceSite.site =
                            GrammarSite.root .expressionStatement := rfl
                      have rootExpressionLayout :
                          EbnfExpr.sequence
                              (expressionStatementRootSequenceSite.children.map
                                GrammarSite.expression) =
                            m2cV1.rhs .expressionStatement := by
                        exact
                          expressionStatementRootSequenceSite.expression_eq_sequence.symm.trans
                            ((congrArg GrammarSite.expression rootSiteEq).trans
                              (GrammarSite.root_expression
                                .expressionStatement))
                      let rawSequenceValue := EbnfValue.sequence
                        (expressionStatementRootSequenceSite.children.map
                          GrammarSite.expression)
                        (EbnfValues.ofAuxiliaries
                          expressionStatementRootSequenceSite.children
                          (GrammarSymbolValues.transport
                            sequenceTargetLayout.symm
                            (firstValue, (optionalValue, ()))))
                      have rootCanonicalEq := root_sequenceTransport_eq_local
                        .expressionStatement
                        expressionStatementRootSequenceSite rootSiteEq
                        rootExpressionLayout rawSequenceValue
                      have parsedInputEq : EbnfValue.transport
                            rootExpressionLayout rawSequenceValue =
                          RuleReduction.inputValue
                            (RuleReduction.expressionStatementTerminal
                            origin finish terminalExpression
                              terminalWitness) :=
                        rootCanonicalEq.symm.trans rootInputEq
                      have childrenExpressionLayout :
                          expressionStatementRootSequenceSite.children.map
                              GrammarSite.expression = [
                            .atom (.nonterminal .expression),
                            .optional (.atom
                              (.terminal (.symbol .semicolon)))] := by
                        rw [expressionStatementRootSequenceSite_children]
                        simp only [List.map]
                        rw [expressionStatementExpressionAtomSite_expression,
                          expressionStatementOptionalSite_expression]
                      have parsedCanonical : EbnfValue.transport
                            (congrArg EbnfExpr.sequence
                              childrenExpressionLayout) rawSequenceValue =
                          RuleReduction.inputValue
                            (RuleReduction.expressionStatementTerminal
                              origin finish terminalExpression
                                terminalWitness) := by
                        have rootExpressionLayoutEq : rootExpressionLayout =
                            congrArg EbnfExpr.sequence
                              childrenExpressionLayout :=
                          Subsingleton.elim _ _
                        rw [rootExpressionLayoutEq] at parsedInputEq
                        exact parsedInputEq
                      have viewedEq := congrArg
                        (fun input => EbnfValue.optionalView
                          (.atom (.terminal (.symbol .semicolon)))
                          (EbnfValue.sequence2View
                            (.atom (.nonterminal .expression))
                            (.optional (.atom
                              (.terminal (.symbol .semicolon)))) input).2)
                        parsedCanonical
                      have leftView :=
                        optionalView_sequence_ofAuxiliary_pair_eq_local
                          expressionStatementRootSequenceSite_children
                          expressionStatementExpressionAtomSite_expression
                          expressionStatementOptionalSite_expression
                          sequenceTargetLayout childrenExpressionLayout
                          firstValue optionalValue
                      have rightView : EbnfValue.optionalView
                            (.atom (.terminal (.symbol .semicolon)))
                            (EbnfValue.sequence2View
                              (.atom (.nonterminal .expression))
                              (.optional (.atom
                                (.terminal (.symbol .semicolon))))
                              (RuleReduction.inputValue
                                (RuleReduction.expressionStatementTerminal
                                  origin finish terminalExpression
                                    terminalWitness))).2 = none := by
                        change EbnfValue.optionalView
                          (.atom (.terminal (.symbol .semicolon)))
                          (EbnfValue.sequence2View
                            (.atom (.nonterminal .expression))
                            (.optional (.atom
                              (.terminal (.symbol .semicolon))))
                            (EbnfValue.sequence [
                              .atom (.nonterminal .expression),
                              .optional (.atom
                                (.terminal (.symbol .semicolon)))]
                              (EbnfValues.cons _ _
                                (EbnfValue.ruleAtom .expression
                                  terminalExpression)
                                (EbnfValues.cons _ _
                                  (EbnfValue.optional _ none)
                                  EbnfValues.nil)))).2 = none
                        rw [sequence2View_pair_second_local]
                        simp [EbnfValue.optionalView, EbnfValue.optional]
                      have viewedRight : EbnfValue.optionalView
                            (.atom (.terminal (.symbol .semicolon)))
                            (EbnfValue.sequence2View
                              (.atom (.nonterminal .expression))
                              (.optional (.atom
                                (.terminal (.symbol .semicolon))))
                              (EbnfValue.transport
                                (congrArg EbnfExpr.sequence
                                  childrenExpressionLayout)
                                rawSequenceValue)).2 = none :=
                        viewedEq.trans rightView
                      have optionalViewNone : EbnfValue.optionalView
                            (.atom (.terminal (.symbol .semicolon)))
                            (EbnfValue.atShape
                              expressionStatementOptionalSite_expression
                              optionalValue) = none :=
                        leftView.symm.trans viewedRight
                      cases optionalReduction with
                      | reduce _ optionalValues _ optionalReached
                          optionalComplete optionalCoherent optionalAction =>
                          have optionalPackedEq : optionalValue =
                              OptionalSite.pack
                                expressionStatementOptionalSite optionalBranch
                                (PrefixValues.fullValue optionalItem
                                  optionalComplete optionalValues) := by
                            have exact :=
                              actionReduces_eleven_shapes_exact.mp optionalAction
                            simpa [optionalItem] using exact
                          rw [optionalPackedEq] at optionalViewNone
                          cases optionalBranch with
                          | some =>
                              obtain ⟨presentValue, present⟩ :=
                                optionalView_atShape_pack_some_present
                                  expressionStatementOptionalSite
                                  expressionStatementOptionalSite_expression
                                  (PrefixValues.fullValue optionalItem
                                    optionalComplete optionalValues)
                              rw [present] at optionalViewNone
                              cases optionalViewNone
                          | none =>
                              have enabled :=
                                optionalReached.enabledProductionInstance
                              have member :
                                  (.G08_terminalExpression, .positive) ∈
                                    guardOf optionalItem.raw.production := by
                                simp [optionalItem, guardOf,
                                  expressionStatementOptionalSite,
                                  GrammarSite.isAt]
                              have rootWaitingContext :
                                  rootWaiting.context = context := by
                                exact rootEdge.1.2.2.symm
                              have sequenceContextEq :
                                  sequence.context = context := by
                                calc
                                  _ = descendContext rootWaiting
                                      sequence.raw.production := rootEdge.1.2.1
                                  _ = rootWaiting.context := by
                                    simp [descendContext,
                                      rootWaitingProduction,
                                      sequenceProduction]
                                  _ = context := rootWaitingContext
                              have sequenceWaitingContext :
                                  sequenceWaiting.context = context := by
                                exact optionalEdge.1.2.2.symm.trans
                                  sequenceContextEq
                              have optionalContextEq :
                                  optionalItem.context = context := by
                                calc
                                  _ = descendContext sequenceWaiting
                                      optionalItem.raw.production :=
                                    optionalEdge.1.2.1
                                  _ = sequenceWaiting.context := by
                                    simp [descendContext,
                                      sequenceWaitingProduction, optionalItem,
                                      ProductionId.lhs,
                                      expressionStatementRootSequenceSite_not_body,
                                      expressionStatementRootSequenceSite_not_matchArm]
                                  _ = context := sequenceWaitingContext
                              have inheritedContext :
                                  optionalItem.context =
                                      .bracedBody regionStart ∨
                                    optionalItem.context =
                                      .armBody regionStart := by
                                rcases regionContext with regionContext |
                                    regionContext
                                · exact Or.inl
                                    (optionalContextEq.trans regionContext)
                                · exact Or.inr
                                    (optionalContextEq.trans regionContext)
                              have nearest :=
                                enabledG08Positive_nearestStatementRegion
                                  ({
                                    production := optionalItem.raw.production
                                    origin := optionalItem.raw.origin
                                    context := optionalItem.context
                                  } : ProductionInstanceKey tokens)
                                  regionStart inheritedContext enabled member
                              have optionalZero :
                                  optionalItem.raw.dot.val = 0 := by
                                calc
                                  _ = optionalItem.raw.production.rhs.length :=
                                    optionalComplete
                                  _ = 0 := by
                                    simp [optionalItem, ProductionId.rhs]
                              have optionalOriginCurrent :
                                  optionalItem.raw.origin =
                                    optionalItem.raw.current :=
                                contextualReach_zero_origin_eq_current
                                  optionalReached optionalZero
                              have optionalCurrentFinish :
                                  optionalItem.raw.current = finish := by
                                have sameCurrent := optionalWitness.advance.2.2.2
                                change sequence.raw.current =
                                  optionalItem.raw.current at sameCurrent
                                have sequenceFinish := rootWitness.advance.2.2.2
                                change finish = sequence.raw.current at sequenceFinish
                                exact sameCurrent.symm.trans sequenceFinish.symm
                              rw [optionalOriginCurrent, optionalCurrentFinish]
                                at nearest
                              exact nearest

/-- Two raw symbols immediately preceding the same boundary are identical. -/
private theorem immediatelyAfterSymbol_symbols_eq_local
    {file : WorkspaceFile} {tokens : List Token}
    {leftSymbol rightSymbol : Symbol}
    {leftCursor rightCursor after : Boundary tokens}
    (leftAfter : ImmediatelyAfterSymbol file tokens leftSymbol
      leftCursor after)
    (rightAfter : ImmediatelyAfterSymbol file tokens rightSymbol
      rightCursor after) :
    leftSymbol = rightSymbol := by
  rcases leftAfter with
    ⟨leftTerminal, leftToken, leftBefore, leftSuccessor,
      leftAt, leftPayload⟩
  rcases rightAfter with
    ⟨rightTerminal, rightToken, rightBefore, rightSuccessor,
      rightAt, rightPayload⟩
  have terminalEq : leftTerminal = rightTerminal := by
    apply Fin.ext
    have successorEq : leftTerminal.afterBoundary =
        rightTerminal.afterBoundary :=
      leftSuccessor.trans rightSuccessor.symm
    have values := congrArg
      (fun boundary : Boundary tokens => boundary.val) successorEq
    change leftTerminal.val + 1 = rightTerminal.val + 1 at values
    omega
  subst rightTerminal
  have streamEq := (TerminalAt.functional leftAt rightAt).1
  have tokenEq : leftToken = rightToken := by
    exact TerminalStreamValue.retained.inj streamEq
  have payloadEq : TokenKind.symbol leftSymbol =
      TokenKind.symbol rightSymbol :=
    leftPayload.symm.trans
      ((congrArg Located.payload tokenEq).trans rightPayload)
  exact TokenKind.symbol.inj payloadEq

/-- A braced context start rules out the match-arm alternative in the shared
nearest-statement-region predicate. -/
private theorem nearestStatementRegion_braced_local
    {file : WorkspaceFile} {tokens : List Token}
    {regionStart regionEnd : Boundary tokens}
    (afterOpen : ∃ openCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .leftBrace openCursor regionStart)
    (nearest : NearestStatementRegion file tokens regionStart regionEnd) :
    ∃ openCursor : Boundary tokens,
      MatchingDelimiter tokens openCursor regionEnd
        .leftBrace .rightBrace := by
  rcases nearest with braced | arm
  · rcases braced with ⟨openCursor, openAfter, matching⟩
    exact ⟨openCursor, matching⟩
  · rcases afterOpen with ⟨openCursor, openAfter⟩
    rcases arm with
      ⟨arrowCursor, frameOpen, frameClose, arrowAfter, frame, next⟩
    have impossible : Symbol.leftBrace = Symbol.fatArrow :=
      immediatelyAfterSymbol_symbols_eq_local openAfter arrowAfter
    cases impossible

/-- A match-arm context start rules out the braced-body alternative in the
shared nearest-statement-region predicate. -/
private theorem nearestStatementRegion_arm_local
    {file : WorkspaceFile} {tokens : List Token}
    {regionStart regionEnd : Boundary tokens}
    (afterArrow : ∃ arrowCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor regionStart)
    (nearest : NearestStatementRegion file tokens regionStart regionEnd) :
    ∃ arrowCursor openCursor closeCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor regionStart ∧
      InnermostContainingBraceFrame tokens arrowCursor openCursor closeCursor ∧
      NextArmOrClose file tokens regionStart closeCursor regionEnd := by
  rcases afterArrow with ⟨arrowCursor, arrowAfter⟩
  rcases nearest with braced | arm
  · rcases braced with ⟨openCursor, openAfter, matching⟩
    have impossible : Symbol.leftBrace = Symbol.fatArrow :=
      immediatelyAfterSymbol_symbols_eq_local openAfter arrowAfter
    cases impossible
  · rcases arm with
      ⟨selectedArrow, openCursor, closeCursor, selectedAfter,
        frame, next⟩
    have arrowEq : selectedArrow = arrowCursor := by
      rcases selectedAfter with
        ⟨leftCursor, leftToken, leftBefore, leftAfter, leftAt, leftPayload⟩
      rcases arrowAfter with
        ⟨rightCursor, rightToken, rightBefore, rightAfter, rightAt,
          rightPayload⟩
      apply Fin.ext
      have afterEq : leftCursor.afterBoundary =
          rightCursor.afterBoundary := leftAfter.trans rightAfter.symm
      have afterVal :=
        congrArg (fun boundary : Boundary tokens => boundary.val) afterEq
      have leftVal := congrArg (fun boundary : Boundary tokens => boundary.val)
        leftBefore
      have rightVal := congrArg
        (fun boundary : Boundary tokens => boundary.val) rightBefore
      change leftCursor.val + 1 = rightCursor.val + 1 at afterVal
      change leftCursor.val = selectedArrow.val at leftVal
      change rightCursor.val = arrowCursor.val at rightVal
      omega
    subst selectedArrow
    exact ⟨arrowCursor, openCursor, closeCursor, arrowAfter, frame, next⟩

/-- The raw right brace of a matching frame cannot simultaneously be a
source-level pipe token at the same boundary. -/
private theorem matchingRightBrace_excludes_pipeAtBoundary_local
    {file : WorkspaceFile} {tokens : List Token}
    {openCursor closeCursor : Boundary tokens}
    (matching : MatchingDelimiter tokens openCursor closeCursor
      .leftBrace .rightBrace)
    (pipeAt : SymbolAtBoundary file tokens closeCursor .pipe) : False := by
  change Symbol.rightBrace = Symbol.rightBrace ∧
      ∃ interiorStart : Boundary tokens,
        (∃ terminalCursor : TerminalCursor tokens, ∃ token : Token,
          terminalCursor.beforeBoundary = openCursor ∧
          terminalCursor.afterBoundary = interiorStart ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol .leftBrace) ∧
        (∃ terminalCursor : TerminalCursor tokens, ∃ token : Token,
          terminalCursor.beforeBoundary = closeCursor ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol .rightBrace) ∧
        ProtectedDelimiterRun tokens
          { head := .rightBrace, tail := [] }
          interiorStart closeCursor
          { head := .rightBrace, tail := [] } at matching
  rcases matching with
    ⟨_, interiorStart, openEvidence, closeEvidence, protectedRun⟩
  rcases closeEvidence with
    ⟨closeTerminal, closeToken, closeBefore, closeLookup, closePayload⟩
  rcases pipeAt with
    ⟨pipeTerminal, pipeToken, pipeBefore, pipeAt, pipePayload⟩
  cases pipeAt with
  | retained _ inRange pipeLookup valid =>
      have cursorEq : closeTerminal = pipeTerminal := by
        apply Fin.ext
        exact congrArg (fun boundary : Boundary tokens => boundary.val)
          (closeBefore.trans pipeBefore.symm)
      subst pipeTerminal
      have tokenEq : closeToken = pipeToken :=
        Option.some.inj (closeLookup.symm.trans pipeLookup)
      subst pipeToken
      rw [closePayload] at pipePayload
      cases pipePayload

/-- Coherent recognition of a complete statement preserves delimiter depth
over its exact chart interval. -/
private theorem coherentStatement_sameDelimiterDepth_local
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {statement : Statement}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
      statement) :
    SameDelimiterDepth tokens origin finish := by
  cases coherent with
  | reduce _ _ _ reached complete coherentPrefix action =>
      have recognized : UnguardedRecognizes file tokens (.rule .statement)
          origin finish := by
        exact ⟨(CanonicalCompleteRootItem tokens .statement origin finish
          context).raw, reached.toUnguarded, complete, rfl, rfl, rfl⟩
      exact recognized.ebnf.sourceRule_sameDelimiterDepth (by decide)

/-- Every coherent complete statement root consumes at least one retained
token. -/
private theorem coherentStatement_progress_local
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {statement : Statement}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
      statement) :
    origin.val < finish.val := by
  cases coherent with
  | reduce _ _ _ reached complete coherentPrefix action =>
      exact completeRoot_progress rfl reached complete (by decide)

/-- A same-depth interval cannot advance from the raw right brace that closes
its surrounding braced region. -/
private theorem matchingRightBrace_excludes_sameDepth_later_local
    {tokens : List Token} {openCursor split finish : Boundary tokens}
    (matching : MatchingDelimiter tokens openCursor split
      .leftBrace .rightBrace)
    (depth : SameDelimiterDepth tokens split finish)
    (later : split.val < finish.val) : False := by
  change Symbol.rightBrace = Symbol.rightBrace ∧
      ∃ interiorStart : Boundary tokens,
        (∃ terminalCursor : TerminalCursor tokens, ∃ token : Token,
          terminalCursor.beforeBoundary = openCursor ∧
          terminalCursor.afterBoundary = interiorStart ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol .leftBrace) ∧
        (∃ terminalCursor : TerminalCursor tokens, ∃ token : Token,
          terminalCursor.beforeBoundary = split ∧
          tokens[terminalCursor.val]? = some token ∧
          token.payload = .symbol .rightBrace) ∧
        ProtectedDelimiterRun tokens
          { head := .rightBrace, tail := [] }
          interiorStart split
          { head := .rightBrace, tail := [] } at matching
  rcases matching with
    ⟨_, interiorStart, openEvidence, closeEvidence, protectedRun⟩
  rcases closeEvidence with
    ⟨closeCursor, closeToken, closeAt, closeLookup, closePayload⟩
  cases depth with
  | nil stack cursor => omega
  | cons before after final cursor start endCursor token atStart lookup step rest =>
      have cursorEq : cursor = closeCursor := by
        apply Fin.ext
        exact congrArg (fun boundary : Boundary tokens => boundary.val)
          (atStart.trans closeAt.symm)
      subst closeCursor
      have tokenEq : token = closeToken :=
        Option.some.inj (lookup.symm.trans closeLookup)
      subst closeToken
      rw [closePayload] at step
      simp [DelimiterStep] at step

/-- A statement is valid before the end of a statement list exactly when it
is not a semicolon-free expression statement. -/
def Statement.ValidBeforeListEnd (statement : Statement) : Prop :=
  match statement with
  | ⟨_, .expression _ none⟩ => False
  | _ => True

/-- Every nonfinal element of a statement list satisfies the grammar's
mandatory-terminator policy. The final element remains unrestricted. -/
def StatementListPositionCoherent : List Statement → Prop
  | [] => True
  | [_] => True
  | head :: second :: rest =>
      head.ValidBeforeListEnd ∧
        StatementListPositionCoherent (second :: rest)

/-- Away from the list end, the strict and final-position statement visitors
agree for every position-valid statement. -/
theorem statementTokenPlan?_false_eq_true_of_validBeforeListEnd
    (statement : Statement) (valid : statement.ValidBeforeListEnd) :
    statementTokenPlan? false statement = statementTokenPlan? true statement := by
  rcases statement with ⟨span, payload⟩
  cases payload <;> try simp [statementTokenPlan?]
  case expression expression terminator =>
    cases terminator with
    | none => contradiction
    | some semicolon => simp [statementTokenPlan?]
  case «return» value terminator =>
    cases value <;> simp [statementTokenPlan?]
  case «match» scrutinees arms terminator =>
    cases terminator <;> simp [statementTokenPlan?]

/-- Once the G08 positional invariant is known, the positional statement-list
visitor equals the unrestricted map used by the repeated grammar input. -/
theorem statementTokenPlans?_eq_mapM_of_positionCoherent
    (statements : List Statement)
    (positioned : StatementListPositionCoherent statements) :
    statementTokenPlans? statements =
      statements.mapM (statementTokenPlan? true) := by
  induction statements with
  | nil => simp [statementTokenPlans?]
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => simp [statementTokenPlans?]
      | cons second rest =>
          change head.ValidBeforeListEnd ∧
            StatementListPositionCoherent (second :: rest) at positioned
          simp only [statementTokenPlans?, List.mapM_cons]
          rw [statementTokenPlan?_false_eq_true_of_validBeforeListEnd
            head positioned.1]
          rw [inductionHypothesis positioned.2]
          simp only [List.mapM_cons]

/-- Successful unrestricted repeated-statement planning transfers to the
positional body visitor under the shared statement-list invariant. -/
theorem statementTokenPlans?_of_mapM_allowTerminal
    (statements : List Statement) (plans : List TokenPlan)
    (positioned : StatementListPositionCoherent statements)
    (success : statements.mapM (statementTokenPlan? true) = some plans) :
    statementTokenPlans? statements = some plans := by
  rw [statementTokenPlans?_eq_mapM_of_positionCoherent statements positioned]
  exact success
/-- Invert the single auxiliary completion of a source-rule root whose EBNF
right-hand side is a sequence. The returned sequence reduction occupies the
same interval and context, and its packed value is exactly the root input. -/
theorem coherentRootSequence_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId} (site : SequenceSite)
    (siteRoot : site.site = GrammarSite.root rule)
    (sequenceLayout : EbnfExpr.sequence
      (site.children.map GrammarSite.expression) = m2cV1.rhs rule)
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens rule origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context)
        priorValues)
    (input : EbnfValue file tokens (m2cV1.rhs rule))
    (inputEq : RootAction.unpack rule
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens rule origin finish context)
          complete priorValues) = input) :
    ∃ (dot : Fin ((ProductionId.seq site).rhs.length + 1))
      (sequenceValue : NonterminalValue file tokens
        (ProductionId.seq site).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .seq site
          dot := dot
          origin := origin
          current := finish
        }
        context := context
      } sequenceValue ∧
      EbnfValue.transport sequenceLayout
        (EbnfValue.atShape site.expression_eq_sequence sequenceValue) =
          input := by
  cases coherentPrefix with
  | zero _ _ zero =>
      change 1 = 0 at zero
      omega
  | scan before after cursor priorValues scanWitness edge prior =>
      have productionEq : before.raw.production = .root rule :=
        scanWitness.advance.1.symm
      have dotEq : before.raw.dot.val = 0 := by
        have advanced := scanWitness.advance.2.1
        change 1 = before.raw.dot.val + 1 at advanced
        omega
      have impossible : some (GrammarSymbol.terminal scanWitness.terminal) =
          some (GrammarSymbol.nonterminal
            (.aux (GrammarSite.root rule))) := by
        let index := before.raw.dot.val
        calc
          _ = before.raw.production.rhs[index]? := scanWitness.next.2.symm
          _ = (ProductionId.root rule).rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) productionEq
          _ = (ProductionId.root rule).rhs[0]? := by
            have indexZero : index = 0 := dotEq
            rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting sequence _ rootShared rootPriorValues sequenceValue
      rootWitness rootEdge rootPrior sequenceReduction =>
      have rootWaitingProduction : rootWaiting.raw.production = .root rule :=
        rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1
        change 1 = rootWaiting.raw.dot.val + 1 at advanced
        omega
      have sequenceLhs : sequence.raw.production.lhs =
          .aux (GrammarSite.root rule) := by
        have selected : some (GrammarSymbol.nonterminal
              sequence.raw.production.lhs) =
            some (GrammarSymbol.nonterminal
              (.aux (GrammarSite.root rule))) := by
          let index := rootWaiting.raw.dot.val
          calc
            _ = rootWaiting.raw.production.rhs[index]? :=
              rootWitness.next.2.symm
            _ = (ProductionId.root rule).rhs[index]? :=
              congrArg (fun production : ProductionId =>
                production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root rule).rhs[0]? := by
              have indexZero : index = 0 := rootWaitingDot
              rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      have sequenceSiteLhs : sequence.raw.production.lhs = .aux site.site :=
        sequenceLhs.trans (congrArg NonterminalSymbol.aux siteRoot.symm)
      have sequenceProduction : sequence.raw.production = .seq site :=
        production_eq_sequence_of_lhs site sequence.raw.production
          sequenceSiteLhs
      have rootWaitingOriginCurrent : rootWaiting.raw.origin =
          rootWaiting.raw.current :=
        contextualReach_zero_origin_eq_current rootEdge.2.1 rootWaitingDot
      have sequenceOrigin : sequence.raw.origin = origin := by
        calc
          _ = rootShared := rootWitness.finishedAtShared
          _ = rootWaiting.raw.current := rootWitness.waitingAtShared.symm
          _ = rootWaiting.raw.origin := rootWaitingOriginCurrent.symm
          _ = origin := by
            simpa only [CanonicalCompleteRootItem] using
              rootWitness.advance.2.2.1.symm
      have sequenceCurrent : sequence.raw.current = finish := by
        simpa only [CanonicalCompleteRootItem] using
          rootWitness.advance.2.2.2.symm
      have sequenceContextEq : sequence.context = context := by
        calc
          _ = descendContext rootWaiting sequence.raw.production :=
            rootEdge.1.2.1
          _ = rootWaiting.context := by
            rw [sequenceProduction]
            simp [descendContext, rootWaitingProduction]
          _ = context := by
            simpa only [CanonicalCompleteRootItem] using rootEdge.1.2.2.symm
      have rootPriorLayout : rootWaiting.raw.production.rhs.take
            rootWaiting.raw.dot.val = [] := by
        let index := rootWaiting.raw.dot.val
        have dotZero : index = 0 := rootWaitingDot
        calc
          _ = (ProductionId.root rule).rhs.take index :=
            congrArg (fun production : ProductionId =>
              production.rhs.take index) rootWaitingProduction
          _ = (ProductionId.root rule).rhs.take 0 := by rw [dotZero]
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
      have rootSymbolLayout : GrammarSymbol.nonterminal
            sequence.raw.production.lhs =
          GrammarSymbol.nonterminal (.aux (GrammarSite.root rule)) :=
        congrArg GrammarSymbol.nonterminal sequenceLhs
      have rootTupleEq :=
        GrammarSymbolValues.transport_append_empty_single_to_local
          rootPriorLayout
          ((prefix_complete_layout rootWaiting.raw sequence.raw
            (CanonicalCompleteRootItem tokens rule origin finish context).raw
            rootWitness.next rootWitness.advance).trans
            (prefix_full_layout
              (CanonicalCompleteRootItem tokens rule origin finish context).raw
              complete))
          (ProductionId.rhs_root rule) rootSymbolLayout rootEmpty sequenceValue
      rw [RootAction.unpack_eq] at inputEq
      unfold GrammarSymbolValues.view at inputEq
      have rootHeadEq := congrArg Prod.fst rootTupleEq
      have rootHeadAtEq := congrArg
        (EbnfValue.atShape (GrammarSite.root_expression rule)) rootHeadEq
      have rootInputEq := rootHeadAtEq.symm.trans inputEq
      rcases sequence with
        ⟨⟨sequenceProductionId, sequenceDot, sequenceOriginValue,
          sequenceCurrentValue⟩, sequenceContextValue⟩
      simp only at sequenceProduction
      subst sequenceProductionId
      change sequenceOriginValue = origin at sequenceOrigin
      change sequenceCurrentValue = finish at sequenceCurrent
      change sequenceContextValue = context at sequenceContextEq
      subst sequenceOriginValue
      subst sequenceCurrentValue
      subst sequenceContextValue
      let canonicalSequence : ContextualItemKey tokens := {
        raw := {
          production := .seq site
          dot := sequenceDot
          origin := origin
          current := finish
        }
        context := context
      }
      change CoherentReduction file tokens memo correct final
        canonicalSequence sequenceValue at sequenceReduction
      have rootSymbolLayoutEq : rootSymbolLayout =
          congrArg GrammarSymbol.nonterminal
            (congrArg NonterminalSymbol.aux siteRoot) := by
        apply Subsingleton.elim
      rw [rootSymbolLayoutEq] at rootInputEq
      have canonicalInputEq := root_sequenceTransport_eq_local
        rule site siteRoot sequenceLayout
        (EbnfValue.atShape site.expression_eq_sequence sequenceValue)
      have restoredSequence : EbnfValue.ofShape site.expression_eq_sequence
            (EbnfValue.atShape site.expression_eq_sequence sequenceValue) =
          sequenceValue := by
        unfold EbnfValue.ofShape EbnfValue.atShape
        rw [EbnfValue.transport_trans]
        exact EbnfValue.transport_self _ _
      rw [restoredSequence] at canonicalInputEq
      have semanticEq : EbnfValue.transport sequenceLayout
            (EbnfValue.atShape site.expression_eq_sequence sequenceValue) =
          input := by
        exact canonicalInputEq.symm.trans rootInputEq
      exact ⟨sequenceDot, sequenceValue, sequenceReduction, semanticEq⟩

/-- Invert the single auxiliary completion of a source-rule root whose EBNF
right-hand side is an atom. -/
private theorem coherentRootAtom_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId} (site : AtomSite)
    (siteRoot : site.site = GrammarSite.root rule)
    (atomLayout : EbnfExpr.atom site.atom = m2cV1.rhs rule)
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens rule origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens rule origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context)
        priorValues)
    (input : EbnfValue file tokens (m2cV1.rhs rule))
    (inputEq : RootAction.unpack rule
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens rule origin finish context)
          complete priorValues) = input) :
    ∃ (dot : Fin ((ProductionId.atom site).rhs.length + 1))
      (atomValue : NonterminalValue file tokens
        (ProductionId.atom site).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .atom site
          dot := dot
          origin := origin
          current := finish
        }
        context := context
      } atomValue ∧
      EbnfValue.transport atomLayout
        (EbnfValue.atShape site.expression_eq_atom atomValue) = input := by
  cases coherentPrefix with
  | zero _ _ zero =>
      change 1 = 0 at zero
      omega
  | scan before after cursor priorValues scanWitness edge prior =>
      have productionEq : before.raw.production = .root rule :=
        scanWitness.advance.1.symm
      have dotEq : before.raw.dot.val = 0 := by
        have advanced := scanWitness.advance.2.1
        change 1 = before.raw.dot.val + 1 at advanced
        omega
      have impossible : some (GrammarSymbol.terminal scanWitness.terminal) =
          some (GrammarSymbol.nonterminal
            (.aux (GrammarSite.root rule))) := by
        let index := before.raw.dot.val
        calc
          _ = before.raw.production.rhs[index]? := scanWitness.next.2.symm
          _ = (ProductionId.root rule).rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) productionEq
          _ = (ProductionId.root rule).rhs[0]? := by
            have indexZero : index = 0 := dotEq
            rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting atomChild _ rootShared rootPriorValues atomValue
      rootWitness rootEdge rootPrior atomReduction =>
      have rootWaitingProduction : rootWaiting.raw.production = .root rule :=
        rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1
        change 1 = rootWaiting.raw.dot.val + 1 at advanced
        omega
      have atomLhs : atomChild.raw.production.lhs =
          .aux (GrammarSite.root rule) := by
        have selected : some (GrammarSymbol.nonterminal
              atomChild.raw.production.lhs) =
            some (GrammarSymbol.nonterminal
              (.aux (GrammarSite.root rule))) := by
          let index := rootWaiting.raw.dot.val
          calc
            _ = rootWaiting.raw.production.rhs[index]? :=
              rootWitness.next.2.symm
            _ = (ProductionId.root rule).rhs[index]? :=
              congrArg (fun production : ProductionId =>
                production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root rule).rhs[0]? := by
              have indexZero : index = 0 := rootWaitingDot
              rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      have atomSiteLhs : atomChild.raw.production.lhs = .aux site.site :=
        atomLhs.trans (congrArg NonterminalSymbol.aux siteRoot.symm)
      have atomProduction : atomChild.raw.production = .atom site :=
        production_atom_of_lhs_local site atomChild.raw.production atomSiteLhs
      have rootWaitingOriginCurrent : rootWaiting.raw.origin =
          rootWaiting.raw.current :=
        contextualReach_zero_origin_eq_current rootEdge.2.1 rootWaitingDot
      have atomOrigin : atomChild.raw.origin = origin := by
        calc
          _ = rootShared := rootWitness.finishedAtShared
          _ = rootWaiting.raw.current := rootWitness.waitingAtShared.symm
          _ = rootWaiting.raw.origin := rootWaitingOriginCurrent.symm
          _ = origin := by
            simpa only [CanonicalCompleteRootItem] using
              rootWitness.advance.2.2.1.symm
      have atomCurrent : atomChild.raw.current = finish := by
        simpa only [CanonicalCompleteRootItem] using
          rootWitness.advance.2.2.2.symm
      have atomContextEq : atomChild.context = context := by
        calc
          _ = descendContext rootWaiting atomChild.raw.production :=
            rootEdge.1.2.1
          _ = rootWaiting.context := by
            rw [atomProduction]
            simp [descendContext, rootWaitingProduction]
          _ = context := by
            simpa only [CanonicalCompleteRootItem] using
              rootEdge.1.2.2.symm
      have rootPriorLayout : rootWaiting.raw.production.rhs.take
            rootWaiting.raw.dot.val = [] := by
        let index := rootWaiting.raw.dot.val
        have dotZero : index = 0 := rootWaitingDot
        calc
          _ = (ProductionId.root rule).rhs.take index :=
            congrArg (fun production : ProductionId =>
              production.rhs.take index) rootWaitingProduction
          _ = (ProductionId.root rule).rhs.take 0 := by rw [dotZero]
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
      have rootSymbolLayout : GrammarSymbol.nonterminal
            atomChild.raw.production.lhs =
          GrammarSymbol.nonterminal (.aux (GrammarSite.root rule)) :=
        congrArg GrammarSymbol.nonterminal atomLhs
      have rootTupleEq :=
        GrammarSymbolValues.transport_append_empty_single_to_local
          rootPriorLayout
          ((prefix_complete_layout rootWaiting.raw atomChild.raw
            (CanonicalCompleteRootItem tokens rule origin finish context).raw
            rootWitness.next rootWitness.advance).trans
            (prefix_full_layout
              (CanonicalCompleteRootItem tokens rule origin finish context).raw
              complete))
          (ProductionId.rhs_root rule) rootSymbolLayout rootEmpty atomValue
      rw [RootAction.unpack_eq] at inputEq
      unfold GrammarSymbolValues.view at inputEq
      have rootHeadEq := congrArg Prod.fst rootTupleEq
      have rootHeadAtEq := congrArg
        (EbnfValue.atShape (GrammarSite.root_expression rule)) rootHeadEq
      have rootInputEq := rootHeadAtEq.symm.trans inputEq
      rcases atomChild with
        ⟨⟨atomProductionId, atomDot, atomOriginValue,
          atomCurrentValue⟩, atomContextValue⟩
      simp only at atomProduction
      subst atomProductionId
      change atomOriginValue = origin at atomOrigin
      change atomCurrentValue = finish at atomCurrent
      change atomContextValue = context at atomContextEq
      subst atomOriginValue
      subst atomCurrentValue
      subst atomContextValue
      let canonicalAtom : ContextualItemKey tokens := {
        raw := {
          production := .atom site
          dot := atomDot
          origin := origin
          current := finish
        }
        context := context
      }
      change CoherentReduction file tokens memo correct final
        canonicalAtom atomValue at atomReduction
      have rootSymbolLayoutEq : rootSymbolLayout =
          congrArg GrammarSymbol.nonterminal
            (congrArg NonterminalSymbol.aux siteRoot) := by
        apply Subsingleton.elim
      rw [rootSymbolLayoutEq] at rootInputEq
      have canonicalInputEq := root_atomTransport_eq_local
        rule site siteRoot atomLayout
        (EbnfValue.atShape site.expression_eq_atom atomValue)
      have restoredAtom : EbnfValue.ofShape site.expression_eq_atom
            (EbnfValue.atShape site.expression_eq_atom atomValue) =
          atomValue := by
        unfold EbnfValue.ofShape EbnfValue.atShape
        rw [EbnfValue.transport_trans]
        exact EbnfValue.transport_self _ _
      rw [restoredAtom] at canonicalInputEq
      have semanticEq : EbnfValue.transport atomLayout
            (EbnfValue.atShape site.expression_eq_atom atomValue) =
          input :=
        canonicalInputEq.symm.trans rootInputEq
      exact ⟨atomDot, atomValue, atomReduction, semanticEq⟩

/-- Invert the root of the source `statement` choice, retaining its selected
choice branch, exact interval/context, and semantic input. -/
theorem coherentStatementChoice_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .statement origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .statement origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
        priorValues)
    (input : EbnfValue file tokens (m2cV1.rhs .statement))
    (inputEq : RootAction.unpack .statement
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .statement origin finish context)
          complete priorValues) = input) :
    ∃ (branch : Fin statementRootChoiceSite.branchCount)
      (dot : Fin
        ((ProductionId.choice statementRootChoiceSite branch).rhs.length + 1))
      (choiceValue : NonterminalValue file tokens
        (ProductionId.choice statementRootChoiceSite branch).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .choice statementRootChoiceSite branch
          dot := dot
          origin := origin
          current := finish
        }
        context := context
      } choiceValue ∧
      EbnfValue.transport statementRootChoiceLayout
        (EbnfValue.atShape statementRootChoiceSite.expression_eq_choice
          choiceValue) = input := by
  cases coherentPrefix with
  | zero _ _ zero =>
      change 1 = 0 at zero
      omega
  | scan before after cursor rootPriorValues scanWitness edge prior =>
      have rootProduction : before.raw.production = .root .statement :=
        scanWitness.advance.1.symm
      have rootDot : before.raw.dot.val = 0 := by
        have advanced := scanWitness.advance.2.1
        change 1 = before.raw.dot.val + 1 at advanced
        omega
      have impossible : some (GrammarSymbol.terminal scanWitness.terminal) =
          some (GrammarSymbol.nonterminal
            (.aux (GrammarSite.root .statement))) := by
        let index := before.raw.dot.val
        calc
          _ = before.raw.production.rhs[index]? := scanWitness.next.2.symm
          _ = (ProductionId.root .statement).rhs[index]? :=
            congrArg (fun production : ProductionId =>
              production.rhs[index]?) rootProduction
          _ = (ProductionId.root .statement).rhs[0]? := by
            have indexZero : index = 0 := rootDot
            rw [indexZero]
          _ = _ := by simp [ProductionId.rhs]
      exact GrammarSymbol.noConfusion (Option.some.inj impossible)
  | complete rootWaiting choiceChild _ rootShared rootPriorValues choiceValue
      rootWitness rootEdge rootPrior choiceReduction =>
      have rootWaitingProduction : rootWaiting.raw.production =
          .root .statement := rootWitness.advance.1.symm
      have rootWaitingDot : rootWaiting.raw.dot.val = 0 := by
        have advanced := rootWitness.advance.2.1
        change 1 = rootWaiting.raw.dot.val + 1 at advanced
        omega
      have choiceLhs : choiceChild.raw.production.lhs =
          .aux (GrammarSite.root .statement) := by
        have selected : some (GrammarSymbol.nonterminal
              choiceChild.raw.production.lhs) =
            some (GrammarSymbol.nonterminal
              (.aux (GrammarSite.root .statement))) := by
          let index := rootWaiting.raw.dot.val
          calc
            _ = rootWaiting.raw.production.rhs[index]? :=
              rootWitness.next.2.symm
            _ = (ProductionId.root .statement).rhs[index]? :=
              congrArg (fun production : ProductionId =>
                production.rhs[index]?) rootWaitingProduction
            _ = (ProductionId.root .statement).rhs[0]? := by
              have indexZero : index = 0 := rootWaitingDot
              rw [indexZero]
            _ = _ := by simp [ProductionId.rhs]
        exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
      have choiceSiteLhs : choiceChild.raw.production.lhs =
          .aux statementRootChoiceSite.site := choiceLhs
      rcases production_choice_of_lhs_local statementRootChoiceSite
          choiceChild.raw.production choiceSiteLhs with
        ⟨branch, choiceProduction⟩
      have rootWaitingOriginCurrent : rootWaiting.raw.origin =
          rootWaiting.raw.current :=
        contextualReach_zero_origin_eq_current rootEdge.2.1 rootWaitingDot
      have choiceOrigin : choiceChild.raw.origin = origin := by
        calc
          _ = rootShared := rootWitness.finishedAtShared
          _ = rootWaiting.raw.current := rootWitness.waitingAtShared.symm
          _ = rootWaiting.raw.origin := rootWaitingOriginCurrent.symm
          _ = origin := by
            simpa only [CanonicalCompleteRootItem] using
              rootWitness.advance.2.2.1.symm
      have choiceCurrent : choiceChild.raw.current = finish := by
        simpa only [CanonicalCompleteRootItem] using
          rootWitness.advance.2.2.2.symm
      have choiceContext : choiceChild.context = context := by
        calc
          _ = descendContext rootWaiting choiceChild.raw.production :=
            rootEdge.1.2.1
          _ = rootWaiting.context := by
            rw [choiceProduction]
            simp [descendContext, rootWaitingProduction]
          _ = context := by
            simpa only [CanonicalCompleteRootItem] using rootEdge.1.2.2.symm
      have rootPriorLayout : rootWaiting.raw.production.rhs.take
            rootWaiting.raw.dot.val = [] := by
        let index := rootWaiting.raw.dot.val
        have dotZero : index = 0 := rootWaitingDot
        calc
          _ = (ProductionId.root .statement).rhs.take index :=
            congrArg (fun production : ProductionId =>
              production.rhs.take index) rootWaitingProduction
          _ = (ProductionId.root .statement).rhs.take 0 := by rw [dotZero]
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
      have rootSymbolLayout : GrammarSymbol.nonterminal
            choiceChild.raw.production.lhs =
          GrammarSymbol.nonterminal
            (.aux (GrammarSite.root .statement)) :=
        congrArg GrammarSymbol.nonterminal choiceLhs
      have rootTupleEq :=
        GrammarSymbolValues.transport_append_empty_single_to_local
          rootPriorLayout
          ((prefix_complete_layout rootWaiting.raw choiceChild.raw
            (CanonicalCompleteRootItem tokens .statement origin finish
              context).raw rootWitness.next rootWitness.advance).trans
            (prefix_full_layout
              (CanonicalCompleteRootItem tokens .statement origin finish
                context).raw complete))
          (ProductionId.rhs_root .statement) rootSymbolLayout rootEmpty
          choiceValue
      rw [RootAction.unpack_eq] at inputEq
      unfold GrammarSymbolValues.view at inputEq
      have rootHeadEq := congrArg Prod.fst rootTupleEq
      have rootHeadAtEq := congrArg
        (EbnfValue.atShape
          (GrammarSite.root_expression .statement)) rootHeadEq
      have rootInputEq := rootHeadAtEq.symm.trans inputEq
      rcases choiceChild with
        ⟨⟨choiceProductionId, choiceDot, choiceOriginValue,
          choiceCurrentValue⟩, choiceContextValue⟩
      simp only at choiceProduction
      subst choiceProductionId
      change choiceOriginValue = origin at choiceOrigin
      change choiceCurrentValue = finish at choiceCurrent
      change choiceContextValue = context at choiceContext
      subst choiceOriginValue
      subst choiceCurrentValue
      subst choiceContextValue
      let canonicalChoice : ContextualItemKey tokens := {
        raw := {
          production := .choice statementRootChoiceSite branch
          dot := choiceDot
          origin := origin
          current := finish
        }
        context := context
      }
      change CoherentReduction file tokens memo correct final
        canonicalChoice choiceValue at choiceReduction
      have rootSymbolLayoutEq : rootSymbolLayout = rfl :=
        Subsingleton.elim _ _
      rw [rootSymbolLayoutEq] at rootInputEq
      have canonicalInputEq := root_choiceTransport_eq_local
        .statement statementRootChoiceSite rfl statementRootChoiceLayout
        (EbnfValue.atShape statementRootChoiceSite.expression_eq_choice
          choiceValue)
      have restoredChoice : EbnfValue.ofShape
            statementRootChoiceSite.expression_eq_choice
            (EbnfValue.atShape
              statementRootChoiceSite.expression_eq_choice choiceValue) =
          choiceValue := by
        unfold EbnfValue.ofShape EbnfValue.atShape
        rw [EbnfValue.transport_trans]
        exact EbnfValue.transport_self _ _
      rw [restoredChoice] at canonicalInputEq
      have semanticEq : EbnfValue.transport statementRootChoiceLayout
            (EbnfValue.atShape
              statementRootChoiceSite.expression_eq_choice choiceValue) =
          input := canonicalInputEq.symm.trans rootInputEq
      exact ⟨branch, choiceDot, choiceValue, choiceReduction, semanticEq⟩

/-- Invert the sole nonterminal child of a coherent choice production when
the selected branch is a source-rule atom. -/
theorem coherentChoiceAtom_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (site : ChoiceSite) (branch : Fin site.branchCount)
    (atomSite : AtomSite)
    (branchSite : site.branch branch = atomSite.site)
    (dot : Fin ((ProductionId.choice site branch).rhs.length + 1))
    (origin finish : Boundary tokens) (context : GuardContext tokens)
    {output : NonterminalValue file tokens
      (ProductionId.choice site branch).lhs}
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .choice site branch
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) :
    ∃ (atomDot : Fin ((ProductionId.atom atomSite).rhs.length + 1))
      (atomValue : NonterminalValue file tokens
        (ProductionId.atom atomSite).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .atom atomSite
          dot := atomDot
          origin := origin
          current := finish
        }
        context := context
      } atomValue ∧
      EbnfValue.atShape site.expression_eq_choice output =
        EbnfValue.choice site.branchExpressions.toList
          ⟨site.branchListIndex branch,
            EbnfValue.transport
              ((congrArg GrammarSite.expression branchSite).symm.trans
                ((site.branch_expression branch).trans
                  (site.branch_get_toList branch).symm))
              atomValue⟩ := by
  let item : ContextualItemKey tokens := {
    raw := {
      production := .choice site branch
      dot := dot
      origin := origin
      current := finish
    }
    context := context
  }
  change CoherentReduction file tokens memo correct final item output at coherent
  cases coherent with
  | reduce _ priorValues _ reached complete coherentPrefix action =>
      have itemComplete : item.raw.dot.val = 1 := by
        calc
          _ = item.raw.production.rhs.length := complete
          _ = 1 := by simp [item, ProductionId.rhs]
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues witness edge prior =>
          have beforeProduction : before.raw.production =
              .choice site branch := by
            simpa [item] using witness.advance.1.symm
          have beforeZero : before.raw.dot.val = 0 := by
            have advanced := witness.advance.2.1
            omega
          have impossible : some (GrammarSymbol.terminal witness.terminal) =
              some (GrammarSymbol.nonterminal (.aux (site.branch branch))) := by
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                witness.next.2.symm
              _ = (ProductionId.choice site branch).rhs[0]? := by
                let index := before.raw.dot.val
                have indexZero : index = 0 := beforeZero
                calc
                  _ = (ProductionId.choice site branch).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexZero]
              _ = _ := by simp [ProductionId.rhs]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete waiting child after shared childPriorValues childValue
          witness edge prior childCoherent =>
          have waitingProduction : waiting.raw.production =
              .choice site branch := by
            simpa [item] using witness.advance.1.symm
          have waitingZero : waiting.raw.dot.val = 0 := by
            have advanced := witness.advance.2.1
            omega
          have childLhs : child.raw.production.lhs =
              .aux (site.branch branch) := by
            have selected : some (GrammarSymbol.nonterminal
                  child.raw.production.lhs) =
                some (GrammarSymbol.nonterminal
                  (.aux (site.branch branch))) := by
              calc
                _ = waiting.raw.production.rhs[waiting.raw.dot.val]? :=
                  witness.next.2.symm
                _ = (ProductionId.choice site branch).rhs[0]? := by
                  let index := waiting.raw.dot.val
                  have indexZero : index = 0 := waitingZero
                  calc
                    _ = (ProductionId.choice site branch).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) waitingProduction
                    _ = _ := by rw [indexZero]
                _ = _ := by simp [ProductionId.rhs]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          have atomLhs : child.raw.production.lhs = .aux atomSite.site :=
            childLhs.trans (congrArg NonterminalSymbol.aux branchSite)
          have childProduction : child.raw.production = .atom atomSite :=
            production_atom_of_lhs_local atomSite child.raw.production atomLhs
          have waitingOriginCurrent : waiting.raw.origin =
              waiting.raw.current :=
            contextualReach_zero_origin_eq_current edge.2.1 waitingZero
          have childOrigin : child.raw.origin = origin := by
            calc
              _ = shared := witness.finishedAtShared
              _ = waiting.raw.current := witness.waitingAtShared.symm
              _ = waiting.raw.origin := waitingOriginCurrent.symm
              _ = origin := by simpa [item] using witness.advance.2.2.1.symm
          have childCurrent : child.raw.current = finish := by
            simpa [item] using witness.advance.2.2.2.symm
          have childContext : child.context = context := by
            calc
              _ = descendContext waiting child.raw.production := edge.1.2.1
              _ = waiting.context := by
                rw [childProduction]
                simp [descendContext, waitingProduction]
              _ = context := by simpa [item] using edge.1.2.2.symm
          have priorLayout : waiting.raw.production.rhs.take
                waiting.raw.dot.val = [] := by
            let index := waiting.raw.dot.val
            have indexZero : index = 0 := waitingZero
            calc
              _ = (ProductionId.choice site branch).rhs.take index :=
                congrArg (fun production : ProductionId =>
                  production.rhs.take index) waitingProduction
              _ = (ProductionId.choice site branch).rhs.take 0 := by
                rw [indexZero]
              _ = [] := by simp
          let empty := GrammarSymbolValues.transport priorLayout
            childPriorValues
          have priorRecover : GrammarSymbolValues.transport priorLayout.symm
                empty = childPriorValues := by
            dsimp only [empty]
            rw [GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have fullLayout : waiting.raw.production.rhs.take
                waiting.raw.dot.val ++ [GrammarSymbol.nonterminal
                  child.raw.production.lhs] =
              (ProductionId.choice site branch).rhs := by
            simpa [item] using
              ((prefix_complete_layout waiting.raw child.raw item.raw
                witness.next witness.advance).trans
                (prefix_full_layout item.raw complete))
          have symbolLayout : GrammarSymbol.nonterminal
                child.raw.production.lhs =
              GrammarSymbol.nonterminal (.aux (site.branch branch)) :=
            congrArg GrammarSymbol.nonterminal childLhs
          have tupleEq :=
            GrammarSymbolValues.transport_append_empty_single_direct_local
              priorLayout fullLayout (ProductionId.rhs_choice site branch)
              symbolLayout empty childValue
          have packedEq := actionReduces_eleven_shapes_exact.mp action
          change output = ChoiceSite.pack site branch _ at packedEq
          rw [PrefixValues.fullValue_completeValue_eq] at packedEq
          rw [← priorRecover] at packedEq
          conv at packedEq in (GrammarSymbolValues.transport _ _) =>
            rw [tupleEq]
          let encodedChild : EbnfValue file tokens
              (site.branch branch).expression :=
            Eq.mp (congrArg (GrammarSymbolValue file tokens)
              symbolLayout) childValue
          let branchValues : GrammarSymbolValues file tokens
              (ProductionId.choice site branch).rhs :=
            GrammarSymbolValues.transport
              (ProductionId.rhs_choice site branch).symm
              (encodedChild, ())
          change output = ChoiceSite.pack site branch branchValues at packedEq
          have branchView : GrammarSymbolValues.view
                (ProductionId.rhs_choice site branch) branchValues =
              (encodedChild, ()) := by
            dsimp only [branchValues, GrammarSymbolValues.view]
            rw [GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have packedView := congrArg
            (EbnfValue.atShape site.expression_eq_choice) packedEq
          rw [ChoiceSite.pack_eq, branchView] at packedView
          rcases child with
            ⟨⟨childProductionId, atomDot, childOriginValue,
              childCurrentValue⟩, childContextValue⟩
          simp only at childProduction
          subst childProductionId
          change childOriginValue = origin at childOrigin
          change childCurrentValue = finish at childCurrent
          change childContextValue = context at childContext
          subst childOriginValue
          subst childCurrentValue
          subst childContextValue
          have symbolLayoutCanonical : symbolLayout =
              congrArg GrammarSymbol.nonterminal
                (congrArg NonterminalSymbol.aux branchSite).symm :=
            Subsingleton.elim _ _
          have encodedChildEq : encodedChild =
              EbnfValue.transport
                (congrArg GrammarSite.expression branchSite).symm
                childValue := by
            dsimp only [encodedChild]
            rw [symbolLayoutCanonical]
            have proofEq :
                congrArg GrammarSymbol.nonterminal
                    (congrArg NonterminalSymbol.aux branchSite).symm =
                  congrArg (fun child =>
                    GrammarSymbol.nonterminal (.aux child)) branchSite.symm :=
              Subsingleton.elim _ _
            rw [proofEq]
            exact auxiliaryValue_transport_eq branchSite.symm childValue
          have encodedEq : EbnfValue.transport
                ((site.branch_expression branch).trans
                  (site.branch_get_toList branch).symm)
                encodedChild =
              EbnfValue.transport
                ((congrArg GrammarSite.expression branchSite).symm.trans
                  ((site.branch_expression branch).trans
                    (site.branch_get_toList branch).symm)) childValue := by
            rw [encodedChildEq]
            exact EbnfValue.transport_trans _ _ _
          rw [encodedEq] at packedView
          exact ⟨atomDot, childValue, childCoherent, packedView⟩

/-- A coherent selected choice atom whose packed value is a source-rule value
exposes the coherent canonical root reduction of that source rule. -/
theorem coherentChoiceAtomRule_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (site : ChoiceSite) (branch : Fin site.branchCount)
    (atomSite : AtomSite)
    (branchSite : site.branch branch = atomSite.site)
    (rule : GrammarRuleId)
    (shape : atomSite.atom = .nonterminal rule)
    (notPostfix : rule ≠ .postfix)
    (dot : Fin ((ProductionId.choice site branch).rhs.length + 1))
    (origin finish : Boundary tokens) (context : GuardContext tokens)
    {output : NonterminalValue file tokens
      (ProductionId.choice site branch).lhs}
    (value : RuleValue rule)
    (choiceView : EbnfValue.atShape site.expression_eq_choice output =
      EbnfValue.choice site.branchExpressions.toList
        ⟨site.branchListIndex branch,
          EbnfValue.transport
            ((congrArg GrammarSite.expression branchSite).symm.trans
              ((site.branch_expression branch).trans
                (site.branch_get_toList branch).symm))
            (EbnfValue.ofShape atomSite.expression_eq_atom
              (EbnfValue.transport (congrArg EbnfExpr.atom shape).symm
                (EbnfValue.ruleAtom rule value)))⟩)
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .choice site branch
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) value := by
  rcases coherentChoiceAtom_child site branch atomSite branchSite dot origin
      finish context coherent with
    ⟨atomDot, atomValue, atomCoherent, actualView⟩
  let expectedAtom : EbnfValue file tokens atomSite.site.expression :=
    EbnfValue.ofShape atomSite.expression_eq_atom
      (EbnfValue.transport (congrArg EbnfExpr.atom shape).symm
        (EbnfValue.ruleAtom rule value))
  have choiceEq := EbnfValue.choice_injective
    site.branchExpressions.toList (actualView.symm.trans choiceView)
  have payloadEq : EbnfValue.transport
        ((congrArg GrammarSite.expression branchSite).symm.trans
          ((site.branch_expression branch).trans
            (site.branch_get_toList branch).symm)) atomValue =
      EbnfValue.transport
        ((congrArg GrammarSite.expression branchSite).symm.trans
          ((site.branch_expression branch).trans
            (site.branch_get_toList branch).symm)) expectedAtom :=
    eq_of_heq (Sigma.ext_iff.mp choiceEq).2
  have atomValueEq : atomValue = expectedAtom :=
    EbnfValue.transport_injective _ payloadEq
  have outputView : EbnfValue.transport (congrArg EbnfExpr.atom shape)
        (EbnfValue.atShape atomSite.expression_eq_atom atomValue) =
      EbnfValue.ruleAtom rule value := by
    rw [atomValueEq]
    dsimp only [expectedAtom, EbnfValue.atShape, EbnfValue.ofShape]
    calc
      _ = EbnfValue.transport (congrArg EbnfExpr.atom shape)
          (EbnfValue.transport
            (atomSite.expression_eq_atom.symm.trans
              atomSite.expression_eq_atom)
            (EbnfValue.transport (congrArg EbnfExpr.atom shape).symm
              (EbnfValue.ruleAtom rule value))) :=
        congrArg _ (EbnfValue.transport_trans _ _ _)
      _ = EbnfValue.transport (congrArg EbnfExpr.atom shape)
          (EbnfValue.transport (congrArg EbnfExpr.atom shape).symm
            (EbnfValue.ruleAtom rule value)) := by
        rw [EbnfValue.transport_self]
      _ = EbnfValue.transport
          ((congrArg EbnfExpr.atom shape).symm.trans
            (congrArg EbnfExpr.atom shape))
          (EbnfValue.ruleAtom rule value) :=
        EbnfValue.transport_trans _ _ _
      _ = EbnfValue.ruleAtom rule value :=
        EbnfValue.transport_self _ _
  exact coherentAtomRule_child atomDot origin finish context shape notPostfix
    outputView atomCoherent

/-- A coherent source `statement` root whose semantic input selects one
specified branch exposes the canonical child root of that branch. -/
theorem coherentStatementSelectedRule_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    (selected : Fin statementRootChoiceSite.branchCount)
    (rule : GrammarRuleId)
    (shape : (statementBranchAtomSite selected).atom = .nonterminal rule)
    (notPostfix : rule ≠ .postfix)
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .statement origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .statement origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
        priorValues)
    (input : EbnfValue file tokens (m2cV1.rhs .statement))
    (inputEq : RootAction.unpack .statement
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .statement origin finish context)
          complete priorValues) = input)
    (value : RuleValue rule)
    (inputChoice : input =
      EbnfValue.transport statementRootChoiceLayout
        (EbnfValue.choice statementRootChoiceSite.branchExpressions.toList
          ⟨statementRootChoiceSite.branchListIndex selected,
            EbnfValue.transport
              ((congrArg GrammarSite.expression
                  (statementBranchAtomSite_site selected)).symm.trans
                ((statementRootChoiceSite.branch_expression selected).trans
                  (statementRootChoiceSite.branch_get_toList selected).symm))
              (EbnfValue.ofShape
                (statementBranchAtomSite selected).expression_eq_atom
                (EbnfValue.transport (congrArg EbnfExpr.atom shape).symm
                  (EbnfValue.ruleAtom rule value)))⟩)) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) value := by
  rcases coherentStatementChoice_child complete coherentPrefix input inputEq with
    ⟨branch, dot, choiceValue, choiceCoherent, semanticEq⟩
  have transportedEq := semanticEq.trans inputChoice
  have choiceValueEq := EbnfValue.transport_injective
    statementRootChoiceLayout transportedEq
  rcases coherentChoiceAtom_child statementRootChoiceSite branch
      (statementBranchAtomSite branch) (statementBranchAtomSite_site branch)
      dot origin finish context choiceCoherent with
    ⟨_atomDot, _atomValue, _atomCoherent, actualView⟩
  have choiceEq := EbnfValue.choice_injective
    statementRootChoiceSite.branchExpressions.toList
      (actualView.symm.trans choiceValueEq)
  have indexEq := congrArg Sigma.fst choiceEq
  have indexValueEq := congrArg Fin.val indexEq
  have branchEq : branch = selected := by
    apply Fin.ext
    simpa only [ChoiceSite.branchListIndex_val] using indexValueEq
  subst branch
  exact coherentChoiceAtomRule_child statementRootChoiceSite selected
    (statementBranchAtomSite selected) (statementBranchAtomSite_site selected)
    rule shape notPostfix dot origin finish context value choiceValueEq
    choiceCoherent

/-- Forget the packed-prefix indices of a coherent complete source-rule root
while retaining its executed source reduction and output equality. -/
theorem coherentCompleteRoot_ruleReduction
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {rule : GrammarRuleId}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {output : RuleValue rule}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens rule origin finish context) output) :
    ∃ (input : EbnfValue file tokens (m2cV1.rhs rule))
      (semanticOutput : RuleValue rule),
      RuleReduction file tokens rule origin finish input semanticOutput ∧
        output = semanticOutput := by
  cases coherent with
  | reduce _ priorValues _ _ complete _ action =>
      exact ⟨RootAction.unpack rule
          (PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens rule origin finish context)
            complete priorValues),
        output, actionReduces_eleven_shapes_exact.mp action, rfl⟩

private theorem coherentLetStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .letStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentReturnStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .returnStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentMatchStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .matchStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentIfStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .ifStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentForStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .forStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentAssemblyStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .assemblyStatement origin finish
        context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentBlockStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .blockStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentBreakStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .breakStatement origin finish context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentContinueStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .continueStatement origin finish
        context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

private theorem coherentAssignmentStatement_not_terminalExpression
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens} {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .assignmentStatement origin finish
        context)
      ⟨span, .expression expression none⟩) : False := by
  rcases coherentCompleteRoot_ruleReduction coherent with
    ⟨_input, _output, actionRule, outputEq⟩
  cases actionRule
  all_goals
    have payloadEq := congrArg Located.payload outputEq
    simp [sourceLoc] at payloadEq

/-- Semantic inversion for a semicolon-free expression statement nested under
the source `statement` choice.  Coherence rules out every pass-through branch
whose own source action constructs a different statement payload. -/
theorem coherentStatement_terminalExpression_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {span : SourceSpan} {expression : Expression}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
      ⟨span, .expression expression none⟩) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .expressionStatement origin finish
        context)
      ⟨span, .expression expression none⟩ := by
  cases coherent with
  | reduce _ priorValues _ _ complete coherentPrefix action =>
      have actionRule : RuleReduction file tokens .statement origin finish
          (RootAction.unpack .statement
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens .statement origin finish
                context) complete priorValues))
          ⟨span, .expression expression none⟩ :=
        actionReduces_eleven_shapes_exact.mp action
      generalize inputEq : RootAction.unpack .statement
          (PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens .statement origin finish context)
            complete priorValues) = semanticInput at actionRule
      cases actionRule with
      | statementLet _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementLetBranch .letStatement statementLetBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentLetStatement_not_terminalExpression child)
      | statementReturn _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementReturnBranch .returnStatement statementReturnBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentReturnStatement_not_terminalExpression child)
      | statementMatch _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementMatchBranch .matchStatement statementMatchBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentMatchStatement_not_terminalExpression child)
      | statementIf _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementIfBranch .ifStatement statementIfBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentIfStatement_not_terminalExpression child)
      | statementFor _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementForBranch .forStatement statementForBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentForStatement_not_terminalExpression child)
      | statementAssembly _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementAssemblyBranch .assemblyStatement
            statementAssemblyBranch_shape (by decide) complete coherentPrefix _
            inputEq ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentAssemblyStatement_not_terminalExpression child)
      | statementBlock _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementBlockBranch .blockStatement statementBlockBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentBlockStatement_not_terminalExpression child)
      | statementBreak _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementBreakBranch .breakStatement statementBreakBranch_shape
            (by decide) complete coherentPrefix _ inputEq
            ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentBreakStatement_not_terminalExpression child)
      | statementContinue _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementContinueBranch .continueStatement
            statementContinueBranch_shape (by decide) complete coherentPrefix _
            inputEq ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentContinueStatement_not_terminalExpression child)
      | statementAssignment _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementAssignmentBranch .assignmentStatement
            statementAssignmentBranch_shape (by decide) complete coherentPrefix _
            inputEq ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact False.elim
            (coherentAssignmentStatement_not_terminalExpression child)
      | statementExpression _ _ _ =>
          have child := coherentStatementSelectedRule_child
            statementExpressionBranch .expressionStatement
            statementExpressionBranch_shape (by decide) complete coherentPrefix _
            inputEq ⟨span, .expression expression none⟩
            (by
              run_tac Lean.Meta.withTransparency .all do
                (← Lean.Elab.Tactic.getMainGoal).refl)
          exact child

/-- The source `armStatement` rule is a coherent pass-through to its single
`statement` child. -/
theorem coherentArmStatement_statement_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens} {context : GuardContext tokens}
    {statement : Statement}
    (coherent : CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .armStatement origin finish context)
      statement) :
    CoherentReduction file tokens memo correct final
      (CanonicalCompleteRootItem tokens .statement origin finish context)
      statement := by
  cases coherent with
  | reduce _ priorValues _ _ complete coherentPrefix action =>
      have actionRule : RuleReduction file tokens .armStatement origin finish
          (RootAction.unpack .armStatement
            (PrefixValues.fullValue
              (CanonicalCompleteRootItem tokens .armStatement origin finish
                context) complete priorValues)) statement :=
        actionReduces_eleven_shapes_exact.mp action
      generalize inputEq : RootAction.unpack .armStatement
          (PrefixValues.fullValue
            (CanonicalCompleteRootItem tokens .armStatement origin finish
              context) complete priorValues) = semanticInput at actionRule
      cases actionRule with
      | armStatement _ _ statement =>
          rcases coherentRootAtom_child armStatementRootAtomSite rfl
              armStatementRootAtomLayout complete coherentPrefix
              (EbnfValue.ruleAtom .statement statement) inputEq with
            ⟨atomDot, atomValue, atomCoherent, atomSemantic⟩
          exact coherentAtomRule_child atomDot origin finish context
            armStatementRootAtomSite_shape (by decide) atomSemantic
            atomCoherent

/-- Structural inversion of the middle repeated-statement child of a
completed body sequence.  Its context is the braced-body context introduced
immediately after the opening-brace child. -/
theorem coherentBodyStatementStar_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {dot : Fin ((ProductionId.seq bodyRootSequenceSite).rhs.length + 1)}
    {sequenceValue : NonterminalValue file tokens
      (ProductionId.seq bodyRootSequenceSite).lhs}
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (bodyWitness : ConsumedSpanWitness file tokens origin finish)
    (sequenceInputEq : EbnfValue.transport bodyRootSequenceLayout
        (EbnfValue.atShape bodyRootSequenceSite.expression_eq_sequence
          sequenceValue) =
      RuleReduction.inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          bodyWitness))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .seq bodyRootSequenceSite
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } sequenceValue) :
    ∃ (branch : NilConsBranch)
      (starDot : Fin ((ProductionId.star bodyStatementStarSite branch).rhs.length + 1))
      (starOrigin starFinish : Boundary tokens)
      (starValue : NonterminalValue file tokens
        (ProductionId.star bodyStatementStarSite branch).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star bodyStatementStarSite branch
          dot := starDot
          origin := starOrigin
          current := starFinish
        }
        context := .bracedBody starOrigin
      } starValue ∧
      EbnfValue.atShape bodyStatementStarSite_expression starValue =
        EbnfValue.star (.atom (.nonterminal .statement))
          (statements.map (EbnfValue.ruleAtom .statement)) ∧
      (∃ openCursor : Boundary tokens,
        ImmediatelyAfterSymbol file tokens .leftBrace openCursor starOrigin) ∧
      starOrigin.val ≤ starFinish.val ∧
      starFinish.val ≤ finish.val := by
  let sequenceItem : ContextualItemKey tokens := {
    raw := {
      production := .seq bodyRootSequenceSite
      dot := dot
      origin := origin
      current := finish
    }
    context := context
  }
  change CoherentReduction file tokens memo correct final sequenceItem
    sequenceValue at coherent
  cases coherent with
  | reduce _ values _ reached complete coherentPrefix action =>
      have sequenceComplete : sequenceItem.raw.dot.val = 3 := by
        calc
          _ = sequenceItem.raw.production.rhs.length := complete
          _ = 3 := by
            simp [sequenceItem, ProductionId.rhs_seq,
              bodyRootSequenceSite_children]
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues witness edge prior =>
          have beforeProduction : before.raw.production =
              .seq bodyRootSequenceSite := by
            simpa [sequenceItem] using witness.advance.1.symm
          have beforeDot : before.raw.dot.val = 2 := by
            have advanced := witness.advance.2.1
            omega
          have impossible : some (GrammarSymbol.terminal witness.terminal) =
              some (GrammarSymbol.nonterminal
                (.aux bodyCloseBraceAtomSite.site)) := by
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                witness.next.2.symm
              _ = (ProductionId.seq bodyRootSequenceSite).rhs[2]? := by
                let index := before.raw.dot.val
                have indexTwo : index = 2 := beforeDot
                calc
                  _ = (ProductionId.seq bodyRootSequenceSite).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexTwo]
              _ = _ := by
                simp [ProductionId.rhs_seq,
                  bodyRootSequenceSite_children]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete closeWaiting closeChild after closeShared closePriorValues
          closeValue closeWitness closeEdge closePrior closeCoherent =>
          have closeWaitingProduction : closeWaiting.raw.production =
              .seq bodyRootSequenceSite := by
            simpa [sequenceItem] using closeWitness.advance.1.symm
          have closeWaitingDot : closeWaiting.raw.dot.val = 2 := by
            have advanced := closeWitness.advance.2.1
            omega
          have closeLhs : closeChild.raw.production.lhs =
              .aux bodyCloseBraceAtomSite.site := by
            have selected : some (GrammarSymbol.nonterminal
                  closeChild.raw.production.lhs) =
                some (GrammarSymbol.nonterminal
                  (.aux bodyCloseBraceAtomSite.site)) := by
              calc
                _ = closeWaiting.raw.production.rhs[
                    closeWaiting.raw.dot.val]? := closeWitness.next.2.symm
                _ = (ProductionId.seq bodyRootSequenceSite).rhs[2]? := by
                  let index := closeWaiting.raw.dot.val
                  have indexTwo : index = 2 := closeWaitingDot
                  calc
                    _ = (ProductionId.seq bodyRootSequenceSite).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) closeWaitingProduction
                    _ = _ := by rw [indexTwo]
                _ = _ := by
                  simp [ProductionId.rhs_seq,
                    bodyRootSequenceSite_children]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          cases closePrior with
          | zero _ _ zero => omega
          | scan before after cursor priorValues witness edge prior =>
              have beforeProduction : before.raw.production =
                  .seq bodyRootSequenceSite := by
                exact witness.advance.1.symm.trans closeWaitingProduction
              have beforeDot : before.raw.dot.val = 1 := by
                have advanced := witness.advance.2.1
                omega
              have impossible : some
                    (GrammarSymbol.terminal witness.terminal) =
                  some (GrammarSymbol.nonterminal
                    (.aux bodyStatementStarSite.site)) := by
                calc
                  _ = before.raw.production.rhs[before.raw.dot.val]? :=
                    witness.next.2.symm
                  _ = (ProductionId.seq bodyRootSequenceSite).rhs[1]? := by
                    let index := before.raw.dot.val
                    have indexOne : index = 1 := beforeDot
                    calc
                      _ = (ProductionId.seq bodyRootSequenceSite).rhs[index]? :=
                        congrArg (fun production : ProductionId =>
                          production.rhs[index]?) beforeProduction
                      _ = _ := by rw [indexOne]
                  _ = _ := by
                    simp [ProductionId.rhs_seq,
                      bodyRootSequenceSite_children]
              exact GrammarSymbol.noConfusion (Option.some.inj impossible)
          | complete starWaiting starChild after starShared starPriorValues
              starValue starWitness starEdge starPrior starCoherent =>
              have starWaitingProduction : starWaiting.raw.production =
                  .seq bodyRootSequenceSite := by
                exact starWitness.advance.1.symm.trans
                  closeWaitingProduction
              have starWaitingDot : starWaiting.raw.dot.val = 1 := by
                have advanced := starWitness.advance.2.1
                omega
              have starLhs : starChild.raw.production.lhs =
                  .aux bodyStatementStarSite.site := by
                have selected : some (GrammarSymbol.nonterminal
                      starChild.raw.production.lhs) =
                    some (GrammarSymbol.nonterminal
                      (.aux bodyStatementStarSite.site)) := by
                  calc
                    _ = starWaiting.raw.production.rhs[
                        starWaiting.raw.dot.val]? := starWitness.next.2.symm
                    _ = (ProductionId.seq bodyRootSequenceSite).rhs[1]? := by
                      let index := starWaiting.raw.dot.val
                      have indexOne : index = 1 := starWaitingDot
                      calc
                        _ = (ProductionId.seq bodyRootSequenceSite).rhs[index]? :=
                          congrArg (fun production : ProductionId =>
                            production.rhs[index]?) starWaitingProduction
                        _ = _ := by rw [indexOne]
                    _ = _ := by
                      simp [ProductionId.rhs_seq,
                        bodyRootSequenceSite_children]
                exact GrammarSymbol.nonterminal.inj
                  (Option.some.inj selected)
              rcases production_star_of_lhs_local bodyStatementStarSite
                  starChild.raw.production starLhs with
                ⟨branch, starProduction⟩
              have starWaitingCurrent : starWaiting.raw.current =
                  starChild.raw.origin := by
                exact starWitness.waitingAtShared.trans
                  starWitness.finishedAtShared.symm
              have openSelected : starWaiting.raw.production.rhs[0]? =
                  some (GrammarSymbol.nonterminal
                    (.aux bodyOpenBraceAtomSite.site)) := by
                rw [starWaitingProduction]
                simp [ProductionId.rhs_seq,
                  bodyRootSequenceSite_children]
              rcases contextualReach_nonterminal_step starEdge.2.1
                  starWaitingDot openSelected with
                ⟨openWaiting, openChild, openWaitingReached,
                  openChildReached, openChildComplete, openChildLhs,
                  openWaitingDot, openWaitingProduction,
                  openWaitingOrigin, openChildOrigin, openChildCurrent⟩
              have openChildProduction : openChild.raw.production =
                  .atom bodyOpenBraceAtomSite :=
                production_atom_of_lhs_local bodyOpenBraceAtomSite
                  openChild.raw.production openChildLhs
              have openChildDot : openChild.raw.dot.val = 1 := by
                calc
                  _ = openChild.raw.production.rhs.length := openChildComplete
                  _ = (ProductionId.atom
                      bodyOpenBraceAtomSite).rhs.length :=
                    congrArg (fun production : ProductionId =>
                      production.rhs.length) openChildProduction
                  _ = 1 := by rfl
              have openChildSelected : openChild.raw.production.rhs[0]? =
                  some (GrammarSymbol.terminal
                    (.symbol .leftBrace)) := by
                rw [openChildProduction]
                have atomEq : bodyOpenBraceAtomSite.atom =
                    .terminal (.symbol .leftBrace) :=
                  EbnfExpr.atom.inj
                    (bodyOpenBraceAtomSite.expression_eq_atom.symm.trans
                      bodyOpenBraceAtomSite_expression)
                simp [ProductionId.rhs, AtomSite.symbol, atomEq,
                  EbnfAtom.grammarSymbol]
              rcases contextualReach_one_terminal openChildReached
                  openChildDot openChildSelected with
                ⟨parsedOpen, parsedOpenOrigin, parsedOpenCurrent⟩
              have starOriginAfterOpen : ∃ openCursor : Boundary tokens,
                  ImmediatelyAfterSymbol file tokens .leftBrace openCursor
                    starChild.raw.origin := by
                refine ⟨parsedOpen.cursor.beforeBoundary, ?_⟩
                have observed :=
                  parsedOpen.immediatelyAfterSymbol_local
                have afterEq : parsedOpen.cursor.afterBoundary =
                    starChild.raw.origin :=
                  parsedOpenCurrent.trans
                    (openChildCurrent.trans starWaitingCurrent)
                rwa [afterEq] at observed
              have starOriginContext : starChild.context =
                  .bracedBody starChild.raw.origin := by
                calc
                  _ = descendContext starWaiting
                      starChild.raw.production := starEdge.1.2.1
                  _ = .bracedBody starWaiting.raw.current := by
                    rw [starProduction]
                    simp [descendContext, starWaitingProduction,
                      starWaitingDot, bodyRootSequenceSite_isAt_body,
                      bodyStatementStarSite_isAt_body,
                      ProductionId.lhs]
                  _ = .bracedBody starChild.raw.origin := by
                    rw [starWaitingCurrent]
              have starFinishClose : starChild.raw.current =
                  closeChild.raw.origin := by
                calc
                  _ = closeWaiting.raw.current :=
                    starWitness.advance.2.2.2.symm
                  _ = closeShared := closeWitness.waitingAtShared
                  _ = closeChild.raw.origin :=
                    closeWitness.finishedAtShared.symm
              have starOrdered := contextualReach_ordered (by
                cases starCoherent
                assumption)
              have closeOrdered := contextualReach_ordered (by
                cases closeCoherent
                assumption)
              have closeFinish : closeChild.raw.current = finish := by
                simpa [sequenceItem] using
                  closeWitness.advance.2.2.2.symm
              have starPriorLayout :
                  starWaiting.raw.production.rhs.take
                    starWaiting.raw.dot.val = [
                      .nonterminal (.aux bodyOpenBraceAtomSite.site)] := by
                let index := starWaiting.raw.dot.val
                have indexOne : index = 1 := starWaitingDot
                calc
                  _ = (ProductionId.seq bodyRootSequenceSite).rhs.take
                      index := congrArg (fun production : ProductionId =>
                        production.rhs.take index) starWaitingProduction
                  _ = (ProductionId.seq bodyRootSequenceSite).rhs.take 1 := by
                    rw [indexOne]
                  _ = _ := by
                    simp [ProductionId.rhs_seq,
                      bodyRootSequenceSite_children]
              generalize canonicalPriorEq : GrammarSymbolValues.transport
                  starPriorLayout starPriorValues = canonicalPrior
              rcases canonicalPrior with ⟨openValue, ⟨⟩⟩
              have starPriorRecover : GrammarSymbolValues.transport
                    starPriorLayout.symm (openValue, ()) =
                  starPriorValues := by
                rw [← canonicalPriorEq,
                  GrammarSymbolValues.transport_trans]
                exact GrammarSymbolValues.transport_self _ _
              have sequenceSymbolLayout :
                  bodyRootSequenceSite.children.map (fun child =>
                    GrammarSymbol.nonterminal (.aux child)) = [
                      .nonterminal (.aux bodyOpenBraceAtomSite.site),
                      .nonterminal starChild.raw.production.lhs,
                      .nonterminal closeChild.raw.production.lhs] := by
                rw [bodyRootSequenceSite_children]
                simp only [List.map]
                rw [starLhs, closeLhs]
              have fullTupleEq :=
                GrammarSymbolValues.transport_append_three_direct_local
                  starPriorLayout
                  (prefix_complete_layout starWaiting.raw starChild.raw
                    closeWaiting.raw starWitness.next starWitness.advance)
                  ((prefix_complete_layout closeWaiting.raw closeChild.raw
                    sequenceItem.raw closeWitness.next closeWitness.advance).trans
                    (prefix_full_layout sequenceItem.raw complete))
                  ((by rfl : sequenceItem.raw.production.rhs =
                      (ProductionId.seq bodyRootSequenceSite).rhs).trans
                    ((ProductionId.rhs_seq bodyRootSequenceSite).trans
                      sequenceSymbolLayout))
                  openValue starValue closeValue
              have packedEq := actionReduces_eleven_shapes_exact.mp action
              change sequenceValue = SequenceSite.pack
                  bodyRootSequenceSite _ at packedEq
              rw [PrefixValues.fullValue_completeValue_eq] at packedEq
              rw [← starPriorRecover] at packedEq
              unfold PrefixValues.completeValue at packedEq
              conv at packedEq in (GrammarSymbolValues.transport _ _) =>
                rw [fullTupleEq]
              let rawSequenceValue := EbnfValue.sequence
                (bodyRootSequenceSite.children.map GrammarSite.expression)
                (EbnfValues.ofAuxiliaries bodyRootSequenceSite.children
                  (GrammarSymbolValues.transport sequenceSymbolLayout.symm
                    (openValue, (starValue, (closeValue, ())))))
              have sequenceValueEq : EbnfValue.atShape
                    bodyRootSequenceSite.expression_eq_sequence sequenceValue =
                  rawSequenceValue := by
                rw [packedEq, SequenceSite.pack_eq]
                rfl
              have bodyExpressionLayout :
                  bodyRootSequenceSite.children.map GrammarSite.expression = [
                    .atom (.terminal (.symbol .leftBrace)),
                    .star (.atom (.nonterminal .statement)),
                    .atom (.terminal (.symbol .rightBrace))] := by
                rw [bodyRootSequenceSite_children]
                simp only [List.map]
                rw [bodyOpenBraceAtomSite_expression,
                  bodyStatementStarSite_expression,
                  bodyCloseBraceAtomSite_expression]
              have canonicalInputEq : EbnfValue.transport
                    (congrArg EbnfExpr.sequence bodyExpressionLayout)
                    rawSequenceValue =
                  RuleReduction.inputValue
                    (RuleReduction.body origin finish openBrace statements
                      closeBrace bodyWitness) := by
                calc
                  _ = EbnfValue.transport bodyRootSequenceLayout
                      rawSequenceValue :=
                    eqMp_proof_irrel_local _ _ rawSequenceValue
                  _ = EbnfValue.transport bodyRootSequenceLayout
                      (EbnfValue.atShape
                        bodyRootSequenceSite.expression_eq_sequence
                        sequenceValue) :=
                    congrArg (EbnfValue.transport bodyRootSequenceLayout)
                      sequenceValueEq.symm
                  _ = _ := sequenceInputEq
              have viewedEq := congrArg
                (fun input =>
                  (EbnfValue.sequence3View
                    (.atom (.terminal (.symbol .leftBrace)))
                    (.star (.atom (.nonterminal .statement)))
                    (.atom (.terminal (.symbol .rightBrace))) input).2.1)
                canonicalInputEq
              have leftView :=
                bodySequenceMiddle_auxiliary_three_eq_local
                  bodyRootSequenceSite_children rfl starLhs closeLhs
                  sequenceSymbolLayout bodyExpressionLayout openValue
                  starValue closeValue
              have rightView :
                  (EbnfValue.sequence3View
                    (.atom (.terminal (.symbol .leftBrace)))
                    (.star (.atom (.nonterminal .statement)))
                    (.atom (.terminal (.symbol .rightBrace)))
                    (RuleReduction.inputValue
                      (RuleReduction.body origin finish openBrace statements
                        closeBrace bodyWitness))).2.1 =
                    EbnfValue.star (.atom (.nonterminal .statement))
                      (statements.map
                        (EbnfValue.ruleAtom .statement)) := by
                change
                  (EbnfValue.sequence3View
                    (.atom (.terminal (.symbol .leftBrace)))
                    (.star (.atom (.nonterminal .statement)))
                    (.atom (.terminal (.symbol .rightBrace)))
                    (EbnfValue.sequence [
                      .atom (.terminal (.symbol .leftBrace)),
                      .star (.atom (.nonterminal .statement)),
                      .atom (.terminal (.symbol .rightBrace))]
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .leftBrace) openBrace)
                        (EbnfValues.cons _ _
                          (EbnfValue.star
                            (.atom (.nonterminal .statement))
                            (statements.map
                              (EbnfValue.ruleAtom .statement)))
                          (EbnfValues.cons _ _
                            (EbnfValue.terminalAtom
                              (.symbol .rightBrace) closeBrace)
                            EbnfValues.nil))))).2.1 = _
                have rebuilt := EbnfValue.sequence3_of_view
                  (.atom (.terminal (.symbol .leftBrace)))
                  (.star (.atom (.nonterminal .statement)))
                  (.atom (.terminal (.symbol .rightBrace)))
                  (EbnfValue.sequence [
                    .atom (.terminal (.symbol .leftBrace)),
                    .star (.atom (.nonterminal .statement)),
                    .atom (.terminal (.symbol .rightBrace))]
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom
                        (.symbol .leftBrace) openBrace)
                      (EbnfValues.cons _ _
                        (EbnfValue.star
                          (.atom (.nonterminal .statement))
                          (statements.map
                            (EbnfValue.ruleAtom .statement)))
                        (EbnfValues.cons _ _
                          (EbnfValue.terminalAtom
                            (.symbol .rightBrace) closeBrace)
                          EbnfValues.nil))))
                have valuesEq := EbnfValue.sequence_injective _ rebuilt
                have tailEq := (EbnfValues.cons_injective _ _ valuesEq).2
                exact (EbnfValues.cons_injective _ _ tailEq).1
              have starSemanticEq :
                  EbnfValue.atShape bodyStatementStarSite_expression
                      (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                        (congrArg GrammarSymbol.nonterminal starLhs))
                        starValue) =
                    EbnfValue.star (.atom (.nonterminal .statement))
                      (statements.map
                        (EbnfValue.ruleAtom .statement)) :=
                leftView.symm.trans (viewedEq.trans rightView)
              rcases starChild with
                ⟨⟨starProductionId, starDot, starOrigin, starFinish⟩,
                  starContext⟩
              simp only at starProduction
              subst starProductionId
              have starLhsProof : starLhs = rfl := Subsingleton.elim _ _
              rw [starLhsProof] at starSemanticEq
              change starContext = .bracedBody starOrigin at starOriginContext
              subst starContext
              change starFinish = closeChild.raw.origin at starFinishClose
              refine ⟨branch, starDot, starOrigin, starFinish, starValue,
                starCoherent, starSemanticEq, ?_, ?_, ?_⟩
              · exact starOriginAfterOpen
              · exact starOrdered
              · rw [starFinishClose, ← closeFinish]
                exact closeOrdered

/-- A coherent completed body root exposes the exact repeated-statement star
and its semantic statement list. -/
theorem coherentBodyStatementStar_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .body origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .body origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .body origin finish context)
        priorValues)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (bodyWitness : ConsumedSpanWitness file tokens origin finish)
    (inputEq : RootAction.unpack .body
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .body origin finish context)
          complete priorValues) =
      RuleReduction.inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          bodyWitness)) :
    ∃ (branch : NilConsBranch)
      (starDot : Fin ((ProductionId.star bodyStatementStarSite branch).rhs.length + 1))
      (starOrigin starFinish : Boundary tokens)
      (starValue : NonterminalValue file tokens
        (ProductionId.star bodyStatementStarSite branch).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star bodyStatementStarSite branch
          dot := starDot
          origin := starOrigin
          current := starFinish
        }
        context := .bracedBody starOrigin
      } starValue ∧
      EbnfValue.atShape bodyStatementStarSite_expression starValue =
        EbnfValue.star (.atom (.nonterminal .statement))
          (statements.map (EbnfValue.ruleAtom .statement)) ∧
      (∃ openCursor : Boundary tokens,
        ImmediatelyAfterSymbol file tokens .leftBrace openCursor starOrigin) ∧
      starOrigin.val ≤ starFinish.val ∧
      starFinish.val ≤ finish.val := by
  rcases coherentRootSequence_child bodyRootSequenceSite rfl
      bodyRootSequenceLayout complete coherentPrefix
      (RuleReduction.inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          bodyWitness)) inputEq with
    ⟨sequenceDot, sequenceValue, sequenceCoherent, sequenceInputEq⟩
  exact coherentBodyStatementStar_child openBrace statements closeBrace
    bodyWitness sequenceInputEq sequenceCoherent

/-- Structural inversion of the final repeated arm-statement child of a
completed match-arm sequence. Its context begins immediately after the
retained fat arrow. -/
theorem coherentMatchArmStatementStar_child
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {dot : Fin ((ProductionId.seq matchArmSequenceSite).rhs.length + 1)}
    {sequenceValue : NonterminalValue file tokens
      (ProductionId.seq matchArmSequenceSite).lhs}
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (sequenceInputEq : EbnfValue.transport matchArmRootSequenceLayout
        (EbnfValue.atShape matchArmSequenceSite.expression_eq_sequence
          sequenceValue) =
      RuleReduction.inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .seq matchArmSequenceSite
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } sequenceValue) :
    ∃ (branch : NilConsBranch)
      (starDot : Fin
        ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1))
      (starOrigin starFinish : Boundary tokens)
      (starValue : NonterminalValue file tokens
        (ProductionId.star matchArmBodyStarSite branch).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star matchArmBodyStarSite branch
          dot := starDot
          origin := starOrigin
          current := starFinish
        }
        context := .armBody starOrigin
      } starValue ∧
      EbnfValue.atShape matchArmBodyStarSite_expression starValue =
        EbnfValue.star (.atom (.nonterminal .armStatement))
          (statements.map (EbnfValue.ruleAtom .armStatement)) ∧
      (∃ arrowCursor : Boundary tokens,
        ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor starOrigin) := by
  let sequenceItem : ContextualItemKey tokens := {
    raw := {
      production := .seq matchArmSequenceSite
      dot := dot
      origin := origin
      current := finish
    }
    context := context
  }
  change CoherentReduction file tokens memo correct final sequenceItem
    sequenceValue at coherent
  cases coherent with
  | reduce _ values _ reached complete coherentPrefix action =>
      have sequenceComplete : sequenceItem.raw.dot.val = 4 := by
        calc
          _ = sequenceItem.raw.production.rhs.length := complete
          _ = 4 := by
            simpa [sequenceItem] using
              ProductionId.rhs_matchArmSequenceSite_length
      cases coherentPrefix with
      | zero _ _ zero => omega
      | scan before after cursor priorValues scanWitness edge prior =>
          have beforeProduction : before.raw.production =
              .seq matchArmSequenceSite := by
            simpa [sequenceItem] using scanWitness.advance.1.symm
          have beforeDot : before.raw.dot.val = 3 := by
            have advanced := scanWitness.advance.2.1
            omega
          have impossible : some
                (GrammarSymbol.terminal scanWitness.terminal) =
              some (GrammarSymbol.nonterminal
                (.aux matchArmBodyStarSite.site)) := by
            calc
              _ = before.raw.production.rhs[before.raw.dot.val]? :=
                scanWitness.next.2.symm
              _ = (ProductionId.seq matchArmSequenceSite).rhs[3]? := by
                let index := before.raw.dot.val
                have indexThree : index = 3 := beforeDot
                calc
                  _ = (ProductionId.seq matchArmSequenceSite).rhs[index]? :=
                    congrArg (fun production : ProductionId =>
                      production.rhs[index]?) beforeProduction
                  _ = _ := by rw [indexThree]
              _ = _ := by
                simp [ProductionId.rhs_seq, matchArmSequenceSite_children]
          exact GrammarSymbol.noConfusion (Option.some.inj impossible)
      | complete starWaiting starChild after starShared starPriorValues
          starValue starWitness starEdge starPrior starCoherent =>
          have starWaitingProduction : starWaiting.raw.production =
              .seq matchArmSequenceSite := by
            simpa [sequenceItem] using starWitness.advance.1.symm
          have starWaitingDot : starWaiting.raw.dot.val = 3 := by
            have advanced := starWitness.advance.2.1
            omega
          have starLhs : starChild.raw.production.lhs =
              .aux matchArmBodyStarSite.site := by
            have selected : some (GrammarSymbol.nonterminal
                  starChild.raw.production.lhs) =
                some (GrammarSymbol.nonterminal
                  (.aux matchArmBodyStarSite.site)) := by
              calc
                _ = starWaiting.raw.production.rhs[
                    starWaiting.raw.dot.val]? := starWitness.next.2.symm
                _ = (ProductionId.seq matchArmSequenceSite).rhs[3]? := by
                  let index := starWaiting.raw.dot.val
                  have indexThree : index = 3 := starWaitingDot
                  calc
                    _ = (ProductionId.seq matchArmSequenceSite).rhs[index]? :=
                      congrArg (fun production : ProductionId =>
                        production.rhs[index]?) starWaitingProduction
                    _ = _ := by rw [indexThree]
                _ = _ := by
                  simp [ProductionId.rhs_seq, matchArmSequenceSite_children]
            exact GrammarSymbol.nonterminal.inj (Option.some.inj selected)
          rcases production_star_of_lhs_local matchArmBodyStarSite
              starChild.raw.production starLhs with
            ⟨branch, starProduction⟩
          have starWaitingCurrent : starWaiting.raw.current =
              starChild.raw.origin :=
            starWitness.waitingAtShared.trans
              starWitness.finishedAtShared.symm
          have arrowSelected : starWaiting.raw.production.rhs[2]? =
              some (GrammarSymbol.nonterminal
                (.aux matchArmFatArrowAtomSite.site)) := by
            rw [starWaitingProduction]
            simp [ProductionId.rhs_seq, matchArmSequenceSite_children]
          rcases contextualReach_nonterminal_step starEdge.2.1
              starWaitingDot arrowSelected with
            ⟨arrowWaiting, arrowChild, arrowWaitingReached,
              arrowChildReached, arrowChildComplete, arrowChildLhs,
              arrowWaitingDot, arrowWaitingProduction,
              arrowWaitingOrigin, arrowChildOrigin, arrowChildCurrent⟩
          have arrowChildProduction : arrowChild.raw.production =
              .atom matchArmFatArrowAtomSite :=
            production_atom_of_lhs_local matchArmFatArrowAtomSite
              arrowChild.raw.production arrowChildLhs
          have arrowChildDot : arrowChild.raw.dot.val = 1 := by
            calc
              _ = arrowChild.raw.production.rhs.length := arrowChildComplete
              _ = (ProductionId.atom
                    matchArmFatArrowAtomSite).rhs.length :=
                congrArg (fun production : ProductionId =>
                  production.rhs.length) arrowChildProduction
              _ = 1 := by rfl
          have arrowChildSelected : arrowChild.raw.production.rhs[0]? =
              some (GrammarSymbol.terminal (.symbol .fatArrow)) := by
            rw [arrowChildProduction]
            have atomEq : matchArmFatArrowAtomSite.atom =
                .terminal (.symbol .fatArrow) :=
              EbnfExpr.atom.inj
                (matchArmFatArrowAtomSite.expression_eq_atom.symm.trans
                  matchArmFatArrowAtomSite_expression)
            simp [ProductionId.rhs, AtomSite.symbol, atomEq,
              EbnfAtom.grammarSymbol]
          rcases contextualReach_one_terminal arrowChildReached
              arrowChildDot arrowChildSelected with
            ⟨parsedArrow, parsedArrowOrigin, parsedArrowCurrent⟩
          have starOriginAfterArrow : ∃ arrowCursor : Boundary tokens,
              ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor
                starChild.raw.origin := by
            refine ⟨parsedArrow.cursor.beforeBoundary, ?_⟩
            have observed := parsedArrow.immediatelyAfterSymbol_local
            have afterEq : parsedArrow.cursor.afterBoundary =
                starChild.raw.origin :=
              parsedArrowCurrent.trans
                (arrowChildCurrent.trans starWaitingCurrent)
            rwa [afterEq] at observed
          have starOriginContext : starChild.context =
              .armBody starChild.raw.origin := by
            calc
              _ = descendContext starWaiting
                  starChild.raw.production := starEdge.1.2.1
              _ = .armBody starWaiting.raw.current := by
                rw [starProduction]
                simp [descendContext, starWaitingProduction,
                  starWaitingDot, matchArmSequenceSite_key,
                  matchArmBodyStarSite_key, GrammarSite.isAt,
                  ProductionId.lhs]
              _ = .armBody starChild.raw.origin := by
                rw [starWaitingCurrent]
          have priorLayout : starWaiting.raw.production.rhs.take
                starWaiting.raw.dot.val = [
              .nonterminal (.aux matchArmPipeAtomSite.site),
              .nonterminal (.aux matchArmPatternListSite.site),
              .nonterminal (.aux matchArmFatArrowAtomSite.site)] := by
            let index := starWaiting.raw.dot.val
            have indexThree : index = 3 := starWaitingDot
            calc
              _ = (ProductionId.seq matchArmSequenceSite).rhs.take index :=
                congrArg (fun production : ProductionId =>
                  production.rhs.take index) starWaitingProduction
              _ = (ProductionId.seq matchArmSequenceSite).rhs.take 3 := by
                rw [indexThree]
              _ = _ := by
                simp [ProductionId.rhs_seq, matchArmSequenceSite_children]
          generalize canonicalPriorEq : GrammarSymbolValues.transport
              priorLayout starPriorValues = canonicalPrior
          rcases canonicalPrior with
            ⟨pipeValue, patternValue, arrowValue, ⟨⟩⟩
          have priorRecover : GrammarSymbolValues.transport
                priorLayout.symm
                (pipeValue, (patternValue, (arrowValue, ()))) =
              starPriorValues := by
            rw [← canonicalPriorEq,
              GrammarSymbolValues.transport_trans]
            exact GrammarSymbolValues.transport_self _ _
          have sequenceSymbolLayout :
              matchArmSequenceSite.children.map (fun child =>
                GrammarSymbol.nonterminal (.aux child)) = [
                .nonterminal (.aux matchArmPipeAtomSite.site),
                .nonterminal (.aux matchArmPatternListSite.site),
                .nonterminal (.aux matchArmFatArrowAtomSite.site),
                .nonterminal starChild.raw.production.lhs] := by
            rw [matchArmSequenceSite_children]
            simp only [List.map]
            rw [starLhs]
          have fullTupleEq :=
            GrammarSymbolValues.transport_append_three_single_direct_local
              priorLayout
              ((prefix_complete_layout starWaiting.raw starChild.raw
                sequenceItem.raw starWitness.next starWitness.advance).trans
                (prefix_full_layout sequenceItem.raw complete))
              ((by rfl : sequenceItem.raw.production.rhs =
                    (ProductionId.seq matchArmSequenceSite).rhs).trans
                ((ProductionId.rhs_seq matchArmSequenceSite).trans
                  sequenceSymbolLayout))
              pipeValue patternValue arrowValue starValue
          have packedEq := actionReduces_eleven_shapes_exact.mp action
          change sequenceValue = SequenceSite.pack
              matchArmSequenceSite _ at packedEq
          rw [PrefixValues.fullValue_completeValue_eq] at packedEq
          rw [← priorRecover] at packedEq
          conv at packedEq in (GrammarSymbolValues.transport _ _) =>
            rw [fullTupleEq]
          let rawSequenceValue := EbnfValue.sequence
            (matchArmSequenceSite.children.map GrammarSite.expression)
            (EbnfValues.ofAuxiliaries matchArmSequenceSite.children
              (GrammarSymbolValues.transport sequenceSymbolLayout.symm
                (pipeValue, (patternValue,
                  (arrowValue, (starValue, ()))))))
          have sequenceValueEq : EbnfValue.atShape
                matchArmSequenceSite.expression_eq_sequence sequenceValue =
              rawSequenceValue := by
            rw [packedEq, SequenceSite.pack_eq]
            rfl
          have expressionLayout :
              matchArmSequenceSite.children.map GrammarSite.expression = [
                .atom (.terminal (.symbol .pipe)),
                .list1 (.atom (.nonterminal .pattern)),
                .atom (.terminal (.symbol .fatArrow)),
                .star (.atom (.nonterminal .armStatement))] := by
            rw [matchArmSequenceSite_children]
            simp only [List.map]
            rw [matchArmPipeAtomSite_expression,
              matchArmPatternListSite_expression,
              matchArmFatArrowAtomSite_expression,
              matchArmBodyStarSite_expression]
          have canonicalInputEq : EbnfValue.transport
                (congrArg EbnfExpr.sequence expressionLayout)
                rawSequenceValue =
              RuleReduction.inputValue
                (RuleReduction.matchArm origin finish pipe patterns fatArrow
                  statements witness) := by
            calc
              _ = EbnfValue.transport matchArmRootSequenceLayout
                  rawSequenceValue :=
                eqMp_proof_irrel_local _ _ rawSequenceValue
              _ = EbnfValue.transport matchArmRootSequenceLayout
                  (EbnfValue.atShape
                    matchArmSequenceSite.expression_eq_sequence
                    sequenceValue) :=
                congrArg (EbnfValue.transport matchArmRootSequenceLayout)
                  sequenceValueEq.symm
              _ = _ := sequenceInputEq
          have viewedEq := congrArg
            (fun input =>
              (EbnfValue.sequence4View
                (.atom (.terminal (.symbol .pipe)))
                (.list1 (.atom (.nonterminal .pattern)))
                (.atom (.terminal (.symbol .fatArrow)))
                (.star (.atom (.nonterminal .armStatement))) input).2.2.2)
            canonicalInputEq
          have leftView :=
            matchArmSequenceFourth_auxiliary_four_eq_local
              matchArmSequenceSite_children rfl rfl rfl starLhs
              sequenceSymbolLayout expressionLayout pipeValue patternValue
              arrowValue starValue
          have rightView :
              (EbnfValue.sequence4View
                (.atom (.terminal (.symbol .pipe)))
                (.list1 (.atom (.nonterminal .pattern)))
                (.atom (.terminal (.symbol .fatArrow)))
                (.star (.atom (.nonterminal .armStatement)))
                (RuleReduction.inputValue
                  (RuleReduction.matchArm origin finish pipe patterns fatArrow
                    statements witness))).2.2.2 =
                EbnfValue.star (.atom (.nonterminal .armStatement))
                  (statements.map
                    (EbnfValue.ruleAtom .armStatement)) := by
            change
              (EbnfValue.sequence4View
                (.atom (.terminal (.symbol .pipe)))
                (.list1 (.atom (.nonterminal .pattern)))
                (.atom (.terminal (.symbol .fatArrow)))
                (.star (.atom (.nonterminal .armStatement)))
                (EbnfValue.sequence [
                  .atom (.terminal (.symbol .pipe)),
                  .list1 (.atom (.nonterminal .pattern)),
                  .atom (.terminal (.symbol .fatArrow)),
                  .star (.atom (.nonterminal .armStatement))]
                  (EbnfValues.cons _ _
                    (EbnfValue.terminalAtom (.symbol .pipe) pipe)
                    (EbnfValues.cons _ _
                      (EbnfValue.list1 (.atom (.nonterminal .pattern))
                        (patterns.map (EbnfValue.ruleAtom .pattern)))
                      (EbnfValues.cons _ _
                        (EbnfValue.terminalAtom
                          (.symbol .fatArrow) fatArrow)
                        (EbnfValues.cons _ _
                          (EbnfValue.star
                            (.atom (.nonterminal .armStatement))
                            (statements.map
                              (EbnfValue.ruleAtom .armStatement)))
                          EbnfValues.nil)))))).2.2.2 = _
            have rebuilt := EbnfValue.sequence4_of_view
              (.atom (.terminal (.symbol .pipe)))
              (.list1 (.atom (.nonterminal .pattern)))
              (.atom (.terminal (.symbol .fatArrow)))
              (.star (.atom (.nonterminal .armStatement)))
              (EbnfValue.sequence [
                .atom (.terminal (.symbol .pipe)),
                .list1 (.atom (.nonterminal .pattern)),
                .atom (.terminal (.symbol .fatArrow)),
                .star (.atom (.nonterminal .armStatement))]
                (EbnfValues.cons _ _
                  (EbnfValue.terminalAtom (.symbol .pipe) pipe)
                  (EbnfValues.cons _ _
                    (EbnfValue.list1 (.atom (.nonterminal .pattern))
                      (patterns.map (EbnfValue.ruleAtom .pattern)))
                    (EbnfValues.cons _ _
                      (EbnfValue.terminalAtom (.symbol .fatArrow) fatArrow)
                      (EbnfValues.cons _ _
                        (EbnfValue.star
                          (.atom (.nonterminal .armStatement))
                          (statements.map
                            (EbnfValue.ruleAtom .armStatement)))
                        EbnfValues.nil)))))
            have valuesEq := EbnfValue.sequence_injective _ rebuilt
            have tailEq := (EbnfValues.cons_injective _ _ valuesEq).2
            have secondTailEq :=
              (EbnfValues.cons_injective _ _ tailEq).2
            have thirdTailEq :=
              (EbnfValues.cons_injective _ _ secondTailEq).2
            exact (EbnfValues.cons_injective _ _ thirdTailEq).1
          have starSemantic :
              EbnfValue.atShape matchArmBodyStarSite_expression
                  (Eq.mp (congrArg (GrammarSymbolValue file tokens)
                    (congrArg GrammarSymbol.nonterminal starLhs))
                    starValue) =
                EbnfValue.star (.atom (.nonterminal .armStatement))
                  (statements.map
                    (EbnfValue.ruleAtom .armStatement)) :=
            leftView.symm.trans (viewedEq.trans rightView)
          rcases starChild with
            ⟨⟨starProductionId, starDot, starOrigin, starFinish⟩,
              starContext⟩
          simp only at starProduction
          subst starProductionId
          have starLhsProof : starLhs = rfl := Subsingleton.elim _ _
          rw [starLhsProof] at starSemantic
          change starContext = .armBody starOrigin at starOriginContext
          subst starContext
          exact ⟨branch, starDot, starOrigin, starFinish, starValue,
            starCoherent, starSemantic, starOriginAfterArrow⟩

/-- A coherent completed match-arm root exposes its repeated arm-statement
star, semantic statement list, and exact post-arrow context start. -/
theorem coherentMatchArmStatementStar_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .matchArm origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .matchArm origin finish context).raw)
    (coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .matchArm origin finish context)
        priorValues)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (inputEq : RootAction.unpack .matchArm
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .matchArm origin finish context)
          complete priorValues) =
      RuleReduction.inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) :
    ∃ (branch : NilConsBranch)
      (starDot : Fin
        ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1))
      (starOrigin starFinish : Boundary tokens)
      (starValue : NonterminalValue file tokens
        (ProductionId.star matchArmBodyStarSite branch).lhs),
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star matchArmBodyStarSite branch
          dot := starDot
          origin := starOrigin
          current := starFinish
        }
        context := .armBody starOrigin
      } starValue ∧
      EbnfValue.atShape matchArmBodyStarSite_expression starValue =
        EbnfValue.star (.atom (.nonterminal .armStatement))
          (statements.map (EbnfValue.ruleAtom .armStatement)) ∧
      (∃ arrowCursor : Boundary tokens,
        ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor starOrigin) := by
  rcases coherentRootSequence_child matchArmSequenceSite rfl
      matchArmRootSequenceLayout complete coherentPrefix
      (RuleReduction.inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow
          statements witness)) inputEq with
    ⟨sequenceDot, sequenceValue, sequenceCoherent, sequenceInputEq⟩
  exact coherentMatchArmStatementStar_child pipe patterns fatArrow statements
    witness sequenceInputEq sequenceCoherent

private theorem EbnfValue.transport_star_eq_map_local
    {file : WorkspaceFile} {tokens : List Token}
    {source target : EbnfExpr} (shape : source = target)
    (values : List (EbnfValue file tokens source)) :
    EbnfValue.transport (congrArg EbnfExpr.star shape)
        (EbnfValue.star source values) =
      EbnfValue.star target
        (values.map (EbnfValue.transport shape)) := by
  cases shape
  rw [EbnfValue.transport_self]
  apply congrArg (EbnfValue.star source)
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons]
      rw [EbnfValue.transport_self]
      exact congrArg (List.cons head) inductionHypothesis

private theorem bodyStar_atShape_eq_transport_local
    {file : WorkspaceFile} {tokens : List Token}
    (value : EbnfValue file tokens bodyStatementStarSite.site.expression) :
    EbnfValue.atShape bodyStatementStarSite_expression value =
      EbnfValue.transport
        (congrArg EbnfExpr.star bodyStatementStarSite_child_expression)
        (EbnfValue.atShape bodyStatementStarSite.expression_eq_star value) := by
  unfold EbnfValue.atShape
  rw [EbnfValue.transport_trans]

private theorem bodyStar_branch_cons_of_semantic_cons
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {branch : NilConsBranch}
    {dot : Fin ((ProductionId.star bodyStatementStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star bodyStatementStarSite branch).lhs}
    (head : Statement) (tail : List Statement)
    (semantic : EbnfValue.atShape bodyStatementStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .statement))
        ((head :: tail).map (EbnfValue.ruleAtom .statement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star bodyStatementStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) : branch = .cons := by
  cases branch with
  | cons => rfl
  | nil =>
      let item : ContextualItemKey tokens := {
        raw := {
          production := .star bodyStatementStarSite .nil
          dot := dot
          origin := origin
          current := finish
        }
        context := context
      }
      change CoherentReduction file tokens memo correct final item output
        at coherent
      cases coherent with
      | reduce _ values _ reached complete coherentPrefix action =>
          have packedEq := actionReduces_eleven_shapes_exact.mp action
          change output = StarSite.pack bodyStatementStarSite .nil _
            at packedEq
          have emptyAtShape : EbnfValue.atShape
                bodyStatementStarSite.expression_eq_star output =
              EbnfValue.star bodyStatementStarSite.child.expression [] := by
            rw [packedEq, StarSite.pack_nil_eq]
          have emptyCanonical : EbnfValue.atShape
                bodyStatementStarSite_expression output =
              EbnfValue.star (.atom (.nonterminal .statement)) [] := by
            rw [bodyStar_atShape_eq_transport_local output, emptyAtShape]
            simpa using EbnfValue.transport_star_eq_map_local
              bodyStatementStarSite_child_expression
              ([] : List (EbnfValue file tokens
                bodyStatementStarSite.child.expression))
          have listEq := EbnfValue.star_injective
            (.atom (.nonterminal .statement))
            (semantic.symm.trans emptyCanonical)
          simp at listEq

/-- One nonempty body statement-star step exposes the coherent statement
root at its head and the coherent semantic tail at the exact split cursor. -/
theorem coherentBodyStatementStar_cons_children
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish regionStart : Boundary tokens}
    {branch : NilConsBranch}
    {dot : Fin ((ProductionId.star bodyStatementStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star bodyStatementStarSite branch).lhs}
    (headStatement : Statement) (tailStatements : List Statement)
    (semantic : EbnfValue.atShape bodyStatementStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .statement))
        ((headStatement :: tailStatements).map
          (EbnfValue.ruleAtom .statement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star bodyStatementStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := .bracedBody regionStart
    } output) :
    ∃ (split : Boundary tokens) (tailBranch : NilConsBranch)
      (tailDot : Fin
        ((ProductionId.star bodyStatementStarSite tailBranch).rhs.length + 1))
      (tailValue : NonterminalValue file tokens
        (ProductionId.star bodyStatementStarSite tailBranch).lhs),
      CoherentReduction file tokens memo correct final
        (CanonicalCompleteRootItem tokens .statement origin split
          (.bracedBody regionStart)) headStatement ∧
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star bodyStatementStarSite tailBranch
          dot := tailDot
          origin := split
          current := finish
        }
        context := .bracedBody regionStart
      } tailValue ∧
      EbnfValue.atShape bodyStatementStarSite_expression tailValue =
        EbnfValue.star (.atom (.nonterminal .statement))
          (tailStatements.map (EbnfValue.ruleAtom .statement)) := by
  have branchEq := bodyStar_branch_cons_of_semantic_cons headStatement
    tailStatements semantic coherent
  subst branch
  rcases coherentStarCons_children dot origin finish
      (.bracedBody regionStart) coherent with
    ⟨head, tail, headValue, tailValue, tailBranch, headLhs, tailLhs,
      tailProduction, headOrigin, headTail, tailFinish, headContext,
      tailContext, headCoherent, tailCoherent, outputView⟩
  have transportedEq : EbnfValue.transport
        (congrArg EbnfExpr.star bodyStatementStarSite_child_expression)
        (EbnfValue.atShape bodyStatementStarSite.expression_eq_star output) =
      EbnfValue.star (.atom (.nonterminal .statement))
        ((headStatement :: tailStatements).map
          (EbnfValue.ruleAtom .statement)) :=
    (bodyStar_atShape_eq_transport_local output).symm.trans semantic
  rw [outputView,
    EbnfValue.transport_star_eq_map_local
      bodyStatementStarSite_child_expression] at transportedEq
  have listEq := EbnfValue.star_injective
    (.atom (.nonterminal .statement)) transportedEq
  simp only [List.map_cons] at listEq
  have headSemantic := (List.cons.inj listEq).1
  have tailListSemantic := (List.cons.inj listEq).2
  let tailEncoded : EbnfValue file tokens
      bodyStatementStarSite.site.expression :=
    Eq.mp (congrArg (NonterminalValue file tokens) tailLhs) tailValue
  have tailSemantic : EbnfValue.atShape
        bodyStatementStarSite_expression tailEncoded =
      EbnfValue.star (.atom (.nonterminal .statement))
        (tailStatements.map (EbnfValue.ruleAtom .statement)) := by
    rw [bodyStar_atShape_eq_transport_local tailEncoded]
    let tailAtStar := EbnfValue.atShape
      bodyStatementStarSite.expression_eq_star tailEncoded
    calc
      EbnfValue.transport
          (congrArg EbnfExpr.star
            bodyStatementStarSite_child_expression) tailAtStar =
        EbnfValue.transport
          (congrArg EbnfExpr.star
            bodyStatementStarSite_child_expression)
          (EbnfValue.star bodyStatementStarSite.child.expression
            (EbnfValue.starView
              bodyStatementStarSite.child.expression tailAtStar)) := by
            apply congrArg
              (EbnfValue.transport
                (congrArg EbnfExpr.star
                  bodyStatementStarSite_child_expression))
            exact (EbnfValue.star_of_view
              bodyStatementStarSite.child.expression tailAtStar).symm
      _ = EbnfValue.star (.atom (.nonterminal .statement))
          ((EbnfValue.starView
            bodyStatementStarSite.child.expression tailAtStar).map
              (EbnfValue.transport
                bodyStatementStarSite_child_expression)) :=
        EbnfValue.transport_star_eq_map_local
          bodyStatementStarSite_child_expression _
      _ = _ := congrArg
        (EbnfValue.star (.atom (.nonterminal .statement)))
        tailListSemantic
  let headAtomSite : AtomSite := {
    site := bodyStatementStarSite.child
    hasKind := by
      rw [bodyStatementStarSite_child_expression]
      rfl
  }
  have headAtomShape : headAtomSite.atom = .nonterminal .statement := by
    have expression := headAtomSite.expression_eq_atom
    change bodyStatementStarSite.child.expression =
      .atom headAtomSite.atom at expression
    exact EbnfExpr.atom.inj
      (expression.symm.trans bodyStatementStarSite_child_expression)
  have headProduction : head.raw.production = .atom headAtomSite :=
    production_atom_of_lhs_local headAtomSite head.raw.production (by
      simpa [headAtomSite] using headLhs)
  rcases head with
    ⟨⟨headProductionId, headDot, headStart, headFinish⟩,
      headGuardContext⟩
  simp only at headProduction
  subst headProductionId
  have headSemanticView : EbnfValue.transport
        (congrArg EbnfExpr.atom headAtomShape)
        (EbnfValue.atShape headAtomSite.expression_eq_atom
          (Eq.mp (congrArg (NonterminalValue file tokens) headLhs)
            headValue)) =
      EbnfValue.ruleAtom .statement headStatement := by
    have composed :
        headAtomSite.expression_eq_atom.trans
            (congrArg EbnfExpr.atom headAtomShape) =
          bodyStatementStarSite_child_expression :=
      Subsingleton.elim _ _
    unfold EbnfValue.atShape
    rw [EbnfValue.transport_trans, composed]
    exact headSemantic
  have headRootCoherent := coherentAtomRule_child
    (site := headAtomSite) (rule := .statement)
    headDot headStart headFinish headGuardContext
    headAtomShape (by intro impossible; cases impossible)
    headSemanticView headCoherent
  have tailLhsProof : tailLhs = by
      rw [tailProduction]
      rfl := Subsingleton.elim _ _
  rcases tail with
    ⟨⟨tailProductionId, tailDot, tailOrigin, tailCurrent⟩,
      tailGuardContext⟩
  simp only at tailProduction
  subst tailProductionId
  change tailCurrent = finish at tailFinish
  change headFinish = tailOrigin at headTail
  change tailGuardContext = .bracedBody regionStart at tailContext
  subst tailCurrent
  subst tailGuardContext
  have headOriginCanonical : headStart = origin := headOrigin
  have headFinishCanonical : headFinish = tailOrigin := headTail
  have headContextCanonical : headGuardContext = .bracedBody regionStart :=
    headContext
  subst headStart
  subst headFinish
  subst headGuardContext
  have tailLhsProofEq : tailLhs = rfl := Subsingleton.elim _ _
  dsimp only [tailEncoded] at tailSemantic
  rw [tailLhsProofEq] at tailSemantic
  change EbnfValue.atShape bodyStatementStarSite_expression tailValue = _
    at tailSemantic
  refine ⟨tailOrigin, tailBranch, tailDot, tailValue,
    headRootCoherent, tailCoherent, tailSemantic⟩

private theorem matchArmStar_atShape_eq_transport_local
    {file : WorkspaceFile} {tokens : List Token}
    (value : EbnfValue file tokens matchArmBodyStarSite.site.expression) :
    EbnfValue.atShape matchArmBodyStarSite_expression value =
      EbnfValue.transport
        (congrArg EbnfExpr.star matchArmBodyStarSite_child_expression)
        (EbnfValue.atShape matchArmBodyStarSite.expression_eq_star value) := by
  unfold EbnfValue.atShape
  rw [EbnfValue.transport_trans]

private theorem matchArmStar_branch_cons_of_semantic_cons
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {branch : NilConsBranch}
    {dot : Fin
      ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star matchArmBodyStarSite branch).lhs}
    (head : Statement) (tail : List Statement)
    (semantic : EbnfValue.atShape matchArmBodyStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        ((head :: tail).map (EbnfValue.ruleAtom .armStatement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star matchArmBodyStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := context
    } output) : branch = .cons := by
  cases branch with
  | cons => rfl
  | nil =>
      let item : ContextualItemKey tokens := {
        raw := {
          production := .star matchArmBodyStarSite .nil
          dot := dot
          origin := origin
          current := finish
        }
        context := context
      }
      change CoherentReduction file tokens memo correct final item output
        at coherent
      cases coherent with
      | reduce _ values _ reached complete coherentPrefix action =>
          have packedEq := actionReduces_eleven_shapes_exact.mp action
          change output = StarSite.pack matchArmBodyStarSite .nil _
            at packedEq
          have emptyAtShape : EbnfValue.atShape
                matchArmBodyStarSite.expression_eq_star output =
              EbnfValue.star matchArmBodyStarSite.child.expression [] := by
            rw [packedEq, StarSite.pack_nil_eq]
          have emptyCanonical : EbnfValue.atShape
                matchArmBodyStarSite_expression output =
              EbnfValue.star (.atom (.nonterminal .armStatement)) [] := by
            rw [matchArmStar_atShape_eq_transport_local output, emptyAtShape]
            simpa using EbnfValue.transport_star_eq_map_local
              matchArmBodyStarSite_child_expression
              ([] : List (EbnfValue file tokens
                matchArmBodyStarSite.child.expression))
          have listEq := EbnfValue.star_injective
            (.atom (.nonterminal .armStatement))
            (semantic.symm.trans emptyCanonical)
          simp at listEq

/-- One nonempty match-arm star step exposes the coherent arm-statement head
as a source statement and the coherent semantic tail at the exact split. -/
theorem coherentMatchArmStatementStar_cons_children
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish regionStart : Boundary tokens}
    {branch : NilConsBranch}
    {dot : Fin
      ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star matchArmBodyStarSite branch).lhs}
    (headStatement : Statement) (tailStatements : List Statement)
    (semantic : EbnfValue.atShape matchArmBodyStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        ((headStatement :: tailStatements).map
          (EbnfValue.ruleAtom .armStatement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star matchArmBodyStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := .armBody regionStart
    } output) :
    ∃ (split : Boundary tokens) (tailBranch : NilConsBranch)
      (tailDot : Fin
        ((ProductionId.star matchArmBodyStarSite tailBranch).rhs.length + 1))
      (tailValue : NonterminalValue file tokens
        (ProductionId.star matchArmBodyStarSite tailBranch).lhs),
      CoherentReduction file tokens memo correct final
        (CanonicalCompleteRootItem tokens .statement origin split
          (.armBody regionStart)) headStatement ∧
      CoherentReduction file tokens memo correct final {
        raw := {
          production := .star matchArmBodyStarSite tailBranch
          dot := tailDot
          origin := split
          current := finish
        }
        context := .armBody regionStart
      } tailValue ∧
      EbnfValue.atShape matchArmBodyStarSite_expression tailValue =
        EbnfValue.star (.atom (.nonterminal .armStatement))
          (tailStatements.map (EbnfValue.ruleAtom .armStatement)) := by
  have branchEq := matchArmStar_branch_cons_of_semantic_cons headStatement
    tailStatements semantic coherent
  subst branch
  rcases coherentStarCons_children dot origin finish
      (.armBody regionStart) coherent with
    ⟨head, tail, headValue, tailValue, tailBranch, headLhs, tailLhs,
      tailProduction, headOrigin, headTail, tailFinish, headContext,
      tailContext, headCoherent, tailCoherent, outputView⟩
  have transportedEq : EbnfValue.transport
        (congrArg EbnfExpr.star matchArmBodyStarSite_child_expression)
        (EbnfValue.atShape matchArmBodyStarSite.expression_eq_star output) =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        ((headStatement :: tailStatements).map
          (EbnfValue.ruleAtom .armStatement)) :=
    (matchArmStar_atShape_eq_transport_local output).symm.trans semantic
  rw [outputView,
    EbnfValue.transport_star_eq_map_local
      matchArmBodyStarSite_child_expression] at transportedEq
  have listEq := EbnfValue.star_injective
    (.atom (.nonterminal .armStatement)) transportedEq
  simp only [List.map_cons] at listEq
  have headSemantic := (List.cons.inj listEq).1
  have tailListSemantic := (List.cons.inj listEq).2
  let tailEncoded : EbnfValue file tokens
      matchArmBodyStarSite.site.expression :=
    Eq.mp (congrArg (NonterminalValue file tokens) tailLhs) tailValue
  have tailSemantic : EbnfValue.atShape
        matchArmBodyStarSite_expression tailEncoded =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        (tailStatements.map (EbnfValue.ruleAtom .armStatement)) := by
    rw [matchArmStar_atShape_eq_transport_local tailEncoded]
    let tailAtStar := EbnfValue.atShape
      matchArmBodyStarSite.expression_eq_star tailEncoded
    calc
      EbnfValue.transport
          (congrArg EbnfExpr.star
            matchArmBodyStarSite_child_expression) tailAtStar =
        EbnfValue.transport
          (congrArg EbnfExpr.star
            matchArmBodyStarSite_child_expression)
          (EbnfValue.star matchArmBodyStarSite.child.expression
            (EbnfValue.starView
              matchArmBodyStarSite.child.expression tailAtStar)) := by
            apply congrArg
              (EbnfValue.transport
                (congrArg EbnfExpr.star
                  matchArmBodyStarSite_child_expression))
            exact (EbnfValue.star_of_view
              matchArmBodyStarSite.child.expression tailAtStar).symm
      _ = EbnfValue.star (.atom (.nonterminal .armStatement))
          ((EbnfValue.starView
            matchArmBodyStarSite.child.expression tailAtStar).map
              (EbnfValue.transport
                matchArmBodyStarSite_child_expression)) :=
        EbnfValue.transport_star_eq_map_local
          matchArmBodyStarSite_child_expression _
      _ = _ := congrArg
        (EbnfValue.star (.atom (.nonterminal .armStatement)))
        tailListSemantic
  let headAtomSite : AtomSite := {
    site := matchArmBodyStarSite.child
    hasKind := by
      rw [matchArmBodyStarSite_child_expression]
      rfl
  }
  have headAtomShape : headAtomSite.atom =
      .nonterminal .armStatement := by
    have expression := headAtomSite.expression_eq_atom
    change matchArmBodyStarSite.child.expression =
      .atom headAtomSite.atom at expression
    exact EbnfExpr.atom.inj
      (expression.symm.trans matchArmBodyStarSite_child_expression)
  have headProduction : head.raw.production = .atom headAtomSite :=
    production_atom_of_lhs_local headAtomSite head.raw.production (by
      simpa [headAtomSite] using headLhs)
  rcases head with
    ⟨⟨headProductionId, headDot, headStart, headFinish⟩,
      headGuardContext⟩
  simp only at headProduction
  subst headProductionId
  have headSemanticView : EbnfValue.transport
        (congrArg EbnfExpr.atom headAtomShape)
        (EbnfValue.atShape headAtomSite.expression_eq_atom
          (Eq.mp (congrArg (NonterminalValue file tokens) headLhs)
            headValue)) =
      EbnfValue.ruleAtom .armStatement headStatement := by
    have composed :
        headAtomSite.expression_eq_atom.trans
            (congrArg EbnfExpr.atom headAtomShape) =
          matchArmBodyStarSite_child_expression :=
      Subsingleton.elim _ _
    unfold EbnfValue.atShape
    rw [EbnfValue.transport_trans, composed]
    exact headSemantic
  have headArmCoherent := coherentAtomRule_child
    (site := headAtomSite) (rule := .armStatement)
    headDot headStart headFinish headGuardContext
    headAtomShape (by decide) headSemanticView headCoherent
  have headRootCoherent :=
    coherentArmStatement_statement_child headArmCoherent
  rcases tail with
    ⟨⟨tailProductionId, tailDot, tailOrigin, tailCurrent⟩,
      tailGuardContext⟩
  simp only at tailProduction
  subst tailProductionId
  change tailCurrent = finish at tailFinish
  change headFinish = tailOrigin at headTail
  change tailGuardContext = .armBody regionStart at tailContext
  subst tailCurrent
  subst tailGuardContext
  have headOriginCanonical : headStart = origin := headOrigin
  have headFinishCanonical : headFinish = tailOrigin := headTail
  have headContextCanonical : headGuardContext = .armBody regionStart :=
    headContext
  subst headStart
  subst headFinish
  subst headGuardContext
  have tailLhsProofEq : tailLhs = rfl := Subsingleton.elim _ _
  dsimp only [tailEncoded] at tailSemantic
  rw [tailLhsProofEq] at tailSemantic
  change EbnfValue.atShape matchArmBodyStarSite_expression tailValue = _
    at tailSemantic
  exact ⟨tailOrigin, tailBranch, tailDot, tailValue,
    headRootCoherent, tailCoherent, tailSemantic⟩

private theorem coherentMatchArmStatementStar_cons_enabled
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish regionStart : Boundary tokens}
    {branch : NilConsBranch}
    {dot : Fin
      ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star matchArmBodyStarSite branch).lhs}
    (headStatement : Statement) (tailStatements : List Statement)
    (semantic : EbnfValue.atShape matchArmBodyStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        ((headStatement :: tailStatements).map
          (EbnfValue.ruleAtom .armStatement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star matchArmBodyStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := .armBody regionStart
    } output) :
    EnabledProductionInstance file tokens memo correct final {
      production := .star matchArmBodyStarSite .cons
      origin := origin
      context := .armBody regionStart
    } := by
  have branchEq := matchArmStar_branch_cons_of_semantic_cons headStatement
    tailStatements semantic coherent
  subst branch
  cases coherent with
  | reduce _ _ _ reached _ _ _ =>
      exact reached.enabledProductionInstance

/-- Every coherent semantic match-arm statement list satisfies the same G08
nonfinal terminator invariant as a braced body. -/
private theorem coherentMatchArmStatementStar_positions
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish regionStart : Boundary tokens}
    {branch : NilConsBranch}
    {dot : Fin
      ((ProductionId.star matchArmBodyStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star matchArmBodyStarSite branch).lhs}
    (afterArrow : ∃ arrowCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .fatArrow arrowCursor regionStart)
    (statements : List Statement)
    (semantic : EbnfValue.atShape matchArmBodyStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .armStatement))
        (statements.map (EbnfValue.ruleAtom .armStatement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star matchArmBodyStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := .armBody regionStart
    } output) :
    StatementListPositionCoherent statements := by
  induction statements generalizing origin branch dot output with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => trivial
      | cons second rest =>
          rcases coherentMatchArmStatementStar_cons_children head
              (second :: rest) semantic coherent with
            ⟨split, tailBranch, tailDot, tailValue, headCoherent,
              tailCoherent, tailSemantic⟩
          change head.ValidBeforeListEnd ∧
            StatementListPositionCoherent (second :: rest)
          constructor
          · rcases head with ⟨headSpan, headPayload⟩
            cases headPayload <;> try trivial
            case expression expression terminator =>
              cases terminator with
              | some semicolon => trivial
              | none =>
                  have terminalCoherent :=
                    coherentStatement_terminalExpression_child headCoherent
                  have nearest :=
                    expressionStatementTerminal_nearestStatementRegion
                      regionStart (Or.inr rfl) terminalCoherent
                  rcases nearestStatementRegion_arm_local afterArrow nearest
                    with
                    ⟨arrowCursor, openCursor, closeCursor, arrowAfter,
                      frame, next⟩
                  rcases coherentMatchArmStatementStar_cons_children second
                      rest tailSemantic tailCoherent with
                    ⟨secondFinish, restBranch, restDot, restValue,
                      secondCoherent, restCoherent, restSemantic⟩
                  rcases next.2.2.2.1 with atClose | header
                  · have depth :=
                      coherentStatement_sameDelimiterDepth_local
                        secondCoherent
                    have later := coherentStatement_progress_local
                      secondCoherent
                    have matching := frame.1.2.2
                    rw [atClose] at depth later
                    exact False.elim
                      (matchingRightBrace_excludes_sameDepth_later_local
                        matching depth later)
                  · have tailEnabled :=
                      coherentMatchArmStatementStar_cons_enabled second rest
                        tailSemantic tailCoherent
                    have member :
                        (.G02_matchArmBoundary, .negative) ∈
                          guardOf
                            (ProductionId.star matchArmBodyStarSite .cons) := by
                      simp [guardOf, matchArmBodyStarSite_key,
                        GrammarSite.isAt]
                    exact False.elim
                      (enabledG02Negative_excludes_armHeader
                        {
                          production := .star matchArmBodyStarSite .cons
                          origin := split
                          context := .armBody regionStart
                        }
                        regionStart rfl tailEnabled member header)
          · exact inductionHypothesis tailSemantic tailCoherent

/-- Every coherent semantic body-star list satisfies the nonfinal-statement
terminator invariant enforced by G08. -/
private theorem coherentBodyStatementStar_positions
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish regionStart : Boundary tokens}
    {branch : NilConsBranch}
    {dot : Fin ((ProductionId.star bodyStatementStarSite branch).rhs.length + 1)}
    {output : NonterminalValue file tokens
      (ProductionId.star bodyStatementStarSite branch).lhs}
    (afterOpen : ∃ openCursor : Boundary tokens,
      ImmediatelyAfterSymbol file tokens .leftBrace openCursor regionStart)
    (statements : List Statement)
    (semantic : EbnfValue.atShape bodyStatementStarSite_expression output =
      EbnfValue.star (.atom (.nonterminal .statement))
        (statements.map (EbnfValue.ruleAtom .statement)))
    (coherent : CoherentReduction file tokens memo correct final {
      raw := {
        production := .star bodyStatementStarSite branch
        dot := dot
        origin := origin
        current := finish
      }
      context := .bracedBody regionStart
    } output) :
    StatementListPositionCoherent statements := by
  induction statements generalizing origin branch dot output with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => trivial
      | cons second rest =>
          rcases coherentBodyStatementStar_cons_children head
              (second :: rest) semantic coherent with
            ⟨split, tailBranch, tailDot, tailValue, headCoherent,
              tailCoherent, tailSemantic⟩
          change head.ValidBeforeListEnd ∧
            StatementListPositionCoherent (second :: rest)
          constructor
          · rcases head with ⟨headSpan, headPayload⟩
            cases headPayload <;> try trivial
            case expression expression terminator =>
              cases terminator with
              | some semicolon => trivial
              | none =>
                  have terminalCoherent :=
                    coherentStatement_terminalExpression_child headCoherent
                  have nearest :=
                    expressionStatementTerminal_nearestStatementRegion
                      regionStart (Or.inl rfl) terminalCoherent
                  rcases nearestStatementRegion_braced_local afterOpen nearest
                    with ⟨closeCursor, matching⟩
                  rcases coherentBodyStatementStar_cons_children second rest
                      tailSemantic tailCoherent with
                    ⟨secondFinish, restBranch, restDot, restValue,
                      secondCoherent, restCoherent, restSemantic⟩
                  have depth :=
                    coherentStatement_sameDelimiterDepth_local secondCoherent
                  have later := coherentStatement_progress_local
                    secondCoherent
                  exact False.elim
                    (matchingRightBrace_excludes_sameDepth_later_local
                      matching depth later)
          · exact inductionHypothesis tailSemantic tailCoherent

/-- The one parser-specific obligation left by the generic body token proof:
every nonfinal coherent braced-body statement obeys G08's terminator policy. -/
def CoherentBodyStatementPositions : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .body origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .body origin finish context).raw)
    (_owned : TokensOwnedBy file tokens)
    (_lexicallyExact : TokensLexicallyExact file tokens)
    (_coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .body origin finish context)
        priorValues)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish),
    RootAction.unpack .body
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .body origin finish context)
          complete priorValues) =
      RuleReduction.inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          witness) →
      StatementListPositionCoherent statements

/-- Coherence itself discharges the body statement-position obligation: a
semicolon-free expression statement cannot precede another statement. -/
theorem coherentBodyStatementPositions :
    CoherentBodyStatementPositions := by
  intro file tokens memo correct final origin finish context priorValues
    complete owned lexicallyExact coherentPrefix openBrace statements
    closeBrace witness inputEq
  rcases coherentBodyStatementStar_of_coherentRoot complete coherentPrefix
      openBrace statements closeBrace witness inputEq with
    ⟨branch, starDot, starOrigin, starFinish, starValue, starCoherent,
      starSemantic, afterOpen, starOrdered, starBounded⟩
  exact coherentBodyStatementStar_positions afterOpen statements
    starSemantic starCoherent

/-- The parser-specific statement-position obligation for one completed match
arm: every semicolon-free expression statement must be the arm's final
statement. -/
def CoherentMatchArmStatementPositions : Prop :=
  ∀ {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalCompleteRootItem tokens .matchArm origin finish context)}
    (complete : CompleteItem
      (CanonicalCompleteRootItem tokens .matchArm origin finish context).raw)
    (_owned : TokensOwnedBy file tokens)
    (_lexicallyExact : TokensLexicallyExact file tokens)
    (_coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalCompleteRootItem tokens .matchArm origin finish context)
        priorValues)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish),
    RootAction.unpack .matchArm
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .matchArm origin finish context)
          complete priorValues) =
      RuleReduction.inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow statements
          witness) →
      StatementListPositionCoherent statements

/-- Coherence and G08 discharge the statement-position obligation for match
arms, including the distinct next-arm boundary guarded by G02. -/
theorem coherentMatchArmStatementPositions :
    CoherentMatchArmStatementPositions := by
  intro file tokens memo correct final origin finish context priorValues
    complete owned lexicallyExact coherentPrefix pipe patterns fatArrow
    statements witness inputEq
  rcases coherentMatchArmStatementStar_of_coherentRoot complete coherentPrefix
      pipe patterns fatArrow statements witness inputEq with
    ⟨branch, starDot, starOrigin, starFinish, starValue, starCoherent,
      starSemantic, afterArrow⟩
  exact coherentMatchArmStatementStar_positions afterArrow statements
    starSemantic starCoherent

/-- Discharging the shared G08 statement-position obligation is sufficient
to obtain coherent exact-token soundness for braced bodies. -/
theorem body_coherentTokenPlanSound_of_statementPositions
    (positions : CoherentBodyStatementPositions) :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout .body := by
  intro file tokens memo correct final origin finish context priorValues output
    complete owned lexicallyExact coherentPrefix reduces inputEvidence
  have rootInputEvidence : TokenPlanEvidence
      ((RootAction.unpack .body
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .body origin finish context)
          complete priorValues)).tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish) := by
    apply inputEvidence.candidate_eq
    symm
    rw [RootAction.unpack_tokenPlan?]
    simpa only [CanonicalCompleteRootItem] using
      (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
        (CanonicalCompleteRootItem tokens .body origin finish context)
        complete priorValues)
  let rootInput := RootAction.unpack .body
    (PrefixValues.fullValue
      (CanonicalCompleteRootItem tokens .body origin finish context)
      complete priorValues)
  change RuleReduction file tokens .body origin finish rootInput output
    at reduces
  change TokenPlanEvidence
    (rootInput.tokenPlan? sourceRuleTokenPlanLayout)
    (PhysicalTokens tokens origin finish) at rootInputEvidence
  generalize inputEq : rootInput = sourceInput at reduces rootInputEvidence
  cases reduces with
  | body origin finish openBrace statements closeBrace witness =>
      have positioned : StatementListPositionCoherent statements := by
        apply positions complete owned lexicallyExact coherentPrefix
          openBrace statements closeBrace witness
        exact inputEq
      have sourceEvidence := rootInputEvidence.candidate_eq
        (bodyInput_tokenPlan? openBrace statements closeBrace)
      cases plansEq : statements.mapM (statementTokenPlan? true) with
      | none =>
          simp [plansEq, TokenPlanEvidence] at sourceEvidence
      | some statementPlans =>
          simp only [plansEq] at sourceEvidence
          let inner := TokenPlan.concat [
            TokenPlan.exact (.symbol .leftBrace) openBrace.span,
            TokenPlan.concat statementPlans,
            TokenPlan.exact (.symbol .rightBrace) closeBrace.span]
          change TokenPlanEvidence (some inner)
            (PhysicalTokens tokens origin finish) at sourceEvidence
          have innerAnchored : inner.WellAnchored := by
            dsimp only [inner]
            simpa using TokenPlan.WellAnchored.concatExactBookended
              (.symbol .leftBrace) openBrace.span
              (.symbol .rightBrace) closeBrace.span
              [TokenPlan.concat statementPlans]
          have enclosed := TokenPlanEvidence.enclose sourceEvidence
            (fun plan success => by
              simp only [Option.some.injEq] at success
              subst plan
              exact innerAnchored)
            witness.consumed
          have positionalEq := statementTokenPlans?_of_mapM_allowTerminal
            statements statementPlans positioned plansEq
          apply enclosed.candidate_eq
          change (some inner).map (TokenPlan.enclose witness.span) =
            ruleTokenPlan? .body
              (sourceLoc witness {
                origin := BodyOrigin.braced openBrace.span closeBrace.span
                statements := statements
              })
          rw [ruleTokenPlan?_body]
          rw [bracedBodyTokenPlan?_sourceLoc openBrace statements closeBrace
            statementPlans positionalEq witness]
          rfl

/-- Every coherent braced-body reduction preserves its exact source token
plan, including G08's nonfinal-statement terminator policy. -/
theorem body_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout .body :=
  body_coherentTokenPlanSound_of_statementPositions
    coherentBodyStatementPositions

private theorem TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
    {plan : TokenPlan} {span : SourceSpan}
    (nonempty : plan.slots ≠ []) :
    (plan.enclose span).slots ≠ [] := by
  intro empty
  have lengthEq := congrArg List.length empty
  rw [enclose_slots_length] at lengthEq
  cases slotsEq : plan.slots with
  | nil => exact nonempty slotsEq
  | cons first rest => simp [slotsEq] at lengthEq

private theorem bracedBodyTokenPlan_nonempty_statementRegionsLocal
    (body : Body) (plan : TokenPlan)
    (success : bodyTokenPlan? .braced body = some plan) :
    plan.slots ≠ [] := by
  rcases body with ⟨span, ⟨origin, statements⟩⟩
  cases origin with
  | matchArm arrow => simp [bodyTokenPlan?] at success
  | braced openBrace closeBrace =>
      rw [bodyTokenPlan?] at success
      cases plansEq : statementTokenPlans? statements with
      | none => simp [plansEq] at success
      | some plans =>
          simp [plansEq, bracedBodyPlanWith?] at success
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.concat, TokenPlan.append, TokenPlan.exact]

private theorem assignmentOperatorTokenPlan_wellAnchored_statementRegionsLocal
    (operator : Located AssignmentOperator) :
    (assignmentOperatorTokenPlan operator).WellAnchored := by
  rcases operator with ⟨span, payload⟩
  cases payload <;> exact TokenPlan.WellAnchored.exact _ _

private theorem statementTokenPlan_true_wellAnchored_statementRegionsLocal
    (statement : Statement) (plan : TokenPlan)
    (success : statementTokenPlan? true statement = some plan) :
    plan.WellAnchored := by
  rcases statement with ⟨span, payload⟩
  cases payload with
  | assignment operator left right =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftPlan, leftEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightPlan, rightEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat
      intro candidate member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact expressionTokenPlanAt?_wellAnchored .annotation left _ leftEq
      · exact assignmentOperatorTokenPlan_wellAnchored_statementRegionsLocal operator
      · exact expressionTokenPlanAt?_wellAnchored .annotation right _ rightEq
      · exact TokenPlan.WellAnchored.plain _
  | letBinding binding =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bindingPlan, bindingEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (TokenPlan.WellAnchored.append
          (letBindingTokenPlan?_wellAnchored binding bindingPlan bindingEq)
          (TokenPlan.WellAnchored.plain _)) span
  | block body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (bracedBodyTokenPlan?_wellAnchored body bodyPlan bodyEq) span
  | expression expression terminator =>
      cases terminator with
      | none =>
          simp only [statementTokenPlan?, if_true] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact TokenPlan.WellAnchored.enclose
            (expressionTokenPlanAt?_wellAnchored .annotation expression
              expressionPlan expressionEq) span
      | some semicolon =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact TokenPlan.WellAnchored.enclose
            (TokenPlan.WellAnchored.append
              (expressionTokenPlanAt?_wellAnchored .annotation expression
                expressionPlan expressionEq)
              (TokenPlan.WellAnchored.exact _ _)) span
  | «return» value terminator =>
      cases value with
      | none =>
          simp [statementTokenPlan?] at success
          subst plan
          apply TokenPlan.WellAnchored.enclose
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain _)
            (TokenPlan.WellAnchored.exact _ _)
      | some expression =>
          simp [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.WellAnchored.enclose
          exact TokenPlan.WellAnchored.append
            (TokenPlan.WellAnchored.plain _)
            (TokenPlan.WellAnchored.append
              (expressionTokenPlanAt?_wellAnchored .annotation expression
                expressionPlan expressionEq)
              (TokenPlan.WellAnchored.exact _ _))
  | «match» scrutinees arms terminator =>
      simp only [statementTokenPlan?.eq_def] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨scrutineePlans, scrutineeEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨armPlans, armEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      cases terminator with
      | none =>
          simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
            TokenPlan.WellAnchored.concatPlainBookended
              (.hardKeyword .matchKw) (.symbol .rightBrace)
              [.commaSeparated scrutineePlans,
                .plain (.symbol .leftBrace), .concat armPlans]
      | some semicolon =>
          apply TokenPlan.WellAnchored.of_starts_ends_append
            (left := TokenPlan.plain (.hardKeyword .matchKw))
            (right := TokenPlan.concat [
              .commaSeparated scrutineePlans,
              .plain (.symbol .leftBrace), .concat armPlans,
              .plain (.symbol .rightBrace), .exact (.symbol .semicolon) semicolon])
          · exact TokenPlan.WellAnchored.StartsRequired.concat_plain_first _ []
          · exact TokenPlan.WellAnchored.EndsRequired.concat_exact_last
              [.commaSeparated scrutineePlans,
                .plain (.symbol .leftBrace), .concat armPlans,
                .plain (.symbol .rightBrace)] _ _
  | assembly slice =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat
      intro candidate member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact TokenPlan.WellAnchored.plain _
      · exact TokenPlan.WellAnchored.exact _ _
  | ifThenElse condition thenBody elseBody =>
      cases elseBody with
      | none =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.WellAnchored.enclose
          simpa [TokenPlan.concat, TokenPlan.append, TokenPlan.empty] using
            TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.plain (.hardKeyword .ifKw))
              (TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.parens conditionPlan)
                (bracedBodyTokenPlan?_wellAnchored thenBody thenPlan thenEq))
      | some elseBody =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨elsePlan, elseEq, resultEq⟩
          have thenAnchored :=
            bracedBodyTokenPlan?_wellAnchored thenBody thenPlan thenEq
          have elseAnchored :=
            bracedBodyTokenPlan?_wellAnchored elseBody elsePlan elseEq
          injection resultEq with planEq
          subst plan
          apply TokenPlan.WellAnchored.enclose
          apply TokenPlan.WellAnchored.concat
          intro candidate member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl
          · exact TokenPlan.WellAnchored.plain _
          · exact TokenPlan.WellAnchored.parens _
          · exact thenAnchored
          · exact TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.plain _)
              elseAnchored
  | forLoop initializers condition post body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨initializerPlans, initializerEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨conditionPlan, conditionEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨postPlans, postEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      have conditionAnchored :=
        expressionTokenPlanAt?_wellAnchored .annotation condition
          conditionPlan conditionEq
      have bodyAnchored :=
        bracedBodyTokenPlan?_wellAnchored body bodyPlan bodyEq
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      apply TokenPlan.WellAnchored.concat
      intro candidate member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact TokenPlan.WellAnchored.plain _
      · exact TokenPlan.WellAnchored.plain _
      · exact TokenPlan.WellAnchored.commaSeparated _
          (forInitTokenPlans?_allWellAnchored initializers initializerPlans
            initializerEq)
      · exact TokenPlan.WellAnchored.plain _
      · exact conditionAnchored
      · exact TokenPlan.WellAnchored.plain _
      · exact TokenPlan.WellAnchored.commaSeparated _
          (forPostTokenPlans?_allWellAnchored post postPlans postEq)
      · exact TokenPlan.WellAnchored.plain _
      · exact bodyAnchored
  | «break» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.concat _ (by
        intro candidate member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact TokenPlan.WellAnchored.plain _
        · exact TokenPlan.WellAnchored.exact _ _)
  | «continue» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.WellAnchored.enclose
      exact TokenPlan.WellAnchored.concat _ (by
        intro candidate member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact TokenPlan.WellAnchored.plain _
        · exact TokenPlan.WellAnchored.exact _ _)

private theorem statementTokenPlan_true_nonempty_statementRegionsLocal
    (statement : Statement) (plan : TokenPlan)
    (success : statementTokenPlan? true statement = some plan) :
    plan.slots ≠ [] := by
  rcases statement with ⟨span, payload⟩
  cases payload with
  | assignment operator left right =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftPlan, leftEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightPlan, rightEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]
  | letBinding binding =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bindingPlan, bindingEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.append, TokenPlan.plain]
  | block body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      have bodyNonempty := bracedBodyTokenPlan_nonempty_statementRegionsLocal body bodyPlan bodyEq
      injection resultEq with planEq
      subst plan
      exact TokenPlan.enclose_slots_ne_nil_statementRegionsLocal bodyNonempty
  | expression expression terminator =>
      cases terminator with
      | none =>
          simp only [statementTokenPlan?, if_true] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          have encloses := expressionTokenPlanAt?_encloses .annotation
            expression expressionPlan expressionEq
          rcases encloses with ⟨core, planEq, coreNonempty⟩
          subst expressionPlan
          injection resultEq with resultPlanEq
          subst plan
          exact TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
            (TokenPlan.enclose_slots_ne_nil_statementRegionsLocal coreNonempty)
      | some semicolon =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.append, TokenPlan.exact]
  | «return» value terminator =>
      cases value with
      | none =>
          simp [statementTokenPlan?] at success
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.append, TokenPlan.plain]
      | some expression =>
          simp [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.append, TokenPlan.plain]
  | «match» scrutinees arms terminator =>
      simp only [statementTokenPlan?.eq_def] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨scrutineePlans, scrutineeEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨armPlans, armEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]
  | assembly slice =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]
  | ifThenElse condition thenBody elseBody =>
      cases elseBody with
      | none =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.concat, TokenPlan.plain]
      | some elseBody =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨elsePlan, elseEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
          simp [TokenPlan.concat, TokenPlan.append, TokenPlan.plain]
  | forLoop initializers condition post body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨initializerPlans, initializerEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨conditionPlan, conditionEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨postPlans, postEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]
  | «break» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]
  | «continue» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      apply TokenPlan.enclose_slots_ne_nil_statementRegionsLocal
      simp [TokenPlan.concat, TokenPlan.plain]

private theorem statementTokenPlan_true_encloses_statementRegionsLocal
    (statement : Statement) (plan : TokenPlan)
    (success : statementTokenPlan? true statement = some plan) :
    ∃ inner : TokenPlan, plan = inner.enclose statement.span := by
  rcases statement with ⟨span, payload⟩
  cases payload with
  | assignment operator left right =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftPlan, leftEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightPlan, rightEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact ⟨.concat [leftPlan, assignmentOperatorTokenPlan operator,
        rightPlan, .plain (.symbol .semicolon)], rfl⟩
  | letBinding binding =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bindingPlan, bindingEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact ⟨.append bindingPlan (.plain (.symbol .semicolon)), rfl⟩
  | block body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact ⟨bodyPlan, rfl⟩
  | expression expression terminator =>
      cases terminator with
      | none =>
          simp only [statementTokenPlan?, if_true] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact ⟨expressionPlan, rfl⟩
      | some semicolon =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact ⟨.append expressionPlan (.exact (.symbol .semicolon)
            semicolon), rfl⟩
  | «return» value terminator =>
      cases value with
      | none =>
          simp [statementTokenPlan?] at success
          subst plan
          exact ⟨.concat [.plain (.hardKeyword .returnKw), .empty,
            .exact (.symbol .semicolon) terminator], rfl⟩
      | some expression =>
          simp [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨expressionPlan, expressionEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact ⟨.concat [.plain (.hardKeyword .returnKw), expressionPlan,
            .exact (.symbol .semicolon) terminator], rfl⟩
  | «match» scrutinees arms terminator =>
      simp only [statementTokenPlan?.eq_def] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨scrutineePlans, scrutineeEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨armPlans, armEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      cases terminator with
      | none =>
          exact ⟨.concat [.plain (.hardKeyword .matchKw),
            .commaSeparated scrutineePlans, .plain (.symbol .leftBrace),
            .concat armPlans, .plain (.symbol .rightBrace), .empty], rfl⟩
      | some semicolon =>
          exact ⟨.concat [.plain (.hardKeyword .matchKw),
            .commaSeparated scrutineePlans, .plain (.symbol .leftBrace),
            .concat armPlans, .plain (.symbol .rightBrace),
            .exact (.symbol .semicolon) semicolon], rfl⟩
  | assembly slice =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      exact ⟨.concat [.plain (.hardKeyword .assemblyKw),
        .exact (.assemblyBlock slice) slice.span], rfl⟩
  | ifThenElse condition thenBody elseBody =>
      cases elseBody with
      | none =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact ⟨.concat [.plain (.hardKeyword .ifKw),
            .parens conditionPlan, thenPlan, .empty], rfl⟩
      | some elseBody =>
          simp only [statementTokenPlan?] at success
          rcases Option.bind_eq_some_iff.mp success with
            ⟨conditionPlan, conditionEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨thenPlan, thenEq, success⟩
          rcases Option.bind_eq_some_iff.mp success with
            ⟨elsePlan, elseEq, resultEq⟩
          injection resultEq with planEq
          subst plan
          exact ⟨.concat [.plain (.hardKeyword .ifKw),
            .parens conditionPlan, thenPlan,
            .append (.plain (.hardKeyword .elseKw)) elsePlan], rfl⟩
  | forLoop initializers condition post body =>
      simp only [statementTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨initializerPlans, initializerEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨conditionPlan, conditionEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨postPlans, postEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bodyPlan, bodyEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact ⟨.concat [.plain (.hardKeyword .forKw),
        .plain (.symbol .leftParen), .commaSeparated initializerPlans,
        .plain (.symbol .semicolon), conditionPlan,
        .plain (.symbol .semicolon), .commaSeparated postPlans,
        .plain (.symbol .rightParen), bodyPlan], rfl⟩
  | «break» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      exact ⟨.concat [.plain (.hardKeyword .breakKw),
        .exact (.symbol .semicolon) terminator], rfl⟩
  | «continue» terminator =>
      simp only [statementTokenPlan?, Option.some.injEq] at success
      subst plan
      exact ⟨.concat [.plain (.hardKeyword .continueKw),
        .exact (.symbol .semicolon) terminator], rfl⟩

private theorem statementPlan_matches_endpoints_statementRegionsLocal
    (statement : Statement) (plan : TokenPlan)
    (success : statementTokenPlan? true statement = some plan)
    {actual : List Token}
    (relation : TokenSlot.ListMatches plan.slots actual) :
    TokenSlot.FirstSatisfies (.starts statement.span) actual ∧
      TokenSlot.LastSatisfies (.ends statement.span) actual := by
  have anchored := statementTokenPlan_true_wellAnchored_statementRegionsLocal
    statement plan success
  have nonempty := statementTokenPlan_true_nonempty_statementRegionsLocal
    statement plan success
  rcases statementTokenPlan_true_encloses_statementRegionsLocal statement plan success with
    ⟨inner, planEq⟩
  subst plan
  exact listMatches_enclose_endpoints anchored nonempty relation

private theorem TokenSlot.FirstSatisfies.append_statementRegionsLocal
    {constraint : TokenSpanConstraint} {left right : List Token}
    (satisfies : TokenSlot.FirstSatisfies constraint left) :
    TokenSlot.FirstSatisfies constraint (left ++ right) := by
  cases left with
  | nil => contradiction
  | cons head tail => exact satisfies

private theorem TokenSlot.LastSatisfies.prepend_statementRegionsLocal
    {constraint : TokenSpanConstraint} {left right : List Token}
    (satisfies : TokenSlot.LastSatisfies constraint right) :
    TokenSlot.LastSatisfies constraint (left ++ right) := by
  induction left with
  | nil => exact satisfies
  | cons head tail induction =>
      cases right with
      | nil => contradiction
      | cons next rest =>
          cases tail with
          | nil => exact satisfies
          | cons second remaining => exact induction

@[simp] private theorem List.getLastD_cons_statementRegionsLocal {alpha : Type}
    (fallback head : alpha) (tail : List alpha) :
    (head :: tail).getLastD fallback = tail.getLastD head := by
  cases tail <;> simp [List.getLastD]

private theorem statementPlanList_matches_endpoints_statementRegionsLocal
    (first : Statement) (rest : List Statement) (plans : List TokenPlan)
    (success : (first :: rest).mapM (statementTokenPlan? true) = some plans)
    {actual : List Token}
    (relation : TokenSlot.ListMatches (TokenPlan.concat plans).slots actual) :
    TokenSlot.FirstSatisfies (.starts first.span) actual ∧
      TokenSlot.LastSatisfies (.ends (rest.getLastD first).span) actual := by
  induction rest generalizing first plans actual with
  | nil =>
      simp only [List.mapM_cons, List.mapM_nil] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPlan, headEq, resultEq⟩
      injection resultEq with plansEq
      subst plans
      have headEndpoints := statementPlan_matches_endpoints_statementRegionsLocal
        first headPlan headEq
          (actual := actual)
          (by simpa [TokenPlan.concat, TokenPlan.append] using relation)
      simpa using headEndpoints
  | cons second tail induction =>
      simp only [List.mapM_cons] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPlan, headEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tailPlans, tailEq, resultEq⟩
      injection resultEq with plansEq
      subst plans
      have normalized : TokenSlot.ListMatches
          (headPlan.append (TokenPlan.concat tailPlans)).slots actual := by
        simpa [TokenPlan.concat, TokenPlan.append] using relation
      rcases normalized.split_append with
        ⟨headActual, tailActual, actualEq, headRelation, tailRelation⟩
      rw [actualEq]
      have headEndpoints := statementPlan_matches_endpoints_statementRegionsLocal
        first headPlan headEq headRelation
      have tailSuccess : (second :: tail).mapM (statementTokenPlan? true) =
          some tailPlans := by
        simpa only [List.mapM_cons] using tailEq
      have tailEndpoints := induction second tailPlans tailSuccess tailRelation
      constructor
      · exact TokenSlot.FirstSatisfies.append_statementRegionsLocal headEndpoints.1
      · rw [List.getLastD_cons_statementRegionsLocal]
        exact TokenSlot.LastSatisfies.prepend_statementRegionsLocal
          (left := headActual) tailEndpoints.2

private theorem statementTokenPlans_true_allWellAnchored_statementRegionsLocal
    (statements : List Statement) (plans : List TokenPlan)
    (success : statements.mapM (statementTokenPlan? true) = some plans) :
    ∀ plan ∈ plans, plan.WellAnchored := by
  induction statements generalizing plans with
  | nil =>
      simp at success
      subst plans
      simp
  | cons head tail induction =>
      simp only [List.mapM_cons] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPlan, headEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tailPlans, tailEq, resultEq⟩
      have headAnchored :=
        statementTokenPlan_true_wellAnchored_statementRegionsLocal head headPlan headEq
      injection resultEq with plansEq
      subst plans
      intro plan member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact headAnchored
      · have tailSuccess : tail.mapM (statementTokenPlan? true) =
            some tailPlans := by
          simpa only using tailEq
        exact induction tailPlans tailSuccess plan member

private def TokensHaveSourceStatementRegionsLocal
    (source : SourceId) (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.span.source = source

private theorem physicalTokens_haveSource_statementRegionsLocal
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (owned : TokensOwnedBy file tokens) :
    TokensHaveSourceStatementRegionsLocal file.id (PhysicalTokens tokens origin finish) := by
  intro token member
  apply (owned token ?_).1
  unfold PhysicalTokens at member
  exact List.mem_of_mem_drop (List.mem_of_mem_take member)

private theorem TokensHaveSourceStatementRegionsLocal.of_append_right
    {source : SourceId} {left right : List Token}
    (all : TokensHaveSourceStatementRegionsLocal source (left ++ right)) :
    TokensHaveSourceStatementRegionsLocal source right := by
  intro token member
  exact all token (List.mem_append_right left member)

private theorem firstSatisfies_between_statementRegionsLocal
    {file : WorkspaceFile} {leftSpan rightSpan : SourceSpan}
    {actual : List Token}
    (sources : TokensHaveSourceStatementRegionsLocal file.id actual)
    (starts : TokenSlot.FirstSatisfies (.starts leftSpan) actual) :
    TokenSlot.FirstSatisfies
      (.starts (RuleReduction.between file leftSpan rightSpan ()).span)
      actual := by
  cases actual with
  | nil => contradiction
  | cons first rest =>
      exact ⟨sources first (by simp), starts.2⟩

private theorem lastSatisfies_between_statementRegionsLocal
    {file : WorkspaceFile} {leftSpan rightSpan : SourceSpan}
    {actual : List Token}
    (sources : TokensHaveSourceStatementRegionsLocal file.id actual)
    (ends : TokenSlot.LastSatisfies (.ends rightSpan) actual) :
    TokenSlot.LastSatisfies
      (.ends (RuleReduction.between file leftSpan rightSpan ()).span)
      actual := by
  induction actual with
  | nil => contradiction
  | cons first rest induction =>
      cases rest with
      | nil => exact ⟨sources first (by simp), ends.2⟩
      | cons next rest =>
          exact induction
            (by
              intro token member
              exact sources token (by simp [member]))
            ends

/-- Every coherent match-arm reduction preserves its exact source token plan,
including the G08 policy for all statements in the arm body. -/
theorem matchArm_coherentTokenPlanSound :
    CoherentGrammarRuleTokenPlanSound sourceRuleTokenPlanLayout .matchArm := by
  intro file tokens memo correct final origin finish context priorValues output
    complete owned lexicallyExact coherentPrefix reduces inputEvidence
  have rootInputEvidence : TokenPlanEvidence
      ((RootAction.unpack .matchArm
        (PrefixValues.fullValue
          (CanonicalCompleteRootItem tokens .matchArm origin finish context)
          complete priorValues)).tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish) := by
    apply inputEvidence.candidate_eq
    symm
    rw [RootAction.unpack_tokenPlan?]
    simpa only [CanonicalCompleteRootItem] using
      (PrefixValues.tokenPlan?_fullValue sourceRuleTokenPlanLayout
        (CanonicalCompleteRootItem tokens .matchArm origin finish context)
        complete priorValues)
  let rootInput := RootAction.unpack .matchArm
    (PrefixValues.fullValue
      (CanonicalCompleteRootItem tokens .matchArm origin finish context)
      complete priorValues)
  change RuleReduction file tokens .matchArm origin finish rootInput output
    at reduces
  change TokenPlanEvidence
    (rootInput.tokenPlan? sourceRuleTokenPlanLayout)
    (PhysicalTokens tokens origin finish) at rootInputEvidence
  generalize inputEq : rootInput = sourceInput at reduces rootInputEvidence
  cases reduces with
  | matchArm origin finish pipe patterns fatArrow statements witness =>
      have positioned : StatementListPositionCoherent statements := by
        apply coherentMatchArmStatementPositions complete owned lexicallyExact
          coherentPrefix pipe patterns fatArrow statements witness
        exact inputEq
      have sourceEvidence := rootInputEvidence.candidate_eq
        (matchArmInput_tokenPlan? origin finish pipe patterns fatArrow
          statements witness)
      cases patternPlansEq : nonemptyPatternTokenPlans? patterns with
      | none =>
          simp [patternPlansEq, TokenPlanEvidence] at sourceEvidence
      | some patternPlans =>
          cases statementPlansEq :
              statements.mapM (statementTokenPlan? true) with
          | none =>
              simp [patternPlansEq, statementPlansEq, TokenPlanEvidence]
                at sourceEvidence
          | some statementPlans =>
              simp only [patternPlansEq, statementPlansEq] at sourceEvidence
              let sourceInner := TokenPlan.concat [
                TokenPlan.exact (.symbol .pipe) pipe.span,
                TokenPlan.commaSeparated patternPlans,
                TokenPlan.exact (.symbol .fatArrow) fatArrow.span,
                TokenPlan.concat statementPlans]
              change TokenPlanEvidence (some sourceInner)
                (PhysicalTokens tokens origin finish) at sourceEvidence
              rcases sourceEvidence with
                ⟨sourcePlan, sourcePlanEq, sourceRelation⟩
              simp only [Option.some.injEq] at sourcePlanEq
              subst sourcePlan
              have normalized : TokenSlot.ListMatches
                  ((TokenPlan.exact (.symbol .pipe) pipe.span).append
                    ((TokenPlan.commaSeparated patternPlans).append
                      ((TokenPlan.exact (.symbol .fatArrow) fatArrow.span).append
                        (TokenPlan.concat statementPlans)))).slots
                  (PhysicalTokens tokens origin finish) := by
                simpa [sourceInner, TokenPlan.concat, TokenPlan.append] using
                  sourceRelation
              rcases normalized.split_append with
                ⟨pipeActual, afterPipeActual, physicalEq, pipeRelation,
                  afterPipeRelation⟩
              rcases afterPipeRelation.split_append with
                ⟨patternActual, afterPatternActual, afterPipeEq,
                  patternRelation, afterPatternRelation⟩
              rcases afterPatternRelation.split_append with
                ⟨arrowActual, statementActual, afterPatternEq,
                  arrowRelation, statementRelation⟩
              have pipePlainRelation : TokenSlot.ListMatches
                  (TokenPlan.plain (.symbol .pipe)).slots pipeActual := by
                cases pipeRelation with
                | required pipeMatch pipeTail =>
                    exact .required
                      (by
                        simpa only [ExpectedToken.exact] using
                          pipeMatch.toPlain)
                      pipeTail
              cases statements with
              | nil =>
                  simp at statementPlansEq
                  subst statementPlans
                  cases statementRelation
                  cases arrowRelation with
                  | required arrowMatch arrowTail =>
                      cases arrowTail
                      rename_i arrowToken
                      have arrowSpanEq : arrowToken.span = fatArrow.span :=
                        arrowMatch.2 (.exact fatArrow.span)
                          (by simp [ExpectedToken.exact])
                      let targetArrow : ExpectedToken :=
                        (ExpectedToken.exact (.symbol .fatArrow) fatArrow.span)
                          |>.anchorEmptyAfter
                            (RuleReduction.armBody fatArrow []).span
                      have emptyAnchor : TokenSpanConstraint.Holds
                          (.anchorsEmptyAfter
                            (RuleReduction.armBody fatArrow []).span)
                          arrowToken := by
                        change arrowToken.span.source = file.id ∧
                          arrowToken.span.endByte = fatArrow.span.endByte ∧
                          fatArrow.span.endByte = fatArrow.span.endByte
                        rw [arrowSpanEq]
                        exact ⟨fatArrow.span_validFor.1, rfl, rfl⟩
                      have targetArrowMatch : targetArrow.Matches arrowToken := by
                        refine ⟨arrowMatch.1, ?_⟩
                        intro constraint member
                        simp only [targetArrow, ExpectedToken.anchorEmptyAfter,
                          List.mem_cons] at member
                        rcases member with rfl | member
                        · exact emptyAnchor
                        · exact arrowMatch.2 constraint member
                      have targetArrowRelation : TokenSlot.ListMatches
                          [.required targetArrow] [arrowToken] :=
                        .required targetArrowMatch .nil
                      let targetInner := TokenPlan.concat [
                        TokenPlan.plain (.symbol .pipe),
                        TokenPlan.commaSeparated patternPlans,
                        ⟨[.required targetArrow]⟩,
                        TokenPlan.empty]
                      have targetRelation : TokenSlot.ListMatches
                          targetInner.slots
                          (PhysicalTokens tokens origin finish) := by
                        rw [physicalEq, afterPipeEq, afterPatternEq]
                        simpa [targetInner, TokenPlan.concat,
                          TokenPlan.append, TokenPlan.empty] using
                          pipePlainRelation.append
                            (patternRelation.append targetArrowRelation)
                      have targetAnchored : targetInner.WellAnchored := by
                        simpa [targetInner, TokenPlan.concat,
                          TokenPlan.append, TokenPlan.plain,
                          TokenPlan.empty] using
                          TokenPlan.WellAnchored.bookended
                            (ExpectedToken.plain (.symbol .pipe)) targetArrow
                            (TokenPlan.commaSeparated patternPlans).slots
                      have targetEvidence : TokenPlanEvidence
                          (some targetInner)
                          (PhysicalTokens tokens origin finish) :=
                        ⟨targetInner, rfl, targetRelation⟩
                      have enclosed := TokenPlanEvidence.enclose targetEvidence
                        (fun plan success => by
                          simp only [Option.some.injEq] at success
                          subst plan
                          exact targetAnchored)
                        witness.consumed
                      apply enclosed.candidate_eq
                      change _ = matchArmTokenPlan? (sourceLoc witness {
                        patterns := patterns
                        body := RuleReduction.armBody fatArrow []
                      })
                      rw [matchArmTokenPlan?_sourceLoc_empty patterns fatArrow
                        witness patternPlans patternPlansEq]
                      rfl
              | cons first rest =>
                  have positionalEq := statementTokenPlans?_of_mapM_allowTerminal
                    (first :: rest) statementPlans positioned statementPlansEq
                  have endpoints := statementPlanList_matches_endpoints_statementRegionsLocal
                    first rest statementPlans statementPlansEq statementRelation
                  have allSources : TokensHaveSourceStatementRegionsLocal file.id
                      (PhysicalTokens tokens origin finish) :=
                    physicalTokens_haveSource_statementRegionsLocal
                      (origin := origin) (finish := finish) owned
                  rw [physicalEq, afterPipeEq, afterPatternEq] at allSources
                  have statementSources : TokensHaveSourceStatementRegionsLocal file.id
                      statementActual :=
                    allSources.of_append_right.of_append_right.of_append_right
                  have bodyStarts : TokenSlot.FirstSatisfies
                      (.starts (RuleReduction.armBody fatArrow
                        (first :: rest)).span) statementActual := by
                    simpa [RuleReduction.armBody, RuleReduction.between] using
                      firstSatisfies_between_statementRegionsLocal statementSources endpoints.1
                  have bodyEnds : TokenSlot.LastSatisfies
                      (.ends (RuleReduction.armBody fatArrow
                        (first :: rest)).span) statementActual := by
                    simpa [RuleReduction.armBody, RuleReduction.between] using
                      lastSatisfies_between_statementRegionsLocal statementSources endpoints.2
                  have statementsAnchored :
                      (TokenPlan.concat statementPlans).WellAnchored :=
                    TokenPlan.WellAnchored.concat statementPlans
                      (statementTokenPlans_true_allWellAnchored_statementRegionsLocal
                        (first :: rest) statementPlans statementPlansEq)
                  have bodyRelation : TokenSlot.ListMatches
                      ((TokenPlan.concat statementPlans).enclose
                        (RuleReduction.armBody fatArrow
                          (first :: rest)).span).slots statementActual :=
                    TokenSlot.ListMatches.enclose statementRelation
                      statementsAnchored bodyStarts bodyEnds
                  let prefixPlan := TokenPlan.concat [
                    TokenPlan.plain (.symbol .pipe),
                    TokenPlan.commaSeparated patternPlans,
                    TokenPlan.exact (.symbol .fatArrow) fatArrow.span]
                  let bodyPlan := (TokenPlan.concat statementPlans).enclose
                    (RuleReduction.armBody fatArrow (first :: rest)).span
                  let targetInner := TokenPlan.concat [
                    TokenPlan.plain (.symbol .pipe),
                    TokenPlan.commaSeparated patternPlans,
                    TokenPlan.exact (.symbol .fatArrow) fatArrow.span,
                    bodyPlan]
                  have targetRelation : TokenSlot.ListMatches targetInner.slots
                      (PhysicalTokens tokens origin finish) := by
                    rw [physicalEq, afterPipeEq, afterPatternEq]
                    simpa [targetInner, bodyPlan, TokenPlan.concat,
                      TokenPlan.append] using
                      pipePlainRelation.append
                        (patternRelation.append
                          (arrowRelation.append bodyRelation))
                  have prefixAnchored : prefixPlan.WellAnchored := by
                    simpa [prefixPlan, TokenPlan.concat, TokenPlan.append,
                      TokenPlan.plain, TokenPlan.exact] using
                      TokenPlan.WellAnchored.bookended
                        (ExpectedToken.plain (.symbol .pipe))
                        (ExpectedToken.exact (.symbol .fatArrow) fatArrow.span)
                        (TokenPlan.commaSeparated patternPlans).slots
                  have bodyAnchored : bodyPlan.WellAnchored := by
                    exact TokenPlan.WellAnchored.enclose statementsAnchored _
                  have targetAnchored : targetInner.WellAnchored := by
                    simpa [targetInner, prefixPlan, bodyPlan,
                      TokenPlan.concat, TokenPlan.append] using
                      TokenPlan.WellAnchored.append prefixAnchored bodyAnchored
                  have targetEvidence : TokenPlanEvidence (some targetInner)
                      (PhysicalTokens tokens origin finish) :=
                    ⟨targetInner, rfl, targetRelation⟩
                  have enclosed := TokenPlanEvidence.enclose targetEvidence
                    (fun plan success => by
                      simp only [Option.some.injEq] at success
                      subst plan
                      exact targetAnchored)
                    witness.consumed
                  apply enclosed.candidate_eq
                  change _ = matchArmTokenPlan? (sourceLoc witness {
                    patterns := patterns
                    body := RuleReduction.armBody fatArrow (first :: rest)
                  })
                  cases statementPlans with
                  | nil =>
                      cases headEq : statementTokenPlan? true first with
                      | none =>
                          simp [List.mapM_cons, headEq] at statementPlansEq
                      | some headPlan =>
                          cases tailEq :
                              (rest.mapM (statementTokenPlan? true)) with
                          | none =>
                              simp [List.mapM_cons, headEq, tailEq]
                                at statementPlansEq
                          | some tailPlans =>
                              simp [List.mapM_cons, headEq, tailEq]
                                at statementPlansEq
                  | cons headPlan tailPlans =>
                      rw [matchArmTokenPlan?_sourceLoc_cons patterns fatArrow
                        first rest witness patternPlans headPlan tailPlans
                        patternPlansEq positionalEq]
                      rfl

end Solcore.Surface.Multi
