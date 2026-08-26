import Solcore.Surface.Multi.ExactTokenRuleParameterBody
import Solcore.Surface.Multi.ExactTokenRulePatternAtom
import Solcore.Surface.Multi.RuleCoherentStatementLayout

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem armStatementRuleValues_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (statements : List Statement) :
    (statements.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .armStatement)).mapM
        (fun value => value.tokenPlan? sourceRuleTokenPlanLayout) =
      statements.mapM (statementTokenPlan? true) := by
  rw [List.mapM_map]
  simp [Function.comp_def, sourceRuleTokenPlanLayout, ruleTokenPlan?]
  rfl

private abbrev matchArmSourceChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .pipe)),
  .list1 (.atom (.nonterminal .pattern)),
  .atom (.terminal (.symbol .fatArrow)),
  .star (.atom (.nonterminal .armStatement))]

private def matchArmSourceValue
    {file : WorkspaceFile} {tokens : List Token}
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement) :
    EbnfValue file tokens (m2cV1.rhs .matchArm) :=
  EbnfValue.transport (by rfl) <|
    EbnfValue.sequence matchArmSourceChildren <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .pipe) pipe) <|
      EbnfValues.cons _ _
        (EbnfValue.list1 (.atom (.nonterminal .pattern))
          (patterns.map (EbnfValue.ruleAtom .pattern))) <|
      EbnfValues.cons _ _
        (EbnfValue.terminalAtom (.symbol .fatArrow) fatArrow) <|
      EbnfValues.cons _ _
        (EbnfValue.star (.atom (.nonterminal .armStatement))
          (statements.map (EbnfValue.ruleAtom .armStatement))) <|
      EbnfValues.nil

/-- The concrete grammar input of a match arm visits its retained delimiters,
patterns, and arm statements in source order. -/
theorem matchArmInput_tokenPlan?
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (pipe : MatchedTerminal file tokens (.symbol .pipe))
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (statements : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (RuleReduction.inputValue
      (RuleReduction.matchArm origin finish pipe patterns fatArrow statements
        witness)).tokenPlan? sourceRuleTokenPlanLayout = (do
      let patternPlans ← nonemptyPatternTokenPlans? patterns
      let statementPlans ← statements.mapM (statementTokenPlan? true)
      pure (TokenPlan.concat [
        .exact (.symbol .pipe) pipe.span,
        .commaSeparated patternPlans,
        .exact (.symbol .fatArrow) fatArrow.span,
        .concat statementPlans])) := by
  have sourceEq : RuleReduction.inputValue
        (RuleReduction.matchArm origin finish pipe patterns fatArrow statements
          witness) =
      matchArmSourceValue pipe patterns fatArrow statements := by
    rfl
  rw [sourceEq]
  unfold matchArmSourceValue
  rw [EbnfValue.tokenPlan?_transport]
  rw [EbnfValue.tokenPlan?_sequence]
  rw [EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    nonemptyPatternRuleValues_tokenPlan?,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_terminalAtom,
    EbnfValues.tokenPlan?_cons,
    EbnfValue.tokenPlan?_star,
    EbnfValues.tokenPlan?_nil]
  rw [MatchedTerminal.physicalTokenPlan_symbol,
    MatchedTerminal.physicalTokenPlan_symbol,
    armStatementRuleValues_tokenPlan?]
  cases patternEq : nonemptyPatternTokenPlans? patterns <;>
    cases statementEq : statements.mapM (statementTokenPlan? true) <;>
    simp_all [TokenPlan.concat, TokenPlan.append, TokenPlan.empty]

/-- The semantic visitor for an empty match-arm body anchors the otherwise
empty body immediately after the retained fat arrow. -/
theorem matchArmTokenPlan?_sourceLoc_empty
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (patternPlans : List TokenPlan)
    (patternsPlan : nonemptyPatternTokenPlans? patterns = some patternPlans) :
    matchArmTokenPlan? (sourceLoc witness {
      patterns := patterns
      body := RuleReduction.armBody fatArrow []
    }) = some (.enclose witness.span (.concat [
      .plain (.symbol .pipe),
      .commaSeparated patternPlans,
      ⟨[.required
        ((ExpectedToken.exact (.symbol .fatArrow) fatArrow.span).anchorEmptyAfter
          (RuleReduction.armBody fatArrow []).span)]⟩,
      .empty])) := by
  unfold matchArmTokenPlan?
  simp only [sourceLoc, RuleReduction.armBody, RuleReduction.emptyAt]
  rw [patternsPlan]
  unfold matchArmArrowPlan bodyTokenPlan?
  simp [armBodyPlanWith?, statementTokenPlans?, TokenPlan.append,
    TokenPlan.empty]

/-- The semantic visitor for a nonempty match arm encloses the positional
statement plans in the span computed from the first and last statements. -/
theorem matchArmTokenPlan?_sourceLoc_cons
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    (patterns : NonemptyList Pattern)
    (fatArrow : MatchedTerminal file tokens (.symbol .fatArrow))
    (first : Statement) (rest : List Statement)
    (witness : ConsumedSpanWitness file tokens origin finish)
    (patternPlans : List TokenPlan)
    (headPlan : TokenPlan) (tailPlans : List TokenPlan)
    (patternsPlan : nonemptyPatternTokenPlans? patterns = some patternPlans)
    (statementsPlan :
      statementTokenPlans? (first :: rest) = some (headPlan :: tailPlans)) :
    matchArmTokenPlan? (sourceLoc witness {
      patterns := patterns
      body := RuleReduction.armBody fatArrow (first :: rest)
    }) = some (.enclose witness.span (.concat [
      .plain (.symbol .pipe),
      .commaSeparated patternPlans,
      .exact (.symbol .fatArrow) fatArrow.span,
      .enclose (RuleReduction.armBody fatArrow (first :: rest)).span
        (.concat (headPlan :: tailPlans))])) := by
  unfold matchArmTokenPlan?
  simp only [sourceLoc, RuleReduction.armBody, RuleReduction.between]
  rw [patternsPlan]
  unfold matchArmArrowPlan bodyTokenPlan?
  rw [statementsPlan]
  unfold armBodyPlanWith?
  rfl

end Solcore.Surface.Multi
