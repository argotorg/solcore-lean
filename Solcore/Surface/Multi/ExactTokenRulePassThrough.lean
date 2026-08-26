import Solcore.Surface.Multi.ExactTokenEvidence
import Solcore.Surface.Multi.ExactTokenRuleLayout
import Solcore.Surface.Multi.ExactTokenTypeAnchoring
import Solcore.Surface.Multi.RuleLocationPassThrough

set_option autoImplicit false
set_option linter.unnecessarySimpa false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

local syntax "statementPassThroughBranches!" : term
local macro_rules
  | `(statementPassThroughBranches!) =>
      `((EbnfExpr.choice [
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
        .atom (.nonterminal .expressionStatement)]).children)

namespace TokenPlanEvidence

/-- Replace a successful candidate by another visitor that returns the same
plan whenever the first visitor succeeds. -/
theorem mapSuccessfulCandidate
    {candidate replacement : Option TokenPlan} {actual : List Token}
    (evidence : TokenPlanEvidence candidate actual)
    (preserves : ∀ plan, candidate = Option.some plan →
      replacement = Option.some plan) :
    TokenPlanEvidence replacement actual := by
  rcases evidence with ⟨plan, success, relation⟩
  exact ⟨plan, preserves plan success, relation⟩

/-- Remove a checked EBNF choice wrapper from token-plan evidence. -/
theorem choice
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (branches : List EbnfExpr)
    (value : (branch : Fin branches.length) ×
      EbnfValue file tokens (branches.get branch))
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.choice branches value).tokenPlan? layout) actual) :
    TokenPlanEvidence (value.2.tokenPlan? layout) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_choice layout branches value)

/-- Remove a checked source-rule atom wrapper from token-plan evidence. -/
theorem rule
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (rule : GrammarRuleId)
    (value : RuleValue rule) {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.ruleAtom (file := file) (tokens := tokens)
        rule value).tokenPlan? layout) actual) :
    TokenPlanEvidence (layout.plan? rule value) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_ruleAtom layout rule value)

/-- Remove a type-level transport around a checked EBNF value. -/
theorem transport
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) {left right : EbnfExpr}
    (shape : left = right) (value : EbnfValue file tokens left)
    {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.transport shape value).tokenPlan? layout) actual) :
    TokenPlanEvidence (value.tokenPlan? layout) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_transport layout shape value)

/-- Remove a checked EBNF sequence wrapper from token-plan evidence. -/
theorem sequence
    {file : WorkspaceFile} {tokens : List Token}
    (layout : RuleTokenPlanLayout) (children : List EbnfExpr)
    (values : EbnfValues file tokens children) {actual : List Token}
    (evidence : TokenPlanEvidence
      ((EbnfValue.sequence children values).tokenPlan? layout) actual) :
    TokenPlanEvidence (values.tokenPlan? layout) actual := by
  exact evidence.candidate_eq
    (EbnfValue.tokenPlan?_sequence layout children values)

end TokenPlanEvidence

/-- A statement accepted where a terminator is mandatory has the identical
plan in the final-statement context. -/
theorem statementTokenPlan?_allowsTerminal
    {statement : Statement} {plan : TokenPlan}
    (success : statementTokenPlan? false statement = Option.some plan) :
    statementTokenPlan? true statement = Option.some plan := by
  rcases statement with ⟨span, payload⟩
  cases payload <;> try simp_all only [statementTokenPlan?]
  case expression expression terminator =>
    cases terminator <;> simp_all [statementTokenPlan?]
  case «return» value terminator =>
    cases value <;> simp_all [statementTokenPlan?]
  case «match» scrutinees arms terminator =>
    cases terminator <;> simp_all [statementTokenPlan?]

/-- Lift exact-token evidence from a mandatory-terminator statement site to a
site where a final terminal expression is also permitted. -/
private theorem TokenPlanEvidence.allowTerminal
    {statement : Statement} {actual : List Token}
    (evidence : TokenPlanEvidence
      (statementTokenPlan? false statement) actual) :
    TokenPlanEvidence (statementTokenPlan? true statement) actual := by
  apply evidence.mapSuccessfulCandidate
  intro plan success
  exact statementTokenPlan?_allowsTerminal success

/-- A plan accepted by the conditional-expression entry has the same plan at
the annotation-expression entry. -/
theorem conditionalExpressionTokenPlan?_promotes
    {expression : Expression} {plan : TokenPlan}
    (success : conditionalExpressionTokenPlan? expression =
      Option.some plan) :
    annotationExpressionTokenPlan? expression = Option.some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;>
    simpa [annotationExpressionTokenPlan?,
      conditionalExpressionTokenPlan?, expressionTokenPlanAt?] using success

/-- A plan accepted by the logical-or entry has the same plan at the
conditional-expression entry. -/
theorem logicalOrExpressionTokenPlan?_promotes
    {expression : Expression} {plan : TokenPlan}
    (success : logicalOrExpressionTokenPlan? expression =
      Option.some plan) :
    conditionalExpressionTokenPlan? expression = Option.some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;>
    simpa [conditionalExpressionTokenPlan?,
      logicalOrExpressionTokenPlan?, expressionTokenPlanAt?] using success

/-- A plan accepted by the relational entry has the same plan at the equality
entry. -/
theorem relationalExpressionTokenPlan?_promotesEquality
    {expression : Expression} {plan : TokenPlan}
    (success : relationalExpressionTokenPlan? expression =
      Option.some plan) :
    equalityExpressionTokenPlan? expression = Option.some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [equalityExpressionTokenPlan?,
      relationalExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [equalityExpressionTokenPlan?,
        relationalExpressionTokenPlan?, expressionTokenPlanAt?] using success

/-- A plan accepted by the bitwise-or entry has the same plan at the
relational entry. -/
theorem bitOrExpressionTokenPlan?_promotesRelational
    {expression : Expression} {plan : TokenPlan}
    (success : bitOrExpressionTokenPlan? expression = Option.some plan) :
    relationalExpressionTokenPlan? expression = Option.some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;> try
    simpa [relationalExpressionTokenPlan?,
      bitOrExpressionTokenPlan?, expressionTokenPlanAt?] using success
  case «infix» operator left right =>
    rcases operator with ⟨operatorSpan, operatorPayload⟩
    cases operatorPayload <;>
      simpa [relationalExpressionTokenPlan?,
        bitOrExpressionTokenPlan?, expressionTokenPlanAt?] using success

/-- A plan accepted by the postfix entry has the same plan at the prefix
entry. -/
theorem postfixExpressionTokenPlan?_promotesPrefix
    {expression : Expression} {plan : TokenPlan}
    (success : postfixExpressionTokenPlan? expression = Option.some plan) :
    prefixExpressionTokenPlan? expression = Option.some plan := by
  rcases expression with ⟨span, payload⟩
  cases payload <;>
    simpa [prefixExpressionTokenPlan?,
      postfixExpressionTokenPlan?, expressionTokenPlanAt?] using success

/-- Every semantic pass-through source action preserves the complete token
plan reconstructed for its selected source-rule child. -/
theorem RuleReduction.SemanticPassThrough.tokenPlanEvidence
    {file : WorkspaceFile} {tokens : List Token}
    {rule : GrammarRuleId} {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs rule)}
    {output : RuleValue rule}
    {reduces : RuleReduction file tokens rule origin finish input output}
    (passThrough : RuleReduction.SemanticPassThrough reduces)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? rule output)
      (PhysicalTokens tokens origin finish) := by
  cases passThrough with
  | instanceMethod origin finish value =>
      simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?, m2cV1, m2cV1Rhs,
        EbnfExpr.children] using inputEvidence
  | typeAtomOnly origin finish value =>
      simp only [EbnfValue.tokenPlan?_transport] at inputEvidence
      simp only [EbnfValue.tokenPlan?_choice] at inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ inputEvidence
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have atomEvidence : TokenPlanEvidence (typeAtomPlan? value)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      apply atomEvidence.mapSuccessfulCandidate
      intro plan success
      exact typeAtomPlan?_promotes success
  | statementLet origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨0, by decide⟩, EbnfValue.ruleAtom .letStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .letStatement value selected
      exact child.allowTerminal
  | statementReturn origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨1, by decide⟩, EbnfValue.ruleAtom .returnStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .returnStatement value selected
      exact child.allowTerminal
  | statementMatch origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨2, by decide⟩, EbnfValue.ruleAtom .matchStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .matchStatement value selected
      exact child.allowTerminal
  | statementIf origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨3, by decide⟩, EbnfValue.ruleAtom .ifStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .ifStatement value selected
      exact child.allowTerminal
  | statementFor origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨4, by decide⟩, EbnfValue.ruleAtom .forStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .forStatement value selected
      exact child.allowTerminal
  | statementAssembly origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨5, by decide⟩, EbnfValue.ruleAtom .assemblyStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .assemblyStatement value selected
      exact child.allowTerminal
  | statementBlock origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨6, by decide⟩, EbnfValue.ruleAtom .blockStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .blockStatement value selected
      exact child.allowTerminal
  | statementBreak origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨7, by decide⟩, EbnfValue.ruleAtom .breakStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .breakStatement value selected
      exact child.allowTerminal
  | statementContinue origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨8, by decide⟩, EbnfValue.ruleAtom .continueStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .continueStatement value selected
      exact child.allowTerminal
  | statementAssignment origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨9, by decide⟩,
          EbnfValue.ruleAtom .assignmentStatement value⟩
        inputEvidence
      have child := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .assignmentStatement value selected
      exact child.allowTerminal
  | statementExpression origin finish value =>
      have selected := TokenPlanEvidence.choice
        (file := file) (tokens := tokens) sourceRuleTokenPlanLayout
        statementPassThroughBranches!
        ⟨⟨10, by decide⟩, EbnfValue.ruleAtom .expressionStatement value⟩
        inputEvidence
      exact TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .expressionStatement value selected
  | armStatement origin finish value =>
      have normal := TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .statement value inputEvidence
      exact normal
  | terminalExpression origin finish value =>
      exact TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .expression value inputEvidence
  | expression origin finish value =>
      exact TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .annotation value inputEvidence
  | annotationNone origin finish value =>
      change TokenPlanEvidence (annotationExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ inputEvidence
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have conditionalEvidence : TokenPlanEvidence
          (conditionalExpressionTokenPlan? value)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      apply conditionalEvidence.mapSuccessfulCandidate
      intro plan success
      exact conditionalExpressionTokenPlan?_promotes success
  | conditionalLogical origin finish value =>
      change TokenPlanEvidence (conditionalExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have logicalEvidence : TokenPlanEvidence
          (logicalOrExpressionTokenPlan? value)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      apply logicalEvidence.mapSuccessfulCandidate
      intro plan success
      exact logicalOrExpressionTokenPlan?_promotes success
  | equalityNone origin finish value =>
      change TokenPlanEvidence (equalityExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ inputEvidence
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have relationalEvidence : TokenPlanEvidence
          (relationalExpressionTokenPlan? value)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      apply relationalEvidence.mapSuccessfulCandidate
      intro plan success
      exact relationalExpressionTokenPlan?_promotesEquality success
  | relationalNone origin finish value =>
      change TokenPlanEvidence (relationalExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ inputEvidence
      simp only [EbnfValues.tokenPlan?_cons,
        EbnfValue.tokenPlan?_ruleAtom,
        EbnfValue.tokenPlan?_optional_none,
        EbnfValues.tokenPlan?_nil] at sequenceEvidence
      have bitOrEvidence : TokenPlanEvidence
          (bitOrExpressionTokenPlan? value)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          sequenceEvidence
      apply bitOrEvidence.mapSuccessfulCandidate
      intro plan success
      exact bitOrExpressionTokenPlan?_promotesRelational success
  | prefixPostfix origin finish value =>
      change TokenPlanEvidence (prefixExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have postfixEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .postfix value selected
      apply postfixEvidence.mapSuccessfulCandidate
      intro plan success
      exact postfixExpressionTokenPlan?_promotesPrefix success
  | atomLambda origin finish value =>
      change TokenPlanEvidence (atomExpressionTokenPlan? value)
        (PhysicalTokens tokens origin finish)
      simp only [EbnfExpr.children] at inputEvidence
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      exact TokenPlanEvidence.rule sourceRuleTokenPlanLayout
        .lambda value selected

end Solcore.Surface.Multi
