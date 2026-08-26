import Solcore.Surface.Multi.ExactTokenExpressionAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRulePassThrough
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem assignmentOperatorTokenPlan_wellAnchored
    (operator : Located AssignmentOperator) :
    (assignmentOperatorTokenPlan operator).WellAnchored := by
  rcases operator with ⟨span, payload⟩
  cases payload <;> exact TokenPlan.WellAnchored.exact _ _

private theorem optionMap_eq_bindPure
    {alpha beta : Type} (function : alpha → beta)
    (candidate : Option alpha) :
    candidate.map function = (do
      let value ← candidate
      pure (function value)) := by
  cases candidate <;> rfl

private def letBindingTypePlan?
    (comptime : Option Marker) (typeExpression : Option TypeExpr) :
    Option TokenPlan :=
  match comptime, typeExpression with
  | none, none => some .empty
  | some _, none => none
  | none, some typeExpression =>
      match typeExpression.payload with
      | .comptime .. => none
      | _ => do
          let plan ← typeExprPlan? typeExpression
          pure (.append (.plain (.symbol .colon)) plan)
  | some marker, some typeExpression =>
      if marker.payload = .comptimeModifier then do
        let plan ← typeExprPlan? typeExpression
        pure (.concat [
          .plain (.symbol .colon),
          .exact (.identifier ContextualKeyword.comptimeKw.spelling)
            marker.span,
          plan])
      else
        none

private def letBindingInitializerPlan? : Option Expression → Option TokenPlan
  | none => some .empty
  | some expression => do
      let plan ← expressionTokenPlanAt? .annotation expression
      pure (.append (.plain (.symbol .equal)) plan)

private theorem letBindingTypePlan?_wellAnchored
    (comptime : Option Marker) (typeExpression : Option TypeExpr)
    (plan : TokenPlan)
    (success : letBindingTypePlan? comptime typeExpression = some plan) :
    plan.WellAnchored := by
  cases comptime with
  | none =>
      cases typeExpression with
      | none =>
          simp [letBindingTypePlan?] at success
          subst plan
          exact TokenPlan.WellAnchored.empty
      | some typeExpression =>
          rcases typeExpression with ⟨span, payload⟩
          cases payload <;> simp [letBindingTypePlan?] at success
          all_goals
            rename_i _
            rcases Option.bind_eq_some_iff.mp success with
              ⟨typePlan, typeEq, resultEq⟩
            injection resultEq with planEq
            subst plan
            exact TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.plain _)
              (typeExprPlan?_wellAnchored _ typePlan typeEq)
  | some marker =>
      cases typeExpression with
      | none => simp [letBindingTypePlan?] at success
      | some typeExpression =>
          by_cases accepted : marker.payload = .comptimeModifier
          · simp only [letBindingTypePlan?, accepted, ↓reduceIte] at success
            rcases Option.bind_eq_some_iff.mp success with
              ⟨typePlan, typeEq, resultEq⟩
            injection resultEq with planEq
            subst plan
            simp only [TokenPlan.concat_cons, TokenPlan.concat_nil,
              TokenPlan.append_empty]
            exact TokenPlan.WellAnchored.append
              (TokenPlan.WellAnchored.plain _)
              (TokenPlan.WellAnchored.append
                (TokenPlan.WellAnchored.exact _ _)
                (typeExprPlan?_wellAnchored typeExpression typePlan typeEq))
          · simp [letBindingTypePlan?, accepted] at success

private theorem letBindingInitializerPlan?_wellAnchored
    (initializer : Option Expression) (plan : TokenPlan)
    (success : letBindingInitializerPlan? initializer = some plan) :
    plan.WellAnchored := by
  cases initializer with
  | none =>
      simp [letBindingInitializerPlan?] at success
      subst plan
      exact TokenPlan.WellAnchored.empty
  | some expression =>
      simp only [letBindingInitializerPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨expressionPlan, expressionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.append
        (TokenPlan.WellAnchored.plain _)
        (expressionTokenPlanAt?_wellAnchored
          .annotation expression expressionPlan expressionEq)

/-- Every accepted let-binding plan has mandatory physical endpoints. -/
theorem letBindingTokenPlan?_wellAnchored
    (binding : LetBinding) (plan : TokenPlan)
    (success : letBindingTokenPlan? binding = some plan) :
    plan.WellAnchored := by
  rcases binding with ⟨span, ⟨comptime, name, typeExpression, initializer⟩⟩
  have decomposition : letBindingTokenPlan?
      ({
        span := span
        payload := {
          comptime := comptime
          name := name
          type := typeExpression
          initializer := initializer
        }
      } : LetBinding) = (do
    let typePlan ← letBindingTypePlan? comptime typeExpression
    let initializerPlan ← letBindingInitializerPlan? initializer
    pure (.enclose span (.concat [
      .plain (.hardKeyword .letKw),
      identifierPlan name,
      typePlan,
      initializerPlan]))) := by
    cases comptime <;> cases typeExpression <;> cases initializer
    case none.some.none typeExpression =>
      rcases typeExpression with ⟨typeSpan, typePayload⟩
      cases typePayload <;>
        simp [letBindingTokenPlan?, letBindingTypePlan?,
          letBindingInitializerPlan?, Option.bind_assoc]
    case none.some.some typeExpression expression =>
      rcases typeExpression with ⟨typeSpan, typePayload⟩
      cases typePayload <;>
        simp [letBindingTokenPlan?, letBindingTypePlan?,
          letBindingInitializerPlan?, TokenPlan.append_assoc,
          Option.bind_assoc]
    case some.some.none marker typeExpression =>
      by_cases accepted : marker.payload = .comptimeModifier <;>
        simp [letBindingTokenPlan?, letBindingTypePlan?,
          letBindingInitializerPlan?, Option.bind_assoc, accepted]
    case some.some.some marker typeExpression expression =>
      by_cases accepted : marker.payload = .comptimeModifier <;>
        simp [letBindingTokenPlan?, letBindingTypePlan?,
          letBindingInitializerPlan?, TokenPlan.append_assoc,
          Option.bind_assoc, accepted]
    all_goals
      simp [letBindingTokenPlan?, letBindingTypePlan?,
        letBindingInitializerPlan?, Option.bind_assoc]
  rw [decomposition] at success
  rcases Option.bind_eq_some_iff.mp success with
    ⟨typePlan, typeEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨initializerPlan, initializerEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  apply TokenPlan.WellAnchored.enclose
  simp only [TokenPlan.concat_cons, TokenPlan.concat_nil,
    TokenPlan.append_empty]
  exact TokenPlan.WellAnchored.append
    (TokenPlan.WellAnchored.plain _)
    (TokenPlan.WellAnchored.append
      (identifierPlan_wellAnchored name)
      (TokenPlan.WellAnchored.append
        (letBindingTypePlan?_wellAnchored comptime typeExpression
          typePlan typeEq)
        (letBindingInitializerPlan?_wellAnchored initializer
          initializerPlan initializerEq)))

private def forAssignmentTokenPlan?
    (left : Expression) (operator : Located AssignmentOperator)
    (right : Expression) : Option TokenPlan := do
  let leftPlan ← expressionTokenPlanAt? .annotation left
  let rightPlan ← expressionTokenPlanAt? .annotation right
  pure (.concat [leftPlan, assignmentOperatorTokenPlan operator, rightPlan])

private theorem forAssignmentTokenPlan?_wellAnchored
    (left : Expression) (operator : Located AssignmentOperator)
    (right : Expression) (plan : TokenPlan)
    (success : forAssignmentTokenPlan? left operator right = some plan) :
    plan.WellAnchored := by
  rcases Option.bind_eq_some_iff.mp success with
    ⟨leftPlan, leftEq, success⟩
  rcases Option.bind_eq_some_iff.mp success with
    ⟨rightPlan, rightEq, resultEq⟩
  injection resultEq with planEq
  subst plan
  simp only [TokenPlan.concat_cons, TokenPlan.concat_nil,
    TokenPlan.append_empty]
  exact TokenPlan.WellAnchored.append
    (expressionTokenPlanAt?_wellAnchored
      .annotation left leftPlan leftEq)
    (TokenPlan.WellAnchored.append
      (assignmentOperatorTokenPlan_wellAnchored operator)
      (expressionTokenPlanAt?_wellAnchored
        .annotation right rightPlan rightEq))

/-- Every accepted for-loop initializer plan has mandatory endpoints. -/
theorem forInitTokenPlan?_wellAnchored
    (item : ForInitItem) (plan : TokenPlan)
    (success : forInitTokenPlan? item = some plan) :
    plan.WellAnchored := by
  rcases item with ⟨span, payload⟩
  cases payload with
  | letBinding binding =>
      simp only [forInitTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨bindingPlan, bindingEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (letBindingTokenPlan?_wellAnchored binding bindingPlan bindingEq) span
  | assignment operator left right =>
      simp only [forInitTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftPlan, leftEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightPlan, rightEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      simp only [TokenPlan.concat_cons, TokenPlan.concat_nil,
        TokenPlan.append_empty]
      exact TokenPlan.WellAnchored.append
        (expressionTokenPlanAt?_wellAnchored
          .annotation left leftPlan leftEq)
        (TokenPlan.WellAnchored.append
          (assignmentOperatorTokenPlan_wellAnchored operator)
          (expressionTokenPlanAt?_wellAnchored
            .annotation right rightPlan rightEq))
  | expression expression =>
      simp only [forInitTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨expressionPlan, expressionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (expressionTokenPlanAt?_wellAnchored
          .annotation expression expressionPlan expressionEq) span

/-- Every successful initializer-list traversal returns anchored plans. -/
theorem forInitTokenPlans?_allWellAnchored
    (items : List ForInitItem) (plans : List TokenPlan)
    (success : forInitTokenPlans? items = some plans) :
    ∀ plan ∈ plans, plan.WellAnchored := by
  induction items generalizing plans with
  | nil =>
      simp [forInitTokenPlans?] at success
      subst plans
      simp
  | cons head tail induction =>
      rw [forInitTokenPlans?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPlan, headEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tailPlans, tailEq, resultEq⟩
      injection resultEq with plansEq
      subst plans
      intro plan member
      simp only [List.mem_cons] at member
      have headAnchored :=
        forInitTokenPlan?_wellAnchored head headPlan headEq
      rcases member with rfl | member
      · exact headAnchored
      · exact induction tailPlans tailEq plan member

/-- Every accepted for-loop post-item plan has mandatory endpoints. -/
theorem forPostTokenPlan?_wellAnchored
    (item : ForPostItem) (plan : TokenPlan)
    (success : forPostTokenPlan? item = some plan) :
    plan.WellAnchored := by
  rcases item with ⟨span, payload⟩
  cases payload with
  | assignment operator left right =>
      simp only [forPostTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨leftPlan, leftEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨rightPlan, rightEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      apply TokenPlan.WellAnchored.enclose
      simp only [TokenPlan.concat_cons, TokenPlan.concat_nil,
        TokenPlan.append_empty]
      exact TokenPlan.WellAnchored.append
        (expressionTokenPlanAt?_wellAnchored
          .annotation left leftPlan leftEq)
        (TokenPlan.WellAnchored.append
          (assignmentOperatorTokenPlan_wellAnchored operator)
          (expressionTokenPlanAt?_wellAnchored
            .annotation right rightPlan rightEq))
  | expression expression =>
      simp only [forPostTokenPlan?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨expressionPlan, expressionEq, resultEq⟩
      injection resultEq with planEq
      subst plan
      exact TokenPlan.WellAnchored.enclose
        (expressionTokenPlanAt?_wellAnchored
          .annotation expression expressionPlan expressionEq) span

/-- Every successful post-list traversal returns anchored plans. -/
theorem forPostTokenPlans?_allWellAnchored
    (items : List ForPostItem) (plans : List TokenPlan)
    (success : forPostTokenPlans? items = some plans) :
    ∀ plan ∈ plans, plan.WellAnchored := by
  induction items generalizing plans with
  | nil =>
      simp [forPostTokenPlans?] at success
      subst plans
      simp
  | cons head tail induction =>
      rw [forPostTokenPlans?] at success
      rcases Option.bind_eq_some_iff.mp success with
        ⟨headPlan, headEq, success⟩
      rcases Option.bind_eq_some_iff.mp success with
        ⟨tailPlans, tailEq, resultEq⟩
      injection resultEq with plansEq
      subst plans
      intro plan member
      simp only [List.mem_cons] at member
      have headAnchored :=
        forPostTokenPlan?_wellAnchored head headPlan headEq
      rcases member with rfl | member
      · exact headAnchored
      · exact induction tailPlans tailEq plan member

private abbrev forInitSourceBranches : List EbnfExpr := [
  .atom (.nonterminal .letBinding),
  .sequence [
    .atom (.nonterminal .expression),
    .atom (.nonterminal .assignmentOperator),
    .atom (.nonterminal .expression)],
  .atom (.nonterminal .expression)]

private abbrev forPostSourceBranches : List EbnfExpr := [
  .sequence [
    .atom (.nonterminal .expression),
    .atom (.nonterminal .assignmentOperator),
    .atom (.nonterminal .expression)],
  .atom (.nonterminal .expression)]

/-- For-loop initializers preserve their selected child plan and add the
checked interval span of the initializer node. -/
theorem forInitItem_tokenPlanSound :
    GrammarRuleTokenPlanSound .forInitItem := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | forInitItemLet origin finish binding witness =>
      change EbnfValue file tokens (.choice forInitSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have bindingEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .letBinding binding selected
      have coreEvidence : TokenPlanEvidence
          (letBindingTokenPlan? binding)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using bindingEvidence
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (letBindingTokenPlan?_wellAnchored binding) witness.consumed
      simpa [ruleTokenPlan?, forInitTokenPlan?, sourceLoc,
        optionMap_eq_bindPure] using enclosed
  | forInitItemAssignment origin finish left operator right witness =>
      change EbnfValue file tokens (.choice forInitSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      have coreEvidence : TokenPlanEvidence
          (forAssignmentTokenPlan? left operator right)
          (PhysicalTokens tokens origin finish) := by
        apply sequenceEvidence.candidate_eq
        simp [forAssignmentTokenPlan?, sourceRuleTokenPlanLayout,
          ruleTokenPlan?, expressionTokenPlan?, Option.bind_assoc]
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (forAssignmentTokenPlan?_wellAnchored left operator right)
        witness.consumed
      simpa [ruleTokenPlan?, forInitTokenPlan?, sourceLoc,
        forAssignmentTokenPlan?, optionMap_eq_bindPure,
        Option.bind_assoc] using enclosed
  | forInitItemExpression origin finish expression witness =>
      change EbnfValue file tokens (.choice forInitSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have expressionEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .expression expression selected
      have coreEvidence : TokenPlanEvidence
          (expressionTokenPlan? expression)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          expressionEvidence
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (expressionTokenPlan?_wellAnchored expression) witness.consumed
      simpa [ruleTokenPlan?, forInitTokenPlan?, sourceLoc,
        expressionTokenPlan?, optionMap_eq_bindPure] using enclosed

/-- For-loop post items preserve their selected expression or assignment
plan and add the checked interval span of the post item. -/
theorem forPostItem_tokenPlanSound :
    GrammarRuleTokenPlanSound .forPostItem := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | forPostItemAssignment origin finish left operator right witness =>
      change EbnfValue file tokens (.choice forPostSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have sequenceEvidence := TokenPlanEvidence.sequence
        sourceRuleTokenPlanLayout _ _ selected
      have coreEvidence : TokenPlanEvidence
          (forAssignmentTokenPlan? left operator right)
          (PhysicalTokens tokens origin finish) := by
        apply sequenceEvidence.candidate_eq
        simp [forAssignmentTokenPlan?, sourceRuleTokenPlanLayout,
          ruleTokenPlan?, expressionTokenPlan?, Option.bind_assoc]
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (forAssignmentTokenPlan?_wellAnchored left operator right)
        witness.consumed
      simpa [ruleTokenPlan?, forPostTokenPlan?, sourceLoc,
        forAssignmentTokenPlan?, optionMap_eq_bindPure,
        Option.bind_assoc] using enclosed
  | forPostItemExpression origin finish expression witness =>
      change EbnfValue file tokens (.choice forPostSourceBranches) at input
      have selected := TokenPlanEvidence.choice
        sourceRuleTokenPlanLayout _ _ inputEvidence
      have expressionEvidence := TokenPlanEvidence.rule
        sourceRuleTokenPlanLayout .expression expression selected
      have coreEvidence : TokenPlanEvidence
          (expressionTokenPlan? expression)
          (PhysicalTokens tokens origin finish) := by
        simpa [sourceRuleTokenPlanLayout, ruleTokenPlan?] using
          expressionEvidence
      have enclosed := TokenPlanEvidence.enclose coreEvidence
        (expressionTokenPlan?_wellAnchored expression) witness.consumed
      simpa [ruleTokenPlan?, forPostTokenPlan?, sourceLoc,
        expressionTokenPlan?, optionMap_eq_bindPure] using enclosed

end Solcore.Surface.Multi
