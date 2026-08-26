import Solcore.Surface.Multi.ExactTokenAnchoring
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A fully selected let-binding plan begins with its fixed keyword. -/
private theorem letBindingCore_startsRequired
    (span : SourceSpan) (name : IdentifierOccurrence)
    (typePlan initializerPlan : TokenPlan) :
    TokenPlan.WellAnchored.StartsRequired (TokenPlan.enclose span
      (TokenPlan.concat [
      .plain (.hardKeyword .letKw),
      identifierPlan name,
      typePlan,
      initializerPlan])) := by
  apply TokenPlan.WellAnchored.StartsRequired.enclose
  exact TokenPlan.WellAnchored.StartsRequired.concat_plain_first
    (.hardKeyword .letKw)
    [identifierPlan name, typePlan, initializerPlan]

/-- The let-binding candidate after its initializer suffix has been selected. -/
private def letBindingTypeResult?
    (span : SourceSpan) (name : IdentifierOccurrence)
    (comptime : Option Marker) (typeExpression : Option TypeExpr)
    (initializerPlan : TokenPlan) : Option TokenPlan :=
  match comptime, typeExpression with
  | none, none => some (.enclose span (.concat [
      .plain (.hardKeyword .letKw),
      identifierPlan name,
      .empty,
      initializerPlan]))
  | some _, none => none
  | none, some typeExpression =>
      match typeExpression.payload with
      | .comptime .. => none
      | _ => do
          let innerPlan ← typeExprPlan? typeExpression
          pure (.enclose span (.concat [
            .plain (.hardKeyword .letKw),
            identifierPlan name,
            .append (.plain (.symbol .colon)) innerPlan,
            initializerPlan]))
  | some marker, some typeExpression =>
      if marker.payload = .comptimeModifier then do
        let innerPlan ← typeExprPlan? typeExpression
        pure (.enclose span (.concat [
          .plain (.hardKeyword .letKw),
          identifierPlan name,
          .concat [
            .plain (.symbol .colon),
            .exact (.identifier ContextualKeyword.comptimeKw.spelling)
              marker.span,
            innerPlan],
          initializerPlan]))
      else
        none

/-- Selecting a successful type suffix leaves the fixed keyword at the start,
regardless of the already-selected initializer suffix. -/
private theorem letBindingType_startsRequired
    (span : SourceSpan) (name : IdentifierOccurrence)
    (comptime : Option Marker) (typeExpression : Option TypeExpr)
    (initializerPlan plan : TokenPlan)
    (success : letBindingTypeResult? span name comptime typeExpression
      initializerPlan = Option.some plan) :
    TokenPlan.WellAnchored.StartsRequired plan := by
  unfold letBindingTypeResult? at success
  cases comptime with
  | none =>
      cases typeExpression with
      | none =>
          injection success with planEq
          subst plan
          exact letBindingCore_startsRequired span name .empty
            initializerPlan
      | some typeExpression =>
          rcases typeExpression with ⟨typeSpan, typePayload⟩
          cases typePayload with
          | named qualified arguments =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨typePlan, _typeSuccess, resultEq⟩
              injection resultEq with planEq
              subst plan
              exact letBindingCore_startsRequired span name
                ((TokenPlan.plain (.symbol .colon)).append typePlan)
                initializerPlan
          | proxy marker inner =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨typePlan, _typeSuccess, resultEq⟩
              injection resultEq with planEq
              subst plan
              exact letBindingCore_startsRequired span name
                ((TokenPlan.plain (.symbol .colon)).append typePlan)
                initializerPlan
          | function domain codomain =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨typePlan, _typeSuccess, resultEq⟩
              injection resultEq with planEq
              subst plan
              exact letBindingCore_startsRequired span name
                ((TokenPlan.plain (.symbol .colon)).append typePlan)
                initializerPlan
          | tuple elements =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨typePlan, _typeSuccess, resultEq⟩
              injection resultEq with planEq
              subst plan
              exact letBindingCore_startsRequired span name
                ((TokenPlan.plain (.symbol .colon)).append typePlan)
                initializerPlan
          | group inner =>
              rcases Option.bind_eq_some_iff.mp success with
                ⟨typePlan, _typeSuccess, resultEq⟩
              injection resultEq with planEq
              subst plan
              exact letBindingCore_startsRequired span name
                ((TokenPlan.plain (.symbol .colon)).append typePlan)
                initializerPlan
          | comptime marker inner =>
              contradiction
  | some comptimeMarker =>
      cases typeExpression with
      | none =>
          contradiction
      | some typeExpression =>
          by_cases accepted : comptimeMarker.payload = .comptimeModifier
          · simp only [accepted, ↓reduceIte] at success
            rcases Option.bind_eq_some_iff.mp success with
              ⟨typePlan, _typeSuccess, resultEq⟩
            injection resultEq with planEq
            subst plan
            exact letBindingCore_startsRequired span name
              (TokenPlan.concat [
                .plain (.symbol .colon),
                .exact
                  (.identifier ContextualKeyword.comptimeKw.spelling)
                  comptimeMarker.span,
                typePlan]) initializerPlan
          · simp [accepted] at success

/-- Every accepted let-binding plan begins with the mandatory `let` token. -/
private theorem letBindingTokenPlan?_startsRequired
    (binding : LetBinding) (plan : TokenPlan)
    (success : letBindingTokenPlan? binding = Option.some plan) :
    TokenPlan.WellAnchored.StartsRequired plan := by
  rcases binding with ⟨span, ⟨comptime, name, typeExpression, initializer⟩⟩
  rw [letBindingTokenPlan?.eq_def] at success
  cases initializer with
  | none =>
      simp only at success
      change letBindingTypeResult? span name comptime typeExpression
        .empty = Option.some plan at success
      exact letBindingType_startsRequired span name comptime typeExpression
        .empty plan success
  | some expression =>
      cases initializerEq : expressionTokenPlanAt? .annotation expression with
      | none =>
          simp only [initializerEq] at success
          cases comptime with
          | none =>
              cases typeExpression with
              | none => simp at success
              | some typeExpression =>
                  rcases typeExpression with ⟨typeSpan, typePayload⟩
                  cases typePayload <;> simp_all
          | some marker =>
              cases typeExpression with
              | none => simp at success
              | some typeExpression =>
                  by_cases accepted : marker.payload = .comptimeModifier <;>
                    simp_all
      | some initializerPlan =>
          simp only [initializerEq] at success
          change letBindingTypeResult? span name comptime typeExpression
            ((TokenPlan.plain (.symbol .equal)).append initializerPlan) =
              Option.some plan at success
          exact letBindingType_startsRequired span name comptime typeExpression
            ((TokenPlan.plain (.symbol .equal)).append initializerPlan)
            plan success

/-- A let statement keeps its binding plan, weakens the grammar-supplied
semicolon, and constrains the resulting statement endpoints. -/
theorem letStatement_tokenPlanSound :
    GrammarRuleTokenPlanSound .letStatement := by
  intro file tokens origin finish input output _owned reduces inputEvidence
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | letStatement origin finish binding semicolon witness =>
      change RuleValue .letBinding at binding
      change EbnfValue file tokens (.sequence [
        .atom (.nonterminal .letBinding),
        .atom (.terminal (.symbol .semicolon))]) at input
      change TokenPlanEvidence
        (statementTokenPlan? false
          (sourceLoc witness (.letBinding binding) : Statement))
        (PhysicalTokens tokens origin finish)
      rw [← inputEq] at inputEvidence
      have sourceCandidateEq :
          input.tokenPlan? sourceRuleTokenPlanLayout = (do
            let bindingPlan ← letBindingTokenPlan? binding
            pure (bindingPlan.append (TokenPlan.exact
              (.symbol .semicolon) semicolon.span))) := by
        rw [inputEq]
        simp only [EbnfExpr.children,
          EbnfValue.tokenPlan?_sequence,
          EbnfValues.tokenPlan?_cons,
          EbnfValue.tokenPlan?_ruleAtom,
          EbnfValue.tokenPlan?_terminalAtom,
          EbnfValues.tokenPlan?_nil,
          sourceRuleTokenPlanLayout]
        rw [MatchedTerminal.physicalTokenPlan_symbol]
        change LetBinding at binding
        rfl
      have sourceEvidence := inputEvidence.candidate_eq sourceCandidateEq
      change LetBinding at binding
      rcases sourceEvidence with ⟨sourcePlan, candidateEq, relation⟩
      cases bindingEq : letBindingTokenPlan? binding with
      | none =>
          simp [bindingEq] at candidateEq
      | some bindingPlan =>
          simp only [bindingEq] at candidateEq
          injection candidateEq with sourcePlanEq
          rw [← sourcePlanEq] at relation
          have innerRelation : TokenSlot.ListMatches
              (bindingPlan.append
                (TokenPlan.plain (.symbol .semicolon))).slots
              (PhysicalTokens tokens origin finish) := by
            apply TokenSlot.ListMatches.exactBetweenToPlain
              (left := bindingPlan) (right := TokenPlan.empty)
            simpa using relation
          have innerAnchored :
              (bindingPlan.append
                (TokenPlan.plain (.symbol .semicolon))).WellAnchored := by
            apply TokenPlan.WellAnchored.of_starts_ends_append
              (letBindingTokenPlan?_startsRequired binding bindingPlan
                bindingEq)
            exact TokenPlan.WellAnchored.EndsRequired.append_plain_last
              TokenPlan.empty (.symbol .semicolon)
          have enclosed := TokenPlanEvidence.enclose
            (TokenPlanEvidence.some innerRelation)
            (fun enclosedPlan success => by
              simp only [Option.some.injEq] at success
              subst enclosedPlan
              exact innerAnchored)
            witness.consumed
          simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
            bindingEq] using enclosed

end Solcore.Surface.Multi
