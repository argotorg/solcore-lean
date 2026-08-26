import Solcore.Surface.Multi.ExactTokenInterval

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- A successful token-plan candidate together with its complete match against
the retained tokens consumed by one parser interval. -/
def TokenPlanEvidence
    (candidate : Option TokenPlan) (actual : List Token) : Prop :=
  ∃ plan, candidate = some plan ∧
    TokenSlot.ListMatches plan.slots actual

namespace TokenPlanEvidence

/-- Package a concrete plan match as successful candidate evidence. -/
theorem some
    {plan : TokenPlan} {actual : List Token}
    (relation : TokenSlot.ListMatches plan.slots actual) :
    TokenPlanEvidence (some plan) actual := by
  exact ⟨plan, rfl, relation⟩

/-- The successful empty plan matches the empty retained-token sequence. -/
theorem empty :
    TokenPlanEvidence (Option.some TokenPlan.empty) [] := by
  exact some TokenSlot.ListMatches.nil

/-- Rewrite the candidate while preserving its token evidence. -/
theorem candidate_eq
    {candidate rewritten : Option TokenPlan} {actual : List Token}
    (evidence : TokenPlanEvidence candidate actual)
    (equation : candidate = rewritten) :
    TokenPlanEvidence rewritten actual := by
  subst rewritten
  exact evidence

/-- Rewrite the actual token sequence while preserving its plan evidence. -/
theorem actual_eq
    {candidate : Option TokenPlan} {actual rewritten : List Token}
    (evidence : TokenPlanEvidence candidate actual)
    (equation : actual = rewritten) :
    TokenPlanEvidence candidate rewritten := by
  subst rewritten
  exact evidence

/-- Successful candidate plans and their matching physical token sequences
compose in source order. -/
theorem append
    {leftCandidate rightCandidate : Option TokenPlan}
    {leftActual rightActual : List Token}
    (left : TokenPlanEvidence leftCandidate leftActual)
    (right : TokenPlanEvidence rightCandidate rightActual) :
    TokenPlanEvidence
      (do
        let leftPlan ← leftCandidate
        let rightPlan ← rightCandidate
        pure (leftPlan.append rightPlan))
      (leftActual ++ rightActual) := by
  rcases left with ⟨leftPlan, leftEq, leftRelation⟩
  rcases right with ⟨rightPlan, rightEq, rightRelation⟩
  refine ⟨leftPlan.append rightPlan, ?_, ?_⟩
  · simp [leftEq, rightEq]
  · exact leftRelation.append rightRelation

/-- Pointwise evidence for a list of values concatenates into evidence for
the corresponding list visitor and flattened physical token sequence. -/
theorem concat
    {alpha : Type}
    (candidate : alpha → Option TokenPlan)
    (actual : alpha → List Token)
    (values : List alpha)
    (evidence : ∀ value ∈ values,
      TokenPlanEvidence (candidate value) (actual value)) :
    TokenPlanEvidence
      (Option.map TokenPlan.concat (values.mapM candidate))
      (values.flatMap actual) := by
  induction values with
  | nil => simpa [TokenPlan.concat, TokenPlan.empty] using empty
  | cons value rest induction =>
      have headEvidence := evidence value (by simp)
      have tailEvidence := induction (by
        intro candidateValue member
        exact evidence candidateValue (by simp [member]))
      have candidateEq :
          (do
            let headPlan ← candidate value
            let tailPlan ←
              Option.map TokenPlan.concat (rest.mapM candidate)
            pure (headPlan.append tailPlan)) =
            Option.map TokenPlan.concat
              ((value :: rest).mapM candidate) := by
        rw [List.mapM_cons]
        cases candidate value <;>
          cases rest.mapM candidate <;>
            rfl
      exact (headEvidence.append tailEvidence).candidate_eq candidateEq

/-- Enclose a successful, endpoint-anchored plan with the exact endpoints of
its consumed parser interval. -/
theorem enclose
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens} {span : SourceSpan}
    {candidate : Option TokenPlan}
    (evidence : TokenPlanEvidence candidate
      (PhysicalTokens tokens origin finish))
    (anchored : ∀ plan,
      candidate = Option.some plan → plan.WellAnchored)
    (consumed : ConsumedSpan file tokens origin finish span) :
    TokenPlanEvidence
      (candidate.map (TokenPlan.enclose span))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  refine ⟨plan.enclose span, ?_, ?_⟩
  · simp [candidateEq]
  · exact TokenPlan.enclose_listMatches relation
      (anchored plan candidateEq)
      consumed.startsPhysicalTokens consumed.endsPhysicalTokens

end TokenPlanEvidence

/-- A checked grammar scan yields token-plan evidence for exactly its local
physical parser interval. -/
theorem MatchedTerminal.grammarTokenPlan_evidence
    {file : WorkspaceFile} {tokens : List Token}
    (terminal : TerminalSymbol)
    (matched : MatchedTerminal file tokens terminal) :
    TokenPlanEvidence (some (matched.grammarTokenPlan terminal))
      (PhysicalTokens tokens matched.cursor.beforeBoundary
        matched.cursor.afterBoundary) := by
  apply TokenPlanEvidence.some
  rw [matched.physicalTokens_before_after]
  exact matched.grammarTokenPlan_matches terminal

end Solcore.Surface.Multi
