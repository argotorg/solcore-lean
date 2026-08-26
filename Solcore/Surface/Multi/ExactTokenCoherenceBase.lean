import Solcore.Surface.Multi.ExactTokenEvidence

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

/-- An interval whose boundaries coincide contains no retained token. -/
@[simp] theorem PhysicalTokens.self
    (tokens : List Token) (boundary : Boundary tokens) :
    PhysicalTokens tokens boundary boundary = [] := by
  simp [PhysicalTokens]

namespace TokenPlanEvidence

/-- Compose evidence carried by two adjacent ordered parser intervals. -/
theorem appendPhysical
    {tokens : List Token} {origin shared finish : Boundary tokens}
    {leftCandidate rightCandidate : Option TokenPlan}
    (leftOrdered : origin.val ≤ shared.val)
    (rightOrdered : shared.val ≤ finish.val)
    (left : TokenPlanEvidence leftCandidate
      (PhysicalTokens tokens origin shared))
    (right : TokenPlanEvidence rightCandidate
      (PhysicalTokens tokens shared finish)) :
    TokenPlanEvidence
      (do
        let leftPlan ← leftCandidate
        let rightPlan ← rightCandidate
        pure (leftPlan.append rightPlan))
      (PhysicalTokens tokens origin finish) := by
  rw [PhysicalTokens.append leftOrdered rightOrdered]
  exact left.append right

/-- Extend an ordered prefix by one checked grammar terminal. -/
theorem appendMatchedTerminal
    {file : WorkspaceFile} {tokens : List Token}
    {origin : Boundary tokens} {terminal : TerminalSymbol}
    {candidate : Option TokenPlan}
    (matched : MatchedTerminal file tokens terminal)
    (ordered : origin.val ≤ matched.cursor.beforeBoundary.val)
    (prior : TokenPlanEvidence candidate
      (PhysicalTokens tokens origin matched.cursor.beforeBoundary)) :
    TokenPlanEvidence
      (do
        let plan ← candidate
        pure (plan.append (matched.grammarTokenPlan terminal)))
      (PhysicalTokens tokens origin matched.cursor.afterBoundary) := by
  exact appendPhysical ordered (by
      simp [TerminalCursor.beforeBoundary, TerminalCursor.afterBoundary])
    prior (matched.grammarTokenPlan_evidence terminal)

end TokenPlanEvidence

end Solcore.Surface.Multi
