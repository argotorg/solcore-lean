import Solcore.Surface.Multi.ExactTokenLexicalEvidence
import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private theorem TokenPlanEvidence.weakenAssemblyKeywordAndEnclose
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {keywordSpan sliceSpan outputSpan : SourceSpan}
    {slice : AssemblySlice}
    (evidence : TokenPlanEvidence
      (Option.some ((TokenPlan.exact (.hardKeyword .assemblyKw) keywordSpan).append
        (TokenPlan.exact (.assemblyBlock slice) sliceSpan)))
      (PhysicalTokens tokens origin finish))
    (consumed : ConsumedSpan file tokens origin finish outputSpan) :
    TokenPlanEvidence
      (Option.some (TokenPlan.enclose outputSpan
        ((TokenPlan.plain (.hardKeyword .assemblyKw)).append
          (TokenPlan.exact (.assemblyBlock slice) sliceSpan))))
      (PhysicalTokens tokens origin finish) := by
  rcases evidence with ⟨plan, candidateEq, relation⟩
  simp only [Option.some.injEq] at candidateEq
  subst plan
  have innerRelation : TokenSlot.ListMatches
      ((TokenPlan.plain (.hardKeyword .assemblyKw)).append
        (TokenPlan.exact (.assemblyBlock slice) sliceSpan)).slots
      (PhysicalTokens tokens origin finish) := by
    apply TokenSlot.ListMatches.exactBetweenToPlain
      (left := TokenPlan.empty)
      (right := TokenPlan.exact (.assemblyBlock slice) sliceSpan)
    simpa using relation
  have innerAnchored :
      ((TokenPlan.plain (.hardKeyword .assemblyKw)).append
        (TokenPlan.exact (.assemblyBlock slice) sliceSpan)).WellAnchored := by
    rfl
  exact TokenPlanEvidence.enclose
    (TokenPlanEvidence.some innerRelation)
    (fun enclosedPlan success => by
      simp only [Option.some.injEq] at success
      subst enclosedPlan
      exact innerAnchored)
    consumed

/-- An assembly-statement reduction preserves its complete token plan when
the retained token stream has both file ownership and exact source evidence. -/
theorem assemblyStatement_tokenPlanSound_of_tokensSourceExact
    {file : WorkspaceFile} {tokens : List Token}
    {origin finish : Boundary tokens}
    {input : EbnfValue file tokens (m2cV1.rhs .assemblyStatement)}
    {output : RuleValue .assemblyStatement}
    (owned : TokensOwnedBy file tokens)
    (sourceExact : TokensSourceExact file tokens)
    (reduces : RuleReduction file tokens .assemblyStatement
      origin finish input output)
    (inputEvidence : TokenPlanEvidence
      (input.tokenPlan? sourceRuleTokenPlanLayout)
      (PhysicalTokens tokens origin finish)) :
    TokenPlanEvidence
      (ruleTokenPlan? .assemblyStatement output)
      (PhysicalTokens tokens origin finish) := by
  generalize inputEq : input = sourceInput at reduces inputEvidence
  cases reduces with
  | assemblyStatement origin finish assemblyKeyword assemblyToken slice
      projects witness =>
      change EbnfValue file tokens (.sequence [
        .atom (.terminal (.hardKeyword .assemblyKw)),
        .atom (.terminal (.category .assemblyBlock))]) at input
      simp only [m2cV1, m2cV1Rhs, Grammar.sequence,
        Grammar.hardKeyword, Grammar.category, Grammar.terminal,
        EbnfExpr.children] at inputEvidence
      rw [EbnfValue.tokenPlan?_sequence] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_cons] at inputEvidence
      rw [EbnfValue.tokenPlan?_terminalAtom] at inputEvidence
      rw [EbnfValues.tokenPlan?_nil] at inputEvidence
      rw [MatchedTerminal.physicalTokenPlan_hardKeyword,
        MatchedTerminal.physicalTokenPlan_assemblyBlock
          owned sourceExact assemblyToken slice projects] at inputEvidence
      have enclosed := inputEvidence.weakenAssemblyKeywordAndEnclose
        witness.consumed
      simpa [ruleTokenPlan?, statementTokenPlan?, sourceLoc,
        TokenPlan.concat_cons] using enclosed

end Solcore.Surface.Multi
