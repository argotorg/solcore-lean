import Solcore.Surface.Multi.ExactTokenRuleLeaf
import Solcore.Surface.Multi.ExactTokenRuleSoundness

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

private def badSegment : PathSegment := {
  text := "contract"
  valid := by decide
}

private def badPath : CanonicalSourcePath := {
  modulePath := {
    segments := [badSegment]
    nonempty := by simp
  }
}

private def badSource : SourceId := {
  library := .main
  path := badPath
}

private def badFile : WorkspaceFile := {
  id := badSource
  content := "contract"
}

private def badSpan : SourceSpan := {
  source := badSource
  startByte := 0
  endByte := 8
}

private def badToken : Token := {
  span := badSpan
  payload := .identifier "contract"
}

private def badTokens : List Token := [badToken]

private def badCursor : TerminalCursor badTokens :=
  ⟨0, by simp [badTokens]⟩

private theorem badSpanValid : badSpan.ValidFor badFile := by
  have contentSize : "contract".utf8ByteSize = 8 := by decide
  simp [badSpan, badFile, badSource, SourceSpan.ValidFor,
    isUtf8Boundary, contentSize]

private def badMatched : MatchedTerminal badFile badTokens
    (.category .pathComponent) := {
  cursor := badCursor
  value := .retained badToken
  span := badSpan
  «at» := .retained badCursor badToken (by simp [badCursor, badTokens])
    (by simp [badCursor, badTokens, badToken]) badSpanValid
  «matches» := Or.inl ⟨"contract", badSegment, rfl, by
    exact PathSegment.parse_render badSegment⟩
}

private def badData : RuleReduction.SpelledTerminalData badFile badTokens
    (.category .pathComponent) PathSegment := {
  matched := badMatched
  spelling := "contract"
  parsed := badSegment
}

private theorem badProjects : PathSegmentProjects badData.matched
    badData.spelling badData.parsed := by
  exact ⟨badToken, rfl, Or.inl rfl, PathSegment.parse_render badSegment⟩

private def badOrigin : Boundary badTokens := Boundary.start badTokens

private def badFinish : Boundary badTokens :=
  badCursor.afterBoundary

private theorem badOwned : TokensOwnedBy badFile badTokens := by
  intro token member
  simp [badTokens] at member
  subst token
  exact badSpanValid

private def badWitness : ConsumedSpanWitness badFile badTokens
    badOrigin badFinish :=
  ConsumedSpanWitness.compute badFile badTokens badOrigin badFinish
    badOwned (by
      simp [badOrigin, badFinish, badCursor, Boundary.start,
        TerminalCursor.afterBoundary])

private abbrev badTailExpression : EbnfExpr :=
  .group (.sequence [
    .atom (.terminal (.symbol .dot)),
    .atom (.terminal (.category .pathComponent))])

private abbrev badRelativeChildren : List EbnfExpr := [
  .atom (.terminal (.category .pathComponent)),
  .star badTailExpression]

private abbrev badBranches : List EbnfExpr := [
      .sequence [
        .atom (.terminal (.symbol .at)),
        .atom (.terminal (.category .pathComponent)),
        .atom (.terminal (.symbol .dot)),
        .atom (.terminal (.category .pathComponent)),
        .star badTailExpression],
      .sequence badRelativeChildren]

private def badSequence : EbnfValue badFile badTokens
    (.sequence badRelativeChildren) :=
  EbnfValue.sequence badRelativeChildren
    (EbnfValues.cons _ _
      (EbnfValue.terminalAtom
        (.category .pathComponent) badData.matched)
      (EbnfValues.cons _ _
        (EbnfValue.star badTailExpression [])
        EbnfValues.nil))

private def badChoice : EbnfValue badFile badTokens
    (.choice badBranches) :=
  EbnfValue.choice badBranches
      ⟨⟨1, by decide⟩,
        badSequence⟩

private def badInput : EbnfValue badFile badTokens
    (m2cV1.rhs .moduleRef) :=
  EbnfValue.transport (by rfl) badChoice

private def badOutput : RuleValue .moduleRef :=
  sourceLoc badWitness (.relative {
    head := RuleReduction.terminalLoc badData.matched badData.parsed
    tail := []
  })

private theorem badReduction : RuleReduction badFile badTokens .moduleRef
    badOrigin badFinish badInput badOutput := by
  simpa [badInput, badChoice, badSequence, badBranches,
    badRelativeChildren, badTailExpression, badOutput] using
    (RuleReduction.moduleRefRelativeOther
      badOrigin badFinish badData [] badProjects (by simp)
        (by decide) (by decide) badWitness)

private theorem badInputEvidence : TokenPlanEvidence
    (badInput.tokenPlan? sourceRuleTokenPlanLayout)
    (PhysicalTokens badTokens badOrigin badFinish) := by
  refine ⟨TokenPlan.exact (.identifier "contract") badSpan, ?_, ?_⟩
  · calc
      _ = badChoice.tokenPlan? sourceRuleTokenPlanLayout :=
        EbnfValue.tokenPlan?_transport sourceRuleTokenPlanLayout _ _
      _ = badSequence.tokenPlan? sourceRuleTokenPlanLayout := by
        simp [badChoice, badBranches, badRelativeChildren,
          EbnfValue.tokenPlan?_choice]
      _ = _ := by
        unfold badSequence
        rw [EbnfValue.tokenPlan?_sequence,
          EbnfValues.tokenPlan?_cons,
          EbnfValue.tokenPlan?_terminalAtom,
          EbnfValues.tokenPlan?_cons,
          EbnfValue.tokenPlan?_star,
          EbnfValues.tokenPlan?_nil]
        simp [badData, badMatched, badToken,
          MatchedTerminal.physicalTokenPlan]
  · change TokenSlot.ListMatches
      [TokenSlot.required
        (ExpectedToken.exact (.identifier "contract") badSpan)]
      [badToken]
    exact .required (by
      simp [ExpectedToken.Matches, ExpectedToken.exact, badToken,
        TokenSpanConstraint.Holds]) .nil

/-- The rule-wide contract is too weak for module references: a synthetic
path-category token may carry an identifier spelling that the visitor
canonically classifies as a hard keyword. -/
theorem moduleRef_tokenPlanSound_counterexample :
    ¬ GrammarRuleTokenPlanSound .moduleRef := by
  intro sound
  have outputEvidence := sound badOwned badReduction badInputEvidence
  rcases outputEvidence with ⟨plan, candidateEq, relation⟩
  simp [badOutput, ruleTokenPlan?, moduleReferencePlan?, sourceLoc,
    badWitness, badData, badMatched, badSegment, badToken,
    relativeModuleReferenceShapeExactBool,
    RuleReduction.terminalLoc] at candidateEq
  rcases candidateEq with ⟨_notStandard, candidateEq⟩
  subst plan
  change TokenSlot.ListMatches _ [badToken] at relation
  cases relation with
  | required head tail =>
      have kindEq := head.1
      simp [tokenKindOfPathSpelling, HardKeyword.ofString?,
        PathSegment.render, badToken, ExpectedToken.exact]
        at kindEq

end Solcore.Surface.Multi
