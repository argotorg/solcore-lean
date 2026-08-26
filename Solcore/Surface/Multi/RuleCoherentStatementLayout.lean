import Solcore.Surface.Multi.RuleCoherentIntervalLocationMatchArmCase

set_option autoImplicit false

namespace Solcore.Surface.Multi

open Grammar Solcore.Workspace

namespace RuleReduction

@[simp] private theorem bodyLayout_statementRuleAtoms
    {file : WorkspaceFile} {tokens : List Token}
    (statements : List Statement) :
    (statements.map (EbnfValue.ruleAtom
      (file := file) (tokens := tokens) .statement)).flatMap
        (fun value => value.layoutSpans matchArmStatementSpanLayout) =
      statements.map (fun statement => statement.span) := by
  induction statements with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      change
        (EbnfValue.ruleAtom (file := file) (tokens := tokens)
            .statement head).layoutSpans matchArmStatementSpanLayout ++
          (tail.map (EbnfValue.ruleAtom .statement)).flatMap
            (fun value => value.layoutSpans matchArmStatementSpanLayout) =
        head.span :: tail.map (fun statement => statement.span)
      rw [EbnfValue.layoutSpans_ruleAtom, inductionHypothesis]
      rfl

private abbrev bodyStatementLayoutChildren : List EbnfExpr := [
  .atom (.terminal (.symbol .leftBrace)),
  .star (.atom (.nonterminal .statement)),
  .atom (.terminal (.symbol .rightBrace))]

private def bodyStatementLayoutSourceValue
    {file : WorkspaceFile} {tokens : List Token}
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace)) :
    EbnfValue file tokens (.sequence bodyStatementLayoutChildren) :=
  EbnfValue.sequence bodyStatementLayoutChildren <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .leftBrace) openBrace) <|
    EbnfValues.cons _ _
      (EbnfValue.star (.atom (.nonterminal .statement))
        (statements.map (EbnfValue.ruleAtom .statement))) <|
    EbnfValues.cons _ _
      (EbnfValue.terminalAtom (.symbol .rightBrace) closeBrace) <|
    EbnfValues.nil

/-- The source-layout trace for a body consists of the opening brace, every
statement span in order, and the closing brace. -/
@[simp] theorem body_inputLayoutSpans
    {file : WorkspaceFile} {tokens : List Token}
    (origin finish : Boundary tokens)
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish) :
    (inputValue
      (RuleReduction.body origin finish openBrace statements closeBrace
        witness)).layoutSpans matchArmStatementSpanLayout =
      openBrace.span ::
        (statements.map (fun statement => statement.span) ++
          [closeBrace.span]) := by
  have sourceEq : inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          witness) =
      EbnfValue.transport (by rfl)
        (bodyStatementLayoutSourceValue openBrace statements closeBrace) := by
    rfl
  rw [sourceEq, EbnfValue.layoutSpans_transport]
  unfold bodyStatementLayoutSourceValue
  rw [EbnfValue.layoutSpans_sequence]
  rw [EbnfValues.layoutSpans_cons, EbnfValues.layoutSpans_cons,
    EbnfValues.layoutSpans_cons, EbnfValues.layoutSpans_nil]
  rw [EbnfValue.layoutSpans_terminalAtom,
    EbnfValue.layoutSpans_star,
    EbnfValue.layoutSpans_terminalAtom]
  rw [bodyLayout_statementRuleAtoms]
  rfl

/-- A coherent completed body root retains every repeated statement span in
grammar order inside the body token interval. -/
theorem body_statementLayout_of_coherentRoot
    {file : WorkspaceFile} {tokens : List Token}
    {memo : GuardMemo tokens}
    {correct : PhaseBCorrect file tokens memo}
    {final : AllGuardsFinal memo}
    {owned : TokensOwnedBy file tokens}
    {origin finish : Boundary tokens}
    {context : GuardContext tokens}
    {priorValues : PrefixValues file tokens
      (CanonicalRootLocationItem tokens .body origin finish context)}
    {complete : CompleteItem
      (CanonicalRootLocationItem tokens .body origin finish context).raw}
    {coherentPrefix : CoherentPrefix file tokens memo correct final
      (CanonicalRootLocationItem tokens .body origin finish context)
        priorValues}
    (openBrace : MatchedTerminal file tokens (.symbol .leftBrace))
    (statements : List Statement)
    (closeBrace : MatchedTerminal file tokens (.symbol .rightBrace))
    (witness : ConsumedSpanWitness file tokens origin finish)
    (inputEq : inputValue
        (RuleReduction.body origin finish openBrace statements closeBrace
          witness) =
      RootAction.unpack .body
        (PrefixValues.fullValue
          (CanonicalRootLocationItem tokens .body origin finish context)
          complete priorValues))
    {trace : SourceAnchorTrace file tokens}
    {carries : PrefixCarriesSourceTrace file tokens memo correct final owned
      coherentPrefix trace} :
    MatchArmStatementLayout (file := file) statements origin finish := by
  have inputLayout := carries.rootInputLayoutSpanEvidence
    matchArmStatementSpanLayout matchArmStatementRootSound inputEq
  rw [body_inputLayoutSpans] at inputLayout
  exact inputLayout.select
    ((List.sublist_append_left
      (statements.map (fun statement => statement.span))
      [closeBrace.span]).trans
      (List.sublist_append_right [openBrace.span]
        (statements.map (fun statement => statement.span) ++
          [closeBrace.span])))

end RuleReduction

end Solcore.Surface.Multi
