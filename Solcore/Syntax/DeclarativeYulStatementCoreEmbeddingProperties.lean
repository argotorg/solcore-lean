import Solcore.Syntax.DeclarativeYulStatementCoreOutcomeProperties

/-! Clean embeddings and recovery-boundary exclusion for the Yul core. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem block_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulBlockStatementParses statementClean input statement output) :
    YulStatementCoreGuardAt input .blockGuard := by
  cases parsed with
  | parsed blockParsed =>
      cases blockParsed with
      | parsed openingSpan openingParsed bodyParsed =>
          exact ⟨openingSpan, openingParsed.1⟩

private theorem let_guard {input output statement}
    (parsed : YulLetStatementParses YulExpressionParses input statement
      output) : YulStatementCoreGuardAt input .letGuard := by
  cases parsed with
  | parsed markerSpan namesSpan markerParsed namesParsed initializerParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem if_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulIfStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .ifGuard := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem for_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulForStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .forGuard := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem switch_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulSwitchStatementParses statementClean YulExpressionParses input
      statement output) : YulStatementCoreGuardAt input .switchGuard := by
  cases parsed with
  | parsed markerSpan markerParsed scrutineeParsed casesParsed
      defaultParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem function_guard
    {statementClean : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output statement}
    (parsed : YulFunctionStatementParses statementClean input statement
      output) : YulStatementCoreGuardAt input .functionGuard := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed nameParsed parametersParsed
      returnsParsed bodyParsed => exact ⟨markerSpan, markerParsed.1⟩

private theorem return_guard {input output statement}
    (parsed : YulReturnBuiltinParses YulExpressionParses input statement
      output) : YulStatementCoreGuardAt input .returnGuard := by
  cases parsed with
  | parsed markerSpan markerParsed argumentsParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

private theorem control_guard {keyword : HardKeyword}
    {statementValue : Syntax.YulStmtValue} {input output statement}
    (parsed : YulControlTokenParses keyword statementValue input statement
      output) : YulStatementCoreTokenAt input (.keyword keyword) := by
  cases parsed with
  | parsed markerSpan markerParsed => exact ⟨markerSpan, markerParsed.1⟩

/-- Every clean prioritized core success embeds into ordinary success with the
same selected branch, AST, span, and output remainder. -/
theorem YulStatementCoreParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (_statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output statement}
    (parsed : YulStatementCoreParses statementClean YulExpressionParses
      yulAssignmentPublicFallbackSpec input statement output) :
    YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
      statement output := by
  cases parsed with
  | block priority primary =>
      exact ⟨.blockGuard, .block priority (block_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | letDecl priority primary =>
      exact ⟨.letGuard, .letDecl priority (let_guard primary)
        (.primary primary.toOrdinary)⟩
  | ifThen priority primary =>
      exact ⟨.ifGuard, .ifThen priority (if_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | forLoop priority primary =>
      exact ⟨.forGuard, .forLoop priority (for_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | switch priority primary =>
      exact ⟨.switchGuard, .switch priority (switch_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | functionDef priority primary =>
      exact ⟨.functionGuard, .functionDef priority (function_guard primary)
        (.primary (primary.toOrdinary cleanToOrdinary))⟩
  | returnBuiltin priority primary =>
      exact ⟨.returnGuard, .returnBuiltin priority (return_guard primary)
        (.primary primary.toOrdinary)⟩
  | leave priority primary =>
      exact ⟨.leaveGuard, .leave priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | «break» priority primary =>
      exact ⟨.breakGuard, .break priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | «continue» priority primary =>
      exact ⟨.continueGuard, .continue priority (control_guard primary)
        (.primary primary.toOrdinary)⟩
  | nameChoice priority primary =>
      cases primary with
      | assignment nameStart assignmentParsed =>
          exact ⟨.nameGuard, .nameChoice priority nameStart
            (.primary assignmentParsed.toOrdinary)⟩
      | rewound nameStart assignmentRejected expressionParsed =>
          exact ⟨.nameGuard, .nameChoice priority nameStart
            ((YulNameStatementChoiceParses.rewound nameStart
              assignmentRejected expressionParsed).toOrdinary)⟩
  | expressionFallback priority fallback =>
      exact ⟨.fallback, .expressionFallback priority fallback.toOrdinary⟩

/-- Every outer statement boundary is also a public-expression rejection. -/
theorem YulStatementRejects.toYulExpressionRejects
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    YulExpressionRejects input rejected := by
  cases rejection with
  | windowEnd atEnd => exact .windowEnd atEnd
  | rightBrace token => exact .rightBrace token
  | missingToken inside missing => exact .missingToken inside missing

/-- Outer statement rejection boundaries exclude every ordinary core success,
including the final expression fallback. -/
theorem YulStatementRejects.disjointCoreOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (_statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulStatementCoreOrdinaryParses statementOrdinary statementRejects input
        statement output := by
  rintro ⟨statement, output, stage, parsed⟩
  by_cases fallback : stage = .fallback
  · subst stage
    cases parsed with
    | expressionFallback priority expressionParsed =>
        exact yulExpressionStatementDeterministicOutcomeSpec
          |>.successRejectDisjoint
            (.expressionRejected rejection.toYulExpressionRejects)
              ⟨_, _, expressionParsed⟩
  · exact rejection.not_coreGuard fallback parsed.guard

end Solcore.Syntax.DeclarativeGrammar
