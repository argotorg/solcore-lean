import Solcore.Syntax.DeclarativeDelimitedFallbackProperties
import Solcore.Syntax.DeclarativeDelimitedTrailingSuccessProperties
import Solcore.Syntax.DeclarativeYulStatementBasicOutcomeGrammar

/-!
Functionality, rejection exclusivity, deterministic outcomes, and clean
embeddings for nonrecursive basic inline-Yul statement primaries.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

/-- Ordinary expression-statement success has a unique output remainder. -/
theorem YulExpressionStatementOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionStatementOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftExpressionParsed =>
      cases rightParsed with
      | parsed rightExpressionParsed =>
          exact yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
            leftExpressionParsed rightExpressionParsed

/-- Exact expression-statement rejection excludes ordinary success. -/
theorem YulExpressionStatementRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulExpressionStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulExpressionStatementOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases rejection with
  | expressionRejected expressionRejected =>
      cases successful with
      | parsed expressionParsed =>
          exact yulExpressionPublicDeterministicOutcomeSpec
            |>.successRejectDisjoint expressionRejected
              ⟨_, _, expressionParsed⟩

/-- Public expression-statement ordinary success and rejection are a
deterministic outcome. -/
theorem yulExpressionStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulExpressionStatementOrdinaryParses
      YulExpressionStatementRejects where
  successOutputUnique := YulExpressionStatementOrdinaryParses.output_unique
  successRejectDisjoint := YulExpressionStatementRejects.disjointOrdinary

/-- A clean public expression statement embeds into ordinary success without
changing its AST, span, or remainder. -/
theorem YulExpressionStatementParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulExpressionStatementParses YulExpressionParses input statement
      output) :
    YulExpressionStatementOrdinaryParses input statement output := by
  cases parsed with
  | parsed expressionParsed => exact .parsed expressionParsed.toOrdinary

/-- Ordinary source-level `return(...)` success has a unique output remainder. -/
theorem YulReturnBuiltinOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnBuiltinOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnBuiltinOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftArgumentsParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightArgumentsParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          exact TrailingDelimitedListParses.output_unique
            (opening := .leftParen) (closing := .rightParen)
            (elementParses := YulExpressionOrdinaryParses)
            (fun left right =>
              yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
                left right)
            leftArgumentsParsed rightArgumentsParsed

/-- Exact source-level `return(...)` rejection excludes ordinary success. -/
theorem YulReturnBuiltinRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulReturnBuiltinRejects input rejected) :
    ¬ ∃ statement output,
      YulReturnBuiltinOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarkerParsed
        successfulArgumentsParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | argumentsRejected rejectedMarkerSpan rejectedMarkerParsed
            argumentsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact argumentsRejected.disjointAllowEmptyTrailing
            yulExpressionPublicDeterministicOutcomeSpec
            (fun parsed => parsed) ⟨_, _, successfulArgumentsParsed⟩

/-- Public source-level `return(...)` ordinary success and rejection are a
deterministic outcome. -/
theorem yulReturnBuiltinDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulReturnBuiltinOrdinaryParses
      YulReturnBuiltinRejects where
  successOutputUnique := YulReturnBuiltinOrdinaryParses.output_unique
  successRejectDisjoint := YulReturnBuiltinRejects.disjointOrdinary

/-- A clean source-level `return(...)` derivation embeds into ordinary success,
preserving its synthesized call, total span, arguments, and remainder. -/
theorem YulReturnBuiltinParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulReturnBuiltinParses YulExpressionParses input statement
      output) :
    YulReturnBuiltinOrdinaryParses input statement output := by
  cases parsed with
  | parsed markerSpan markerParsed argumentsParsed =>
      exact .parsed markerSpan markerParsed
        (argumentsParsed.mapElementRelation fun expressionParsed =>
          expressionParsed.toOrdinary)

/-- Keyword-only control success has a unique output remainder. -/
theorem YulControlTokenOrdinaryParses.output_unique
    {keyword : HardKeyword} {statementValue : Syntax.YulStmtValue}
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulControlTokenOrdinaryParses keyword statementValue input
      left afterLeft)
    (rightParsed : YulControlTokenOrdinaryParses keyword statementValue input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed =>
          exact exactToken_output_unique leftMarkerParsed rightMarkerParsed

/-- Exact keyword-only control rejection excludes ordinary success. -/
theorem YulControlTokenRejects.disjointOrdinary
    {keyword : HardKeyword} {statementValue : Syntax.YulStmtValue}
    {input rejected : Remainder}
    (rejection : YulControlTokenRejects keyword input rejected) :
    ¬ ∃ statement output,
      YulControlTokenOrdinaryParses keyword statementValue input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases rejection with
  | keywordMissing keywordAbsent =>
      cases successful with
      | parsed markerSpan markerParsed =>
          exact absent_conflicts_exact keywordAbsent markerParsed

/-- Every keyword-only control token has a deterministic ordinary outcome. -/
theorem yulControlTokenDeterministicOutcomeSpec
    (keyword : HardKeyword) (statementValue : Syntax.YulStmtValue) :
    DeterministicOutcomeSpec
      (YulControlTokenOrdinaryParses keyword statementValue)
      (YulControlTokenRejects keyword) where
  successOutputUnique := YulControlTokenOrdinaryParses.output_unique
  successRejectDisjoint := YulControlTokenRejects.disjointOrdinary

/-- The exact clean control-token grammar is already its ordinary grammar. -/
theorem YulControlTokenParses.toOrdinary
    {keyword : HardKeyword} {statementValue : Syntax.YulStmtValue}
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulControlTokenParses keyword statementValue input statement
      output) :
    YulControlTokenOrdinaryParses keyword statementValue input statement
      output :=
  parsed

end Solcore.Syntax.DeclarativeGrammar
