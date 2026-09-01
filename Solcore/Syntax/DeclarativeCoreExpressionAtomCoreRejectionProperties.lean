import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreSuccessProperties

/-! Rejection exclusion for the ordered Core atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_token {tokens : Array Token}
    {endIndex cursor : Nat} {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt tokens endIndex cursor kind)
    (present : TokenAt tokens endIndex cursor { span, value := kind }) : False :=
  absent ⟨span, present⟩

/-- Exact ordered Core atom rejection excludes every ordinary success. -/
theorem ExpressionAtomCoreRejects.disjointOrdinary
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    {parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop}
    {parameterRejects : Remainder → Remainder → Prop}
    {typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop}
    {typeRejects : Remainder → Remainder → Prop}
    {blockOrdinary : Remainder → Syntax.Block → Remainder → Prop}
    {blockRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (parameterOutcomes : DeterministicOutcomeSpec parameterOrdinary
      parameterRejects)
    (typeOutcomes : DeterministicOutcomeSpec typeOrdinary typeRejects)
    (blockOutcomes : DeterministicOutcomeSpec blockOrdinary blockRejects)
    {input rejected : Remainder}
    (rejection : ExpressionAtomCoreRejects nestedOrdinary nestedRejects
      parameterOrdinary parameterRejects typeOrdinary typeRejects
        blockRejects input rejected) :
    ¬ ∃ expression output,
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output := by
  rintro ⟨expression, output, successful⟩
  cases rejection with
  | dotConstructor rejectedLiteralAbsent rejectedNameAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          exact (dotConstructorDeterministicOutcomeSpec nestedOutcomes)
            |>.successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | proxy _ _ dotAbsent _ =>
          exact absent_conflicts_token dotAbsent rejectedMarker
      | parenthesized _ _ dotAbsent _ _ =>
          exact absent_conflicts_token dotAbsent rejectedMarker
      | array _ _ dotAbsent _ _ _ =>
          exact absent_conflicts_token dotAbsent rejectedMarker
      | lambda _ _ dotAbsent _ _ _ _ =>
          exact absent_conflicts_token dotAbsent rejectedMarker
  | proxy rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          exact (proxyExpressionDeterministicOutcomeSpec typeOutcomes)
            |>.successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | parenthesized _ _ _ atAbsent _ =>
          exact absent_conflicts_token atAbsent rejectedMarker
      | array _ _ _ atAbsent _ _ =>
          exact absent_conflicts_token atAbsent rejectedMarker
      | lambda _ _ _ atAbsent _ _ _ =>
          exact absent_conflicts_token atAbsent rejectedMarker
  | parenthesized rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          exact (parenthesizedExpressionDeterministicOutcomeSpec
            nestedOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | array _ _ _ _ leftParenAbsent _ =>
          exact absent_conflicts_token leftParenAbsent rejectedMarker
      | lambda _ _ _ _ leftParenAbsent _ _ =>
          exact absent_conflicts_token leftParenAbsent rejectedMarker
  | array rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedLeftParenAbsent rejectedBranch =>
      rcases rejectedBranch.marker_present with
        ⟨rejectedSpan, rejectedMarker⟩
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedLeftParenAbsent
            successfulMarker
      | array _ _ _ _ _ successfulBranch =>
          exact (arrayLiteralExpressionDeterministicOutcomeSpec
            nestedOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
      | lambda _ _ _ _ _ leftBracketAbsent _ =>
          exact absent_conflicts_token leftBracketAbsent rejectedMarker
  | lambda rejectedLiteralAbsent rejectedNameAbsent rejectedDotAbsent
        rejectedAtAbsent rejectedLeftParenAbsent rejectedLeftBracketAbsent
        rejectedBranch =>
      cases successful with
      | literal successfulBranch =>
          exact rejectedLiteralAbsent successfulBranch.coreLiteralStartsAt
      | identifier _ successfulBranch =>
          exact rejectedNameAbsent successfulBranch.expressionNameStartsAt
      | dotConstructor _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedDotAbsent successfulMarker
      | proxy _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedAtAbsent successfulMarker
      | parenthesized _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedLeftParenAbsent
            successfulMarker
      | array _ _ _ _ _ successfulBranch =>
          rcases successfulBranch.marker_present with
            ⟨successfulSpan, successfulMarker⟩
          exact absent_conflicts_token rejectedLeftBracketAbsent
            successfulMarker
      | lambda _ _ _ _ _ _ successfulBranch =>
          exact (lambdaExpressionDeterministicOutcomeSpec parameterOutcomes
            typeOutcomes blockOutcomes).successRejectDisjoint rejectedBranch
              ⟨_, _, successfulBranch⟩
  | final finalRejected =>
      exact finalRejected.disjointBranchSelected
        successful.exists_branch_selected

end Solcore.Syntax.DeclarativeGrammar
