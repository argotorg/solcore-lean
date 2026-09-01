import Solcore.Syntax.DeclarativeYulLetOrdinaryGrammar
import Solcore.Syntax.DeclarativeYulNameOutcomeProperties

/-!
Functionality, rejection exclusivity, and clean embeddings for public Yul
`let` outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem exactToken_output_unique {kind : TokenKind}
    {input leftOutput rightOutput : Remainder}
    {leftSpan rightSpan : SourceSpan}
    (leftParsed : ExactTokenParses kind input leftSpan leftOutput)
    (rightParsed : ExactTokenParses kind input rightSpan rightOutput) :
    leftOutput = rightOutput := by
  rw [leftParsed.2, rightParsed.2]

private theorem absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- Ordinary optional initializer success has a unique output remainder. -/
theorem YulLetInitializerOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetInitializerOrdinaryParses input left afterLeft)
    (rightParsed : YulLetInitializerOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present operatorSpan operatorParsed valueParsed =>
          exact False.elim
            (absent_conflicts_exact leftAbsent operatorParsed)
  | present leftSpan leftOperator leftValue =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftOperator)
      | present rightSpan rightOperator rightValue =>
          have afterOperatorEq :=
            exactToken_output_unique leftOperator rightOperator
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftValue rightValue

/-- Initializer rejection excludes both its absent success and its present
ordinary expression success. -/
theorem YulLetInitializerRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulLetInitializerRejects input rejected) :
    ¬ ∃ initializer output,
      YulLetInitializerOrdinaryParses input initializer output := by
  rintro ⟨initializer, output, successful⟩
  cases rejection with
  | expressionRejected rejectedSpan rejectedOperator valueRejected =>
      cases successful with
      | absent operatorAbsent =>
          exact absent_conflicts_exact operatorAbsent rejectedOperator
      | present successfulSpan successfulOperator valueParsed =>
          have afterOperatorEq := exactToken_output_unique
            rejectedOperator successfulOperator
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successRejectDisjoint
              valueRejected ⟨_, _, valueParsed⟩

/-- Ordinary initializer outcomes are deterministic and exclusive. -/
theorem yulLetInitializerDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulLetInitializerOrdinaryParses
      YulLetInitializerRejects where
  successOutputUnique := YulLetInitializerOrdinaryParses.output_unique
  successRejectDisjoint := YulLetInitializerRejects.disjointOrdinary

/-- Ordinary public `let` success has a unique output remainder. -/
theorem YulLetStatementOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulLetStatementOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarker leftNames leftInitializer =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarker rightNames rightInitializer =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNamesEq := leftNames.output_unique rightNames
          subst afterNamesEq
          exact leftInitializer.output_unique rightInitializer

/-- Exact public `let` rejection excludes every ordinary success. -/
theorem YulLetStatementRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulLetStatementRejects input rejected) :
    ¬ ∃ statement output,
      YulLetStatementOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarker successfulNames
        successfulInitializer =>
      cases rejection with
      | markerRejected markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | namesRejected rejectedMarkerSpan rejectedMarker namesRejected =>
          have afterMarkerEq :=
            exactToken_output_unique rejectedMarker successfulMarker
          subst afterMarkerEq
          exact namesRejected.disjoint ⟨_, _, successfulNames⟩
      | initializerRejected rejectedMarkerSpan rejectedMarker rejectedNames
            initializerRejected =>
          have afterMarkerEq :=
            exactToken_output_unique rejectedMarker successfulMarker
          subst afterMarkerEq
          have afterNamesEq :=
            rejectedNames.output_unique successfulNames
          subst afterNamesEq
          exact initializerRejected.disjointOrdinary
            ⟨_, _, successfulInitializer⟩

/-- Public `let` ordinary successes and exact rejections form a deterministic
outcome contract. -/
theorem yulLetStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulLetStatementOrdinaryParses
      YulLetStatementRejects where
  successOutputUnique := YulLetStatementOrdinaryParses.output_unique
  successRejectDisjoint := YulLetStatementRejects.disjointOrdinary

/-- Every clean optional initializer embeds into its ordinary outcome. -/
theorem YulLetInitializerParses.toOrdinary
    {input output : Remainder} {initializer : Option Syntax.YulExpr}
    (parsed : YulLetInitializerParses YulExpressionParses input initializer
      output) :
    YulLetInitializerOrdinaryParses input initializer output := by
  cases parsed with
  | absent operatorAbsent => exact .absent operatorAbsent
  | present operatorSpan operatorParsed valueParsed =>
      exact .present operatorSpan operatorParsed valueParsed.toOrdinary

/-- Every clean public `let` embeds into ordinary success with identical AST,
span, name order, and remainder. -/
theorem YulLetStatementParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulLetStatementParses YulExpressionParses input statement
      output) :
    YulLetStatementOrdinaryParses input statement output := by
  cases parsed with
  | parsed markerSpan namesSpan markerParsed namesParsed initializerParsed =>
      exact .parsed markerSpan markerParsed namesParsed.toOrdinary
        initializerParsed.toOrdinary

end Solcore.Syntax.DeclarativeGrammar
