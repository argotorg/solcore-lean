import Solcore.Syntax.Internal.DelimitedExactness
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Grammar.YulOrdinary
import Solcore.Syntax.Internal.YulBlockOutcomes
import Solcore.Syntax.Grammar.Yul

/-!
Properties of the declarative grammar of Yul assignments, control flow, functions and
switches: outcomes are deterministic, and successful values and rejection points are
unique. Nothing here mentions the parser.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementBasicOutcomeProperties
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulLetOrdinaryOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embeddings for public Yul
`let` outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulSwitchCaseOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for the internal
case-list and optional-default stages of ordinary inline-Yul switches.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every successful case arm starts at an exact `case` token. -/
theorem YulCaseArmParses.startsAt
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {arm : Syntax.YulCase}
    (parsed : YulCaseArmOrdinaryParses statementOrdinary input arm output) :
    ∃ span, TokenAt input.tokens input.endIndex input.cursor
      { span, value := .keyword .caseKw } := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed literalParsed bodyParsed =>
      exact ⟨markerSpan, markerParsed.1⟩

/-- Ordinary case-arm success has a unique final remainder. -/
theorem YulCaseArmParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseArmOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulCaseArmOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftBodySpan leftMarkerParsed leftLiteralParsed
        leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightBodySpan rightMarkerParsed
            rightLiteralParsed rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterLiteralEq := leftLiteralParsed.output_unique
            rightLiteralParsed
          subst afterLiteralEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact case-arm rejection excludes ordinary case-arm success. -/
theorem YulCaseArmRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulCaseArmRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ arm output,
      YulCaseArmOrdinaryParses statementOrdinary input arm output := by
  rintro ⟨arm, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulBodySpan successfulMarkerParsed
        successfulLiteralParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | literalMissing rejectedMarkerSpan rejectedMarkerParsed
            literalAbsent =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact literalAbsent successfulLiteralParsed.startsAt
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedLiteralParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterLiteralEq := rejectedLiteralParsed.output_unique
            successfulLiteralParsed
          subst afterLiteralEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary maximal case-list success has a unique final remainder. -/
theorem YulCaseListParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : List Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseListOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulCaseListOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done rightAbsent => rfl
      | next rightArmParsed rightProgress rightTail =>
          rcases rightArmParsed.startsAt with ⟨span, present⟩
          exact False.elim (leftAbsent ⟨span, present⟩)
  | next leftArmParsed leftProgress leftTail inductionHypothesis =>
      cases rightParsed with
      | done rightAbsent =>
          rcases leftArmParsed.startsAt with ⟨span, present⟩
          exact False.elim (rightAbsent ⟨span, present⟩)
      | next rightArmParsed rightProgress rightTail =>
          have afterArmEq := leftArmParsed.output_unique statementOutcomes
            rightArmParsed
          subst afterArmEq
          exact inductionHypothesis rightTail

/-- A rejected case-list iteration excludes maximal ordinary success. -/
theorem YulCaseListRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulCaseListRejects statementOrdinary statementRejects input
      rejected) :
    ¬ ∃ cases output,
      YulCaseListOrdinaryParses statementOrdinary input cases output := by
  induction rejection with
  | firstRejected casePresent armRejected =>
      rintro ⟨cases, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent casePresent
      | next armParsed progress tail =>
          exact armRejected.disjointOrdinary statementOutcomes
            ⟨_, _, armParsed⟩
  | laterRejected rejectedArmParsed progress tailRejected
        inductionHypothesis =>
      rintro ⟨cases, output, successful⟩
      cases successful with
      | done caseAbsent => exact caseAbsent rejectedArmParsed.startsAt
      | next successfulArmParsed otherProgress successfulTail =>
          have afterArmEq := rejectedArmParsed.output_unique statementOutcomes
            successfulArmParsed
          subst afterArmEq
          exact inductionHypothesis ⟨_, _, successfulTail⟩

/-- Optional-default success has a unique final remainder. -/
theorem OptionalYulDefaultParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {leftSpan rightSpan : Option SourceSpan}
    {leftBody rightBody : Option (List Syntax.YulStmt)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      leftSpan leftBody afterLeft)
    (rightParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      rightSpan rightBody afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent rightAbsent => rfl
      | present markerSpan bodySpan markerParsed bodyParsed =>
          exact False.elim (absent_conflicts_exact leftAbsent markerParsed)
  | present leftMarkerSpan leftBodySpan leftMarkerParsed leftBodyParsed =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (absent_conflicts_exact rightAbsent leftMarkerParsed)
      | present rightMarkerSpan rightBodySpan rightMarkerParsed
            rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact optional-default rejection excludes ordinary success. -/
theorem OptionalYulDefaultRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : OptionalYulDefaultRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ defaultSpan defaultBody output,
      OptionalYulDefaultOrdinaryParses statementOrdinary input defaultSpan
        defaultBody output := by
  rintro ⟨defaultSpan, defaultBody, output, successful⟩
  cases rejection with
  | bodyRejected rejectedMarkerSpan rejectedMarkerParsed bodyRejected =>
      cases successful with
      | absent defaultAbsent =>
          exact absent_conflicts_exact defaultAbsent rejectedMarkerParsed
      | present successfulMarkerSpan successfulBodySpan successfulMarkerParsed
            successfulBodyParsed =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulSwitchOutcomeProperties
/-!
Deterministic outcomes and clean embedding for complete ordinary inline-Yul
switch statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem switchStages_output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input leftAfterMarker rightAfterMarker leftAfterScrutinee
      rightAfterScrutinee leftAfterCases rightAfterCases leftOutput
      rightOutput : Remainder}
    {leftScrutinee rightScrutinee : Syntax.YulExpr}
    {leftCases rightCases : List Syntax.YulCase}
    {leftDefaultSpan rightDefaultSpan : Option SourceSpan}
    {leftDefaultBody rightDefaultBody : Option (List Syntax.YulStmt)}
    {leftMarkerSpan rightMarkerSpan : SourceSpan}
    (leftMarkerParsed : ExactTokenParses (.keyword .switchKw) input
      leftMarkerSpan leftAfterMarker)
    (leftScrutineeParsed : YulExpressionOrdinaryParses leftAfterMarker
      leftScrutinee leftAfterScrutinee)
    (leftCasesParsed : YulCaseListOrdinaryParses statementOrdinary
      leftAfterScrutinee leftCases leftAfterCases)
    (leftDefaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      leftAfterCases leftDefaultSpan leftDefaultBody leftOutput)
    (rightMarkerParsed : ExactTokenParses (.keyword .switchKw) input
      rightMarkerSpan rightAfterMarker)
    (rightScrutineeParsed : YulExpressionOrdinaryParses rightAfterMarker
      rightScrutinee rightAfterScrutinee)
    (rightCasesParsed : YulCaseListOrdinaryParses statementOrdinary
      rightAfterScrutinee rightCases rightAfterCases)
    (rightDefaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      rightAfterCases rightDefaultSpan rightDefaultBody rightOutput) :
    leftOutput = rightOutput := by
  have afterMarkerEq := exactToken_output_unique leftMarkerParsed
    rightMarkerParsed
  subst afterMarkerEq
  have afterScrutineeEq :=
    yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
      leftScrutineeParsed rightScrutineeParsed
  subst afterScrutineeEq
  have afterCasesEq := leftCasesParsed.output_unique statementOutcomes
    rightCasesParsed
  subst afterCasesEq
  exact leftDefaultParsed.output_unique statementOutcomes rightDefaultParsed

private theorem switchStages_disjoint
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input afterMarker afterScrutinee afterCases output rejected : Remainder}
    {scrutinee : Syntax.YulExpr} {cases : List Syntax.YulCase}
    {defaultSpan : Option SourceSpan}
    {defaultBody : Option (List Syntax.YulStmt)} {markerSpan : SourceSpan}
    (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
      afterMarker)
    (scrutineeParsed : YulExpressionOrdinaryParses afterMarker scrutinee
      afterScrutinee)
    (casesParsed : YulCaseListOrdinaryParses statementOrdinary
      afterScrutinee cases afterCases)
    (defaultParsed : OptionalYulDefaultOrdinaryParses statementOrdinary
      afterCases defaultSpan defaultBody output)
    (rejection : YulSwitchStatementRejects statementOrdinary statementRejects
      input rejected) : False := by
  cases rejection with
  | markerMissing markerAbsent =>
      exact absent_conflicts_exact markerAbsent markerParsed
  | scrutineeRejected rejectedMarkerSpan rejectedMarkerParsed
        scrutineeRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      exact yulExpressionPublicDeterministicOutcomeSpec
        |>.successRejectDisjoint scrutineeRejected ⟨_, _, scrutineeParsed⟩
  | casesRejected rejectedMarkerSpan rejectedMarkerParsed
        rejectedScrutineeParsed casesRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      have afterScrutineeEq :=
        yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
          rejectedScrutineeParsed scrutineeParsed
      subst afterScrutineeEq
      exact casesRejected.disjointOrdinary statementOutcomes
        ⟨_, _, casesParsed⟩
  | defaultRejected rejectedMarkerSpan rejectedMarkerParsed
        rejectedScrutineeParsed rejectedCasesParsed defaultRejected =>
      have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
        markerParsed
      subst afterMarkerEq
      have afterScrutineeEq :=
        yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
          rejectedScrutineeParsed scrutineeParsed
      subst afterScrutineeEq
      have afterCasesEq := rejectedCasesParsed.output_unique statementOutcomes
        casesParsed
      subst afterCasesEq
      exact defaultRejected.disjointOrdinary statementOutcomes
        ⟨_, _, _, defaultParsed⟩

/-- Ordinary complete-switch success has a unique final remainder. -/
theorem YulSwitchStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulSwitchStatementOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : YulSwitchStatementOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | nonempty leftMarkerSpan leftMarkerParsed leftScrutineeParsed
        leftCasesParsed leftDefaultParsed =>
      cases rightParsed with
      | nonempty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
      | empty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
  | empty leftMarkerSpan leftMarkerParsed leftScrutineeParsed leftCasesParsed
        leftDefaultParsed =>
      cases rightParsed with
      | nonempty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed
      | empty rightMarkerSpan rightMarkerParsed rightScrutineeParsed
            rightCasesParsed rightDefaultParsed =>
          exact switchStages_output_unique statementOutcomes leftMarkerParsed
            leftScrutineeParsed leftCasesParsed leftDefaultParsed
            rightMarkerParsed rightScrutineeParsed rightCasesParsed
            rightDefaultParsed

/-- Exact complete-switch rejection excludes every ordinary success. -/
theorem YulSwitchStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulSwitchStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulSwitchStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases successful <;>
    apply switchStages_disjoint statementOutcomes <;> assumption

/-- Ordinary switch success and exact rejection form a deterministic outcome. -/
theorem yulSwitchStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulSwitchStatementOrdinaryParses statementOrdinary)
      (YulSwitchStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulSwitchStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulSwitchStatementRejects.disjointOrdinary statementOutcomes

/-- A clean case arm embeds into the ordinary case-arm relation. -/
theorem YulCaseArmParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {arm : Syntax.YulCase}
    (parsed : YulCaseArmParses statementClean input arm output) :
    YulCaseArmOrdinaryParses statementOrdinary input arm output := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed literalParsed bodyParsed =>
      exact .parsed markerSpan bodySpan markerParsed literalParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

/-- A clean maximal case list embeds into the ordinary list relation. -/
theorem YulCaseListParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {cases : List Syntax.YulCase}
    (parsed : YulCaseListParses statementClean input cases output) :
    YulCaseListOrdinaryParses statementOrdinary input cases output := by
  induction parsed with
  | done caseAbsent => exact .done caseAbsent
  | next armParsed progress tail inductionHypothesis =>
      exact .next (armParsed.toOrdinary cleanToOrdinary) progress
        inductionHypothesis

/-- A clean optional default embeds into its ordinary relation. -/
theorem OptionalYulDefaultParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {defaultSpan : Option SourceSpan}
    {defaultBody : Option (List Syntax.YulStmt)}
    (parsed : OptionalYulDefaultParses statementClean input defaultSpan
      defaultBody output) :
    OptionalYulDefaultOrdinaryParses statementOrdinary input defaultSpan
      defaultBody output := by
  cases parsed with
  | absent defaultAbsent => exact .absent defaultAbsent
  | present markerSpan bodySpan markerParsed bodyParsed =>
      exact .present markerSpan bodySpan markerParsed
        (bodyParsed.toOrdinary cleanToOrdinary)

/-- Every diagnostic-free switch derivation embeds into ordinary success. -/
theorem YulSwitchStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulSwitchStatementParses statementClean YulExpressionParses
      input statement output) :
    YulSwitchStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed markerSpan markerParsed scrutineeParsed casesParsed
        defaultParsed =>
      exact .nonempty markerSpan markerParsed scrutineeParsed.toOrdinary
        (casesParsed.toOrdinary cleanToOrdinary)
        (defaultParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulAssignmentOrdinaryOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for ordinary public
inline-Yul assignment outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary public assignment success has a unique output remainder. -/
theorem YulAssignmentOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulAssignmentOrdinaryParses input left afterLeft)
    (rightParsed : YulAssignmentOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOperatorSpan leftNamesParsed leftOperatorParsed
        leftValueParsed =>
      cases rightParsed with
      | parsed rightOperatorSpan rightNamesParsed rightOperatorParsed
            rightValueParsed =>
          have afterNamesEq :=
            leftNamesParsed.output_unique rightNamesParsed
          subst afterNamesEq
          have afterOperatorEq :=
            exactToken_output_unique leftOperatorParsed rightOperatorParsed
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftValueParsed rightValueParsed

/-- Exact ordinary assignment rejection excludes every ordinary assignment
success. -/
theorem YulAssignmentRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulAssignmentRejects YulExpressionRejects input rejected) :
    ¬ ∃ statement output,
      YulAssignmentOrdinaryParses input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulOperatorSpan successfulNamesParsed
        successfulOperatorParsed successfulValueParsed =>
      cases rejection with
      | namesRejected namesRejected =>
          exact namesRejected.disjoint
            ⟨_, _, successfulNamesParsed⟩
      | operatorAbsent rejectedNamesParsed operatorAbsent =>
          have afterNamesEq :=
            rejectedNamesParsed.output_unique successfulNamesParsed
          subst afterNamesEq
          exact absent_conflicts_exact operatorAbsent
            successfulOperatorParsed
      | expressionRejected rejectedOperatorSpan rejectedNamesParsed
            rejectedOperatorParsed valueRejected =>
          have afterNamesEq :=
            rejectedNamesParsed.output_unique successfulNamesParsed
          subst afterNamesEq
          have afterOperatorEq := exactToken_output_unique
            rejectedOperatorParsed successfulOperatorParsed
          subst afterOperatorEq
          exact
            yulExpressionPublicDeterministicOutcomeSpec.successRejectDisjoint
              valueRejected ⟨_, _, successfulValueParsed⟩

/-- Public assignment ordinary success and rejection form a deterministic
outcome contract. -/
theorem yulAssignmentDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulAssignmentOrdinaryParses
      (YulAssignmentRejects YulExpressionRejects) where
  successOutputUnique := YulAssignmentOrdinaryParses.output_unique
  successRejectDisjoint := YulAssignmentRejects.disjointOrdinary

/-- Every clean public assignment success is an ordinary public assignment
success with the same AST, span, name order, and remainder. -/
theorem YulAssignmentParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulAssignmentParses YulExpressionParses input statement
      output) :
    YulAssignmentOrdinaryParses input statement output := by
  cases parsed with
  | parsed namesSpan operatorSpan namesParsed operatorParsed valueParsed =>
      exact .parsed operatorSpan namesParsed.toOrdinary operatorParsed
        valueParsed.toOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementControlOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embedding for ordinary
inline-Yul `if` and `for` outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary `if` success has a unique output remainder. -/
theorem YulIfStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulIfStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulIfStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftConditionParsed
        leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightConditionParsed
            rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftConditionParsed rightConditionParsed
          subst afterConditionEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact `if` rejection excludes every ordinary `if` success. -/
theorem YulIfStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulIfStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulIfStatementOrdinaryParses statementOrdinary input statement output :=
by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarkerParsed
        successfulConditionParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | conditionRejected rejectedMarkerSpan rejectedMarkerParsed
            conditionRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact yulExpressionPublicDeterministicOutcomeSpec
            |>.successRejectDisjoint conditionRejected
              ⟨_, _, successfulConditionParsed⟩
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedConditionParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary `if` success and rejection form a deterministic outcome. -/
theorem yulIfStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulIfStatementOrdinaryParses statementOrdinary)
      (YulIfStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulIfStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulIfStatementRejects.disjointOrdinary statementOutcomes

/-- A clean `if` derivation embeds into the ordinary `if` relation. -/
theorem YulIfStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementCleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementClean YulExpressionParses input
      statement output) :
    YulIfStatementOrdinaryParses statementOrdinary input statement output := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      exact .parsed markerSpan markerParsed conditionParsed.toOrdinary
        (bodyParsed.toOrdinary statementCleanToOrdinary)

/-- Ordinary `for` success has a unique output remainder. -/
theorem YulForStatementOrdinaryParses.output_unique
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulForStatementOrdinaryParses statementOrdinary input left
      afterLeft)
    (rightParsed : YulForStatementOrdinaryParses statementOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftMarkerParsed leftInitializerParsed
        leftConditionParsed leftPostParsed leftBodyParsed =>
      cases rightParsed with
      | parsed rightMarkerSpan rightMarkerParsed rightInitializerParsed
            rightConditionParsed rightPostParsed rightBodyParsed =>
          have afterMarkerEq := exactToken_output_unique leftMarkerParsed
            rightMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := leftInitializerParsed.output_unique
            statementOutcomes rightInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              leftConditionParsed rightConditionParsed
          subst afterConditionEq
          have afterPostEq := leftPostParsed.output_unique statementOutcomes
            rightPostParsed
          subst afterPostEq
          exact leftBodyParsed.output_unique statementOutcomes rightBodyParsed

/-- Exact `for` rejection excludes every ordinary `for` success. -/
theorem YulForStatementRejects.disjointOrdinary
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects)
    {input rejected : Remainder}
    (rejection : YulForStatementRejects statementOrdinary statementRejects
      input rejected) :
    ¬ ∃ statement output,
      YulForStatementOrdinaryParses statementOrdinary input statement output :=
by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulMarkerParsed
        successfulInitializerParsed successfulConditionParsed
        successfulPostParsed successfulBodyParsed =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarkerParsed
      | initializerRejected rejectedMarkerSpan rejectedMarkerParsed
            initializerRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          exact initializerRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulInitializerParsed⟩
      | conditionRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed conditionRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          exact yulExpressionPublicDeterministicOutcomeSpec
            |>.successRejectDisjoint conditionRejected
              ⟨_, _, successfulConditionParsed⟩
      | postRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed rejectedConditionParsed postRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          exact postRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulPostParsed⟩
      | bodyRejected rejectedMarkerSpan rejectedMarkerParsed
            rejectedInitializerParsed rejectedConditionParsed
            rejectedPostParsed bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarkerParsed
            successfulMarkerParsed
          subst afterMarkerEq
          have afterInitializerEq := rejectedInitializerParsed.output_unique
            statementOutcomes successfulInitializerParsed
          subst afterInitializerEq
          have afterConditionEq :=
            yulExpressionPublicDeterministicOutcomeSpec.successOutputUnique
              rejectedConditionParsed successfulConditionParsed
          subst afterConditionEq
          have afterPostEq := rejectedPostParsed.output_unique
            statementOutcomes successfulPostParsed
          subst afterPostEq
          exact bodyRejected.disjointOrdinary statementOutcomes
            ⟨_, _, _, successfulBodyParsed⟩

/-- Ordinary `for` success and rejection form a deterministic outcome. -/
theorem yulForStatementDeterministicOutcomeSpec
    {statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (statementOutcomes : DeterministicOutcomeSpec statementOrdinary
      statementRejects) :
    DeterministicOutcomeSpec
      (YulForStatementOrdinaryParses statementOrdinary)
      (YulForStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulForStatementOrdinaryParses.output_unique statementOutcomes
  successRejectDisjoint :=
    YulForStatementRejects.disjointOrdinary statementOutcomes

/-- A clean `for` derivation embeds into the ordinary `for` relation. -/
theorem YulForStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementCleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementClean YulExpressionParses input
      statement output) :
    YulForStatementOrdinaryParses statementOrdinary input statement output :=
by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
        postParsed bodyParsed =>
      exact .parsed markerSpan markerParsed
        (initializerParsed.toOrdinary statementCleanToOrdinary)
        conditionParsed.toOrdinary
        (postParsed.toOrdinary statementCleanToOrdinary)
        (bodyParsed.toOrdinary statementCleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionLeafExactnessProperties
/-! Exact values and endpoints of non-recursive inline-Yul expression leaves. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The current token fixes an ordinary Yul name, including its source span. -/
theorem YulNameOrdinaryParses.value_unique {input : Remainder}
    {left right : Syntax.YulIdentifier} {afterLeft afterRight : Remainder}
    (leftParsed : YulNameOrdinaryParses input left afterLeft)
    (rightParsed : YulNameOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind [IdentifierParses, IdentifierParses.value_unique, TokenAt.token_unique]

/-- An ordinary Yul name fixes its complete value and final remainder. -/
theorem YulNameOrdinaryParses.result_unique {input : Remainder}
    {left right : Syntax.YulIdentifier} {afterLeft afterRight : Remainder}
    (leftParsed : YulNameOrdinaryParses input left afterLeft)
    (rightParsed : YulNameOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- Rejected ordinary Yul names have one non-consuming endpoint. -/
theorem YulNameRejects.output_unique {input left right : Remainder}
    (leftRejected : YulNameRejects input left)
    (rightRejected : YulNameRejects input right) : left = right := by
  cases leftRejected
  cases rightRejected
  rfl

/-- Ordinary Yul names have exact successful values and rejecting endpoints. -/
theorem yulNameExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulNameOrdinaryParses YulNameRejects where
  toDeterministicOutcomeSpec := yulNameDeterministicOutcomeSpec
  successValueUnique := YulNameOrdinaryParses.value_unique
  rejectOutputUnique := YulNameRejects.output_unique

/-- The current literal token fixes its complete Yul literal value. -/
theorem YulLiteralParses.value_unique {input : Remainder}
    {left right : Syntax.YulLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : YulLiteralParses input left afterLeft)
    (rightParsed : YulLiteralParses input right afterRight) : left = right := by
  cases leftParsed <;> cases rightParsed <;> grind [TokenAt.token_unique]

/-- An inline-Yul literal fixes both its value and final remainder. -/
theorem YulLiteralParses.result_unique {input : Remainder}
    {left right : Syntax.YulLiteral} {afterLeft afterRight : Remainder}
    (leftParsed : YulLiteralParses input left afterLeft)
    (rightParsed : YulLiteralParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulNamesExactnessProperties
/-! Exact source-order names and spans of ordinary Yul name sequences. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A fixed accumulated name tail fixes the finished span and forward names. -/
theorem YulNamesTailOrdinaryParses.value_unique
    {first : Syntax.YulIdentifier} {input : Remainder}
    {last : Syntax.YulIdentifier} {tailRev : List Syntax.YulIdentifier}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesTailOrdinaryParses first input last tailRev left afterLeft)
    (rightParsed : YulNamesTailOrdinaryParses first input last tailRev right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent leftFinished =>
      cases rightParsed with
      | done _ rightFinished => cases leftFinished; cases rightFinished; rfl
      | next rightSpan rightToken _ _ => exact False.elim (leftAbsent ⟨_, rightToken⟩)
  | next leftSpan leftToken leftName leftTail ih =>
      cases rightParsed with
      | done rightAbsent _ => exact False.elim (rightAbsent ⟨_, leftToken⟩)
      | next _ _ rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          exact ih rightTail

/-- An ordinary Yul name sequence fixes its span and forward-order names. -/
theorem YulNamesOrdinaryParses.value_unique {input : Remainder}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesOrdinaryParses input left afterLeft)
    (rightParsed : YulNamesOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftName leftTail =>
      cases rightParsed with
      | parsed rightName rightTail =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          exact leftTail.value_unique rightTail

/-- An ordinary name sequence fixes its complete successful result. -/
theorem YulNamesOrdinaryParses.result_unique {input : Remainder}
    {left right : YulNamesOrdinaryValue} {afterLeft afterRight : Remainder}
    (leftParsed : YulNamesOrdinaryParses input left afterLeft)
    (rightParsed : YulNamesOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionCoreExactnessProperties
/-! Exact ordinary inline-Yul expression cores, conditional on nested outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional call arguments fix their complete optional list value. -/
theorem OptionalYulCallArgumentsOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.YulExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          exact False.elim
            (leftAbsent (YulCallArgumentsParses.opening_present rightPresent))
  | rewound openingSpan openingToken leftRejected =>
      cases rightParsed with
      | absent | rewound => rfl
      | present rightPresent =>
          exact False.elim
            (leftRejected.disjointOrdinary outcomes.toDeterministicOutcomeSpec
              ⟨_, _, rightPresent⟩)
  | present leftPresent =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (rightAbsent (YulCallArgumentsParses.opening_present leftPresent))
      | rewound openingSpan openingToken rightRejected =>
          exact False.elim
            (rightRejected.disjointOrdinary outcomes.toDeterministicOutcomeSpec
              ⟨_, _, leftPresent⟩)
      | present rightPresent =>
          exact congrArg some (leftPresent.value_unique outcomes rightPresent)

/-- Transactional call arguments fix both their optional value and remainder. -/
theorem OptionalYulCallArgumentsOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder}
    {left right : Option (DelimitedList Syntax.YulExpr)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input left afterLeft)
    (rightParsed : OptionalYulCallArgumentsOrdinaryParses ordinaryParses
      nestedRejects input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Named expressions fix the identifier/call branch and complete AST. -/
theorem YulNamedExpressionOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | identifier leftName leftArguments =>
      cases rightParsed with
      | identifier rightName rightArguments =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          rfl
      | call rightName rightArguments =>
          have outputEq := leftName.output_unique rightName
          subst outputEq
          have impossible := leftArguments.value_unique outcomes rightArguments
          contradiction
  | call leftName leftArguments =>
      cases rightParsed with
      | identifier rightName rightArguments =>
          have outputEq := leftName.output_unique rightName
          subst outputEq
          have impossible := leftArguments.value_unique outcomes rightArguments
          contradiction
      | call rightName rightArguments =>
          rcases leftName.result_unique rightName with ⟨nameEq, outputEq⟩
          subst nameEq
          subst outputEq
          have argumentsEq := leftArguments.value_unique outcomes rightArguments
          cases Option.some.inj argumentsEq
          rfl

/-- Named expressions fix their complete AST and final remainder. -/
theorem YulNamedExpressionOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulNamedExpressionOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Literal-before-name priority fixes every ordinary Yul-expression core AST. -/
theorem YulExpressionCoreOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | literal leftLiteral =>
      cases rightParsed with
      | literal rightLiteral =>
          cases leftLiteral.value_unique rightLiteral
          rfl
      | named rightAbsent _
      | metaBacktick rightAbsent _ _
      | metaInterpolation rightAbsent _ _ =>
          exact False.elim (rightAbsent leftLiteral.startsAt)
  | named leftAbsent leftNamed =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftAbsent rightLiteral.startsAt)
      | named _ rightNamed => exact leftNamed.value_unique outcomes rightNamed
      | metaBacktick _ rightAbsent _
      | metaInterpolation _ rightAbsent _ =>
          exact False.elim (rightAbsent leftNamed.startsAt)
  | metaBacktick leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named _ rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick _ _ rightToken
      | metaInterpolation _ _ rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          grind
  | metaInterpolation leftLiteralAbsent leftNameAbsent leftToken =>
      cases rightParsed with
      | literal rightLiteral =>
          exact False.elim (leftLiteralAbsent rightLiteral.startsAt)
      | named _ rightNamed =>
          exact False.elim (leftNameAbsent rightNamed.startsAt)
      | metaBacktick _ _ rightToken
      | metaInterpolation _ _ rightToken =>
          have tokenEq := leftToken.token_unique rightToken
          grind

/-- An ordinary Yul-expression core fixes its AST and complete remainder. -/
theorem YulExpressionCoreOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionCoreOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionLayerExactnessProperties
/-! Exact recovery spans and full outcomes of one inline-Yul expression layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A recovery scan fixes its error AST when both accumulated spans are fixed. -/
theorem YulExpressionRecoveryScanParses.value_unique :
    ∀ {first last : SourceSpan} {input : Remainder}
      {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder},
      YulExpressionRecoveryScanParses first last input left afterLeft →
      YulExpressionRecoveryScanParses first last input right afterRight →
      left = right := by
  intro first last input left right afterLeft afterRight leftParsed
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      intro rightParsed
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail inductionHypothesis =>
      intro rightParsed
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightCurrent rightTail =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact inductionHypothesis rightTail

/-- A recovery scan fixes both the error AST and its complete remainder. -/
theorem YulExpressionRecoveryScanParses.result_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.YulExpr} {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionRecoveryScanParses first last input left afterLeft)
    (rightParsed : YulExpressionRecoveryScanParses first last input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique rightParsed, leftParsed.output_unique rightParsed⟩

/-- An ordinary recovering Yul-expression layer fixes its complete AST. -/
theorem YulExpressionLayerOrdinaryParses.value_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | core leftCore =>
      cases rightParsed with
      | core rightCore => exact leftCore.value_unique outcomes rightCore
      | recovered rightRejected _ _ _ =>
          exact False.elim (rightRejected.disjointOrdinary ⟨_, _, leftCore⟩)
  | recovered leftRejected _ leftCurrent leftScan =>
      cases rightParsed with
      | core rightCore =>
          exact False.elim (leftRejected.disjointOrdinary ⟨_, _, rightCore⟩)
      | recovered _ _ rightCurrent rightScan =>
          have currentEq := leftCurrent.token_unique rightCurrent
          cases currentEq
          exact leftScan.value_unique rightScan

/-- An ordinary recovering Yul-expression layer fixes its AST and remainder. -/
theorem YulExpressionLayerOrdinaryParses.result_unique
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects)
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input left afterLeft)
    (rightParsed : YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects
      input right afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique outcomes rightParsed,
    leftParsed.output_unique outcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- Every Yul-expression rejection has the same non-consuming endpoint. -/
theorem YulExpressionRejects.output_unique {input left right : Remainder}
    (leftRejected : YulExpressionRejects input left)
    (rightRejected : YulExpressionRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- One recovering Yul-expression layer preserves exact ordinary outcomes. -/
theorem yulExpressionLayerExactOutcomeSpec
    {ordinaryParses : Remainder → Syntax.YulExpr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec ordinaryParses nestedRejects) :
    ExactDeterministicOutcomeSpec
      (YulExpressionLayerOrdinaryParses ordinaryParses nestedRejects)
      YulExpressionRejects where
  toDeterministicOutcomeSpec :=
    yulExpressionDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulExpressionLayerOrdinaryParses.value_unique outcomes
  rejectOutputUnique := YulExpressionRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionExactnessProperties
/-! Exact fixed-fuel and public inline-Yul expression outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every recursive Yul-expression fuel has exact success and reject outcomes. -/
theorem yulExpressionExactOutcomeSpecWithFuel (fuel : Nat) :
    ExactDeterministicOutcomeSpec
      (YulExpressionOrdinaryParsesWithFuel fuel)
      (YulExpressionRejectsWithFuel fuel) := by
  induction fuel with
  | zero =>
      exact {
        toDeterministicOutcomeSpec := yulExpressionOutcomeSpecWithFuel 0
        successValueUnique := by
          intro input left right afterLeft afterRight leftParsed
          exact False.elim (YulExpressionOrdinaryParsesWithFuel.zero leftParsed)
        rejectOutputUnique := by
          intro input left right leftRejected
          exact False.elim (YulExpressionRejectsWithFuel.zero leftRejected)
      }
  | succ fuel inductionHypothesis =>
      exact yulExpressionLayerExactOutcomeSpec inductionHypothesis

/-- Fixed-fuel ordinary Yul expressions fix their complete AST. -/
theorem YulExpressionOrdinaryParsesWithFuel.value_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParsesWithFuel fuel input right
      afterRight) : left = right :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).successValueUnique
    leftParsed rightParsed

/-- Fixed-fuel ordinary Yul expressions fix their complete result. -/
theorem YulExpressionOrdinaryParsesWithFuel.result_unique {fuel : Nat}
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParsesWithFuel fuel input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParsesWithFuel fuel input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).successResultUnique
    leftParsed rightParsed

/-- Fixed-fuel Yul-expression rejection fixes its complete endpoint. -/
theorem YulExpressionRejectsWithFuel.output_unique {fuel : Nat}
    {input left right : Remainder}
    (leftRejected : YulExpressionRejectsWithFuel fuel input left)
    (rightRejected : YulExpressionRejectsWithFuel fuel input right) :
    left = right :=
  (yulExpressionExactOutcomeSpecWithFuel fuel).rejectOutputUnique
    leftRejected rightRejected

/-- The input-selected public fuel preserves exact ordinary expression outcomes. -/
theorem yulExpressionPublicExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionPublicRejects where
  toDeterministicOutcomeSpec := yulExpressionPublicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact (yulExpressionExactOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).successValueUnique leftParsed rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact (yulExpressionExactOutcomeSpecWithFuel
      (yulExpressionPublicFuel input)).rejectOutputUnique
        leftRejected rightRejected

/-- Exact public outcomes stated with the concrete boundary-rejection relation. -/
theorem yulExpressionExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionOrdinaryParses
      YulExpressionRejects where
  toDeterministicOutcomeSpec := yulExpressionPublicDeterministicOutcomeSpec
  successValueUnique := yulExpressionPublicExactOutcomeSpec.successValueUnique
  rejectOutputUnique := YulExpressionRejects.output_unique

/-- Public ordinary Yul expressions fix the complete AST and final remainder. -/
theorem YulExpressionOrdinaryParses.result_unique
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParses input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  yulExpressionExactOutcomeSpec.successResultUnique leftParsed rightParsed

/-- Public ordinary Yul expressions fix the complete AST. -/
theorem YulExpressionOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionOrdinaryParses input right afterRight) :
    left = right :=
  yulExpressionExactOutcomeSpec.successValueUnique leftParsed rightParsed

/-- Public fuel-indexed Yul-expression rejection fixes its complete endpoint. -/
theorem YulExpressionPublicRejects.output_unique
    {input left right : Remainder}
    (leftRejected : YulExpressionPublicRejects input left)
    (rightRejected : YulExpressionPublicRejects input right) : left = right :=
  yulExpressionPublicExactOutcomeSpec.rejectOutputUnique leftRejected rightRejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulFunctionOutcomeProperties
/-!
Functionality, rejection exclusivity, and clean embeddings for ordinary
inline-Yul function outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary parameter-list output is functional. -/
theorem YulParametersOrdinaryParses.output_unique
    {input : Remainder} {left right : DelimitedList Syntax.YulIdentifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulParametersOrdinaryParses input left afterLeft)
    (rightParsed : YulParametersOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  unfold YulParametersOrdinaryParses at leftParsed rightParsed
  exact TrailingDelimitedListParses.output_unique
    (opening := .leftParen) (closing := .rightParen)
    (elementParses := YulNameOrdinaryParses)
    (fun leftName rightName => leftName.output_unique rightName)
    leftParsed rightParsed

/-- Exact parameter rejection excludes ordinary parameter success. -/
theorem YulParametersRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : YulParametersRejects input rejected) :
    ¬ ∃ parameters output,
      YulParametersOrdinaryParses input parameters output := by
  exact rejection.disjointAllowEmptyTrailing
    yulNameDeterministicOutcomeSpec (fun parsed => parsed)

/-- Ordinary return-clause output is functional. -/
theorem YulReturnClauseOrdinaryParses.output_unique
    {input : Remainder} {left right : Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnClauseOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnClauseOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftArrowSpan leftArrow leftNames =>
      cases rightParsed with
      | parsed rightArrowSpan rightArrow rightNames =>
          have afterArrowEq := exactToken_output_unique leftArrow rightArrow
          subst afterArrowEq
          exact leftNames.output_unique rightNames

/-- Direct return-clause rejection excludes ordinary success. -/
theorem YulReturnClauseRejects.disjointOrdinary
    {input rejected : Remainder}
    (rejection : YulReturnClauseRejects input rejected) :
    ¬ ∃ clause output,
      YulReturnClauseOrdinaryParses input clause output := by
  rintro ⟨clause, output, successful⟩
  cases successful with
  | parsed successfulArrowSpan successfulArrow successfulNames =>
      cases rejection with
      | arrowMissing arrowAbsent =>
          exact absent_conflicts_exact arrowAbsent successfulArrow
      | namesRejected rejectedArrowSpan rejectedArrow namesRejected =>
          have afterArrowEq := exactToken_output_unique rejectedArrow
            successfulArrow
          subst afterArrowEq
          exact namesRejected.disjoint ⟨_, _, successfulNames⟩

/-- Direct return-clause outcomes are deterministic and exclusive. -/
theorem yulReturnClauseDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulReturnClauseOrdinaryParses
      YulReturnClauseRejects where
  successOutputUnique := YulReturnClauseOrdinaryParses.output_unique
  successRejectDisjoint := YulReturnClauseRejects.disjointOrdinary

/-- Optional-return output is functional, including arrow branch priority. -/
theorem YulReturnsOrdinaryParses.output_unique
    {input : Remainder} {left right : Option Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnsOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnsOrdinaryParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          cases rightClause with
          | parsed arrowSpan arrowParsed namesParsed =>
              exact False.elim
                (absent_conflicts_exact leftAbsent arrowParsed)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftClause with
          | parsed arrowSpan arrowParsed namesParsed =>
              exact False.elim
                (absent_conflicts_exact rightAbsent arrowParsed)
      | present rightClause =>
          exact leftClause.output_unique rightClause

/-- Preferred optional-return rejection excludes both optional successes. -/
theorem YulReturnsRejects.disjointOrdinary {input rejected : Remainder}
    (rejection : YulReturnsRejects input rejected) :
    ¬ ∃ returns output, YulReturnsOrdinaryParses input returns output := by
  rintro ⟨returns, output, successful⟩
  cases rejection with
  | namesRejected rejectedArrowSpan rejectedArrow namesRejected =>
      cases successful with
      | absent arrowAbsent =>
          exact absent_conflicts_exact arrowAbsent rejectedArrow
      | present clauseParsed =>
          cases clauseParsed with
          | parsed successfulArrowSpan successfulArrow successfulNames =>
              have afterArrowEq := exactToken_output_unique rejectedArrow
                successfulArrow
              subst afterArrowEq
              exact namesRejected.disjoint ⟨_, _, successfulNames⟩

/-- Optional-return outcomes are deterministic and exclusive. -/
theorem yulReturnsDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulReturnsOrdinaryParses YulReturnsRejects where
  successOutputUnique := YulReturnsOrdinaryParses.output_unique
  successRejectDisjoint := YulReturnsRejects.disjointOrdinary

/-- Ordinary function success has a unique final remainder. -/
theorem YulFunctionStatementOrdinaryParses.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulFunctionStatementOrdinaryParses statementOrdinary input
      left afterLeft)
    (rightParsed : YulFunctionStatementOrdinaryParses statementOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftMarkerSpan leftBodySpan leftMarker leftName leftParameters
        leftReturns leftBody =>
      cases rightParsed with
      | parsed rightMarkerSpan rightBodySpan rightMarker rightName
            rightParameters rightReturns rightBody =>
          have afterMarkerEq := exactToken_output_unique leftMarker rightMarker
          subst afterMarkerEq
          have afterNameEq := leftName.output_unique rightName
          subst afterNameEq
          have afterParametersEq := leftParameters.output_unique
            rightParameters
          subst afterParametersEq
          have afterReturnsEq := leftReturns.output_unique rightReturns
          subst afterReturnsEq
          exact leftBody.output_unique outcomes rightBody

/-- Exact function rejection excludes every ordinary function success. -/
theorem YulFunctionStatementRejects.disjointOrdinary
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects)
    {input rejected : Remainder}
    (rejection : YulFunctionStatementRejects statementOrdinary
      statementRejects input rejected) :
    ¬ ∃ statement output,
      YulFunctionStatementOrdinaryParses statementOrdinary input statement
        output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed successfulMarkerSpan successfulBodySpan successfulMarker
        successfulName successfulParameters successfulReturns successfulBody =>
      cases rejection with
      | markerMissing markerAbsent =>
          exact absent_conflicts_exact markerAbsent successfulMarker
      | nameRejected rejectedMarkerSpan rejectedMarker nameRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          exact nameRejected.disjoint ⟨_, _, successfulName⟩
      | parametersRejected rejectedMarkerSpan rejectedMarker rejectedName
            parametersRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          exact parametersRejected.disjointOrdinary
            ⟨_, _, successfulParameters⟩
      | returnsRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters returnsRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          exact returnsRejected.disjointOrdinary ⟨_, _, successfulReturns⟩
      | bodyRejected rejectedMarkerSpan rejectedMarker rejectedName
            rejectedParameters rejectedReturns bodyRejected =>
          have afterMarkerEq := exactToken_output_unique rejectedMarker
            successfulMarker
          subst afterMarkerEq
          have afterNameEq := rejectedName.output_unique successfulName
          subst afterNameEq
          have afterParametersEq := rejectedParameters.output_unique
            successfulParameters
          subst afterParametersEq
          have afterReturnsEq := rejectedReturns.output_unique successfulReturns
          subst afterReturnsEq
          exact bodyRejected.disjointOrdinary outcomes
            ⟨_, _, _, successfulBody⟩

/-- Ordinary function successes and exact rejections form a deterministic
outcome contract. -/
theorem yulFunctionStatementDeterministicOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : DeterministicOutcomeSpec statementOrdinary statementRejects) :
    DeterministicOutcomeSpec
      (YulFunctionStatementOrdinaryParses statementOrdinary)
      (YulFunctionStatementRejects statementOrdinary statementRejects) where
  successOutputUnique :=
    YulFunctionStatementOrdinaryParses.output_unique outcomes
  successRejectDisjoint :=
    YulFunctionStatementRejects.disjointOrdinary outcomes

/-- Every clean parameter list embeds into ordinary parameter success. -/
theorem YulParametersParses.toOrdinary {input output : Remainder}
    {parameters : DelimitedList Syntax.YulIdentifier}
    (parsed : YulParametersParses input parameters output) :
    YulParametersOrdinaryParses input parameters output :=
  parsed.mapElementRelation YulNameParses.toOrdinary

/-- Every clean return clause embeds into ordinary success. -/
theorem YulReturnClauseParses.toOrdinary {input output : Remainder}
    {clause : Syntax.YulReturnClause}
    (parsed : YulReturnClauseParses input clause output) :
    YulReturnClauseOrdinaryParses input clause output := by
  cases parsed with
  | parsed arrowSpan namesSpan arrowParsed namesParsed =>
      exact .parsed arrowSpan arrowParsed namesParsed.toOrdinary

/-- Every clean optional return clause embeds into ordinary success. -/
theorem YulReturnsParses.toOrdinary {input output : Remainder}
    {returns : Option Syntax.YulReturnClause}
    (parsed : YulReturnsParses input returns output) :
    YulReturnsOrdinaryParses input returns output := by
  cases parsed with
  | absent arrowAbsent => exact .absent arrowAbsent
  | present clauseParsed => exact .present clauseParsed.toOrdinary

/-- Every clean function embeds into ordinary success with identical AST,
span, order, and remainder. -/
theorem YulFunctionStatementParses.toOrdinary
    {statementClean statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (cleanToOrdinary : ∀ {input statement output},
      statementClean input statement output →
        statementOrdinary input statement output)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulFunctionStatementParses statementClean input statement
      output) :
    YulFunctionStatementOrdinaryParses statementOrdinary input statement
      output := by
  cases parsed with
  | parsed markerSpan bodySpan markerParsed nameParsed parametersParsed
        returnsParsed bodyParsed =>
      exact .parsed markerSpan bodySpan markerParsed nameParsed.toOrdinary
        parametersParsed.toOrdinary returnsParsed.toOrdinary
        (bodyParsed.toOrdinary cleanToOrdinary)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBlockExactnessProperties
/-! Exact spans, source-order bodies, and rejection endpoints of Yul blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact statements fix every block-item span, forward body, and remainder. -/
theorem YulBlockItemsParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {openingSpan : SourceSpan} {input : Remainder}
    {leftSpan rightSpan : SourceSpan} {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockItemsParses statementOrdinary openingSpan input
      leftSpan leftBody afterLeft)
    (rightParsed : YulBlockItemsParses statementOrdinary openingSpan input
      rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  induction leftParsed generalizing rightSpan rightBody afterRight with
  | close leftClosing leftToken =>
      cases rightParsed with
      | close rightClosing rightToken =>
          rcases leftToken.result_unique rightToken with ⟨spanEq, outputEq⟩
          subst spanEq
          exact ⟨rfl, rfl, outputEq⟩
      | next _ rightAbsent _ _ _ =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
  | next leftNotAtEnd leftAbsent leftStatement leftProgress leftTail ih =>
      cases rightParsed with
      | close _ rightToken =>
          exact False.elim (absent_conflicts_exact leftAbsent rightToken)
      | next _ _ rightStatement _ rightTail =>
          rcases outcomes.successResultUnique leftStatement rightStatement with
            ⟨statementEq, outputEq⟩
          subst statementEq
          subst outputEq
          rcases ih rightTail with ⟨spanEq, bodyEq, finalEq⟩
          subst bodyEq
          exact ⟨spanEq, rfl, finalEq⟩

/-- A complete Yul block fixes its covering span, forward body, and remainder. -/
theorem YulBlockParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : SourceSpan}
    {leftBody rightBody : List Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockOrdinaryParses statementOrdinary input leftSpan
      leftBody afterLeft)
    (rightParsed : YulBlockOrdinaryParses statementOrdinary input rightSpan
      rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftOpening leftToken leftItems =>
      cases rightParsed with
      | parsed rightOpening rightToken rightItems =>
          rcases leftToken.result_unique rightToken with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          exact leftItems.result_unique outcomes rightItems

/-- Exact statements fix the first rejecting block-item endpoint. -/
theorem YulBlockItemsRejects.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input left right : Remainder}
    (leftRejected : YulBlockItemsRejects statementOrdinary statementRejects input left)
    (rightRejected : YulBlockItemsRejects statementOrdinary statementRejects input right) :
    left = right := by
  induction leftRejected generalizing right with
  | missingClose leftAbsent leftAtEnd =>
      cases rightRejected with
      | missingClose => rfl
      | statementRejected rightNotAtEnd _ _
      | laterRejected rightNotAtEnd _ _ _ _ =>
          exact False.elim ((Nat.not_lt_of_ge leftAtEnd) rightNotAtEnd)
  | statementRejected leftNotAtEnd leftAbsent leftStatementRejected =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact outcomes.rejectOutputUnique leftStatementRejected rightStatementRejected
      | laterRejected _ _ rightStatement _ _ =>
          exact False.elim
            (outcomes.successRejectDisjoint leftStatementRejected ⟨_, _, rightStatement⟩)
  | laterRejected leftNotAtEnd leftAbsent leftStatement leftProgress leftTail ih =>
      cases rightRejected with
      | missingClose _ rightAtEnd =>
          exact False.elim ((Nat.not_lt_of_ge rightAtEnd) leftNotAtEnd)
      | statementRejected _ _ rightStatementRejected =>
          exact False.elim
            (outcomes.successRejectDisjoint rightStatementRejected ⟨_, _, leftStatement⟩)
      | laterRejected _ _ rightStatement _ rightTail =>
          have outputEq := outcomes.successOutputUnique leftStatement rightStatement
          subst outputEq
          exact ih rightTail

/-- Exact statements fix the rejecting endpoint of a complete Yul block. -/
theorem YulBlockRejects.output_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input left right : Remainder}
    (leftRejected : YulBlockRejects statementOrdinary statementRejects input left)
    (rightRejected : YulBlockRejects statementOrdinary statementRejects input right) :
    left = right := by
  cases leftRejected with
  | openingMissing leftAbsent =>
      cases rightRejected with
      | openingMissing => rfl
      | itemsRejected _ rightOpening _ =>
          exact False.elim (absent_conflicts_exact leftAbsent rightOpening)
  | itemsRejected _ leftOpening leftItems =>
      cases rightRejected with
      | openingMissing rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftOpening)
      | itemsRejected _ rightOpening rightItems =>
          have outputEq := leftOpening.output_unique rightOpening
          subst outputEq
          exact leftItems.output_unique outcomes rightItems

/-- Exact statements lift to fully exact block outcomes. -/
theorem yulBlockExactOutcomeSpec
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects) :
    ExactDeterministicOutcomeSpec (YulBlockOutcomeParses statementOrdinary)
      (YulBlockRejects statementOrdinary statementRejects) where
  toDeterministicOutcomeSpec := yulBlockDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    rcases YulBlockParses.result_unique outcomes leftParsed rightParsed with
      ⟨spanEq, bodyEq, outputEq⟩
    cases left
    cases right
    simp_all
  rejectOutputUnique := YulBlockRejects.output_unique outcomes

/-- Lifting a block to statement position preserves the exact AST. -/
theorem YulBlockStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulBlockStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulBlockStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftBlock =>
      cases rightParsed with
      | parsed rightBlock =>
          rcases leftBlock.result_unique outcomes rightBlock with ⟨spanEq, bodyEq, outputEq⟩
          subst spanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementControlExactnessProperties
/-! Exact ASTs of recursive inline-Yul conditional and loop statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive blocks and public expressions fix an entire Yul if AST. -/
theorem YulIfStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulIfStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulIfStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftCondition leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightCondition rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftCondition.result_unique rightCondition with ⟨conditionEq, conditionOutputEq⟩
          subst conditionEq
          subst conditionOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

/-- Exact recursive blocks fix all three source-order loop bodies and its span. -/
theorem YulForStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulForStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulForStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftInitializer leftCondition leftPost leftBody =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightInitializer rightCondition rightPost rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftInitializer.result_unique outcomes rightInitializer with
            ⟨initializerSpanEq, initializerEq, initializerOutputEq⟩
          subst initializerEq
          subst initializerOutputEq
          rcases leftCondition.result_unique rightCondition with ⟨conditionEq, conditionOutputEq⟩
          subst conditionEq
          subst conditionOutputEq
          rcases leftPost.result_unique outcomes rightPost with ⟨postSpanEq, postEq, postOutputEq⟩
          subst postEq
          subst postOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulSwitchExactnessProperties
/-! Exact case order, optional default spans, and complete Yul switch ASTs. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact recursive blocks fix each complete switch case arm and remainder. -/
theorem YulCaseArmParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseArmOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulCaseArmOrdinaryParses statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftSpan leftBodySpan leftMarker leftLiteral leftBody =>
      cases rightParsed with
      | parsed rightSpan rightBodySpan rightMarker rightLiteral rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftLiteral.result_unique rightLiteral with ⟨literalEq, literalOutputEq⟩
          subst literalEq
          subst literalOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          exact ⟨rfl, finalEq⟩

/-- A maximal case list fixes its full source-order arm list and remainder. -/
theorem YulCaseListParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : List Syntax.YulCase}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulCaseListOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulCaseListOrdinaryParses statementOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight := by
  induction leftParsed generalizing right afterRight with
  | done leftAbsent =>
      cases rightParsed with
      | done => exact ⟨rfl, rfl⟩
      | next rightArm _ _ => exact False.elim (leftAbsent rightArm.startsAt)
  | next leftArm leftProgress leftTail ih =>
      cases rightParsed with
      | done rightAbsent => exact False.elim (rightAbsent leftArm.startsAt)
      | next rightArm _ rightTail =>
          rcases leftArm.result_unique outcomes rightArm with ⟨armEq, outputEq⟩
          subst armEq
          subst outputEq
          rcases ih rightTail with ⟨tailEq, finalEq⟩
          subst tailEq
          exact ⟨rfl, finalEq⟩

/-- Default priority fixes its aligned optional span/body pair and remainder. -/
theorem OptionalYulDefaultParses.result_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {leftSpan rightSpan : Option SourceSpan}
    {leftBody rightBody : Option (List Syntax.YulStmt)}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      leftSpan leftBody afterLeft)
    (rightParsed : OptionalYulDefaultOrdinaryParses statementOrdinary input
      rightSpan rightBody afterRight) :
    leftSpan = rightSpan ∧ leftBody = rightBody ∧ afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => exact ⟨rfl, rfl, rfl⟩
      | present _ _ rightMarker _ => exact False.elim (leftAbsent ⟨_, rightMarker.1⟩)
  | present leftMarkerSpan leftBodySpan leftMarker leftBody =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftMarker.1⟩)
      | present rightMarkerSpan rightBodySpan rightMarker rightBody =>
          have outputEq := leftMarker.output_unique rightMarker
          subst outputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨spanEq, bodyEq, finalEq⟩
          subst spanEq
          subst bodyEq
          exact ⟨rfl, rfl, finalEq⟩

/-- Ordinary switches fix both normal switch ASTs and diagnosed empty-case ASTs. -/
theorem YulSwitchStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulSwitchStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulSwitchStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed <;> cases rightParsed <;>
    grind (ematch := 15) [ExactTokenParses.result_unique,
      YulExpressionOrdinaryParses.result_unique,
      YulCaseListParses.result_unique outcomes,
      OptionalYulDefaultParses.result_unique outcomes]

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulFunctionExactnessProperties
/-! Exact ASTs and source-order signatures of inline-Yul function statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary Yul parameter lists fix their names and complete covering span. -/
theorem YulParametersOrdinaryParses.value_unique
    {input : Remainder} {left right : DelimitedList Syntax.YulIdentifier}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulParametersOrdinaryParses input left afterLeft)
    (rightParsed : YulParametersOrdinaryParses input right afterRight) : left = right :=
  TrailingDelimitedListParses.value_unique yulNameExactOutcomeSpec leftParsed rightParsed

/-- A return clause fixes its arrow, source-order names, and covering span. -/
theorem YulReturnClauseOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnClauseOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnClauseOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | parsed leftSpan leftArrow leftNames =>
      cases rightParsed with
      | parsed rightSpan rightArrow rightNames =>
          rcases leftArrow.result_unique rightArrow with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases leftNames.value_unique rightNames
          rfl

/-- Optional returns fix the absent/present branch and complete return clause. -/
theorem YulReturnsOrdinaryParses.value_unique
    {input : Remainder} {left right : Option Syntax.YulReturnClause}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnsOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnsOrdinaryParses input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightClause =>
          cases rightClause with
          | parsed _ rightToken _ => exact False.elim (leftAbsent ⟨_, rightToken.1⟩)
  | present leftClause =>
      cases rightParsed with
      | absent rightAbsent =>
          cases leftClause with
          | parsed _ leftToken _ => exact False.elim (rightAbsent ⟨_, leftToken.1⟩)
      | present rightClause => exact congrArg some (leftClause.value_unique rightClause)

/-- Exact recursive blocks fix the complete ordinary Yul function AST. -/
theorem YulFunctionStatementOrdinaryParses.value_unique
    {statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {statementRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec statementOrdinary statementRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulFunctionStatementOrdinaryParses statementOrdinary input left afterLeft)
    (rightParsed : YulFunctionStatementOrdinaryParses statementOrdinary input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftBodySpan leftMarker leftName leftParameters leftReturns leftBody =>
      cases rightParsed with
      | parsed rightSpan rightBodySpan rightMarker rightName rightParameters rightReturns rightBody =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftName.result_unique rightName with ⟨nameEq, nameOutputEq⟩
          subst nameEq
          subst nameOutputEq
          have parametersEq := leftParameters.value_unique rightParameters
          have parametersOutputEq := leftParameters.output_unique rightParameters
          subst parametersEq
          subst parametersOutputEq
          have returnsEq := leftReturns.value_unique rightReturns
          have returnsOutputEq := leftReturns.output_unique rightReturns
          subst returnsEq
          subst returnsOutputEq
          rcases leftBody.result_unique outcomes rightBody with ⟨bodySpanEq, bodyEq, finalEq⟩
          subst bodySpanEq
          subst bodyEq
          rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementLayerExactnessProperties
/-! Exact optional termination and recovery outcomes for one Yul statement layer. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Optional semicolon consumption preserves the complete core statement AST. -/
theorem YulStatementTerminatedOrdinaryParses.value_unique
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec coreOrdinary coreRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input left afterLeft)
    (rightParsed : YulStatementTerminatedOrdinaryParses coreOrdinary input right afterRight) :
    left = right := by
  rcases leftParsed with ⟨leftCore, leftCoreParsed, leftSemicolon⟩
  rcases rightParsed with ⟨rightCore, rightCoreParsed, rightSemicolon⟩
  exact outcomes.successValueUnique leftCoreParsed rightCoreParsed

/-- Exact core outcomes remain exact after maximal optional termination. -/
theorem yulStatementTerminatedExactOutcomeSpec
    {coreOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {coreRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec coreOrdinary coreRejects) :
    ExactDeterministicOutcomeSpec (YulStatementTerminatedOrdinaryParses coreOrdinary)
      (YulStatementTerminatedRejects coreRejects) where
  toDeterministicOutcomeSpec :=
    yulStatementTerminatedDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec
  successValueUnique := YulStatementTerminatedOrdinaryParses.value_unique outcomes
  rejectOutputUnique := outcomes.rejectOutputUnique

/-- Recovery fixes its error span and AST when the accumulated spans are fixed. -/
theorem YulStatementRecoveryScanParses.value_unique
    {first last : SourceSpan} {input : Remainder}
    {left right : Syntax.YulStmt} {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementRecoveryScanParses first last input left afterLeft)
    (rightParsed : YulStatementRecoveryScanParses first last input right afterRight) :
    left = right := by
  induction leftParsed generalizing right afterRight with
  | stop leftStops =>
      cases rightParsed with
      | stop => rfl
      | next rightContinues _ _ => exact False.elim (rightContinues leftStops)
  | next leftContinues leftCurrent leftTail ih =>
      cases rightParsed with
      | stop rightStops => exact False.elim (leftContinues rightStops)
      | next _ rightCurrent rightTail =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact ih rightTail

/-- Ordinary recovery preserves exact successful statement ASTs. -/
theorem YulStatementLayerOrdinaryParses.value_unique
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec terminatedOrdinary terminatedRejects)
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input left afterLeft)
    (rightParsed : YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
      input right afterRight) : left = right := by
  cases leftParsed with
  | terminated leftTerminated =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact outcomes.successValueUnique leftTerminated rightTerminated
      | recovered rightRejected _ _ _ =>
          exact False.elim (outcomes.successRejectDisjoint rightRejected ⟨_, _, leftTerminated⟩)
  | recovered leftRejected _ leftCurrent leftScan =>
      cases rightParsed with
      | terminated rightTerminated =>
          exact False.elim (outcomes.successRejectDisjoint leftRejected ⟨_, _, rightTerminated⟩)
      | recovered _ _ rightCurrent rightScan =>
          have tokenEq := leftCurrent.token_unique rightCurrent
          cases tokenEq
          exact leftScan.value_unique rightScan

/-- Statement boundary rejection has a unique complete non-consuming endpoint. -/
theorem YulStatementRejects.output_unique {input left right : Remainder}
    (leftRejected : YulStatementRejects input left)
    (rightRejected : YulStatementRejects input right) : left = right := by
  rw [leftRejected.output_eq, rightRejected.output_eq]

/-- Exact terminated outcomes lift through statement recovery unchanged. -/
theorem yulStatementLayerExactOutcomeSpec
    {terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop}
    {terminatedRejects : Remainder → Remainder → Prop}
    (outcomes : ExactDeterministicOutcomeSpec terminatedOrdinary terminatedRejects)
    (boundaryDisjoint : ∀ {input rejected}, YulStatementRejects input rejected →
      ¬ ∃ statement output, terminatedOrdinary input statement output) :
    ExactDeterministicOutcomeSpec
      (YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects)
      YulStatementRejects where
  toDeterministicOutcomeSpec :=
    yulStatementLayerDeterministicOutcomeSpec outcomes.toDeterministicOutcomeSpec boundaryDisjoint
  successValueUnique := YulStatementLayerOrdinaryParses.value_unique outcomes
  rejectOutputUnique := YulStatementRejects.output_unique

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulAssignmentOutcomeProperties
/-!
Disjointness of exact transactional Yul-assignment rejection and the strict
clean assignment grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem absent_conflicts_exact_variant {input output : Remainder}
    {kind : TokenKind} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact assignment rejection cannot overlap a clean assignment success
when clean expression successes embed into deterministic ordinary outcomes. -/
theorem YulAssignmentRejects.disjointClean
    (ordinaryExpression cleanExpression :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryExpression
      expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output)
    {input rejected : Remainder}
    (rejection : YulAssignmentRejects expressionRejects input rejected) :
    ¬ ∃ statement output,
      YulAssignmentParses cleanExpression input statement output := by
  rintro ⟨statement, output, successful⟩
  cases successful with
  | parsed namesSpan operatorSpan cleanNamesParsed cleanOperatorParsed
        cleanValueParsed =>
      have cleanNamesOrdinary := cleanNamesParsed.toOrdinary
      cases rejection with
      | namesRejected namesRejected =>
          exact namesRejected.disjoint
            ⟨{ span := namesSpan, names := _ }, _, cleanNamesOrdinary⟩
      | operatorAbsent rejectedNamesParsed operatorAbsent =>
          have afterNamesEq :=
            yulNamesDeterministicOutcomeSpec.successOutputUnique
              rejectedNamesParsed cleanNamesOrdinary
          subst afterNamesEq
          exact absent_conflicts_exact_variant operatorAbsent cleanOperatorParsed
      | expressionRejected rejectedOperatorSpan rejectedNamesParsed
            rejectedOperatorParsed valueRejected =>
          have afterNamesEq :=
            yulNamesDeterministicOutcomeSpec.successOutputUnique
              rejectedNamesParsed cleanNamesOrdinary
          subst afterNamesEq
          exact outcomes.successRejectDisjoint valueRejected
            ⟨_, _, by
              simpa [rejectedOperatorParsed.2, cleanOperatorParsed.2] using
                cleanToOrdinary cleanValueParsed⟩

/-- Build the exact committed-assignment fallback from deterministic ordinary
expression outcomes. -/
def YulAssignmentFallbackSpec.ofOutcomes
    (ordinaryExpression cleanExpression :
      Remainder → Syntax.YulExpr → Remainder → Prop)
    (expressionRejects : Remainder → Remainder → Prop)
    (outcomes : DeterministicOutcomeSpec ordinaryExpression
      expressionRejects)
    (cleanToOrdinary : ∀ {input value output},
      cleanExpression input value output →
        ordinaryExpression input value output) :
    YulAssignmentFallbackSpec cleanExpression where
  rejects := YulAssignmentFallbackRejects expressionRejects
  disjoint := by
    intro input rejected
    rcases rejected with ⟨rejectedOutput, rejection⟩
    exact rejection.disjointClean ordinaryExpression cleanExpression
      expressionRejects outcomes cleanToOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulAssignmentPublicFallbackProperties
/-!
Concrete parser-independent transactional assignment fallback for the public
recursive inline-Yul expression grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Transactional Yul-assignment fallback induced by the complete public
expression outcome contract. -/
def yulAssignmentPublicFallbackSpec :
    YulAssignmentFallbackSpec YulExpressionParses :=
  YulAssignmentFallbackSpec.ofOutcomes YulExpressionOrdinaryParses
    YulExpressionParses YulExpressionRejects
    yulExpressionPublicDeterministicOutcomeSpec
    YulExpressionParses.toOrdinary

/-- The concrete fallback records exactly an existential public-expression
assignment rejection. -/
@[simp] theorem yulAssignmentPublicFallbackSpec_rejects_iff
    {input : Remainder} :
    yulAssignmentPublicFallbackSpec.rejects input ↔
      YulAssignmentFallbackRejects YulExpressionRejects input := by
  rfl

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulNameStatementOutcomeProperties
/-!
Parser-independent ordinary outcomes for the name-start branch of the Yul
statement dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary success of the transactional assignment-or-expression choice. -/
abbrev YulNameStatementOrdinaryParses :=
  TransactionalFallbackOrdinaryParses
    YulAssignmentOrdinaryParses
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementOrdinaryParses

/-- Exact nonconsuming rejection when both name-start alternatives reject. -/
abbrev YulNameStatementRejects :=
  TransactionalFallbackRejects
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementRejects

/-- Name-start ordinary outcomes inherit determinism from assignment and
expression-statement outcomes. -/
theorem yulNameStatementDeterministicOutcomeSpec :
    DeterministicOutcomeSpec YulNameStatementOrdinaryParses
      YulNameStatementRejects :=
  transactionalFallbackDeterministicOutcomeSpec
    YulAssignmentOrdinaryParses YulExpressionStatementOrdinaryParses
    (YulAssignmentRejects YulExpressionRejects)
    YulExpressionStatementRejects
    yulAssignmentDeterministicOutcomeSpec
    yulExpressionStatementDeterministicOutcomeSpec

/-- The clean name-choice grammar embeds into the public ordinary outcome
without changing the selected AST or remainder. -/
theorem YulNameStatementChoiceParses.toOrdinary
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulNameStatementChoiceParses YulExpressionParses
      yulAssignmentPublicFallbackSpec input statement output) :
    YulNameStatementOrdinaryParses input statement output := by
  cases parsed with
  | assignment nameStart assignmentParsed =>
      exact .primary assignmentParsed.toOrdinary
  | rewound nameStart assignmentRejected expressionParsed =>
      rw [yulAssignmentPublicFallbackSpec_rejects_iff]
        at assignmentRejected
      rcases assignmentRejected with ⟨rejected, rejection⟩
      exact .fallback rejection expressionParsed.toOrdinary

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementBasicExactnessProperties
/-! Exact ASTs of basic inline-Yul statement primaries. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lifting an ordinary expression to statement position fixes its AST. -/
theorem YulExpressionStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulExpressionStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulExpressionStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftExpression =>
      cases rightParsed with
      | parsed rightExpression =>
          cases leftExpression.value_unique rightExpression
          rfl

/-- Expression-statement rejection has one exact non-consuming endpoint. -/
theorem YulExpressionStatementRejects.output_eq {input rejected : Remainder}
    (rejectedAt : YulExpressionStatementRejects input rejected) : rejected = input := by
  cases rejectedAt with
  | expressionRejected rejection => exact rejection.output_eq

/-- Public ordinary expressions give exact expression-statement outcomes. -/
theorem yulExpressionStatementExactOutcomeSpec :
    ExactDeterministicOutcomeSpec YulExpressionStatementOrdinaryParses
      YulExpressionStatementRejects where
  toDeterministicOutcomeSpec := yulExpressionStatementDeterministicOutcomeSpec
  successValueUnique := YulExpressionStatementOrdinaryParses.value_unique
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    rw [leftRejected.output_eq, rightRejected.output_eq]

/-- The synthesized source-level return call has one complete AST. -/
theorem YulReturnBuiltinOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulReturnBuiltinOrdinaryParses input left afterLeft)
    (rightParsed : YulReturnBuiltinOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftArguments =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightArguments =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          cases leftArguments.value_unique yulExpressionExactOutcomeSpec rightArguments
          rfl

/-- Keyword-only Yul statements have the exact current token span and AST. -/
theorem YulControlTokenOrdinaryParses.value_unique
    {keyword : HardKeyword} {statementValue : Syntax.YulStmtValue}
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulControlTokenOrdinaryParses keyword statementValue input left afterLeft)
    (rightParsed : YulControlTokenOrdinaryParses keyword statementValue input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftToken =>
      cases rightParsed with
      | parsed rightSpan rightToken =>
          cases leftToken.span_unique rightToken
          rfl

/-- The optional initializer fixes its absence/presence branch and expression. -/
theorem YulLetInitializerOrdinaryParses.value_unique
    {input : Remainder} {left right : Option Syntax.YulExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetInitializerOrdinaryParses input left afterLeft)
    (rightParsed : YulLetInitializerOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present _ rightToken _ => exact False.elim (leftAbsent ⟨_, rightToken.1⟩)
  | present _ leftToken leftExpression =>
      cases rightParsed with
      | absent rightAbsent => exact False.elim (rightAbsent ⟨_, leftToken.1⟩)
      | present _ rightToken rightExpression =>
          have outputEq := leftToken.output_unique rightToken
          subst outputEq
          exact congrArg some (leftExpression.value_unique rightExpression)

/-- Ordinary let statements fix exact names, initializer, and covering span. -/
theorem YulLetStatementOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulLetStatementOrdinaryParses input left afterLeft)
    (rightParsed : YulLetStatementOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftMarker leftNames leftInitializer =>
      cases rightParsed with
      | parsed rightSpan rightMarker rightNames rightInitializer =>
          rcases leftMarker.result_unique rightMarker with ⟨spanEq, outputEq⟩
          subst spanEq
          subst outputEq
          rcases leftNames.result_unique rightNames with ⟨namesEq, namesOutputEq⟩
          subst namesEq
          subst namesOutputEq
          cases leftInitializer.value_unique rightInitializer
          rfl

/-- Ordinary assignments fix the forward target list, expression, and span. -/
theorem YulAssignmentOrdinaryParses.value_unique
    {input : Remainder} {left right : Syntax.YulStmt}
    {afterLeft afterRight : Remainder}
    (leftParsed : YulAssignmentOrdinaryParses input left afterLeft)
    (rightParsed : YulAssignmentOrdinaryParses input right afterRight) :
    left = right := by
  cases leftParsed with
  | parsed leftSpan leftNames leftOperator leftExpression =>
      cases rightParsed with
      | parsed rightSpan rightNames rightOperator rightExpression =>
          rcases leftNames.result_unique rightNames with ⟨namesEq, namesOutputEq⟩
          subst namesEq
          subst namesOutputEq
          have outputEq := leftOperator.output_unique rightOperator
          subst outputEq
          cases leftExpression.value_unique rightExpression
          rfl

end Solcore.Syntax.DeclarativeGrammar
end
