import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeCoreStatementSimpleOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties

/-! Deterministic ordinary outcomes of Core `let` and `return` statements. -/

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

private theorem absent_conflicts_token {kind : TokenKind}
    {input : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (token : TokenAt input.tokens input.endIndex input.cursor {
      span, value := kind }) : False :=
  absent ⟨span, token⟩

/-- Optional let types have functional ordinary success. -/
theorem OptionalLetTypeParses.output_unique
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input : Remainder} {left right : Option Syntax.TypeExpr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetTypeParses input left afterLeft)
    (rightParsed : OptionalLetTypeParses input right afterRight) :
    afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present span token parsed =>
          exact False.elim (absent_conflicts_exact leftAbsent token)
  | present leftSpan leftToken leftType =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken rightType =>
          have afterTokenEq := exactToken_output_unique leftToken rightToken
          subst afterTokenEq
          exact typeOutcomes.successOutputUnique leftType rightType

/-- Optional let-type rejection excludes ordinary success. -/
theorem OptionalLetTypeRejects.disjointOrdinary
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects)
    {input rejected : Remainder}
    (rejection : OptionalLetTypeRejects typeRejects input rejected) :
    ¬ ∃ type output, OptionalLetTypeParses input type output := by
  rintro ⟨type, output, successful⟩
  cases rejection with
  | typeRejected rejectedSpan rejectedToken rejectedType =>
      cases successful with
      | absent colonAbsent =>
          exact absent_conflicts_exact colonAbsent rejectedToken
      | present successfulSpan successfulToken successfulType =>
          have afterTokenEq := exactToken_output_unique rejectedToken
            successfulToken
          subst afterTokenEq
          exact typeOutcomes.successRejectDisjoint rejectedType
            ⟨_, _, successfulType⟩

/-- Deterministic outcomes for optional let types. -/
theorem optionalLetTypeDeterministicOutcomeSpec
    {typeRejects : Remainder → Remainder → Prop}
    (typeOutcomes : DeterministicOutcomeSpec TypeExprParses typeRejects) :
    DeterministicOutcomeSpec OptionalLetTypeParses
      (OptionalLetTypeRejects typeRejects) where
  successOutputUnique := OptionalLetTypeParses.output_unique typeOutcomes
  successRejectDisjoint :=
    OptionalLetTypeRejects.disjointOrdinary typeOutcomes

/-- Optional let initializers have functional ordinary success. -/
theorem OptionalLetInitializerOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input left afterLeft)
    (rightParsed : OptionalLetInitializerOrdinaryParses expressionOrdinary
      input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present span token parsed =>
          exact False.elim (absent_conflicts_exact leftAbsent token)
  | present leftSpan leftToken leftValue =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftToken)
      | present rightSpan rightToken rightValue =>
          have afterTokenEq := exactToken_output_unique leftToken rightToken
          subst afterTokenEq
          exact expressionOutcomes.successOutputUnique leftValue rightValue

/-- Optional initializer rejection excludes ordinary success. -/
theorem OptionalLetInitializerRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalLetInitializerRejects expressionRejects input
      rejected) :
    ¬ ∃ initializer output,
      OptionalLetInitializerOrdinaryParses expressionOrdinary input
        initializer output := by
  rintro ⟨initializer, output, successful⟩
  cases rejection with
  | expressionRejected rejectedSpan rejectedToken rejectedExpression =>
      cases successful with
      | absent equalAbsent =>
          exact absent_conflicts_exact equalAbsent rejectedToken
      | present successfulSpan successfulToken successfulExpression =>
          have afterTokenEq := exactToken_output_unique rejectedToken
            successfulToken
          subst afterTokenEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Deterministic outcomes for optional let initializers. -/
theorem optionalLetInitializerDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalLetInitializerOrdinaryParses expressionOrdinary)
      (OptionalLetInitializerRejects expressionRejects) where
  successOutputUnique :=
    OptionalLetInitializerOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    OptionalLetInitializerRejects.disjointOrdinary expressionOutcomes

/-- Optional return values have functional ordinary success. -/
theorem OptionalReturnValueOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      left afterLeft)
    (rightParsed : OptionalReturnValueOrdinaryParses expressionOrdinary input
      right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftSpan leftToken =>
      cases rightParsed with
      | absent => rfl
      | present rightAbsent rightValue =>
          exact False.elim
            (absent_conflicts_token rightAbsent leftToken)
  | present leftAbsent leftValue =>
      cases rightParsed with
      | absent rightSpan rightToken =>
          exact False.elim
            (absent_conflicts_token leftAbsent rightToken)
      | present rightAbsent rightValue =>
          exact expressionOutcomes.successOutputUnique leftValue rightValue

/-- Optional return-value rejection excludes ordinary success. -/
theorem OptionalReturnValueRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalReturnValueRejects expressionRejects input rejected) :
    ¬ ∃ value output,
      OptionalReturnValueOrdinaryParses expressionOrdinary input value
        output := by
  rintro ⟨value, output, successful⟩
  cases rejection with
  | expressionRejected semicolonAbsent rejectedExpression =>
      cases successful with
      | absent span token =>
          exact absent_conflicts_token semicolonAbsent token
      | present successfulAbsent successfulExpression =>
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Deterministic outcomes for optional return values. -/
theorem optionalReturnValueDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalReturnValueOrdinaryParses expressionOrdinary)
      (OptionalReturnValueRejects expressionRejects) where
  successOutputUnique :=
    OptionalReturnValueOrdinaryParses.output_unique expressionOutcomes
  successRejectDisjoint :=
    OptionalReturnValueRejects.disjointOrdinary expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
