import Solcore.Syntax.DeclarativeContractFieldOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreExpressionPostfixOrdinaryProperties
import Solcore.Syntax.DeclarativeCoreTypeOutcomeProperties

/-! Deterministic exact ordinary outcomes for contract storage fields. -/

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

/-- Optional field initializers have one final remainder. -/
theorem OptionalContractFieldInitializerOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightEqual rightExpression =>
          exact False.elim (absent_conflicts_exact leftAbsent rightEqual)
  | present leftSpan leftEqual leftExpression =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim (absent_conflicts_exact rightAbsent leftEqual)
      | present rightSpan rightEqual rightExpression =>
          have afterEqualEq := exactToken_output_unique leftEqual rightEqual
          subst afterEqualEq
          exact expressionOutcomes.successOutputUnique leftExpression
            rightExpression

/-- Optional field-initializer rejection excludes ordinary success. -/
theorem OptionalContractFieldInitializerRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : OptionalContractFieldInitializerRejects expressionRejects
      input rejected) :
    ¬ ∃ initializer output,
      OptionalContractFieldInitializerOrdinaryParses expressionOrdinary input
        initializer output := by
  rintro ⟨initializer, output, successful⟩
  cases rejection with
  | expressionRejected rejectedSpan rejectedEqual rejectedExpression =>
      cases successful with
      | absent equalAbsent =>
          exact absent_conflicts_exact equalAbsent rejectedEqual
      | present successfulSpan successfulEqual successfulExpression =>
          have afterEqualEq := exactToken_output_unique rejectedEqual
            successfulEqual
          subst afterEqualEq
          exact expressionOutcomes.successRejectDisjoint rejectedExpression
            ⟨_, _, successfulExpression⟩

/-- Optional contract-field initializers have deterministic ordinary outcomes. -/
theorem optionalContractFieldInitializerDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (OptionalContractFieldInitializerOrdinaryParses expressionOrdinary)
      (OptionalContractFieldInitializerRejects expressionRejects) where
  successOutputUnique :=
    OptionalContractFieldInitializerOrdinaryParses.output_unique
      expressionOutcomes
  successRejectDisjoint :=
    OptionalContractFieldInitializerRejects.disjointOrdinary
      expressionOutcomes

/-- Ordinary contract-field success has one final remainder. -/
theorem ContractFieldOrdinaryParses.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : afterLeft = afterRight := by
  cases leftParsed with
  | parsed leftColonSpan leftSemicolonSpan leftName leftColon leftType
        leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightColonSpan rightSemicolonSpan rightName rightColon rightType
            rightInitializer rightSemicolon =>
          have afterNameEq := IdentifierParses.output_unique leftName rightName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique leftColon rightColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique leftType rightType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalContractFieldInitializerOrdinaryParses.output_unique
              expressionOutcomes leftInitializer rightInitializer
          subst afterInitializerEq
          exact exactToken_output_unique leftSemicolon rightSemicolon

/-- Exact contract-field rejection excludes every ordinary success. -/
theorem ContractFieldRejects.disjointOrdinary
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input rejected : Remainder}
    (rejection : ContractFieldRejects expressionOrdinary expressionRejects
      input rejected) :
    ¬ ∃ field output,
      ContractFieldOrdinaryParses expressionOrdinary input field output := by
  rintro ⟨field, output, successful⟩
  cases successful with
  | parsed successfulColonSpan successfulSemicolonSpan successfulName
        successfulColon successfulType successfulInitializer
        successfulSemicolon =>
      cases rejection with
      | nameRejected nameRejected =>
          exact identifierDeterministicOutcomeSpec.successRejectDisjoint
            nameRejected ⟨_, _, successfulName⟩
      | colonMissing rejectedName colonAbsent =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          exact absent_conflicts_exact colonAbsent successfulColon
      | typeRejected rejectedColonSpan rejectedName rejectedColon
            typeRejected =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          exact typeExprDeterministicOutcomeSpec.successRejectDisjoint
            typeRejected ⟨_, _, successfulType⟩
      | initializerRejected rejectedColonSpan rejectedName rejectedColon
            rejectedType initializerRejected =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique rejectedType successfulType
          subst afterTypeEq
          exact (optionalContractFieldInitializerDeterministicOutcomeSpec
            expressionOutcomes).successRejectDisjoint initializerRejected
              ⟨_, _, successfulInitializer⟩
      | semicolonMissing rejectedColonSpan rejectedName rejectedColon
            rejectedType rejectedInitializer semicolonAbsent =>
          have afterNameEq := IdentifierParses.output_unique rejectedName
            successfulName
          subst afterNameEq
          have afterColonEq := exactToken_output_unique rejectedColon
            successfulColon
          subst afterColonEq
          have afterTypeEq := typeExprDeterministicOutcomeSpec
            |>.successOutputUnique rejectedType successfulType
          subst afterTypeEq
          have afterInitializerEq :=
            OptionalContractFieldInitializerOrdinaryParses.output_unique
              expressionOutcomes rejectedInitializer successfulInitializer
          subst afterInitializerEq
          exact absent_conflicts_exact semicolonAbsent successfulSemicolon

/-- Contract storage fields have deterministic and exclusive ordinary
outcomes. -/
theorem contractFieldDeterministicOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : DeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    DeterministicOutcomeSpec
      (ContractFieldOrdinaryParses expressionOrdinary)
      (ContractFieldRejects expressionOrdinary expressionRejects) where
  successOutputUnique := ContractFieldOrdinaryParses.output_unique
    expressionOutcomes
  successRejectDisjoint := ContractFieldRejects.disjointOrdinary
    expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
