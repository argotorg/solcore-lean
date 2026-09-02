import Solcore.Syntax.DeclarativeContractFieldOutcomeProperties
import Solcore.Syntax.DeclarativeCoreTypeExactnessProperties
import Solcore.Syntax.DeclarativePrimitiveExactnessProperties

/-!
Exactness transport through contract storage fields.

Core types are already unconditionally exact.  The only premise is an exact
outcome contract for the optional initializer expression.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

private theorem field_absent_conflicts_exact {kind : TokenKind}
    {input output : Remainder} {span : SourceSpan}
    (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor kind)
    (parsed : ExactTokenParses kind input span output) : False :=
  absent ⟨span, parsed.1⟩

/-- An exact initializer expression fixes the optional initializer value. -/
theorem OptionalContractFieldInitializerOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) : left = right := by
  cases leftParsed with
  | absent leftAbsent =>
      cases rightParsed with
      | absent => rfl
      | present rightSpan rightEqual rightExpression =>
          exact False.elim
            (field_absent_conflicts_exact leftAbsent rightEqual)
  | present leftSpan leftEqual leftExpression =>
      cases rightParsed with
      | absent rightAbsent =>
          exact False.elim
            (field_absent_conflicts_exact rightAbsent leftEqual)
      | present rightSpan rightEqual rightExpression =>
          have afterEqualEq := leftEqual.output_unique rightEqual
          subst afterEqualEq
          have expressionEq := expressionOutcomes.successValueUnique
            leftExpression rightExpression
          subst expressionEq
          rfl

/-- An exact initializer expression fixes both the optional value and final
remainder. -/
theorem OptionalContractFieldInitializerOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Option Syntax.Expr}
    {afterLeft afterRight : Remainder}
    (leftParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input left afterLeft)
    (rightParsed : OptionalContractFieldInitializerOrdinaryParses
      expressionOrdinary input right afterRight) :
    left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique expressionOutcomes rightParsed,
    leftParsed.output_unique
      expressionOutcomes.toDeterministicOutcomeSpec rightParsed⟩

/-- An exact initializer expression fixes the committed rejection endpoint. -/
theorem OptionalContractFieldInitializerRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : OptionalContractFieldInitializerRejects expressionRejects
      input left)
    (rightRejects : OptionalContractFieldInitializerRejects expressionRejects
      input right) : left = right := by
  cases leftRejects with
  | expressionRejected leftSpan leftEqual leftExpression =>
      cases rightRejects with
      | expressionRejected rightSpan rightEqual rightExpression =>
          have afterEqualEq := leftEqual.output_unique rightEqual
          subst afterEqualEq
          exact expressionOutcomes.rejectOutputUnique leftExpression
            rightExpression

/-- Exact expression outcomes lift through the optional `=` initializer. -/
theorem optionalContractFieldInitializerExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (OptionalContractFieldInitializerOrdinaryParses expressionOrdinary)
      (OptionalContractFieldInitializerRejects expressionRejects) where
  toDeterministicOutcomeSpec :=
    optionalContractFieldInitializerDeterministicOutcomeSpec
      expressionOutcomes.toDeterministicOutcomeSpec
  successValueUnique :=
    OptionalContractFieldInitializerOrdinaryParses.value_unique
      expressionOutcomes
  rejectOutputUnique :=
    OptionalContractFieldInitializerRejects.output_unique expressionOutcomes

/-- Exact initializer outcomes make a successful field fix its complete AST. -/
theorem ContractFieldOrdinaryParses.value_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : left = right := by
  cases leftParsed with
  | parsed leftColonSpan leftSemicolonSpan leftName leftColon leftType
      leftInitializer leftSemicolon =>
      cases rightParsed with
      | parsed rightColonSpan rightSemicolonSpan rightName rightColon rightType
          rightInitializer rightSemicolon =>
          rcases leftName.result_unique rightName with
            ⟨nameEq, afterNameEq⟩
          subst nameEq
          subst afterNameEq
          rcases leftColon.result_unique rightColon with
            ⟨colonSpanEq, afterColonEq⟩
          subst colonSpanEq
          subst afterColonEq
          rcases typeExprExactOutcomeSpec.successResultUnique leftType
              rightType with ⟨typeEq, afterTypeEq⟩
          subst typeEq
          subst afterTypeEq
          rcases (optionalContractFieldInitializerExactOutcomeSpec
              expressionOutcomes).successResultUnique leftInitializer
              rightInitializer with ⟨initializerEq, afterInitializerEq⟩
          subst initializerEq
          subst afterInitializerEq
          have semicolonSpanEq := leftSemicolon.span_unique rightSemicolon
          subst semicolonSpanEq
          rfl

/-- Exact initializer outcomes fix the complete field AST and remainder. -/
theorem ContractFieldOrdinaryParses.result_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input : Remainder} {left right : Syntax.ContractField}
    {afterLeft afterRight : Remainder}
    (leftParsed : ContractFieldOrdinaryParses expressionOrdinary input left
      afterLeft)
    (rightParsed : ContractFieldOrdinaryParses expressionOrdinary input right
      afterRight) : left = right ∧ afterLeft = afterRight :=
  ⟨leftParsed.value_unique expressionOutcomes rightParsed,
    leftParsed.output_unique expressionOutcomes.toDeterministicOutcomeSpec
      rightParsed⟩

/-- The five-stage field rejection sequence has one endpoint. -/
theorem ContractFieldRejects.output_unique
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects)
    {input left right : Remainder}
    (leftRejects : ContractFieldRejects expressionOrdinary expressionRejects
      input left)
    (rightRejects : ContractFieldRejects expressionOrdinary expressionRejects
      input right) : left = right := by
  cases leftRejects <;> cases rightRejects <;>
    grind (ematch := 10) [field_absent_conflicts_exact,
      ExactTokenParses.output_unique,
      identifierExactOutcomeSpec.successOutputUnique,
      identifierExactOutcomeSpec.successRejectDisjoint,
      identifierExactOutcomeSpec.rejectOutputUnique,
      typeExprExactOutcomeSpec.successOutputUnique,
      typeExprExactOutcomeSpec.successRejectDisjoint,
      typeExprExactOutcomeSpec.rejectOutputUnique,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).successOutputUnique,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).successRejectDisjoint,
      (optionalContractFieldInitializerExactOutcomeSpec
        expressionOutcomes).rejectOutputUnique]

/-- Exact initializer expressions lift to exact complete field outcomes. -/
theorem contractFieldExactOutcomeSpec
    {expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {expressionRejects : Remainder → Remainder → Prop}
    (expressionOutcomes : ExactDeterministicOutcomeSpec expressionOrdinary
      expressionRejects) :
    ExactDeterministicOutcomeSpec
      (ContractFieldOrdinaryParses expressionOrdinary)
      (ContractFieldRejects expressionOrdinary expressionRejects) where
  toDeterministicOutcomeSpec := contractFieldDeterministicOutcomeSpec
    expressionOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ContractFieldOrdinaryParses.value_unique
    expressionOutcomes
  rejectOutputUnique := ContractFieldRejects.output_unique expressionOutcomes

end Solcore.Syntax.DeclarativeGrammar
