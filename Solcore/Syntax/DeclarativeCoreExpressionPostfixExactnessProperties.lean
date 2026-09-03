import Solcore.Syntax.DeclarativeCoreExpressionPostfixRejectionExactnessProperties
import Solcore.Syntax.DeclarativeCoreExpressionPostfixSuccessExactnessProperties

/-! Exact ordinary outcomes for Core atom-plus-postfix expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- At any fixed base AST, a maximal postfix tail has exact success values,
final remainders, and rejection endpoints. -/
theorem postfixTailExactOutcomeSpec
    {nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (base : Syntax.Expr) :
    ExactDeterministicOutcomeSpec
      (fun input expression output =>
        PostfixTailOrdinaryParses nestedOrdinary input base expression output)
      (fun input rejected =>
        PostfixTailRejects nestedOrdinary nestedRejects input base rejected) where
  successOutputUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.output_unique nestedOutcomes.toDeterministicOutcomeSpec
      rightParsed
  successRejectDisjoint := by
    intro input rejected rejection
    rintro ⟨expression, output, parsed⟩
    exact rejection.disjointOrdinary nestedOutcomes.toDeterministicOutcomeSpec
      ⟨base, expression, output, parsed⟩
  successValueUnique := by
    intro input left right afterLeft afterRight leftParsed rightParsed
    exact leftParsed.value_unique nestedOutcomes rightParsed
  rejectOutputUnique := by
    intro input left right leftRejected rightRejected
    exact leftRejected.output_unique nestedOutcomes rightRejected

/-- Exact atom and nested-expression outcomes lift through every maximal
index, call, and field suffix to a complete exact postfix outcome. -/
theorem expressionPostfixExactOutcomeSpec
    {atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {atomRejects nestedRejects : Remainder → Remainder → Prop}
    (atomOutcomes : ExactDeterministicOutcomeSpec atomOrdinary atomRejects)
    (nestedOutcomes : ExactDeterministicOutcomeSpec nestedOrdinary nestedRejects) :
    ExactDeterministicOutcomeSpec
      (ExpressionPostfixOrdinaryParses atomOrdinary nestedOrdinary)
      (ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects) where
  toDeterministicOutcomeSpec := expressionPostfixDeterministicOutcomeSpec
    atomOutcomes.toDeterministicOutcomeSpec
    nestedOutcomes.toDeterministicOutcomeSpec
  successValueUnique := ExpressionPostfixOrdinaryParses.value_unique
    atomOutcomes nestedOutcomes
  rejectOutputUnique := ExpressionPostfixRejects.output_unique
    atomOutcomes nestedOutcomes

end Solcore.Syntax.DeclarativeGrammar
