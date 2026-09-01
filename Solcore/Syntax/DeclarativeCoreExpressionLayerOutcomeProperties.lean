import Solcore.Syntax.DeclarativeCoreExpressionConditionalOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionNonAssociativeOutcomeProperties
import Solcore.Syntax.DeclarativeCoreExpressionUnaryLeftOutcomeProperties

/-!
Deterministic outcomes and clean embedding for the complete Core expression
operator stack.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Compose nested and postfix outcome contracts through every expression
operator layer. -/
theorem expressionLayerDeterministicOutcomeSpec
    {nestedOrdinary postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    {nestedRejects postfixRejects : Remainder → Remainder → Prop}
    (nestedOutcomes : DeterministicOutcomeSpec nestedOrdinary nestedRejects)
    (postfixOutcomes : DeterministicOutcomeSpec postfixOrdinary
      postfixRejects) :
    DeterministicOutcomeSpec
      (ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary)
      (ExpressionLayerRejects nestedOrdinary nestedRejects postfixOrdinary
        postfixRejects) := by
  let unaryOutcomes := expressionUnaryDeterministicOutcomeSpec
    postfixOutcomes
  let multiplyOutcomes := leftAssociativeDeterministicOutcomeSpec
    unaryOutcomes 8
  let addOutcomes := leftAssociativeDeterministicOutcomeSpec
    multiplyOutcomes 7
  let bitAndOutcomes := leftAssociativeDeterministicOutcomeSpec
    addOutcomes 6
  let bitXorOutcomes := leftAssociativeDeterministicOutcomeSpec
    bitAndOutcomes 5
  let bitOrOutcomes := leftAssociativeDeterministicOutcomeSpec
    bitXorOutcomes 4
  let relationalOutcomes := nonAssociativeDeterministicOutcomeSpec
    bitOrOutcomes 3
  let equalityOutcomes := nonAssociativeDeterministicOutcomeSpec
    relationalOutcomes 2
  let logicalAndOutcomes := leftAssociativeDeterministicOutcomeSpec
    equalityOutcomes 1
  let logicalOrOutcomes := leftAssociativeDeterministicOutcomeSpec
    logicalAndOutcomes 0
  simpa [ExpressionLayerOrdinaryParses, ExpressionLayerParses,
    ExpressionLayerRejects, unaryOutcomes, multiplyOutcomes, addOutcomes,
    bitAndOutcomes, bitXorOutcomes, bitOrOutcomes, relationalOutcomes,
    equalityOutcomes, logicalAndOutcomes, logicalOrOutcomes] using
      conditionalDeterministicOutcomeSpec nestedOutcomes logicalOrOutcomes

/-- Unary success embeds when its postfix success embeds. -/
theorem ExpressionUnaryParses.toOrdinary
    {postfixClean postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (postfixEmbedding : ∀ {input expression output},
      postfixClean input expression output →
        postfixOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionUnaryParses postfixClean input expression output) :
    ExpressionUnaryParses postfixOrdinary input expression output := by
  rcases parsed with
    ⟨operators, afterOperators, base, operatorsParsed, baseParsed,
      expressionEq⟩
  exact ⟨operators, afterOperators, base, operatorsParsed,
    postfixEmbedding baseParsed, expressionEq⟩

/-- A left-associated tail embeds when each operand embeds. -/
theorem LeftAssociativeTailParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {left expression : Syntax.Expr}
    (parsed : LeftAssociativeTailParses operandClean precedence input left
      expression output) :
    LeftAssociativeTailParses operandOrdinary precedence input left expression
      output := by
  induction parsed with
  | done absent => exact .done absent
  | next operatorParsed rightParsed tail inductionHypothesis =>
      exact .next operatorParsed (operandEmbedding rightParsed)
        inductionHypothesis

/-- A complete left-associated layer embeds with its operand relation. -/
theorem LeftAssociativeParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {expression : Syntax.Expr}
    (parsed : LeftAssociativeParses operandClean precedence input expression
      output) :
    LeftAssociativeParses operandOrdinary precedence input expression output :=
    by
  rcases parsed with ⟨left, afterLeft, leftParsed, tailParsed⟩
  exact ⟨left, afterLeft, operandEmbedding leftParsed,
    tailParsed.toOrdinary operandEmbedding⟩

/-- A non-associative layer embeds with its operand relation. -/
theorem NonAssociativeParses.toOrdinary
    {operandClean operandOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (operandEmbedding : ∀ {input expression output},
      operandClean input expression output →
        operandOrdinary input expression output)
    {precedence : Nat} {input output : Remainder}
    {expression : Syntax.Expr}
    (parsed : NonAssociativeParses operandClean precedence input expression
      output) :
    NonAssociativeParses operandOrdinary precedence input expression output :=
    by
  cases parsed with
  | plain leftParsed absent => exact .plain (operandEmbedding leftParsed) absent
  | binary leftParsed operatorParsed rightParsed =>
      exact .binary (operandEmbedding leftParsed) operatorParsed
        (operandEmbedding rightParsed)

/-- A conditional tail embeds with both recursive operand relations. -/
theorem ConditionalTailParses.toOrdinary
    {nestedClean nestedOrdinary alternativeClean alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (alternativeEmbedding : ∀ {input expression output},
      alternativeClean input expression output →
        alternativeOrdinary input expression output)
    {input output : Remainder} {condition expression : Syntax.Expr}
    (parsed : ConditionalTailParses nestedClean alternativeClean input
      condition expression output) :
    ConditionalTailParses nestedOrdinary alternativeOrdinary input condition
      expression output := by
  induction parsed with
  | done absent => exact .done absent
  | next questionSpan colonSpan questionParsed thenParsed colonParsed
        alternativeParsed tail inductionHypothesis =>
      exact .next questionSpan colonSpan questionParsed
        (nestedEmbedding thenParsed) colonParsed
        (alternativeEmbedding alternativeParsed) inductionHypothesis

/-- A complete conditional layer embeds with both operand relations. -/
theorem ConditionalParses.toOrdinary
    {nestedClean nestedOrdinary alternativeClean alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (alternativeEmbedding : ∀ {input expression output},
      alternativeClean input expression output →
        alternativeOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ConditionalParses nestedClean alternativeClean input expression
      output) :
    ConditionalParses nestedOrdinary alternativeOrdinary input expression
      output := by
  rcases parsed with ⟨condition, afterCondition, conditionParsed, tailParsed⟩
  exact ⟨condition, afterCondition, alternativeEmbedding conditionParsed,
    tailParsed.toOrdinary nestedEmbedding alternativeEmbedding⟩

/-- The complete clean operator stack embeds into its ordinary counterpart. -/
theorem ExpressionLayerParses.toOrdinary
    {nestedClean nestedOrdinary postfixClean postfixOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop}
    (nestedEmbedding : ∀ {input expression output},
      nestedClean input expression output →
        nestedOrdinary input expression output)
    (postfixEmbedding : ∀ {input expression output},
      postfixClean input expression output →
        postfixOrdinary input expression output)
    {input output : Remainder} {expression : Syntax.Expr}
    (parsed : ExpressionLayerParses nestedClean postfixClean input expression
      output) :
    ExpressionLayerOrdinaryParses nestedOrdinary postfixOrdinary input
      expression output := by
  let unaryClean := ExpressionUnaryParses postfixClean
  let unaryOrdinary := ExpressionUnaryParses postfixOrdinary
  let multiplyClean := LeftAssociativeParses unaryClean 8
  let multiplyOrdinary := LeftAssociativeParses unaryOrdinary 8
  let addClean := LeftAssociativeParses multiplyClean 7
  let addOrdinary := LeftAssociativeParses multiplyOrdinary 7
  let bitAndClean := LeftAssociativeParses addClean 6
  let bitAndOrdinary := LeftAssociativeParses addOrdinary 6
  let bitXorClean := LeftAssociativeParses bitAndClean 5
  let bitXorOrdinary := LeftAssociativeParses bitAndOrdinary 5
  let bitOrClean := LeftAssociativeParses bitXorClean 4
  let bitOrOrdinary := LeftAssociativeParses bitXorOrdinary 4
  let relationalClean := NonAssociativeParses bitOrClean 3
  let relationalOrdinary := NonAssociativeParses bitOrOrdinary 3
  let equalityClean := NonAssociativeParses relationalClean 2
  let equalityOrdinary := NonAssociativeParses relationalOrdinary 2
  let logicalAndClean := LeftAssociativeParses equalityClean 1
  let logicalAndOrdinary := LeftAssociativeParses equalityOrdinary 1
  let logicalOrClean := LeftAssociativeParses logicalAndClean 0
  let logicalOrOrdinary := LeftAssociativeParses logicalAndOrdinary 0
  let unaryEmbedding : ∀ {input expression output},
      unaryClean input expression output →
        unaryOrdinary input expression output :=
    fun parsed => parsed.toOrdinary postfixEmbedding
  let multiplyEmbedding : ∀ {input expression output},
      multiplyClean input expression output →
        multiplyOrdinary input expression output :=
    fun parsed => parsed.toOrdinary unaryEmbedding
  let addEmbedding : ∀ {input expression output},
      addClean input expression output →
        addOrdinary input expression output :=
    fun parsed => parsed.toOrdinary multiplyEmbedding
  let bitAndEmbedding : ∀ {input expression output},
      bitAndClean input expression output →
        bitAndOrdinary input expression output :=
    fun parsed => parsed.toOrdinary addEmbedding
  let bitXorEmbedding : ∀ {input expression output},
      bitXorClean input expression output →
        bitXorOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitAndEmbedding
  let bitOrEmbedding : ∀ {input expression output},
      bitOrClean input expression output →
        bitOrOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitXorEmbedding
  let relationalEmbedding : ∀ {input expression output},
      relationalClean input expression output →
        relationalOrdinary input expression output :=
    fun parsed => parsed.toOrdinary bitOrEmbedding
  let equalityEmbedding : ∀ {input expression output},
      equalityClean input expression output →
        equalityOrdinary input expression output :=
    fun parsed => parsed.toOrdinary relationalEmbedding
  let logicalAndEmbedding : ∀ {input expression output},
      logicalAndClean input expression output →
        logicalAndOrdinary input expression output :=
    fun parsed => parsed.toOrdinary equalityEmbedding
  let logicalOrEmbedding : ∀ {input expression output},
      logicalOrClean input expression output →
        logicalOrOrdinary input expression output :=
    fun parsed => parsed.toOrdinary logicalAndEmbedding
  change ConditionalParses nestedClean logicalOrClean input expression output
    at parsed
  change ConditionalParses nestedOrdinary logicalOrOrdinary input expression
    output
  exact ConditionalParses.toOrdinary nestedEmbedding logicalOrEmbedding parsed

end Solcore.Syntax.DeclarativeGrammar
