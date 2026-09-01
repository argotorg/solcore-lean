import Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeProperties
import Solcore.Syntax.Parser.CoreExpressionConditionalOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionLeftAssociativeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionNonAssociativeOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionUnaryOrdinaryOutcomeSoundnessProperties

/-!
Executable ordinary-success and exact-rejection soundness for the complete
Core operator stack over supplied recursive and postfix outcomes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Compose executable outcome bridges through unary, every binary precedence,
and the conditional layer. -/
theorem expressionLayer_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary postfixOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop)
    (nestedRejects postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (postfixSuccessSound :
      ∀ {input output : State} {expression : Expr},
        expressionPostfix nested block input = .ok expression output →
          postfixOrdinary input.declarativeRemainder expression
            output.declarativeRemainder)
    (postfixRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        expressionPostfix nested block input = .reject failure rejected →
          postfixRejects input.declarativeRemainder
            rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      expressionLayer nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionLayerOrdinaryParses nestedOrdinary
          postfixOrdinary input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionLayer nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionLayerRejects nestedOrdinary nestedRejects
          postfixOrdinary postfixRejects input.declarativeRemainder
            rejected.declarativeRemainder) := by
  let unary := ExpressionInternals.expressionUnary nested block
  let multiply := ExpressionInternals.leftAssociative unary 8
  let add := ExpressionInternals.leftAssociative multiply 7
  let bitAnd := ExpressionInternals.leftAssociative add 6
  let bitXor := ExpressionInternals.leftAssociative bitAnd 5
  let bitOr := ExpressionInternals.leftAssociative bitXor 4
  let relational := ExpressionInternals.nonAssociative bitOr 3
  let equality := ExpressionInternals.nonAssociative relational 2
  let logicalAnd := ExpressionInternals.leftAssociative equality 1
  let logicalOr := ExpressionInternals.leftAssociative logicalAnd 0
  let unaryOrdinary :=
    DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary
  let unaryRejects :=
    DeclarativeGrammar.ExpressionUnaryRejects postfixRejects
  let multiplyOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses unaryOrdinary 8
  let multiplyRejects :=
    DeclarativeGrammar.LeftAssociativeRejects unaryOrdinary unaryRejects 8
  let addOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses multiplyOrdinary 7
  let addRejects :=
    DeclarativeGrammar.LeftAssociativeRejects multiplyOrdinary
      multiplyRejects 7
  let bitAndOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses addOrdinary 6
  let bitAndRejects :=
    DeclarativeGrammar.LeftAssociativeRejects addOrdinary addRejects 6
  let bitXorOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses bitAndOrdinary 5
  let bitXorRejects :=
    DeclarativeGrammar.LeftAssociativeRejects bitAndOrdinary bitAndRejects 5
  let bitOrOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses bitXorOrdinary 4
  let bitOrRejects :=
    DeclarativeGrammar.LeftAssociativeRejects bitXorOrdinary bitXorRejects 4
  let relationalOrdinary :=
    DeclarativeGrammar.NonAssociativeOrdinaryParses bitOrOrdinary 3
  let relationalRejects :=
    DeclarativeGrammar.NonAssociativeRejects bitOrOrdinary bitOrRejects 3
  let equalityOrdinary :=
    DeclarativeGrammar.NonAssociativeOrdinaryParses relationalOrdinary 2
  let equalityRejects :=
    DeclarativeGrammar.NonAssociativeRejects relationalOrdinary
      relationalRejects 2
  let logicalAndOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses equalityOrdinary 1
  let logicalAndRejects :=
    DeclarativeGrammar.LeftAssociativeRejects equalityOrdinary
      equalityRejects 1
  let logicalOrOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses logicalAndOrdinary 0
  let logicalOrRejects :=
    DeclarativeGrammar.LeftAssociativeRejects logicalAndOrdinary
      logicalAndRejects 0
  have unarySound :=
    ExpressionInternals.expressionUnary_ordinaryOutcome_sound nested block
      postfixOrdinary postfixRejects postfixSuccessSound postfixRejectSound
  have multiplySound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound unary
      unaryOrdinary unaryRejects unarySound.1 unarySound.2 8
  have addSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound multiply
      multiplyOrdinary multiplyRejects multiplySound.1 multiplySound.2 7
  have bitAndSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound add addOrdinary
      addRejects addSound.1 addSound.2 6
  have bitXorSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound bitAnd
      bitAndOrdinary bitAndRejects bitAndSound.1 bitAndSound.2 5
  have bitOrSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound bitXor
      bitXorOrdinary bitXorRejects bitXorSound.1 bitXorSound.2 4
  have relationalSound :=
    ExpressionInternals.nonAssociative_ordinaryOutcome_sound bitOr
      bitOrOrdinary bitOrRejects bitOrSound.1 bitOrSound.2 3
  have equalitySound :=
    ExpressionInternals.nonAssociative_ordinaryOutcome_sound relational
      relationalOrdinary relationalRejects relationalSound.1
        relationalSound.2 2
  have logicalAndSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound equality
      equalityOrdinary equalityRejects equalitySound.1 equalitySound.2 1
  have logicalOrSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound logicalAnd
      logicalAndOrdinary logicalAndRejects logicalAndSound.1
        logicalAndSound.2 0
  have completeSound :=
    ExpressionInternals.conditional_ordinaryOutcome_sound nested logicalOr
      nestedOrdinary logicalOrOrdinary nestedRejects logicalOrRejects
        nestedSuccessSound nestedRejectSound logicalOrSound.1 logicalOrSound.2
  simpa only [expressionLayer,
    DeclarativeGrammar.ExpressionLayerOrdinaryParses,
    DeclarativeGrammar.ExpressionLayerParses,
    DeclarativeGrammar.ExpressionLayerRejects, unary, multiply, add, bitAnd,
    bitXor, bitOr, relational, equality, logicalAnd, logicalOr, unaryOrdinary,
    unaryRejects, multiplyOrdinary, multiplyRejects, addOrdinary, addRejects,
    bitAndOrdinary, bitAndRejects, bitXorOrdinary, bitXorRejects,
    bitOrOrdinary, bitOrRejects, relationalOrdinary, relationalRejects,
    equalityOrdinary, equalityRejects, logicalAndOrdinary, logicalAndRejects,
    logicalOrOrdinary, logicalOrRejects] using completeSound

/-- Lift deterministic supplied outcomes through the executable operator-stack
relations. -/
theorem expressionLayer_ordinaryOutcomeSpec
    {nestedOrdinary postfixOrdinary :
      DeclarativeGrammar.Remainder → Expr →
        DeclarativeGrammar.Remainder → Prop}
    {nestedRejects postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects)
    (postfixOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      postfixOrdinary postfixRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionLayerOrdinaryParses nestedOrdinary
        postfixOrdinary)
      (DeclarativeGrammar.ExpressionLayerRejects nestedOrdinary nestedRejects
        postfixOrdinary postfixRejects) :=
  DeclarativeGrammar.expressionLayerDeterministicOutcomeSpec nestedOutcomes
    postfixOutcomes

end Solcore.Syntax.Parser
