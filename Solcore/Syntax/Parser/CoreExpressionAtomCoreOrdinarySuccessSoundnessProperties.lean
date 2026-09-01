import Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeGrammar
import Solcore.Syntax.Parser.CoreArrayLiteralOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreExpressionAtomDispatcherLookaheadProperties
import Solcore.Syntax.Parser.CoreExpressionDotConstructorOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreIdentifierExpressionOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaExpressionOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.CoreLiteralOutcomeSoundnessProperties
import Solcore.Syntax.Parser.CoreParenthesizedOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.CoreProxyExpressionOrdinaryOutcomeSoundnessProperties

/-! Unconditional ordinary-success reflection for `expressionAtomCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable Core-atom success follows the exact selected ordinary
branch, retaining every earlier failed guard. -/
theorem expressionAtomCore_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterShape : Parser.PreservesTokenWindow lambdaParameter)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : expressionAtomCore nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionAtomCoreOrdinaryParses nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary input.declarativeRemainder
        expression output.declarativeRemainder := by
  unfold expressionAtomCore at result
  split at result
  next literalPresent =>
    exact .literal (literalExpression_success_sound result)
  next literalAbsent =>
    have literalAbsentEq : isCoreLiteral input = false :=
      Bool.eq_false_iff.mpr literalAbsent
    have noLiteral :=
      not_coreLiteralStartsAt_of_isCoreLiteral_eq_false literalAbsentEq
    split at result
    next namePresent =>
      exact .identifier noLiteral (identifierExpression_success_sound result)
    next nameAbsent =>
      have nameAbsentEq :
          (isBooleanValue input || isIdentifier input) = false :=
        Bool.eq_false_iff.mpr nameAbsent
      have noName :=
        not_expressionNameStartsAt_of_expressionNameGuard_eq_false
          nameAbsentEq
      split at result
      next dotPresent =>
        exact .dotConstructor noLiteral noName
          (dotConstructor_success_ordinary_sound nested nestedOrdinary
            nestedSuccessSound nestedShape result)
      next dotAbsent =>
        have dotAbsentEq : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr dotAbsent
        have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot dotAbsentEq
        split at result
        next atPresent =>
          exact .proxy noLiteral noName noDot
            (proxyExpression_success_ordinary_sound typeOrdinary
              typeSuccessSound result)
        next atAbsent =>
          have atAbsentEq : isSymbol input .at = false :=
            Bool.eq_false_iff.mpr atAbsent
          have noAt := symbolAbsentAt_of_isSymbol_eq_false .at atAbsentEq
          split at result
          next leftParenPresent =>
            exact .parenthesized noLiteral noName noDot noAt
              (parenthesized_success_ordinary_sound nested nestedOrdinary
                nestedSuccessSound result)
          next leftParenAbsent =>
            have leftParenAbsentEq : isSymbol input .leftParen = false :=
              Bool.eq_false_iff.mpr leftParenAbsent
            have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen leftParenAbsentEq
            split at result
            next leftBracketPresent =>
              exact .array noLiteral noName noDot noAt noLeftParen
                (arrayLiteral_success_ordinary_sound nested nestedOrdinary
                  nestedSuccessSound nestedShape result)
            next leftBracketAbsent =>
              have leftBracketAbsentEq :
                  isSymbol input .leftBracket = false :=
                Bool.eq_false_iff.mpr leftBracketAbsent
              have noLeftBracket := symbolAbsentAt_of_isSymbol_eq_false
                .leftBracket leftBracketAbsentEq
              split at result
              next lambdaPresent =>
                exact .lambda noLiteral noName noDot noAt noLeftParen
                  noLeftBracket
                  (lambdaExpression_success_ordinary_sound block
                    parameterOrdinary typeOrdinary blockOrdinary
                    parameterSuccessSound parameterShape typeSuccessSound
                    blockSuccessSound result)
              next lambdaAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
