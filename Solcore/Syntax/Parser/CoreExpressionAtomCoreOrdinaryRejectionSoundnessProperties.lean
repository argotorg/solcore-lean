import Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinarySuccessSoundnessProperties
import Solcore.Syntax.Parser.CoreLambdaExpressionOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreParenthesizedOrdinaryRejectionSoundnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties

/-! Exact ordinary-rejection reflection for `expressionAtomCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem expressionNameStartsAt_of_guard_eq_true {input : State}
    (present : (isBooleanValue input || isIdentifier input) = true) :
    DeclarativeGrammar.ExpressionNameStartsAt
      input.declarativeRemainder := by
  rcases Bool.or_eq_true_iff.mp present with booleanPresent |
      identifierPresent
  · rcases Bool.or_eq_true_iff.mp (by
        simpa only [isBooleanValue] using booleanPresent) with truePresent |
        falsePresent
    · rcases keyword_eq_ok_of_isKeyword_eq_true .trueKw .expression
          truePresent with ⟨token, parsed⟩
      exact Or.inl ⟨token.span,
        (keyword_success_exactTokenParses .trueKw .expression parsed).1⟩
    · rcases keyword_eq_ok_of_isKeyword_eq_true .falseKw .expression
          falsePresent with ⟨token, parsed⟩
      exact Or.inr (Or.inl ⟨token.span,
        (keyword_success_exactTokenParses .falseKw .expression parsed).1⟩)
  · rcases identifierPresentAt_of_isIdentifier_eq_true identifierPresent
        with ⟨span, spelling, token⟩
    exact Or.inr (Or.inr ⟨span, spelling, token⟩)

private theorem identifierExpression_ne_reject_of_name_guard_eq_true
    {input rejected : State} {failure : Failure}
    (present : (isBooleanValue input || isIdentifier input) = true)
    (result : identifierExpression input = .reject failure rejected) :
    False := by
  have starts := expressionNameStartsAt_of_guard_eq_true present
  have rejection := identifierExpression_reject_ordinary_sound result
  apply rejection.disjointOrdinary
  rcases starts with ⟨span, token⟩ | ⟨span, token⟩ |
      ⟨span, spelling, token⟩
  · exact ⟨_, _, .parsed (.boolean (.trueKeyword token))⟩
  · exact ⟨_, _, .parsed (.boolean (.falseKeyword token))⟩
  · let name : Identifier := { span, value := spelling }
    let output : DeclarativeGrammar.Remainder :=
      { input.declarativeRemainder with
        cursor := input.declarativeRemainder.cursor + 1 }
    have identifierParsed : DeclarativeGrammar.IdentifierParses
        input.declarativeRemainder name output := by
      exact ⟨token, rfl, rfl, rfl⟩
    have trueAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
        input.window.endIndex input.cursor (.keyword .trueKw) := by
      intro presentToken
      rcases presentToken with ⟨keywordSpan, keywordToken⟩
      change DeclarativeGrammar.TokenAt input.declarativeRemainder.tokens
        input.declarativeRemainder.endIndex input.declarativeRemainder.cursor
          { span := keywordSpan, value := .keyword .trueKw } at keywordToken
      have tokenEq : ({ span, value := .identifier spelling } : Token) =
          { span := keywordSpan, value := .keyword .trueKw } := by
        apply Option.some.inj
        rw [← token.2, ← keywordToken.2]
      have kindEq := congrArg (fun current : Token => current.value) tokenEq
      cases kindEq
    have falseAbsent : DeclarativeGrammar.TokenKindAbsentAt input.tokens
        input.window.endIndex input.cursor (.keyword .falseKw) := by
      intro presentToken
      rcases presentToken with ⟨keywordSpan, keywordToken⟩
      change DeclarativeGrammar.TokenAt input.declarativeRemainder.tokens
        input.declarativeRemainder.endIndex input.declarativeRemainder.cursor
          { span := keywordSpan, value := .keyword .falseKw } at keywordToken
      have tokenEq : ({ span, value := .identifier spelling } : Token) =
          { span := keywordSpan, value := .keyword .falseKw } := by
        apply Option.some.inj
        rw [← token.2, ← keywordToken.2]
      have kindEq := congrArg (fun current : Token => current.value) tokenEq
      cases kindEq
    exact ⟨_, output, .parsed
      (.identifier trueAbsent falseAbsent identifierParsed)⟩

/-- Every executable Core-atom rejection follows the exact selected branch;
positive literal and name guards are proved unable to reject. -/
theorem expressionAtomCore_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        lambdaParameter input = .reject failure rejected →
          parameterRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (parameterShape : Parser.PreservesTokenWindow lambdaParameter)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : expressionAtomCore nested block input =
      .reject failure rejected) :
    DeclarativeGrammar.ExpressionAtomCoreRejects nestedOrdinary nestedRejects
      parameterOrdinary parameterRejects typeOrdinary typeRejects blockRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  unfold expressionAtomCore at result
  split at result
  next literalPresent =>
    exact False.elim
      (literalExpression_ne_reject_of_isCoreLiteral_eq_true literalPresent
        result)
  next literalAbsent =>
    have literalAbsentEq : isCoreLiteral input = false :=
      Bool.eq_false_iff.mpr literalAbsent
    have noLiteral :=
      not_coreLiteralStartsAt_of_isCoreLiteral_eq_false literalAbsentEq
    split at result
    next namePresent =>
      exact False.elim
        (identifierExpression_ne_reject_of_name_guard_eq_true namePresent
          result)
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
          (dotConstructor_reject_ordinary_sound nested nestedOrdinary
            nestedRejects nestedSuccessSound nestedRejectSound dotPresent
              result)
      next dotAbsent =>
        have dotAbsentEq : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr dotAbsent
        have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot dotAbsentEq
        split at result
        next atPresent =>
          exact .proxy noLiteral noName noDot
            (proxyExpression_reject_ordinary_sound typeRejects typeRejectSound
              atPresent result)
        next atAbsent =>
          have atAbsentEq : isSymbol input .at = false :=
            Bool.eq_false_iff.mpr atAbsent
          have noAt := symbolAbsentAt_of_isSymbol_eq_false .at atAbsentEq
          split at result
          next leftParenPresent =>
            exact .parenthesized noLiteral noName noDot noAt
              (parenthesized_reject_ordinary_sound nested nestedOrdinary
                nestedRejects nestedSuccessSound nestedRejectSound
                  leftParenPresent result)
          next leftParenAbsent =>
            have leftParenAbsentEq : isSymbol input .leftParen = false :=
              Bool.eq_false_iff.mpr leftParenAbsent
            have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen leftParenAbsentEq
            split at result
            next leftBracketPresent =>
              exact .array noLiteral noName noDot noAt noLeftParen
                (arrayLiteral_reject_ordinary_sound nested nestedOrdinary
                  nestedRejects nestedSuccessSound nestedRejectSound
                    leftBracketPresent result)
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
                  (lambdaExpression_reject_ordinary_sound block
                    parameterOrdinary parameterRejects typeOrdinary
                    typeRejects blockRejects parameterSuccessSound
                    parameterRejectSound parameterShape typeSuccessSound
                    typeRejectSound blockRejectSound lambdaPresent result)
              next lambdaAbsent =>
                have lambdaAbsentEq : isKeyword input .lamKw = false :=
                  Bool.eq_false_iff.mpr lambdaAbsent
                have noLambda := keywordAbsentAt_of_isKeyword_eq_false
                  .lamKw lambdaAbsentEq
                unfold rejectAt at result
                cases result
                exact .final (.final noLiteral noName noDot noAt noLeftParen
                  noLeftBracket noLambda)

end Solcore.Syntax.Parser.ExpressionAtomInternals
