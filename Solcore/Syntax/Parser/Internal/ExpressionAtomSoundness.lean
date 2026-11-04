import Solcore.Syntax.Internal.ExpressionAtomOutcomes
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Parser.Internal.ExpressionAtomProofs
import Solcore.Syntax.Parser.Internal.ParameterBasics
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Parser.Internal.CollectionSoundness
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.ExpressionProofs
import Solcore.Syntax.Internal.ExpressionOutcomes
import Solcore.Syntax.Parser.Internal.OperatorSoundness
import Solcore.Syntax.Parser.Internal.LambdaParameterSoundness

/-!
Soundness of the parsers of expression atoms and lambda expressions: each success and each
rejection has its declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaReturnTypeOrdinaryOutcomeSoundnessProperties
/-! Executable ordinary outcomes for an optional Core lambda return type. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every optional-return success takes exactly the absent-arrow branch or a
present arrow followed by the supplied ordinary type success. -/
theorem optionalLambdaReturnType_success_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    {input output : State} {returnType : Option TypeExpr}
    (result : optionalLambdaReturnType input = .ok returnType output) :
    DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
      input.declarativeRemainder returnType output.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    cases arrowResult : symbol .arrow .typeExpr input with
    | invariant error => simp [arrowResult] at result
    | reject failure rejected => simp [arrowResult] at result
    | ok arrow afterArrow =>
        simp only [arrowResult] at result
        cases typeResult : typeExpr afterArrow with
        | invariant error => simp [typeResult] at result
        | reject failure rejected => simp [typeResult] at result
        | ok type afterType =>
            simp only [typeResult, pure] at result
            cases result
            exact .present arrow.span
              (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
              (typeSuccessSound typeResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .arrow absent)

/-- Every optional-return rejection occurs only after a present arrow and is
the exact supplied type rejection. -/
theorem optionalLambdaReturnType_reject_ordinary_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : optionalLambdaReturnType input = .reject failure rejected) :
    DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
      typeRejects input.declarativeRemainder
        rejected.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · rcases symbol_eq_ok_of_isSymbol_eq_true .arrow .typeExpr present with
      ⟨arrow, arrowResult⟩
    simp only [present, if_true, arrowResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | ok type afterType => simp [typeResult, pure] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact .typeRejected arrow.span
          (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
          (typeRejectSound typeResult)
  · have absent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package both executable optional-return outcomes. -/
theorem optionalLambdaReturnType_ordinaryOutcome_sound
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {returnType : Option TypeExpr},
      optionalLambdaReturnType input = .ok returnType output →
        DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses
          typeOrdinary input.declarativeRemainder returnType
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      optionalLambdaReturnType input = .reject failure rejected →
        DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
          typeRejects input.declarativeRemainder
            rejected.declarativeRemainder) :=
  ⟨optionalLambdaReturnType_success_ordinary_sound typeOrdinary
      typeSuccessSound,
    optionalLambdaReturnType_reject_ordinary_sound typeOrdinary typeRejects
      typeRejectSound⟩

/-- Lift a deterministic supplied type outcome to optional returns. -/
theorem optionalLambdaReturnType_ordinaryOutcomeSpec
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.OptionalLambdaReturnTypeOrdinaryParses
        typeOrdinary)
      (DeclarativeGrammar.OptionalLambdaReturnTypeRejects typeOrdinary
        typeRejects) :=
  DeclarativeGrammar.optionalLambdaReturnTypeDeterministicOutcomeSpec
    typeOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaExpressionOrdinarySuccessSoundnessProperties
/-! Unconditional ordinary-success reflection for Core lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Every executable lambda success retains its exact marker, source-order
parameters, optional return, body, outer span, AST, and final remainder. -/
theorem lambdaExpression_success_ordinary_sound
    (block : Parser Block)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
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
    (result : lambdaExpression block input = .ok expression output) :
    DeclarativeGrammar.LambdaExpressionOrdinaryParses parameterOrdinary
      typeOrdinary blockOrdinary input.declarativeRemainder expression
        output.declarativeRemainder := by
  unfold lambdaExpression at result
  cases markerResult : keyword .lamKw .expression input with
  | invariant error => simp [bind, markerResult] at result
  | reject failure rejected => simp [bind, markerResult] at result
  | ok marker afterMarker =>
      simp only [bind, markerResult] at result
      cases parametersResult : delimited .leftParen .rightParen true
          lambdaParameter .parameter .expression afterMarker with
      | invariant error => simp [parametersResult] at result
      | reject failure rejected => simp [parametersResult] at result
      | ok parameters afterParameters =>
          simp only [parametersResult] at result
          cases returnResult : optionalLambdaReturnType afterParameters with
          | invariant error => simp [returnResult] at result
          | reject failure rejected => simp [returnResult] at result
          | ok returnType afterReturn =>
              simp only [returnResult] at result
              cases bodyResult : block afterReturn with
              | invariant error => simp [bodyResult] at result
              | reject failure rejected => simp [bodyResult] at result
              | ok body afterBody =>
                  simp only [bodyResult, pure] at result
                  cases result
                  exact .parsed marker.span
                    (keyword_success_exactTokenParses .lamKw .expression
                      markerResult)
                    (delimited_allowEmpty_trailing_success_sound .leftParen
                      .rightParen lambdaParameter parameterOrdinary .parameter
                        .expression parameterSuccessSound parameterShape
                          parametersResult)
                    (optionalLambdaReturnType_success_ordinary_sound
                      typeOrdinary typeSuccessSound returnResult)
                    (blockSuccessSound bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaExpressionOrdinaryRejectionSoundnessProperties
/-! Exact guarded ordinary-rejection reflection for Core lambda expressions. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Under the atom dispatcher's positive lambda guard, every executable
rejection occurs exactly in the parameter list, optional return, or body. -/
theorem lambdaExpression_reject_ordinary_sound
    (block : Parser Block)
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
    (markerPresent : isKeyword input .lamKw = true)
    (result : lambdaExpression block input = .reject failure rejected) :
    DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
      parameterRejects typeOrdinary typeRejects blockRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  rcases keyword_eq_ok_of_isKeyword_eq_true .lamKw .expression markerPresent
    with ⟨marker, markerResult⟩
  unfold lambdaExpression at result
  simp only [bind, markerResult] at result
  cases parametersResult : delimited .leftParen .rightParen true
      lambdaParameter .parameter .expression
        { input with cursor := input.cursor + 1 } with
  | invariant error => simp [parametersResult] at result
  | reject parametersFailure parametersRejected =>
      simp only [parametersResult] at result
      cases result
      exact .parametersRejected marker.span
        (keyword_success_exactTokenParses .lamKw .expression markerResult)
        (delimited_reject_sound .leftParen .rightParen true lambdaParameter
          parameterOrdinary parameterRejects .parameter .expression
            parameterSuccessSound parameterRejectSound parametersResult)
  | ok parameters afterParameters =>
      simp only [parametersResult] at result
      have parametersParsed := delimited_allowEmpty_trailing_success_sound
        .leftParen .rightParen lambdaParameter parameterOrdinary .parameter
          .expression parameterSuccessSound parameterShape parametersResult
      cases returnResult : optionalLambdaReturnType afterParameters with
      | invariant error => simp [returnResult] at result
      | reject returnFailure returnRejected =>
          simp only [returnResult] at result
          cases result
          exact .returnTypeRejected marker.span
            (keyword_success_exactTokenParses .lamKw .expression markerResult)
            parametersParsed
            (optionalLambdaReturnType_reject_ordinary_sound typeOrdinary
              typeRejects typeRejectSound returnResult)
      | ok returnType afterReturn =>
          simp only [returnResult] at result
          have returnParsed := optionalLambdaReturnType_success_ordinary_sound
            typeOrdinary typeSuccessSound returnResult
          cases bodyResult : block afterReturn with
          | invariant error => simp [bodyResult] at result
          | ok body afterBody => simp [bodyResult, pure] at result
          | reject bodyFailure bodyRejected =>
              simp only [bodyResult] at result
              cases result
              exact .bodyRejected marker.span
                (keyword_success_exactTokenParses .lamKw .expression
                  markerResult)
                parametersParsed returnParsed (blockRejectSound bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaExpressionOrdinaryOutcomeSoundnessProperties
/-! Composed executable ordinary outcomes for guarded Core lambdas. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional lambda success with rejection under the atom
dispatcher's positive lambda-keyword guard. -/
theorem lambdaExpression_guardedOrdinaryOutcome_sound
    (block : Parser Block)
    (parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop)
    (parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
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
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      lambdaExpression block input = .ok expression output →
        DeclarativeGrammar.LambdaExpressionOrdinaryParses
          parameterOrdinary typeOrdinary blockOrdinary
            input.declarativeRemainder expression
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      isKeyword input .lamKw = true →
        lambdaExpression block input = .reject failure rejected →
          DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
            parameterRejects typeOrdinary typeRejects blockRejects
              input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨lambdaExpression_success_ordinary_sound block parameterOrdinary
      typeOrdinary blockOrdinary parameterSuccessSound parameterShape
        typeSuccessSound blockSuccessSound,
    lambdaExpression_reject_ordinary_sound block parameterOrdinary
      parameterRejects typeOrdinary typeRejects blockRejects
        parameterSuccessSound parameterRejectSound parameterShape
          typeSuccessSound typeRejectSound blockRejectSound⟩

/-- Lift deterministic subordinate outcomes to the guarded lambda branch. -/
theorem lambdaExpression_ordinaryOutcomeSpec
    {parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop}
    {parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop}
    {blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parameterOrdinary parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec blockOrdinary
      blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.LambdaExpressionOrdinaryParses parameterOrdinary
        typeOrdinary blockOrdinary)
      (DeclarativeGrammar.LambdaExpressionRejects parameterOrdinary
        parameterRejects typeOrdinary typeRejects blockRejects) :=
  DeclarativeGrammar.lambdaExpressionDeterministicOutcomeSpec
    parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinarySuccessSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinaryRejectionSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomCoreOrdinaryOutcomeSoundnessProperties
/-! Packaged executable ordinary outcomes for `expressionAtomCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- Package unconditional Core-atom success and exact selected rejection over
supplied subordinate executable outcome bridges. -/
theorem expressionAtomCore_ordinaryOutcome_sound
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
    (blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
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
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → blockRejects
        input.declarativeRemainder rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      expressionAtomCore nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionAtomCoreOrdinaryParses nestedOrdinary
          parameterOrdinary typeOrdinary blockOrdinary
            input.declarativeRemainder expression
              output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionAtomCore nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionAtomCoreRejects nestedOrdinary
          nestedRejects parameterOrdinary parameterRejects typeOrdinary
            typeRejects blockRejects input.declarativeRemainder
              rejected.declarativeRemainder) :=
  ⟨expressionAtomCore_success_ordinary_sound nested block nestedOrdinary
      parameterOrdinary typeOrdinary blockOrdinary nestedSuccessSound
        nestedShape parameterSuccessSound parameterShape typeSuccessSound
          blockSuccessSound,
    expressionAtomCore_reject_ordinary_sound nested block nestedOrdinary
      nestedRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects nestedSuccessSound nestedRejectSound
          parameterSuccessSound parameterRejectSound parameterShape
            typeSuccessSound typeRejectSound blockRejectSound⟩

/-- Lift deterministic subordinate outcomes through the executable Core-atom
dispatcher relations. -/
theorem expressionAtomCore_ordinaryOutcomeSpec
    {nestedOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {nestedRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {parameterOrdinary : DeclarativeGrammar.Remainder → LambdaParameter →
      DeclarativeGrammar.Remainder → Prop}
    {parameterRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {typeOrdinary : DeclarativeGrammar.Remainder → TypeExpr →
      DeclarativeGrammar.Remainder → Prop}
    {typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    {blockOrdinary : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop}
    {blockRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      nestedOrdinary nestedRejects)
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      parameterOrdinary parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec typeOrdinary
      typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec blockOrdinary
      blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionAtomCoreOrdinaryParses nestedOrdinary
        parameterOrdinary typeOrdinary blockOrdinary)
      (DeclarativeGrammar.ExpressionAtomCoreRejects nestedOrdinary
        nestedRejects parameterOrdinary parameterRejects typeOrdinary
          typeRejects blockRejects) :=
  DeclarativeGrammar.expressionAtomCoreDeterministicOutcomeSpec
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionUnaryOrdinaryOutcomeSoundnessProperties
/-!
Executable ordinary-success and exact-rejection bridges for the Core prefix
unary expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionInternals

private theorem applyUnaryOperators_eq_declarative
    (operators : List (Located UnaryOp)) (base : Expr) :
    applyUnaryOperators operators base =
      DeclarativeGrammar.applyUnaryOperators operators base := by
  rfl

/-- Every executable unary success follows the maximal prefix grammar and the
supplied ordinary postfix grammar, independently of diagnostics. -/
theorem expressionUnary_success_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (postfixSuccessSound :
      ∀ {postfixInput postfixOutput : State} {base : Expr},
        expressionPostfix nested block postfixInput = .ok base postfixOutput →
          postfixOrdinary postfixInput.declarativeRemainder base
            postfixOutput.declarativeRemainder)
    {input output : State} {expression : Expr}
    (result : expressionUnary nested block input = .ok expression output) :
    DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary
      input.declarativeRemainder expression output.declarativeRemainder := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  unfold expressionUnary at result
  simp only [operatorsResult] at result
  cases postfixResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [postfixResult] at result
  | reject failure rejected => simp [postfixResult] at result
  | ok base afterPostfix =>
      simp only [postfixResult] at result
      cases result
      exact ⟨operators, afterOperators.declarativeRemainder, base,
        unaryOperators_success_sound operatorsResult,
        postfixSuccessSound postfixResult,
        applyUnaryOperators_eq_declarative operators base⟩

/-- Every executable unary rejection is exactly a postfix rejection after the
same maximal prefix scan. -/
theorem expressionUnary_reject_ordinary_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (postfixRejectSound :
      ∀ {postfixInput rejected : State} {failure : Failure},
        expressionPostfix nested block postfixInput =
            .reject failure rejected →
          postfixRejects postfixInput.declarativeRemainder
            rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : expressionUnary nested block input =
      .reject failure rejected) :
    DeclarativeGrammar.ExpressionUnaryRejects postfixRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases unaryOperators_production_exists_ok [] input with
    ⟨operators, afterOperators, operatorsResult⟩
  unfold expressionUnary at result
  simp only [operatorsResult] at result
  cases postfixResult : expressionPostfix nested block afterOperators with
  | invariant error => simp [postfixResult] at result
  | ok base afterPostfix => simp [postfixResult] at result
  | reject postfixFailure postfixRejected =>
      simp only [postfixResult] at result
      cases result
      exact .postfixRejected
        (unaryOperators_success_sound operatorsResult)
        (postfixRejectSound postfixResult)

/-- Package both executable ordinary outcomes for a supplied postfix bridge. -/
theorem expressionUnary_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (postfixSuccessSound :
      ∀ {postfixInput postfixOutput : State} {base : Expr},
        expressionPostfix nested block postfixInput = .ok base postfixOutput →
          postfixOrdinary postfixInput.declarativeRemainder base
            postfixOutput.declarativeRemainder)
    (postfixRejectSound :
      ∀ {postfixInput rejected : State} {failure : Failure},
        expressionPostfix nested block postfixInput =
            .reject failure rejected →
          postfixRejects postfixInput.declarativeRemainder
            rejected.declarativeRemainder) :
    (∀ {input output : State} {expression : Expr},
      expressionUnary nested block input = .ok expression output →
        DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary
          input.declarativeRemainder expression
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionUnary nested block input = .reject failure rejected →
        DeclarativeGrammar.ExpressionUnaryRejects postfixRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨expressionUnary_success_ordinary_sound nested block postfixOrdinary
      postfixSuccessSound,
    expressionUnary_reject_ordinary_sound nested block postfixRejects
      postfixRejectSound⟩

/-- Lift a deterministic postfix outcome contract to the unary layer. -/
theorem expressionUnary_ordinaryOutcomeSpec
    {postfixOrdinary : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop}
    {postfixRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.DeterministicOutcomeSpec postfixOrdinary
      postfixRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.ExpressionUnaryOrdinaryParses postfixOrdinary)
      (DeclarativeGrammar.ExpressionUnaryRejects postfixRejects) :=
  DeclarativeGrammar.expressionUnaryDeterministicOutcomeSpec outcomes

end Solcore.Syntax.Parser.ExpressionInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionLayerOrdinaryOutcomeSoundnessProperties
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
  let multiply := ExpressionInternals.leftAssociative unary 9
  let add := ExpressionInternals.leftAssociative multiply 8
  let shift := ExpressionInternals.leftAssociative add 7
  let bitAnd := ExpressionInternals.leftAssociative shift 6
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
    DeclarativeGrammar.LeftAssociativeOrdinaryParses unaryOrdinary 9
  let multiplyRejects :=
    DeclarativeGrammar.LeftAssociativeRejects unaryOrdinary unaryRejects 9
  let addOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses multiplyOrdinary 8
  let addRejects :=
    DeclarativeGrammar.LeftAssociativeRejects multiplyOrdinary
      multiplyRejects 8
  let shiftOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses addOrdinary 7
  let bitAndOrdinary :=
    DeclarativeGrammar.LeftAssociativeOrdinaryParses shiftOrdinary 6
  let shiftRejects :=
    DeclarativeGrammar.LeftAssociativeRejects addOrdinary addRejects 7
  let bitAndRejects :=
    DeclarativeGrammar.LeftAssociativeRejects shiftOrdinary shiftRejects 6
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
      unaryOrdinary unaryRejects unarySound.1 unarySound.2 9
  have addSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound multiply
      multiplyOrdinary multiplyRejects multiplySound.1 multiplySound.2 8
  have shiftSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound add addOrdinary
      addRejects addSound.1 addSound.2 7
  have bitAndSound :=
    ExpressionInternals.leftAssociative_ordinaryOutcome_sound shift shiftOrdinary
      shiftRejects shiftSound.1 shiftSound.2 6
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionStepOrdinaryOutcomeSoundnessProperties
/-!
One-call executable ordinary outcomes for a complete Core expression step.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Compose the exact executable bridges through atom dispatch, public atom
recovery, postfix parsing, and the complete operator stack. -/
theorem coreExpressionStep_ordinaryOutcome_sound
    (nested : Parser Expr) (block : Parser Block)
    (relations : DeclarativeGrammar.CoreExpressionStepRelations)
    (nestedSuccessSound : ∀ {input output : State} {expression : Expr},
      nested input = .ok expression output → relations.nestedOrdinary
        input.declarativeRemainder expression output.declarativeRemainder)
    (nestedRejectSound : ∀ {input rejected : State} {failure : Failure},
      nested input = .reject failure rejected → relations.nestedRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (nestedWindow : Parser.PreservesTokenWindow nested)
    (parameterSuccessSound :
      ∀ {input output : State} {parameter : LambdaParameter},
        lambdaParameter input = .ok parameter output →
          relations.parameterOrdinary input.declarativeRemainder parameter
            output.declarativeRemainder)
    (parameterRejectSound :
      ∀ {input rejected : State} {failure : Failure},
        lambdaParameter input = .reject failure rejected →
          relations.parameterRejects input.declarativeRemainder
            rejected.declarativeRemainder)
    (typeSuccessSound : ∀ {input output : State} {type : TypeExpr},
      typeExpr input = .ok type output → relations.typeOrdinary
        input.declarativeRemainder type output.declarativeRemainder)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → relations.typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockSuccessSound : ∀ {input output : State} {body : Block},
      block input = .ok body output → relations.blockOrdinary
        input.declarativeRemainder body output.declarativeRemainder)
    (blockRejectSound : ∀ {input rejected : State} {failure : Failure},
      block input = .reject failure rejected → relations.blockRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (blockWindow : Parser.PreservesTokenWindow block) :
    (∀ {input output : State} {expression : Expr},
      expressionLayer nested block input = .ok expression output →
        DeclarativeGrammar.CoreExpressionStepOrdinaryParses relations
          input.declarativeRemainder expression output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      expressionLayer nested block input = .reject failure rejected →
        DeclarativeGrammar.CoreExpressionStepRejects relations
          input.declarativeRemainder rejected.declarativeRemainder) := by
  have coreSound :=
    ExpressionAtomInternals.expressionAtomCore_ordinaryOutcome_sound nested
      block relations.nestedOrdinary relations.nestedRejects
        relations.parameterOrdinary relations.parameterRejects
          relations.typeOrdinary relations.typeRejects
            relations.blockOrdinary relations.blockRejects nestedSuccessSound
              nestedRejectSound nestedWindow parameterSuccessSound
                parameterRejectSound lambdaParameter_preservesTokenWindow
                  typeSuccessSound typeRejectSound blockSuccessSound
                    blockRejectSound
  have coreWindow :=
    ExpressionAtomInternals.expressionAtomCore_preservesTokenWindow nested
      block nestedWindow blockWindow
  have atomSound := expressionAtom_ordinaryOutcome_sound nested block
    relations.atomCoreOrdinary relations.atomCoreRejects coreSound.1
      coreSound.2 coreWindow
  have postfixSound := expressionPostfix_ordinaryOutcome_sound nested block
    relations.atomOrdinary relations.nestedOrdinary relations.atomRejects
      relations.nestedRejects atomSound.1 atomSound.2 nestedSuccessSound
        nestedRejectSound nestedWindow
  exact expressionLayer_ordinaryOutcome_sound nested block
    relations.nestedOrdinary relations.postfixOrdinary
      relations.nestedRejects relations.postfixRejects nestedSuccessSound
        nestedRejectSound postfixSound.1 postfixSound.2

/-- Re-export the deterministic contract under the executable bridge name. -/
theorem coreExpressionStep_ordinaryOutcomeSpec
    (relations : DeclarativeGrammar.CoreExpressionStepRelations)
    (nestedOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.nestedOrdinary relations.nestedRejects)
    (parameterOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.parameterOrdinary relations.parameterRejects)
    (typeOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.typeOrdinary relations.typeRejects)
    (blockOutcomes : DeclarativeGrammar.DeterministicOutcomeSpec
      relations.blockOrdinary relations.blockRejects) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.CoreExpressionStepOrdinaryParses relations)
      (DeclarativeGrammar.CoreExpressionStepRejects relations) :=
  DeclarativeGrammar.coreExpressionStepDeterministicOutcomeSpec relations
    nestedOutcomes parameterOutcomes typeOutcomes blockOutcomes

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaReturnTypeSoundnessProperties
/-!
Exact declarative soundness for optional Core lambda return types.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

private theorem bind_ok_components {alpha beta : Type} {first : Parser alpha}
    {next : alpha → Parser beta} {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- Every successful optional lambda return type retains exact arrow absence or
the exact arrow and recursive type transition. -/
theorem optionalLambdaReturnType_success_sound {input next : State}
    {value : Option TypeExpr}
    (result : optionalLambdaReturnType input = .ok value next) :
    DeclarativeGrammar.OptionalLambdaReturnTypeParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold optionalLambdaReturnType getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .arrow
  · simp only [present, if_true] at result
    rcases bind_ok_components result with
      ⟨arrow, afterArrow, arrowResult, rest⟩
    rcases bind_ok_components rest with
      ⟨type, afterType, typeResult, finished⟩
    cases finished
    exact .present arrow.span
      (symbol_success_exactTokenParses .arrow .typeExpr arrowResult)
      (typeExpr_success_sound typeResult)
  · have arrowAbsent : isSymbol input .arrow = false :=
      Bool.eq_false_iff.mpr present
    simp only [arrowAbsent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent
      (symbolAbsentAt_of_isSymbol_eq_false .arrow arrowAbsent)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreLambdaExpressionSoundnessProperties
/-!
Diagnostic reflection and exact parser-independent soundness for Core lambda
expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/-- A diagnostic-free successful lambda parse had a diagnostic-free input
whenever its supplied block parser has the same property. -/
theorem lambdaExpression_reflectsDiagnosticFreeOnSuccess
    (block : Parser Block)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess (lambdaExpression block) := by
  unfold lambdaExpression
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .lamKw .expression)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimited_reflectsDiagnosticFreeOnSuccess .leftParen .rightParen true
      lambdaParameter .parameter .expression
      lambdaParameter_reflectsDiagnosticFreeOnSuccess)
  intro parameters
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    optionalLambdaReturnType_reflectsDiagnosticFreeOnSuccess
  intro returnType
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess blockReflects
  intro body
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Every diagnostic-free successful lambda parse follows the exact
parser-independent lambda grammar over the supplied block judgment. -/
theorem lambdaExpression_success_sound
    (block : Parser Block)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {input next : State} {value : Block},
      next.diagnosticsRev = [] → block input = .ok value next →
      blockParses input.declarativeRemainder value
        next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : lambdaExpression block input = .ok value next) :
    DeclarativeGrammar.LambdaExpressionParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
  unfold lambdaExpression at result
  rcases bind_ok_components result with
    ⟨marker, afterMarker, markerResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, returnStage⟩
  rcases bind_ok_components returnStage with
    ⟨returnType, afterReturn, returnResult, bodyStage⟩
  rcases bind_ok_components bodyStage with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  have afterReturnFree := blockReflects afterReturn body next bodyResult
    diagnosticFree
  have afterParametersFree :=
    optionalLambdaReturnType_reflectsDiagnosticFreeOnSuccess
      afterParameters returnType afterReturn returnResult afterReturnFree
  have parametersGrammar :=
    delimited_allowEmpty_trailing_success_sound_of_diagnosticFree
      .leftParen .rightParen lambdaParameter
      DeclarativeGrammar.LambdaParameterParses .parameter .expression
      lambdaParameter_success_sound
      lambdaParameter_reflectsDiagnosticFreeOnSuccess
      lambdaParameter_preservesTokenWindow afterParametersFree
      parametersResult
  exact .parsed marker.span
    (keyword_success_exactTokenParses .lamKw .expression markerResult)
    parametersGrammar
    (optionalLambdaReturnType_success_sound returnResult)
    (blockSound diagnosticFree bodyResult)

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomCoreDiagnosticReflectionProperties
/-! Diagnostic reflection for the ordered Core expression-atom dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/--
The seven-way Core atom dispatcher cannot erase diagnostics when its supplied
recursive expression and block parsers cannot erase them.
-/
theorem expressionAtomCore_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtomCore nested block) := by
  intro input value next result diagnosticFree
  unfold expressionAtomCore at result
  split at result
  · exact literalExpression_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  split at result
  · exact identifierExpression_reflectsDiagnosticFreeOnSuccess input value
      next result diagnosticFree
  split at result
  · exact dotConstructor_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects input value next result diagnosticFree
  split at result
  · exact proxyExpression_reflectsDiagnosticFreeOnSuccess input value next
      result diagnosticFree
  split at result
  · exact parenthesized_reflectsDiagnosticFreeOnSuccess nested
      nestedReflects input value next result diagnosticFree
  split at result
  · exact arrayLiteral_reflectsDiagnosticFreeOnSuccess nested nestedReflects
      input value next result diagnosticFree
  split at result
  · exact lambdaExpression_reflectsDiagnosticFreeOnSuccess block
      blockReflects input value next result diagnosticFree
  · simp [rejectAt] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomCoreSoundnessProperties
/-!
Exact diagnostic-free soundness for the ordered Core expression-atom
dispatcher.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

/--
Every diagnostic-free Core atom success follows exactly one of the seven
ordered declarative branches, with all earlier executable guards excluded.
-/
theorem expressionAtomCore_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {nestedInput nestedNext : State} {nestedValue : Expr},
      nestedNext.diagnosticsRev = [] →
      nested nestedInput = .ok nestedValue nestedNext →
      nestedParses nestedInput.declarativeRemainder nestedValue
        nestedNext.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {blockInput blockNext : State} {blockValue : Block},
      blockNext.diagnosticsRev = [] →
      block blockInput = .ok blockValue blockNext →
      blockParses blockInput.declarativeRemainder blockValue
        blockNext.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionAtomCore nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
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
      exact .identifier noLiteral
        (identifierExpression_success_sound result)
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
          (dotConstructor_success_sound nested nestedParses nestedReflects
            nestedSound nestedShape diagnosticFree result)
      next dotAbsent =>
        have dotAbsentEq : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr dotAbsent
        have noDot := symbolAbsentAt_of_isSymbol_eq_false .dot dotAbsentEq
        split at result
        next atPresent =>
          exact .proxy noLiteral noName noDot
            (proxyExpression_success_sound result)
        next atAbsent =>
          have atAbsentEq : isSymbol input .at = false :=
            Bool.eq_false_iff.mpr atAbsent
          have noAt := symbolAbsentAt_of_isSymbol_eq_false .at atAbsentEq
          split at result
          next leftParenPresent =>
            exact .parenthesized noLiteral noName noDot noAt
              (parenthesized_success_sound nested nestedParses nestedReflects
                nestedSound diagnosticFree result)
          next leftParenAbsent =>
            have leftParenAbsentEq : isSymbol input .leftParen = false :=
              Bool.eq_false_iff.mpr leftParenAbsent
            have noLeftParen := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen leftParenAbsentEq
            split at result
            next leftBracketPresent =>
              exact .array noLiteral noName noDot noAt noLeftParen
                (arrayLiteral_success_sound nested nestedParses nestedReflects
                  nestedSound nestedShape diagnosticFree result)
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
                  (lambdaExpression_success_sound block blockParses
                    blockReflects blockSound diagnosticFree result)
              next lambdaAbsent =>
                simp [rejectAt] at result

end Solcore.Syntax.Parser.ExpressionAtomInternals
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionAtomSoundnessProperties
/-!
Exact diagnostic-free soundness at the public recoverable Core atom boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Public atom parsing reflects diagnostic freedom through the exact ordered
Core dispatcher. -/
theorem coreExpressionAtom_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (expressionAtom nested block) :=
  expressionAtom_reflectsDiagnosticFreeOnSuccess nested block
    (ExpressionAtomInternals.expressionAtomCore_reflectsDiagnosticFreeOnSuccess
      nested block nestedReflects blockReflects)

/-- Every diagnostic-free public atom success follows the exact seven-way
Core atom grammar; recovery successes are excluded. -/
theorem expressionAtom_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {input next : State} {value : Block},
      next.diagnosticsRev = [] → block input = .ok value next →
      blockParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionAtom nested block input = .ok value next) :
    DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses
      input.declarativeRemainder value next.declarativeRemainder := by
  exact ExpressionAtomInternals.expressionAtomCore_success_sound nested block
    nestedParses blockParses nestedReflects nestedSound nestedShape
      blockReflects blockSound diagnosticFree
        (expressionAtomCore_of_diagnosticFree_success nested block result
          diagnosticFree)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.CoreExpressionSoundnessProperties
/-!
Aggregate diagnostic reflection and exact declarative soundness for one
concrete Core expression recursion layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A concrete Core expression layer reflects through its supplied recursive
expression and block parsers. -/
theorem coreExpressionStep_reflectsDiagnosticFreeOnSuccess
    (nested : Parser Expr) (block : Parser Block)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block) :
    Parser.ReflectsDiagnosticFreeOnSuccess (expressionLayer nested block) :=
  expressionStep_reflectsDiagnosticFreeOnSuccess nested block
    (coreExpressionAtom_reflectsDiagnosticFreeOnSuccess nested block
      nestedReflects blockReflects)
    nestedReflects

/-- Every diagnostic-free success of one concrete Core expression layer
follows the exact atom, postfix, precedence, and conditional grammar. -/
theorem coreExpressionStep_success_sound
    (nested : Parser Expr) (block : Parser Block)
    (nestedParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (blockParses : DeclarativeGrammar.Remainder → Block →
      DeclarativeGrammar.Remainder → Prop)
    (nestedReflects : Parser.ReflectsDiagnosticFreeOnSuccess nested)
    (nestedSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → nested input = .ok value next →
      nestedParses input.declarativeRemainder value next.declarativeRemainder)
    (nestedShape : Parser.PreservesTokenWindow nested)
    (blockReflects : Parser.ReflectsDiagnosticFreeOnSuccess block)
    (blockSound : ∀ {input next : State} {value : Block},
      next.diagnosticsRev = [] → block input = .ok value next →
      blockParses input.declarativeRemainder value next.declarativeRemainder)
    {input next : State} {value : Expr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : expressionLayer nested block input = .ok value next) :
    DeclarativeGrammar.CoreExpressionStepWithBlockParses nestedParses
      blockParses input.declarativeRemainder value
        next.declarativeRemainder := by
  apply expressionStep_success_sound nested block
    (DeclarativeGrammar.ExpressionAtomCoreParses nestedParses blockParses)
    nestedParses
    (coreExpressionAtom_reflectsDiagnosticFreeOnSuccess nested block
      nestedReflects blockReflects)
    (fun atomFree atomResult =>
      expressionAtom_success_sound nested block nestedParses blockParses
        nestedReflects nestedSound nestedShape blockReflects blockSound
          atomFree atomResult)
    nestedReflects nestedSound nestedShape diagnosticFree result

end Solcore.Syntax.Parser
end
