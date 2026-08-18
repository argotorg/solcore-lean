import Solcore.Surface.Wire.V1.Syntax
import Solcore.Surface.Properties

set_option autoImplicit false

namespace Solcore.Surface.Wire.V1

private def TokensValidFor
    (file : Solcore.Surface.SourceFile)
    (tokens : List Solcore.Surface.Token) : Prop :=
  ∀ token ∈ tokens, token.ValidFor file

private theorem tokensValidFor_tail
    {file : Solcore.Surface.SourceFile}
    {head : Solcore.Surface.Token}
    {tail : List Solcore.Surface.Token}
    (valid : TokensValidFor file (head :: tail)) :
    TokensValidFor file tail := by
  intro token member
  exact valid token (by simp [member])

private def ExprProjectable
    (expression : Solcore.Surface.Expr) : Prop :=
  ∃ wire : Expr, Expr.ofSurface? expression = some wire

private def ExprListProjectable
    (expressions : List Solcore.Surface.Expr) : Prop :=
  ∃ wires : List Expr, expressions.mapM Expr.ofSurface? = some wires

private theorem identifierTextProjectable_of_validToken
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (text : String)
    (valid : token.ValidFor file)
    (kind : token.kind = .identifier text) :
    ∃ wire : IdentifierText, IdentifierText.ofString? text = some wire := by
  have canonical :
      (Solcore.Surface.TokenKind.identifier text).Canonical := by
    rw [← kind]
    exact valid.1
  have validator : identifierTextValid text = true := by
    rw [identifierTextValid_eq_tokenKind_isCanonical]
    exact canonical
  let wire : IdentifierText := { value := text, valid := validator }
  refine ⟨wire, ?_⟩
  change IdentifierText.ofString? wire.value = some wire
  exact IdentifierText.ofString?_value wire

private theorem decimalDigitsProjectable_of_validToken
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (digits : String)
    (valid : token.ValidFor file)
    (kind : token.kind = .decimal digits) :
    ∃ wire : DecimalDigits, DecimalDigits.ofString? digits = some wire := by
  have canonical :
      (Solcore.Surface.TokenKind.decimal digits).Canonical := by
    rw [← kind]
    exact valid.1
  have validator : decimalDigitsValid digits = true := by
    rw [decimalDigitsValid_eq_tokenKind_isCanonical]
    exact canonical
  let wire : DecimalDigits := { value := digits, valid := validator }
  refine ⟨wire, ?_⟩
  change DecimalDigits.ofString? wire.value = some wire
  exact DecimalDigits.ofString?_value wire

private theorem hexadecimalDigitsProjectable_of_validToken
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (digits : String)
    (valid : token.ValidFor file)
    (kind : token.kind = .hexadecimal digits) :
    ∃ wire : HexadecimalDigits,
      HexadecimalDigits.ofString? digits = some wire := by
  have canonical :
      (Solcore.Surface.TokenKind.hexadecimal digits).Canonical := by
    rw [← kind]
    exact valid.1
  have validator : hexadecimalDigitsValid digits = true := by
    rw [hexadecimalDigitsValid_eq_tokenKind_isCanonical]
    exact canonical
  let wire : HexadecimalDigits := { value := digits, valid := validator }
  refine ⟨wire, ?_⟩
  change HexadecimalDigits.ofString? wire.value = some wire
  exact HexadecimalDigits.ofString?_value wire

private theorem nameProjectable_of_validToken
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (text : String)
    (valid : token.ValidFor file)
    (kind : token.kind = .identifier text) :
    ∃ wire : Name,
      Name.ofSurface?
        ({ span := token.span, value := text } : Solcore.Surface.Name) =
          some wire := by
  obtain ⟨wireText, projection⟩ :=
    identifierTextProjectable_of_validToken file token text valid kind
  refine ⟨{ span := SourceSpan.ofSurface token.span, text := wireText }, ?_⟩
  simp [Name.ofSurface?, projection]

private theorem binaryOperatorProjectable_of_binding
    {kind : Solcore.Surface.TokenKind}
    {operator : Solcore.Surface.BinaryOp}
    {precedence : Nat}
    {associativity : Solcore.Surface.Associativity}
    (span : Solcore.Surface.SourceSpan)
    (binding :
      Solcore.Surface.BinaryBinding kind operator precedence associativity) :
    ∃ wire : BinaryOperator,
      BinaryOperator.ofSurface?
        ({ span, value := operator } :
          Solcore.Surface.Located Solcore.Surface.BinaryOp) = some wire := by
  cases binding <;>
    simp [BinaryOperator.ofSurface?, BinaryOp.ofSurface?]

private def ExprProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (_minimum : Nat)
    (input : List Solcore.Surface.Token)
    (expression : Solcore.Surface.Expr)
    (remaining : List Solcore.Surface.Token) : Prop :=
  TokensValidFor file input ->
    ExprProjectable expression ∧ TokensValidFor file remaining

private def PrefixProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (input : List Solcore.Surface.Token)
    (expression : Solcore.Surface.Expr)
    (remaining : List Solcore.Surface.Token) : Prop :=
  TokensValidFor file input ->
    ExprProjectable expression ∧ TokensValidFor file remaining

private def InfixProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (_minimum : Nat)
    (left : Solcore.Surface.Expr)
    (input : List Solcore.Surface.Token)
    (expression : Solcore.Surface.Expr)
    (remaining : List Solcore.Surface.Token) : Prop :=
  ExprProjectable left ->
    TokensValidFor file input ->
      ExprProjectable expression ∧ TokensValidFor file remaining

private def ArgumentsProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (input : List Solcore.Surface.Token)
    (arguments : List Solcore.Surface.Expr)
    (_right : Solcore.Surface.Token)
    (remaining : List Solcore.Surface.Token) : Prop :=
  TokensValidFor file input ->
    ExprListProjectable arguments ∧ TokensValidFor file remaining

private def ArgumentTailProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (input : List Solcore.Surface.Token)
    (arguments : List Solcore.Surface.Expr)
    (_right : Solcore.Surface.Token)
    (remaining : List Solcore.Surface.Token) : Prop :=
  TokensValidFor file input ->
    ExprListProjectable arguments ∧ TokensValidFor file remaining

private theorem exprConditionalProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (ifToken thenToken elseToken : Solcore.Surface.Token)
    (afterIf afterThen afterElse remaining : List Solcore.Surface.Token)
    (condition thenBranch elseBranch : Solcore.Surface.Expr)
    (_ifKind : ifToken.kind = .keywordIf)
    (_conditionParse :
      Solcore.Surface.ExprParses 0 afterIf condition (thenToken :: afterThen))
    (_thenKind : thenToken.kind = .identifier "then")
    (_thenParse :
      Solcore.Surface.ExprParses 0 afterThen thenBranch
        (elseToken :: afterElse))
    (_elseKind : elseToken.kind = .keywordElse)
    (_elseParse :
      Solcore.Surface.ExprParses 0 afterElse elseBranch remaining)
    (conditionIH :
      ExprProjectionProperty file 0 afterIf condition
        (thenToken :: afterThen))
    (thenIH :
      ExprProjectionProperty file 0 afterThen thenBranch
        (elseToken :: afterElse))
    (elseIH :
      ExprProjectionProperty file 0 afterElse elseBranch remaining) :
    ExprProjectionProperty file 0 (ifToken :: afterIf)
      (.ifThenElse
        (Solcore.Surface.SourceSpan.cover ifToken.span elseBranch.span)
        condition thenBranch elseBranch)
      remaining := by
  intro inputValid
  obtain ⟨⟨conditionWire, conditionProjection⟩, afterConditionValid⟩ :=
    conditionIH (tokensValidFor_tail inputValid)
  obtain ⟨⟨thenWire, thenProjection⟩, afterThenValid⟩ :=
    thenIH (tokensValidFor_tail afterConditionValid)
  obtain ⟨⟨elseWire, elseProjection⟩, remainingValid⟩ :=
    elseIH (tokensValidFor_tail afterThenValid)
  refine ⟨⟨.ifThenElse
    (SourceSpan.ofSurface
      (Solcore.Surface.SourceSpan.cover ifToken.span elseBranch.span))
    conditionWire thenWire elseWire, ?_⟩, remainingValid⟩
  simp [Expr.ofSurface?, conditionProjection, thenProjection, elseProjection]

private theorem exprOrdinaryProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (minimum : Nat)
    (input afterPrefix remaining : List Solcore.Surface.Token)
    (initial result : Solcore.Surface.Expr)
    (_prefixParse : Solcore.Surface.PrefixParses input initial afterPrefix)
    (_infixParse :
      Solcore.Surface.InfixParses minimum initial afterPrefix result remaining)
    (prefixIH : PrefixProjectionProperty file input initial afterPrefix)
    (infixIH :
      InfixProjectionProperty file minimum initial afterPrefix result remaining) :
    ExprProjectionProperty file minimum input result remaining := by
  intro inputValid
  obtain ⟨initialProjectable, afterPrefixValid⟩ := prefixIH inputValid
  exact infixIH initialProjectable afterPrefixValid

private theorem prefixNotProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (operatorToken : Solcore.Surface.Token)
    (afterOperator remaining : List Solcore.Surface.Token)
    (operand : Solcore.Surface.Expr)
    (_operatorKind : operatorToken.kind = .bang)
    (_operandParse :
      Solcore.Surface.PrefixParses afterOperator operand remaining)
    (operandIH :
      PrefixProjectionProperty file afterOperator operand remaining) :
    PrefixProjectionProperty file (operatorToken :: afterOperator)
      (.unary
        (Solcore.Surface.SourceSpan.cover operatorToken.span operand.span)
        { value := .not, span := operatorToken.span }
        operand)
      remaining := by
  intro inputValid
  obtain ⟨⟨operandWire, operandProjection⟩, remainingValid⟩ :=
    operandIH (tokensValidFor_tail inputValid)
  let operatorWire : UnaryOperator := {
    span := SourceSpan.ofSurface operatorToken.span
    operator := .not
  }
  refine ⟨⟨.unary
    (SourceSpan.ofSurface
      (Solcore.Surface.SourceSpan.cover operatorToken.span operand.span))
    operatorWire operandWire, ?_⟩, remainingValid⟩
  simp [Expr.ofSurface?, UnaryOperator.ofSurface?, UnaryOp.ofSurface?,
    operatorWire, operandProjection]

private theorem prefixUnitProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (left right : Solcore.Surface.Token)
    (remaining : List Solcore.Surface.Token)
    (_leftKind : left.kind = .leftParen)
    (_rightKind : right.kind = .rightParen) :
    PrefixProjectionProperty file (left :: right :: remaining)
      (.unit (Solcore.Surface.SourceSpan.cover left.span right.span))
      remaining := by
  intro inputValid
  refine ⟨⟨.unit
    (SourceSpan.ofSurface
      (Solcore.Surface.SourceSpan.cover left.span right.span)), ?_⟩, ?_⟩
  · simp [Expr.ofSurface?]
  exact tokensValidFor_tail (tokensValidFor_tail inputValid)

private theorem prefixGroupProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (left right : Solcore.Surface.Token)
    (afterLeft remaining : List Solcore.Surface.Token)
    (inner : Solcore.Surface.Expr)
    (_leftKind : left.kind = .leftParen)
    (_innerParse :
      Solcore.Surface.ExprParses 0 afterLeft inner (right :: remaining))
    (_rightKind : right.kind = .rightParen)
    (innerIH :
      ExprProjectionProperty file 0 afterLeft inner (right :: remaining)) :
    PrefixProjectionProperty file (left :: afterLeft)
      (.group (Solcore.Surface.SourceSpan.cover left.span right.span) inner)
      remaining := by
  intro inputValid
  obtain ⟨⟨innerWire, innerProjection⟩, afterInnerValid⟩ :=
    innerIH (tokensValidFor_tail inputValid)
  refine ⟨⟨.group
    (SourceSpan.ofSurface
      (Solcore.Surface.SourceSpan.cover left.span right.span))
    innerWire, ?_⟩, tokensValidFor_tail afterInnerValid⟩
  simp [Expr.ofSurface?, innerProjection]

private theorem prefixDecimalProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (digits : String)
    (remaining : List Solcore.Surface.Token)
    (kind : token.kind = .decimal digits) :
    PrefixProjectionProperty file (token :: remaining)
      (.integer { base := .decimal, digits, span := token.span })
      remaining := by
  intro inputValid
  have tokenValid := inputValid token (by simp)
  obtain ⟨digitsWire, digitsProjection⟩ :=
    decimalDigitsProjectable_of_validToken file token digits tokenValid kind
  refine ⟨⟨.integer
    (.decimal (SourceSpan.ofSurface token.span) digitsWire), ?_⟩,
    tokensValidFor_tail inputValid⟩
  simp [Expr.ofSurface?, IntegerLiteral.ofSurface?, digitsProjection]

private theorem prefixHexadecimalProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (digits : String)
    (remaining : List Solcore.Surface.Token)
    (kind : token.kind = .hexadecimal digits) :
    PrefixProjectionProperty file (token :: remaining)
      (.integer { base := .hexadecimal, digits, span := token.span })
      remaining := by
  intro inputValid
  have tokenValid := inputValid token (by simp)
  obtain ⟨digitsWire, digitsProjection⟩ :=
    hexadecimalDigitsProjectable_of_validToken
      file token digits tokenValid kind
  refine ⟨⟨.integer
    (.hexadecimal (SourceSpan.ofSurface token.span) digitsWire), ?_⟩,
    tokensValidFor_tail inputValid⟩
  simp [Expr.ofSurface?, IntegerLiteral.ofSurface?, digitsProjection]

private theorem prefixNameProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (token : Solcore.Surface.Token)
    (text : String)
    (remaining : List Solcore.Surface.Token)
    (kind : token.kind = .identifier text)
    (_notCall : Solcore.Surface.HeadKindNe .leftParen remaining) :
    PrefixProjectionProperty file (token :: remaining)
      (.name { value := text, span := token.span }) remaining := by
  intro inputValid
  have tokenValid := inputValid token (by simp)
  obtain ⟨nameWire, nameProjection⟩ :=
    nameProjectable_of_validToken file token text tokenValid kind
  exact ⟨⟨.name nameWire, by simpa [Expr.ofSurface?] using nameProjection⟩,
    tokensValidFor_tail inputValid⟩

private theorem prefixCallProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (identifier left right : Solcore.Surface.Token)
    (text : String)
    (afterLeft remaining : List Solcore.Surface.Token)
    (arguments : List Solcore.Surface.Expr)
    (identifierKind : identifier.kind = .identifier text)
    (_leftKind : left.kind = .leftParen)
    (_argumentsParse :
      Solcore.Surface.ArgumentsParse afterLeft arguments right remaining)
    (argumentsIH :
      ArgumentsProjectionProperty file afterLeft arguments right remaining) :
    PrefixProjectionProperty file (identifier :: left :: afterLeft)
      (.call
        (Solcore.Surface.SourceSpan.cover identifier.span right.span)
        { value := text, span := identifier.span }
        arguments)
      remaining := by
  intro inputValid
  have identifierValid := inputValid identifier (by simp)
  obtain ⟨calleeWire, calleeProjection⟩ :=
    nameProjectable_of_validToken
      file identifier text identifierValid identifierKind
  obtain ⟨⟨argumentWires, argumentsProjection⟩, remainingValid⟩ :=
    argumentsIH (tokensValidFor_tail (tokensValidFor_tail inputValid))
  refine ⟨⟨.call
    (SourceSpan.ofSurface
      (Solcore.Surface.SourceSpan.cover identifier.span right.span))
    calleeWire argumentWires, ?_⟩, remainingValid⟩
  simp [Expr.ofSurface?, calleeProjection, argumentsProjection]

private theorem infixStopProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (minimum : Nat)
    (left : Solcore.Surface.Expr)
    (tokens : List Solcore.Surface.Token)
    (_blocked : Solcore.Surface.InfixBlocked minimum tokens) :
    InfixProjectionProperty file minimum left tokens left tokens := by
  intro leftProjectable inputValid
  exact ⟨leftProjectable, inputValid⟩

private theorem infixLeftStepProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (minimum precedence : Nat)
    (left right result : Solcore.Surface.Expr)
    (operatorToken : Solcore.Surface.Token)
    (operator : Solcore.Surface.BinaryOp)
    (afterOperator afterRight remaining : List Solcore.Surface.Token)
    (binding :
      Solcore.Surface.BinaryBinding operatorToken.kind operator precedence
        .left)
    (_eligible : minimum ≤ precedence)
    (_rightParse :
      Solcore.Surface.ExprParses (precedence + 1) afterOperator right afterRight)
    (_tailParse :
      Solcore.Surface.InfixParses minimum
        (.binary
          (Solcore.Surface.SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH :
      ExprProjectionProperty file (precedence + 1)
        afterOperator right afterRight)
    (tailIH :
      InfixProjectionProperty file minimum
        (.binary
          (Solcore.Surface.SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixProjectionProperty file minimum left
      (operatorToken :: afterOperator) result remaining := by
  rintro ⟨leftWire, leftProjection⟩ inputValid
  obtain ⟨⟨rightWire, rightProjection⟩, afterRightValid⟩ :=
    rightIH (tokensValidFor_tail inputValid)
  obtain ⟨operatorWire, operatorProjection⟩ :=
    binaryOperatorProjectable_of_binding operatorToken.span binding
  have binaryProjectable : ExprProjectable
      (.binary
        (Solcore.Surface.SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right) := by
    refine ⟨.binary
      (SourceSpan.ofSurface
        (Solcore.Surface.SourceSpan.cover left.span right.span))
      operatorWire leftWire rightWire, ?_⟩
    simp [Expr.ofSurface?, operatorProjection, leftProjection, rightProjection]
  exact tailIH binaryProjectable afterRightValid

private theorem infixNonAssociativeStepProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (minimum precedence : Nat)
    (left right result : Solcore.Surface.Expr)
    (operatorToken : Solcore.Surface.Token)
    (operator : Solcore.Surface.BinaryOp)
    (afterOperator afterRight remaining : List Solcore.Surface.Token)
    (binding :
      Solcore.Surface.BinaryBinding operatorToken.kind operator precedence
        .nonAssociative)
    (_eligible : minimum ≤ precedence)
    (_rightParse :
      Solcore.Surface.ExprParses (precedence + 1) afterOperator right afterRight)
    (_notRepeated : Solcore.Surface.HeadPrecedenceNe precedence afterRight)
    (_tailParse :
      Solcore.Surface.InfixParses minimum
        (.binary
          (Solcore.Surface.SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH :
      ExprProjectionProperty file (precedence + 1)
        afterOperator right afterRight)
    (tailIH :
      InfixProjectionProperty file minimum
        (.binary
          (Solcore.Surface.SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixProjectionProperty file minimum left
      (operatorToken :: afterOperator) result remaining := by
  rintro ⟨leftWire, leftProjection⟩ inputValid
  obtain ⟨⟨rightWire, rightProjection⟩, afterRightValid⟩ :=
    rightIH (tokensValidFor_tail inputValid)
  obtain ⟨operatorWire, operatorProjection⟩ :=
    binaryOperatorProjectable_of_binding operatorToken.span binding
  have binaryProjectable : ExprProjectable
      (.binary
        (Solcore.Surface.SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right) := by
    refine ⟨.binary
      (SourceSpan.ofSurface
        (Solcore.Surface.SourceSpan.cover left.span right.span))
      operatorWire leftWire rightWire, ?_⟩
    simp [Expr.ofSurface?, operatorProjection, leftProjection, rightProjection]
  exact tailIH binaryProjectable afterRightValid

private theorem argumentsEmptyProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (right : Solcore.Surface.Token)
    (remaining : List Solcore.Surface.Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentsProjectionProperty file (right :: remaining) [] right remaining := by
  intro inputValid
  exact ⟨⟨[], rfl⟩, tokensValidFor_tail inputValid⟩

private theorem argumentsNonemptyProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (input afterFirst remaining : List Solcore.Surface.Token)
    (first : Solcore.Surface.Expr)
    (tail : List Solcore.Surface.Expr)
    (right : Solcore.Surface.Token)
    (_firstParse : Solcore.Surface.ExprParses 0 input first afterFirst)
    (_tailParse :
      Solcore.Surface.ArgumentTailParses afterFirst tail right remaining)
    (firstIH : ExprProjectionProperty file 0 input first afterFirst)
    (tailIH :
      ArgumentTailProjectionProperty file afterFirst tail right remaining) :
    ArgumentsProjectionProperty file input (first :: tail) right remaining := by
  intro inputValid
  obtain ⟨⟨firstWire, firstProjection⟩, afterFirstValid⟩ :=
    firstIH inputValid
  obtain ⟨⟨tailWires, tailProjection⟩, remainingValid⟩ :=
    tailIH afterFirstValid
  refine ⟨⟨firstWire :: tailWires, ?_⟩, remainingValid⟩
  simp [firstProjection, tailProjection]

private theorem argumentTailDoneProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (right : Solcore.Surface.Token)
    (remaining : List Solcore.Surface.Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentTailProjectionProperty file
      (right :: remaining) [] right remaining := by
  intro inputValid
  exact ⟨⟨[], rfl⟩, tokensValidFor_tail inputValid⟩

private theorem argumentTailMoreProjectionProperty
    (file : Solcore.Surface.SourceFile)
    (comma right : Solcore.Surface.Token)
    (afterComma afterNext remaining : List Solcore.Surface.Token)
    (next : Solcore.Surface.Expr)
    (tail : List Solcore.Surface.Expr)
    (_commaKind : comma.kind = .comma)
    (_nextParse : Solcore.Surface.ExprParses 0 afterComma next afterNext)
    (_tailParse :
      Solcore.Surface.ArgumentTailParses afterNext tail right remaining)
    (nextIH : ExprProjectionProperty file 0 afterComma next afterNext)
    (tailIH :
      ArgumentTailProjectionProperty file afterNext tail right remaining) :
    ArgumentTailProjectionProperty file (comma :: afterComma)
      (next :: tail) right remaining := by
  intro inputValid
  obtain ⟨⟨nextWire, nextProjection⟩, afterNextValid⟩ :=
    nextIH (tokensValidFor_tail inputValid)
  obtain ⟨⟨tailWires, tailProjection⟩, remainingValid⟩ :=
    tailIH afterNextValid
  refine ⟨⟨nextWire :: tailWires, ?_⟩, remainingValid⟩
  simp [nextProjection, tailProjection]

private theorem exprParsesProjectionProperty
    (file : Solcore.Surface.SourceFile)
    {minimum : Nat}
    {input remaining : List Solcore.Surface.Token}
    {expression : Solcore.Surface.Expr}
    (derivation :
      Solcore.Surface.ExprParses minimum input expression remaining) :
    ExprProjectionProperty file minimum input expression remaining :=
  Solcore.Surface.ExprParses.rec
    (motive_1 := fun minimum input expression remaining _ =>
      ExprProjectionProperty file minimum input expression remaining)
    (motive_2 := fun input expression remaining _ =>
      PrefixProjectionProperty file input expression remaining)
    (motive_3 := fun minimum left input expression remaining _ =>
      InfixProjectionProperty file minimum left input expression remaining)
    (motive_4 := fun input arguments right remaining _ =>
      ArgumentsProjectionProperty file input arguments right remaining)
    (motive_5 := fun input arguments right remaining _ =>
      ArgumentTailProjectionProperty file input arguments right remaining)
    (exprConditionalProjectionProperty file)
    (exprOrdinaryProjectionProperty file)
    (prefixNotProjectionProperty file)
    (prefixUnitProjectionProperty file)
    (prefixGroupProjectionProperty file)
    (prefixDecimalProjectionProperty file)
    (prefixHexadecimalProjectionProperty file)
    (prefixNameProjectionProperty file)
    (prefixCallProjectionProperty file)
    (infixStopProjectionProperty file)
    (infixLeftStepProjectionProperty file)
    (infixNonAssociativeStepProjectionProperty file)
    (argumentsEmptyProjectionProperty file)
    (argumentsNonemptyProjectionProperty file)
    (argumentTailDoneProjectionProperty file)
    (argumentTailMoreProjectionProperty file)
    derivation

private theorem typeProjectable_of_parses
    (file : Solcore.Surface.SourceFile)
    {input remaining : List Solcore.Surface.Token}
    {type : Solcore.Surface.TypeSyntax}
    (derivation : Solcore.Surface.TypeParses input type remaining)
    (inputValid : TokensValidFor file input) :
    (∃ wire : TypeSyntax, TypeSyntax.ofSurface? type = some wire) ∧
      TokensValidFor file remaining := by
  cases derivation with
  | unit left right remaining _ _ =>
      refine ⟨⟨.unit
        (SourceSpan.ofSurface
          (Solcore.Surface.SourceSpan.cover left.span right.span)), rfl⟩, ?_⟩
      exact tokensValidFor_tail (tokensValidFor_tail inputValid)
  | bool token remaining _ =>
      refine ⟨⟨.named {
        span := SourceSpan.ofSurface token.span
        text := .bool
      }, rfl⟩, tokensValidFor_tail inputValid⟩
  | word token remaining _ =>
      refine ⟨⟨.named {
        span := SourceSpan.ofSurface token.span
        text := .word
      }, rfl⟩, tokensValidFor_tail inputValid⟩

private theorem letProjectable_of_parses
    (file : Solcore.Surface.SourceFile)
    {input remaining : List Solcore.Surface.Token}
    {statement : Solcore.Surface.LetStatement}
    (derivation : Solcore.Surface.LetParses input statement remaining)
    (inputValid : TokensValidFor file input) :
    (∃ wire : LetStatement, LetStatement.ofSurface? statement = some wire) ∧
      TokensValidFor file remaining := by
  cases derivation with
  | intro letToken nameToken colonToken equalToken semicolonToken nameText
      afterColon afterEqual remaining type value _ nameKind _ typeParse _
      valueParse _ =>
      have nameValid := inputValid nameToken (by simp)
      obtain ⟨nameWire, nameProjection⟩ :=
        nameProjectable_of_validToken
          file nameToken nameText nameValid nameKind
      have afterColonValid :=
        tokensValidFor_tail
          (tokensValidFor_tail (tokensValidFor_tail inputValid))
      obtain ⟨⟨typeWire, typeProjection⟩, afterTypeValid⟩ :=
        typeProjectable_of_parses file typeParse afterColonValid
      obtain ⟨⟨valueWire, valueProjection⟩, afterValueValid⟩ :=
        exprParsesProjectionProperty file valueParse
          (tokensValidFor_tail afterTypeValid)
      refine ⟨⟨{
        span := SourceSpan.ofSurface
          (Solcore.Surface.SourceSpan.cover letToken.span semicolonToken.span)
        name := nameWire
        type := typeWire
        value := valueWire
      }, ?_⟩, tokensValidFor_tail afterValueValid⟩
      simp [LetStatement.ofSurface?, nameProjection, typeProjection,
        valueProjection]

private theorem bindingsProjectable_of_parses
    (file : Solcore.Surface.SourceFile)
    {input remaining : List Solcore.Surface.Token}
    {bindings : List Solcore.Surface.LetStatement}
    (derivation : Solcore.Surface.BindingsParse input bindings remaining)
    (inputValid : TokensValidFor file input) :
    (∃ wires : List LetStatement,
      bindings.mapM LetStatement.ofSurface? = some wires) ∧
      TokensValidFor file remaining := by
  induction derivation with
  | done returnToken remaining _ =>
      exact ⟨⟨[], rfl⟩, inputValid⟩
  | more input afterBinding remaining binding bindings bindingParse tailParse
      tailIH =>
      obtain ⟨⟨bindingWire, bindingProjection⟩, afterBindingValid⟩ :=
        letProjectable_of_parses file bindingParse inputValid
      obtain ⟨⟨bindingWires, bindingsProjection⟩, remainingValid⟩ :=
        tailIH afterBindingValid
      refine ⟨⟨bindingWire :: bindingWires, ?_⟩, remainingValid⟩
      simp [bindingProjection, bindingsProjection]

private theorem returnProjectable_of_parses
    (file : Solcore.Surface.SourceFile)
    {input remaining : List Solcore.Surface.Token}
    {statement : Solcore.Surface.ReturnStatement}
    (derivation : Solcore.Surface.ReturnParses input statement remaining)
    (inputValid : TokensValidFor file input) :
    (∃ wire : ReturnStatement,
      ReturnStatement.ofSurface? statement = some wire) ∧
      TokensValidFor file remaining := by
  cases derivation with
  | intro returnToken semicolonToken afterReturn remaining value _ valueParse _ =>
      obtain ⟨⟨valueWire, valueProjection⟩, afterValueValid⟩ :=
        exprParsesProjectionProperty file valueParse
          (tokensValidFor_tail inputValid)
      refine ⟨⟨{
        span := SourceSpan.ofSurface
          (Solcore.Surface.SourceSpan.cover returnToken.span semicolonToken.span)
        value := valueWire
      }, ?_⟩, tokensValidFor_tail afterValueValid⟩
      simp [ReturnStatement.ofSurface?, valueProjection]

private theorem functionProjectable_of_parses
    (file : Solcore.Surface.SourceFile)
    {input remaining : List Solcore.Surface.Token}
    {declaration : Solcore.Surface.FunctionDecl}
    (derivation :
      Solcore.Surface.FunctionParses input declaration remaining)
    (inputValid : TokensValidFor file input) :
    (∃ wire : FunctionDecl,
      FunctionDecl.ofSurface? declaration = some wire) ∧
      TokensValidFor file remaining := by
  cases derivation with
  | intro functionToken nameToken leftParen rightParen arrow leftBrace
      rightBrace nameText afterArrow afterLeftBrace afterBindings afterResult
      unused returnType bindings result _ nameKind _ _ _ typeParse _
      bindingsParse resultParse _ =>
      have nameValid := inputValid nameToken (by simp)
      obtain ⟨nameWire, nameProjection⟩ :=
        nameProjectable_of_validToken
          file nameToken nameText nameValid nameKind
      have afterArrowValid :=
        tokensValidFor_tail
          (tokensValidFor_tail
            (tokensValidFor_tail
              (tokensValidFor_tail (tokensValidFor_tail inputValid))))
      obtain ⟨⟨returnTypeWire, returnTypeProjection⟩, afterTypeValid⟩ :=
        typeProjectable_of_parses file typeParse afterArrowValid
      obtain ⟨⟨bindingWires, bindingsProjection⟩, afterBindingsValid⟩ :=
        bindingsProjectable_of_parses file bindingsParse
          (tokensValidFor_tail afterTypeValid)
      obtain ⟨⟨resultWire, resultProjection⟩, afterResultValid⟩ :=
        returnProjectable_of_parses file resultParse afterBindingsValid
      refine ⟨⟨{
        span := SourceSpan.ofSurface
          (Solcore.Surface.SourceSpan.cover functionToken.span rightBrace.span)
        name := nameWire
        returnType := returnTypeWire
        bindings := bindingWires
        result := resultWire
      }, ?_⟩, tokensValidFor_tail afterResultValid⟩
      simp [FunctionDecl.ofSurface?, nameProjection, returnTypeProjection,
        bindingsProjection, resultProjection]

private theorem commentsProjectable
    (comments : List Solcore.Surface.Comment) :
    ∃ wires : List Comment, comments.mapM Comment.ofSurface? = some wires := by
  induction comments with
  | nil => exact ⟨[], rfl⟩
  | cons comment comments inductionHypothesis =>
      obtain ⟨wires, projection⟩ := inductionHypothesis
      cases comment with
      | mk kind span =>
          cases kind <;>
            simp [Comment.ofSurface?, CommentKind.ofSurface?, projection]

namespace File

/--
Independent lexical and complete-file grammar derivations make the internal
Surface result representable by the closed v1 wire syntax.
-/
theorem projectable_of_lexes_of_fileParses
    (file : Solcore.Surface.SourceFile)
    {lexed : Solcore.Surface.Lexed}
    {parsed : Solcore.Surface.ParsedFile}
    (lexes : Solcore.Surface.LexicalGrammar.Lexes file lexed)
    (derivation : Solcore.Surface.FileParses lexed parsed) :
    ∃ wire : File, File.ofSurface? parsed = some wire := by
  cases derivation with
  | intro tokens comments declaration functionParse =>
      obtain ⟨⟨functionWire, functionProjection⟩, _⟩ :=
        functionProjectable_of_parses file functionParse lexes.1.1
      obtain ⟨commentWires, commentsProjection⟩ :=
        commentsProjectable comments
      refine ⟨{
        span := SourceSpan.ofSurface declaration.span
        function := functionWire
        comments := commentWires
      }, ?_⟩
      simp [File.ofSurface?, functionProjection, commentsProjection]

/-- Every successful public Surface parse has an exact v1 projection witness. -/
theorem projectable_of_parse_success
    (file : Solcore.Surface.SourceFile)
    (parsed : Solcore.Surface.ParsedFile)
    (success : Solcore.Surface.Parser.parse file = .ok parsed) :
    ∃ wire : File, File.ofSurface? parsed = some wire := by
  obtain ⟨lexed, lexing, derivation⟩ :=
    Solcore.Surface.Parser.parse_success_fileParses file parsed success
  exact projectable_of_lexes_of_fileParses file
    (Solcore.Surface.Lexer.lex_success_lexes file lexed lexing)
    derivation

end File

end Solcore.Surface.Wire.V1
