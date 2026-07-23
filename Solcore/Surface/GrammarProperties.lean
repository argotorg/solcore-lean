import Solcore.Surface.Grammar

set_option autoImplicit false

namespace Solcore.Surface

namespace BinaryBinding

/-- The declarative binding table assigns one interpretation to each token. -/
theorem functional
    {kind : TokenKind}
    {firstOperator secondOperator : BinaryOp}
    {firstPrecedence secondPrecedence : Nat}
    {firstAssociativity secondAssociativity : Associativity}
    (first :
      BinaryBinding kind firstOperator firstPrecedence firstAssociativity)
    (second :
      BinaryBinding kind secondOperator secondPrecedence secondAssociativity) :
    firstOperator = secondOperator ∧
      firstPrecedence = secondPrecedence ∧
      firstAssociativity = secondAssociativity := by
  cases first <;> cases second <;> simp

end BinaryBinding

namespace BinaryOp

/--
The executable operator metadata agrees with the independent declarative
binding table.
-/
theorem has_binding (operator : BinaryOp) :
    BinaryBinding operator.tokenKind operator operator.precedence
      operator.associativity := by
  cases operator <;> constructor

end BinaryOp

namespace InfixBlocked

theorem contradicts_binding
    {minimum precedence : Nat}
    {token : Token}
    {tail : List Token}
    {operator : BinaryOp}
    {associativity : Associativity}
    (blocked : InfixBlocked minimum (token :: tail))
    (binding :
      BinaryBinding token.kind operator precedence associativity)
    (eligible : minimum ≤ precedence) :
    False :=
  Nat.not_le_of_gt
    (blocked token tail operator precedence associativity rfl binding)
    eligible

end InfixBlocked

namespace HeadPrecedenceNe

theorem contradicts_binding
    {precedence : Nat}
    {token : Token}
    {tail : List Token}
    {operator : BinaryOp}
    {associativity : Associativity}
    (different : HeadPrecedenceNe precedence (token :: tail))
    (binding :
      BinaryBinding token.kind operator precedence associativity) :
    False :=
  different token tail operator precedence associativity rfl binding rfl

end HeadPrecedenceNe

namespace HeadKindNe

theorem contradicts_head
    {kind : TokenKind}
    {token : Token}
    {tail : List Token}
    (different : HeadKindNe kind (token :: tail))
    (kindEquals : token.kind = kind) :
    False :=
  different token tail rfl kindEquals

end HeadKindNe

private theorem ExprParses.cannot_start_with_right_paren
    {minimum : Nat}
    {token : Token}
    {tail remaining : List Token}
    {expression : Expr}
    (parse : ExprParses minimum (token :: tail) expression remaining)
    (rightParenKind : token.kind = .rightParen) :
    False := by
  cases parse with
  | conditional =>
      simp_all
  | ordinary _ _ _ _ _ _ prefixParse _ =>
      cases prefixParse <;> simp_all

private def ExprDeterministic
    (minimum : Nat)
    (input : List Token)
    (firstExpression : Expr)
    (firstRest : List Token) : Prop :=
    ∀ {secondExpression secondRest},
      ExprParses minimum input secondExpression secondRest →
        firstExpression = secondExpression ∧ firstRest = secondRest

private def PrefixDeterministic
    (input : List Token)
    (firstExpression : Expr)
    (firstRest : List Token) : Prop :=
  ∀ {secondExpression secondRest},
    PrefixParses input secondExpression secondRest →
      firstExpression = secondExpression ∧ firstRest = secondRest

private def InfixDeterministic
    (minimum : Nat)
    (left : Expr)
    (input : List Token)
    (firstExpression : Expr)
    (firstRest : List Token) : Prop :=
  ∀ {secondExpression secondRest},
    InfixParses minimum left input secondExpression secondRest →
      firstExpression = secondExpression ∧ firstRest = secondRest

private def ArgumentsDeterministic
    (input : List Token)
    (firstArguments : List Expr)
    (firstRight : Token)
    (firstRest : List Token) : Prop :=
  ∀ {secondArguments secondRight secondRest},
    ArgumentsParse input secondArguments secondRight secondRest →
      firstArguments = secondArguments ∧
        firstRight = secondRight ∧ firstRest = secondRest

private def ArgumentTailDeterministic
    (input : List Token)
    (firstArguments : List Expr)
    (firstRight : Token)
    (firstRest : List Token) : Prop :=
  ∀ {secondArguments secondRight secondRest},
    ArgumentTailParses input secondArguments secondRight secondRest →
      firstArguments = secondArguments ∧
        firstRight = secondRight ∧ firstRest = secondRest

private theorem exprConditionalDeterministic
    (ifToken thenToken elseToken : Token)
    (afterIf afterThen afterElse remaining : List Token)
    (condition thenBranch elseBranch : Expr)
    (ifKind : ifToken.kind = .keywordIf)
    (conditionParse :
      ExprParses 0 afterIf condition (thenToken :: afterThen))
    (_thenKind : thenToken.kind = .identifier "then")
    (_thenParse :
      ExprParses 0 afterThen thenBranch (elseToken :: afterElse))
    (_elseKind : elseToken.kind = .keywordElse)
    (_elseParse :
      ExprParses 0 afterElse elseBranch remaining)
    (conditionIH :
      ExprDeterministic 0 afterIf condition (thenToken :: afterThen))
    (thenIH :
      ExprDeterministic 0 afterThen thenBranch (elseToken :: afterElse))
    (elseIH :
      ExprDeterministic 0 afterElse elseBranch remaining) :
    ExprDeterministic 0
      (ifToken :: afterIf)
      (.ifThenElse
        (SourceSpan.cover ifToken.span elseBranch.span)
        condition thenBranch elseBranch)
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | conditional _ _ _ _ _ _ _ secondCondition secondThenBranch
      secondElseBranch _ secondConditionParse _ secondThenParse _
      secondElseParse =>
      rcases conditionIH secondConditionParse with
        ⟨conditionEquals, conditionRestEquals⟩
      cases conditionEquals
      cases conditionRestEquals
      rcases thenIH secondThenParse with
        ⟨thenBranchEquals, thenRestEquals⟩
      cases thenBranchEquals
      cases thenRestEquals
      rcases elseIH secondElseParse with
        ⟨elseBranchEquals, restEquals⟩
      cases elseBranchEquals
      exact ⟨rfl, restEquals⟩
  | ordinary _ _ _ _ _ _ secondPrefixParse _ =>
      cases secondPrefixParse <;> simp_all

private theorem exprOrdinaryDeterministic
    (minimum : Nat)
    (input afterPrefix remaining : List Token)
    (initial result : Expr)
    (prefixParse : PrefixParses input initial afterPrefix)
    (infixParse :
      InfixParses minimum initial afterPrefix result remaining)
    (prefixIH :
      PrefixDeterministic input initial afterPrefix)
    (infixIH :
      InfixDeterministic minimum initial afterPrefix result remaining) :
    ExprDeterministic minimum input result remaining := by
  intro secondExpression secondRest second
  cases second with
  | conditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ =>
      cases prefixParse <;> simp_all
  | ordinary _ _ _ _ _ _ secondPrefixParse secondInfixParse =>
      rcases prefixIH secondPrefixParse with
        ⟨initialEquals, prefixRestEquals⟩
      cases initialEquals
      cases prefixRestEquals
      exact infixIH secondInfixParse

private theorem prefixNotDeterministic
    (operatorToken : Token)
    (afterOperator remaining : List Token)
    (operand : Expr)
    (operatorKind : operatorToken.kind = .bang)
    (operandParse : PrefixParses afterOperator operand remaining)
    (operandIH :
      PrefixDeterministic afterOperator operand remaining) :
    PrefixDeterministic
      (operatorToken :: afterOperator)
      (.unary
        (SourceSpan.cover operatorToken.span operand.span)
        { value := .not, span := operatorToken.span }
        operand)
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | not _ _ _ secondOperand _ secondOperandParse =>
      rcases operandIH secondOperandParse with
        ⟨operandEquals, restEquals⟩
      cases operandEquals
      exact ⟨rfl, restEquals⟩
  | unit => simp_all
  | group => simp_all
  | decimal => simp_all
  | hexadecimal => simp_all
  | name => simp_all
  | call => simp_all

private theorem prefixUnitDeterministic
    (left right : Token)
    (remaining : List Token)
    (leftKind : left.kind = .leftParen)
    (rightKind : right.kind = .rightParen) :
    PrefixDeterministic
      (left :: right :: remaining)
      (.unit (SourceSpan.cover left.span right.span))
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | not => simp_all
  | unit => exact ⟨rfl, rfl⟩
  | group _ secondRight _ _ _ _ innerParse _ =>
      exact False.elim
        (ExprParses.cannot_start_with_right_paren innerParse rightKind)
  | decimal => simp_all
  | hexadecimal => simp_all
  | name => simp_all
  | call => simp_all

private theorem prefixGroupDeterministic
    (left right : Token)
    (afterLeft remaining : List Token)
    (inner : Expr)
    (leftKind : left.kind = .leftParen)
    (innerParse :
      ExprParses 0 afterLeft inner (right :: remaining))
    (_rightKind : right.kind = .rightParen)
    (innerIH :
      ExprDeterministic 0 afterLeft inner (right :: remaining)) :
    PrefixDeterministic
      (left :: afterLeft)
      (.group (SourceSpan.cover left.span right.span) inner)
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | not => simp_all
  | unit _ immediateRight _ _ immediateRightKind =>
      exact False.elim
        (ExprParses.cannot_start_with_right_paren innerParse
          immediateRightKind)
  | group _ _ _ _ secondInner _ secondInnerParse _ =>
      rcases innerIH secondInnerParse with
        ⟨innerEquals, restEquals⟩
      cases innerEquals
      cases restEquals
      exact ⟨rfl, rfl⟩
  | decimal => simp_all
  | hexadecimal => simp_all
  | name => simp_all
  | call => simp_all

private theorem prefixDecimalDeterministic
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (kind : token.kind = .decimal digits) :
    PrefixDeterministic
      (token :: remaining)
      (.integer { base := .decimal, digits, span := token.span })
      remaining := by
  intro secondExpression secondRest second
  cases second <;> simp_all

private theorem prefixHexadecimalDeterministic
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (kind : token.kind = .hexadecimal digits) :
    PrefixDeterministic
      (token :: remaining)
      (.integer { base := .hexadecimal, digits, span := token.span })
      remaining := by
  intro secondExpression secondRest second
  cases second <;> simp_all

private theorem prefixNameDeterministic
    (token : Token)
    (text : String)
    (remaining : List Token)
    (kind : token.kind = .identifier text)
    (notCall : HeadKindNe .leftParen remaining) :
    PrefixDeterministic
      (token :: remaining)
      (.name { value := text, span := token.span })
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | not => simp_all
  | unit => simp_all
  | group => simp_all
  | decimal => simp_all
  | hexadecimal => simp_all
  | name => simp_all
  | call _ left _ _ _ _ _ _ leftKind _ =>
      exact False.elim
        (HeadKindNe.contradicts_head notCall leftKind)

private theorem prefixCallDeterministic
    (identifier left right : Token)
    (text : String)
    (afterLeft remaining : List Token)
    (arguments : List Expr)
    (identifierKind : identifier.kind = .identifier text)
    (leftKind : left.kind = .leftParen)
    (_argumentsParse :
      ArgumentsParse afterLeft arguments right remaining)
    (argumentsIH :
      ArgumentsDeterministic afterLeft arguments right remaining) :
    PrefixDeterministic
      (identifier :: left :: afterLeft)
      (.call
        (SourceSpan.cover identifier.span right.span)
        { value := text, span := identifier.span }
        arguments)
      remaining := by
  intro secondExpression secondRest second
  cases second with
  | not => simp_all
  | unit => simp_all
  | group => simp_all
  | decimal => simp_all
  | hexadecimal => simp_all
  | name _ _ _ _ secondNotCall =>
      exact False.elim
        (HeadKindNe.contradicts_head secondNotCall leftKind)
  | call _ _ _ secondText _ _ secondArguments secondIdentifierKind _
      secondArgumentsParse =>
      rcases argumentsIH secondArgumentsParse with
        ⟨argumentsEqual, rightEqual, restEqual⟩
      have textEqual : text = secondText := by
        rw [identifierKind] at secondIdentifierKind
        exact TokenKind.identifier.inj secondIdentifierKind
      cases textEqual
      cases argumentsEqual
      cases rightEqual
      exact ⟨rfl, restEqual⟩

private theorem infixStopDeterministic
    (minimum : Nat)
    (left : Expr)
    (tokens : List Token)
    (blocked : InfixBlocked minimum tokens) :
    InfixDeterministic minimum left tokens left tokens := by
  intro secondExpression secondRest second
  cases second with
  | stop => exact ⟨rfl, rfl⟩
  | leftStep _ _ _ _ _ _ _ _ _ _ binding eligible _ _ =>
      exact False.elim
        (InfixBlocked.contradicts_binding blocked binding eligible)
  | nonAssociativeStep _ _ _ _ _ _ _ _ _ _ binding eligible _ _ _ =>
      exact False.elim
        (InfixBlocked.contradicts_binding blocked binding eligible)

private theorem infixLeftStepDeterministic
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding :
      BinaryBinding operatorToken.kind operator precedence .left)
    (eligible : minimum ≤ precedence)
    (_rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (_tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH :
      ExprDeterministic (precedence + 1) afterOperator right afterRight)
    (tailIH :
      InfixDeterministic minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixDeterministic minimum left
      (operatorToken :: afterOperator) result remaining := by
  intro secondExpression secondRest second
  cases second with
  | stop _ _ _ secondBlocked =>
      exact False.elim
        (InfixBlocked.contradicts_binding secondBlocked binding eligible)
  | leftStep _ secondPrecedence _ secondRight _ _ secondOperator _
      secondAfterRight _ secondBinding _ secondRightParse
      secondTailParse =>
      rcases BinaryBinding.functional binding secondBinding with
        ⟨operatorEquals, precedenceEquals, _⟩
      cases operatorEquals
      cases precedenceEquals
      rcases rightIH secondRightParse with
        ⟨rightEquals, rightRestEquals⟩
      cases rightEquals
      cases rightRestEquals
      exact tailIH secondTailParse
  | nonAssociativeStep _ _ _ _ _ _ _ _ _ _ secondBinding _ _ _ _ =>
      have associativityEquals :=
        (BinaryBinding.functional binding secondBinding).2.2
      cases associativityEquals

private theorem infixNonAssociativeStepDeterministic
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding :
      BinaryBinding operatorToken.kind operator precedence .nonAssociative)
    (eligible : minimum ≤ precedence)
    (_rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (_notRepeated : HeadPrecedenceNe precedence afterRight)
    (_tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH :
      ExprDeterministic (precedence + 1) afterOperator right afterRight)
    (tailIH :
      InfixDeterministic minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixDeterministic minimum left
      (operatorToken :: afterOperator) result remaining := by
  intro secondExpression secondRest second
  cases second with
  | stop _ _ _ secondBlocked =>
      exact False.elim
        (InfixBlocked.contradicts_binding secondBlocked binding eligible)
  | leftStep _ _ _ _ _ _ _ _ _ _ secondBinding _ _ _ =>
      have associativityEquals :=
        (BinaryBinding.functional binding secondBinding).2.2
      cases associativityEquals
  | nonAssociativeStep _ _ _ secondRight _ _ secondOperator _
      secondAfterRight _ secondBinding _ secondRightParse _
      secondTailParse =>
      rcases BinaryBinding.functional binding secondBinding with
        ⟨operatorEquals, precedenceEquals, _⟩
      cases operatorEquals
      cases precedenceEquals
      rcases rightIH secondRightParse with
        ⟨rightEquals, rightRestEquals⟩
      cases rightEquals
      cases rightRestEquals
      exact tailIH secondTailParse

private theorem argumentsEmptyDeterministic
    (right : Token)
    (remaining : List Token)
    (rightKind : right.kind = .rightParen) :
    ArgumentsDeterministic (right :: remaining) [] right remaining := by
  intro secondArguments secondRight secondRest second
  cases second with
  | empty => exact ⟨rfl, rfl, rfl⟩
  | nonempty _ _ _ _ _ _ firstParse _ =>
      exact False.elim
        (ExprParses.cannot_start_with_right_paren firstParse rightKind)

private theorem argumentsNonemptyDeterministic
    (input afterFirst remaining : List Token)
    (firstExpression : Expr)
    (tail : List Expr)
    (right : Token)
    (firstParse : ExprParses 0 input firstExpression afterFirst)
    (_tailParse :
      ArgumentTailParses afterFirst tail right remaining)
    (firstIH :
      ExprDeterministic 0 input firstExpression afterFirst)
    (tailIH :
      ArgumentTailDeterministic afterFirst tail right remaining) :
    ArgumentsDeterministic input
      (firstExpression :: tail) right remaining := by
  intro secondArguments secondRight secondRest second
  cases second with
  | empty immediateRight _ immediateRightKind =>
      exact False.elim
        (ExprParses.cannot_start_with_right_paren firstParse
          immediateRightKind)
  | nonempty _ _ _ secondFirst secondTail _ secondFirstParse
      secondTailParse =>
      rcases firstIH secondFirstParse with
        ⟨firstEquals, firstRestEquals⟩
      cases firstEquals
      cases firstRestEquals
      rcases tailIH secondTailParse with
        ⟨tailEquals, rightEquals, restEquals⟩
      cases tailEquals
      exact ⟨rfl, rightEquals, restEquals⟩

private theorem argumentTailDoneDeterministic
    (right : Token)
    (remaining : List Token)
    (rightKind : right.kind = .rightParen) :
    ArgumentTailDeterministic
      (right :: remaining) [] right remaining := by
  intro secondArguments secondRight secondRest second
  cases second <;> simp_all

private theorem argumentTailMoreDeterministic
    (comma right : Token)
    (afterComma afterNext remaining : List Token)
    (next : Expr)
    (tail : List Expr)
    (commaKind : comma.kind = .comma)
    (_nextParse : ExprParses 0 afterComma next afterNext)
    (_tailParse :
      ArgumentTailParses afterNext tail right remaining)
    (nextIH :
      ExprDeterministic 0 afterComma next afterNext)
    (tailIH :
      ArgumentTailDeterministic afterNext tail right remaining) :
    ArgumentTailDeterministic
      (comma :: afterComma) (next :: tail) right remaining := by
  intro secondArguments secondRight secondRest second
  cases second with
  | done => simp_all
  | more _ _ _ _ _ secondNext secondTail _ secondNextParse
      secondTailParse =>
      rcases nextIH secondNextParse with
        ⟨nextEquals, nextRestEquals⟩
      cases nextEquals
      cases nextRestEquals
      rcases tailIH secondTailParse with
        ⟨tailEquals, rightEquals, restEquals⟩
      cases tailEquals
      exact ⟨rfl, rightEquals, restEquals⟩

private theorem exprParsesDeterministic
    {minimum : Nat}
    {input : List Token}
    {firstExpression : Expr}
    {firstRest : List Token}
    (first :
      ExprParses minimum input firstExpression firstRest) :
    ExprDeterministic minimum input firstExpression firstRest :=
  ExprParses.rec
    (motive_1 := fun minimum input expression rest _ =>
      ExprDeterministic minimum input expression rest)
    (motive_2 := fun input expression rest _ =>
      PrefixDeterministic input expression rest)
    (motive_3 := fun minimum left input expression rest _ =>
      InfixDeterministic minimum left input expression rest)
    (motive_4 := fun input arguments right rest _ =>
      ArgumentsDeterministic input arguments right rest)
    (motive_5 := fun input arguments right rest _ =>
      ArgumentTailDeterministic input arguments right rest)
    exprConditionalDeterministic
    exprOrdinaryDeterministic
    prefixNotDeterministic
    prefixUnitDeterministic
    prefixGroupDeterministic
    prefixDecimalDeterministic
    prefixHexadecimalDeterministic
    prefixNameDeterministic
    prefixCallDeterministic
    infixStopDeterministic
    infixLeftStepDeterministic
    infixNonAssociativeStepDeterministic
    argumentsEmptyDeterministic
    argumentsNonemptyDeterministic
    argumentTailDoneDeterministic
    argumentTailMoreDeterministic
    first

private theorem prefixParsesDeterministic
    {input : List Token}
    {firstExpression : Expr}
    {firstRest : List Token}
    (first :
      PrefixParses input firstExpression firstRest) :
    PrefixDeterministic input firstExpression firstRest :=
  PrefixParses.rec
    (motive_1 := fun minimum input expression rest _ =>
      ExprDeterministic minimum input expression rest)
    (motive_2 := fun input expression rest _ =>
      PrefixDeterministic input expression rest)
    (motive_3 := fun minimum left input expression rest _ =>
      InfixDeterministic minimum left input expression rest)
    (motive_4 := fun input arguments right rest _ =>
      ArgumentsDeterministic input arguments right rest)
    (motive_5 := fun input arguments right rest _ =>
      ArgumentTailDeterministic input arguments right rest)
    exprConditionalDeterministic
    exprOrdinaryDeterministic
    prefixNotDeterministic
    prefixUnitDeterministic
    prefixGroupDeterministic
    prefixDecimalDeterministic
    prefixHexadecimalDeterministic
    prefixNameDeterministic
    prefixCallDeterministic
    infixStopDeterministic
    infixLeftStepDeterministic
    infixNonAssociativeStepDeterministic
    argumentsEmptyDeterministic
    argumentsNonemptyDeterministic
    argumentTailDoneDeterministic
    argumentTailMoreDeterministic
    first

private theorem infixParsesDeterministic
    {minimum : Nat}
    {left : Expr}
    {input : List Token}
    {firstExpression : Expr}
    {firstRest : List Token}
    (first :
      InfixParses minimum left input firstExpression firstRest) :
    InfixDeterministic minimum left input firstExpression firstRest :=
  InfixParses.rec
    (motive_1 := fun minimum input expression rest _ =>
      ExprDeterministic minimum input expression rest)
    (motive_2 := fun input expression rest _ =>
      PrefixDeterministic input expression rest)
    (motive_3 := fun minimum left input expression rest _ =>
      InfixDeterministic minimum left input expression rest)
    (motive_4 := fun input arguments right rest _ =>
      ArgumentsDeterministic input arguments right rest)
    (motive_5 := fun input arguments right rest _ =>
      ArgumentTailDeterministic input arguments right rest)
    exprConditionalDeterministic
    exprOrdinaryDeterministic
    prefixNotDeterministic
    prefixUnitDeterministic
    prefixGroupDeterministic
    prefixDecimalDeterministic
    prefixHexadecimalDeterministic
    prefixNameDeterministic
    prefixCallDeterministic
    infixStopDeterministic
    infixLeftStepDeterministic
    infixNonAssociativeStepDeterministic
    argumentsEmptyDeterministic
    argumentsNonemptyDeterministic
    argumentTailDoneDeterministic
    argumentTailMoreDeterministic
    first

private theorem argumentsParseDeterministic
    {input : List Token}
    {firstArguments : List Expr}
    {firstRight : Token}
    {firstRest : List Token}
    (first :
      ArgumentsParse input firstArguments firstRight firstRest) :
    ArgumentsDeterministic input firstArguments firstRight firstRest :=
  ArgumentsParse.rec
    (motive_1 := fun minimum input expression rest _ =>
      ExprDeterministic minimum input expression rest)
    (motive_2 := fun input expression rest _ =>
      PrefixDeterministic input expression rest)
    (motive_3 := fun minimum left input expression rest _ =>
      InfixDeterministic minimum left input expression rest)
    (motive_4 := fun input arguments right rest _ =>
      ArgumentsDeterministic input arguments right rest)
    (motive_5 := fun input arguments right rest _ =>
      ArgumentTailDeterministic input arguments right rest)
    exprConditionalDeterministic
    exprOrdinaryDeterministic
    prefixNotDeterministic
    prefixUnitDeterministic
    prefixGroupDeterministic
    prefixDecimalDeterministic
    prefixHexadecimalDeterministic
    prefixNameDeterministic
    prefixCallDeterministic
    infixStopDeterministic
    infixLeftStepDeterministic
    infixNonAssociativeStepDeterministic
    argumentsEmptyDeterministic
    argumentsNonemptyDeterministic
    argumentTailDoneDeterministic
    argumentTailMoreDeterministic
    first

private theorem argumentTailParsesDeterministic
    {input : List Token}
    {firstArguments : List Expr}
    {firstRight : Token}
    {firstRest : List Token}
    (first :
      ArgumentTailParses input firstArguments firstRight firstRest) :
    ArgumentTailDeterministic input firstArguments firstRight firstRest :=
  ArgumentTailParses.rec
    (motive_1 := fun minimum input expression rest _ =>
      ExprDeterministic minimum input expression rest)
    (motive_2 := fun input expression rest _ =>
      PrefixDeterministic input expression rest)
    (motive_3 := fun minimum left input expression rest _ =>
      InfixDeterministic minimum left input expression rest)
    (motive_4 := fun input arguments right rest _ =>
      ArgumentsDeterministic input arguments right rest)
    (motive_5 := fun input arguments right rest _ =>
      ArgumentTailDeterministic input arguments right rest)
    exprConditionalDeterministic
    exprOrdinaryDeterministic
    prefixNotDeterministic
    prefixUnitDeterministic
    prefixGroupDeterministic
    prefixDecimalDeterministic
    prefixHexadecimalDeterministic
    prefixNameDeterministic
    prefixCallDeterministic
    infixStopDeterministic
    infixLeftStepDeterministic
    infixNonAssociativeStepDeterministic
    argumentsEmptyDeterministic
    argumentsNonemptyDeterministic
    argumentTailDoneDeterministic
    argumentTailMoreDeterministic
    first

namespace ExprParses

/-- The declarative expression grammar has at most one result and remainder. -/
theorem deterministic
    {minimum : Nat}
    {input : List Token}
    {firstExpression secondExpression : Expr}
    {firstRest secondRest : List Token}
    (first :
      ExprParses minimum input firstExpression firstRest)
    (second :
      ExprParses minimum input secondExpression secondRest) :
    firstExpression = secondExpression ∧ firstRest = secondRest :=
  exprParsesDeterministic first second

end ExprParses

namespace PrefixParses

/-- Prefix parsing has at most one result and remainder. -/
theorem deterministic
    {input : List Token}
    {firstExpression secondExpression : Expr}
    {firstRest secondRest : List Token}
    (first :
      PrefixParses input firstExpression firstRest)
    (second :
      PrefixParses input secondExpression secondRest) :
    firstExpression = secondExpression ∧ firstRest = secondRest :=
  prefixParsesDeterministic first second

end PrefixParses

namespace InfixParses

/-- Infix parsing is deterministic for a fixed minimum and left operand. -/
theorem deterministic
    {minimum : Nat}
    {left : Expr}
    {input : List Token}
    {firstExpression secondExpression : Expr}
    {firstRest secondRest : List Token}
    (first :
      InfixParses minimum left input firstExpression firstRest)
    (second :
      InfixParses minimum left input secondExpression secondRest) :
    firstExpression = secondExpression ∧ firstRest = secondRest :=
  infixParsesDeterministic first second

end InfixParses

namespace ArgumentsParse

/-- Argument parsing uniquely determines arguments, closing token, and rest. -/
theorem deterministic
    {input : List Token}
    {firstArguments secondArguments : List Expr}
    {firstRight secondRight : Token}
    {firstRest secondRest : List Token}
    (first :
      ArgumentsParse input firstArguments firstRight firstRest)
    (second :
      ArgumentsParse input secondArguments secondRight secondRest) :
    firstArguments = secondArguments ∧
      firstRight = secondRight ∧ firstRest = secondRest :=
  argumentsParseDeterministic first second

end ArgumentsParse

namespace ArgumentTailParses

/--
Argument-tail parsing uniquely determines arguments, closing token, and rest.
-/
theorem deterministic
    {input : List Token}
    {firstArguments secondArguments : List Expr}
    {firstRight secondRight : Token}
    {firstRest secondRest : List Token}
    (first :
      ArgumentTailParses input firstArguments firstRight firstRest)
    (second :
      ArgumentTailParses input secondArguments secondRight secondRest) :
    firstArguments = secondArguments ∧
      firstRight = secondRight ∧ firstRest = secondRest :=
  argumentTailParsesDeterministic first second

end ArgumentTailParses

namespace TypeParses

/-- Type parsing has at most one result and remainder. -/
theorem deterministic
    {input : List Token}
    {firstType secondType : TypeSyntax}
    {firstRest secondRest : List Token}
    (first : TypeParses input firstType firstRest)
    (second : TypeParses input secondType secondRest) :
    firstType = secondType ∧ firstRest = secondRest := by
  cases first <;> cases second <;> simp_all

end TypeParses

namespace LetParses

/-- A let-statement input has at most one statement and remainder. -/
theorem deterministic
    {input : List Token}
    {firstStatement secondStatement : LetStatement}
    {firstRest secondRest : List Token}
    (first : LetParses input firstStatement firstRest)
    (second : LetParses input secondStatement secondRest) :
    firstStatement = secondStatement ∧ firstRest = secondRest := by
  cases first with
  | intro letToken nameToken colonToken equalToken semicolonToken
      nameText afterColon afterEqual remaining type value letKind nameKind
      colonKind typeParse equalKind valueParse semicolonKind =>
      cases second with
      | intro _ _ _ secondEqualToken secondSemicolonToken secondNameText
          _ secondAfterEqual _ secondType secondValue _ secondNameKind _
          secondTypeParse secondEqualKind secondValueParse
          secondSemicolonKind =>
          have nameEqual : nameText = secondNameText := by
            rw [nameKind] at secondNameKind
            exact TokenKind.identifier.inj secondNameKind
          cases nameEqual
          rcases TypeParses.deterministic typeParse secondTypeParse with
            ⟨typeEqual, typeRestEqual⟩
          cases typeEqual
          cases typeRestEqual
          rcases ExprParses.deterministic valueParse secondValueParse with
            ⟨valueEqual, valueRestEqual⟩
          cases valueEqual
          cases valueRestEqual
          exact ⟨rfl, rfl⟩

end LetParses

namespace BindingsParse

/-- A binding sequence uniquely determines its statements and remainder. -/
theorem deterministic
    {input : List Token}
    {firstBindings secondBindings : List LetStatement}
    {firstRest secondRest : List Token}
    (first :
      BindingsParse input firstBindings firstRest)
    (second :
      BindingsParse input secondBindings secondRest) :
    firstBindings = secondBindings ∧ firstRest = secondRest := by
  revert secondBindings secondRest
  induction first with
  | done returnToken remaining returnKind =>
      intro secondBindings secondRest second
      cases second with
      | done => exact ⟨rfl, rfl⟩
      | more _ _ _ _ _ bindingParse _ =>
          cases bindingParse
          simp_all
  | more input afterBinding remaining binding bindings bindingParse
      tailParse tailIH =>
      intro secondBindings secondRest second
      cases second with
      | done _ _ returnKind =>
          cases bindingParse
          simp_all
      | more _ secondAfterBinding _ secondBinding secondBindings
          secondBindingParse secondTailParse =>
          rcases LetParses.deterministic bindingParse secondBindingParse with
            ⟨bindingEqual, bindingRestEqual⟩
          cases bindingEqual
          cases bindingRestEqual
          rcases tailIH secondTailParse with
            ⟨bindingsEqual, restEqual⟩
          cases bindingsEqual
          exact ⟨rfl, restEqual⟩

end BindingsParse

namespace ReturnParses

/-- A return-statement input has at most one statement and remainder. -/
theorem deterministic
    {input : List Token}
    {firstStatement secondStatement : ReturnStatement}
    {firstRest secondRest : List Token}
    (first : ReturnParses input firstStatement firstRest)
    (second : ReturnParses input secondStatement secondRest) :
    firstStatement = secondStatement ∧ firstRest = secondRest := by
  cases first with
  | intro returnToken semicolonToken afterReturn remaining value returnKind
      valueParse semicolonKind =>
      cases second with
      | intro _ secondSemicolonToken _ _ secondValue _ secondValueParse
          secondSemicolonKind =>
          rcases ExprParses.deterministic valueParse secondValueParse with
            ⟨valueEqual, valueRestEqual⟩
          cases valueEqual
          cases valueRestEqual
          exact ⟨rfl, rfl⟩

end ReturnParses

namespace FunctionParses

/-- A function input has at most one declaration and remainder. -/
theorem deterministic
    {input : List Token}
    {firstDeclaration secondDeclaration : FunctionDecl}
    {firstRest secondRest : List Token}
    (first :
      FunctionParses input firstDeclaration firstRest)
    (second :
      FunctionParses input secondDeclaration secondRest) :
    firstDeclaration = secondDeclaration ∧ firstRest = secondRest := by
  cases first with
  | intro functionToken nameToken leftParen rightParen arrow leftBrace
      rightBrace nameText afterArrow afterLeftBrace afterBindings afterResult
      remaining returnType bindings result functionKind nameKind leftParenKind
      rightParenKind arrowKind typeParse leftBraceKind bindingsParse
      resultParse rightBraceKind =>
      cases second with
      | intro _ _ _ _ _ secondLeftBrace secondRightBrace secondNameText _
          secondAfterLeftBrace secondAfterBindings secondAfterResult _
          secondReturnType secondBindings secondResult _ secondNameKind _ _ _
          secondTypeParse secondLeftBraceKind secondBindingsParse
          secondResultParse secondRightBraceKind =>
          have nameEqual : nameText = secondNameText := by
            rw [nameKind] at secondNameKind
            exact TokenKind.identifier.inj secondNameKind
          cases nameEqual
          rcases TypeParses.deterministic typeParse secondTypeParse with
            ⟨typeEqual, typeRestEqual⟩
          cases typeEqual
          cases typeRestEqual
          rcases BindingsParse.deterministic bindingsParse
              secondBindingsParse with
            ⟨bindingsEqual, bindingsRestEqual⟩
          cases bindingsEqual
          cases bindingsRestEqual
          rcases ReturnParses.deterministic resultParse secondResultParse with
            ⟨resultEqual, resultRestEqual⟩
          cases resultEqual
          cases resultRestEqual
          exact ⟨rfl, rfl⟩

end FunctionParses

namespace FileParses

/-- A fully consumed lexed file has at most one parsed file. -/
theorem deterministic
    {lexed : Lexed}
    {firstParsed secondParsed : ParsedFile}
    (first : FileParses lexed firstParsed)
    (second : FileParses lexed secondParsed) :
    firstParsed = secondParsed := by
  cases first with
  | intro tokens comments firstDeclaration firstFunctionParse =>
      cases second with
      | intro _ _ secondDeclaration secondFunctionParse =>
          have declarationEqual :=
            (FunctionParses.deterministic firstFunctionParse
              secondFunctionParse).1
          cases declarationEqual
          rfl

end FileParses

end Solcore.Surface
