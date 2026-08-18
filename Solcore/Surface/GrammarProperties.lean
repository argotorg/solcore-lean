import Solcore.Surface.Grammar
import Solcore.Surface.LexicalGrammar

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

private def InfixAdmissible (left : Expr) (input : List Token) : Prop :=
  ∀ (token : Token) (tail : List Token) (operator : BinaryOp)
      (precedence : Nat) (associativity : Associativity),
    input = token :: tail →
      BinaryBinding token.kind operator precedence associativity →
        match associativity with
        | .left => precedence ≤ left.outerPrecedence
        | .nonAssociative => precedence < left.outerPrecedence

private def ExprGrammarProperty
    (minimum : Nat)
    (_input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  expression.GrammarValid ∧
    InfixBlocked minimum remaining ∧
    (minimum ≤ 8 → minimum ≤ expression.outerPrecedence)

private def PrefixGrammarProperty
    (_input : List Token)
    (expression : Expr)
    (_remaining : List Token) : Prop :=
  expression.GrammarValid ∧ 8 ≤ expression.outerPrecedence

private def InfixGrammarProperty
    (minimum : Nat)
    (left : Expr)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  left.GrammarValid →
    InfixAdmissible left input →
    expression.GrammarValid ∧
      InfixBlocked minimum remaining ∧
      (minimum ≤ left.outerPrecedence →
        minimum ≤ expression.outerPrecedence)

private def ArgumentsGrammarProperty
    (_input : List Token)
    (arguments : List Expr)
    (_right : Token)
    (_remaining : List Token) : Prop :=
  ∀ argument ∈ arguments, argument.GrammarValid

private def ArgumentTailGrammarProperty
    (_input : List Token)
    (arguments : List Expr)
    (_right : Token)
    (_remaining : List Token) : Prop :=
  ∀ argument ∈ arguments, argument.GrammarValid

private theorem binaryBinding_precedence_lt_eight
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    {associativity : Associativity}
    (binding :
      BinaryBinding kind operator precedence associativity) :
    precedence < 8 := by
  cases binding <;> omega

private theorem binaryBinding_precedence_eq
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    {associativity : Associativity}
    (binding :
      BinaryBinding kind operator precedence associativity) :
    operator.precedence = precedence := by
  cases binding <;> rfl

private theorem binaryBinding_kind_eq
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    {associativity : Associativity}
    (binding :
      BinaryBinding kind operator precedence associativity) :
    kind = operator.tokenKind := by
  cases binding <;> rfl

private theorem nonAssociative_precedence_lt_of_left_binding
    {firstKind secondKind : TokenKind}
    {firstOperator secondOperator : BinaryOp}
    {firstPrecedence secondPrecedence : Nat}
    (firstBinding :
      BinaryBinding firstKind firstOperator firstPrecedence .left)
    (secondBinding :
      BinaryBinding secondKind secondOperator secondPrecedence
        .nonAssociative)
    (precedenceLe : secondPrecedence ≤ firstPrecedence) :
    secondPrecedence < firstPrecedence := by
  cases firstBinding <;> cases secondBinding <;> omega

private theorem exprUnitGrammarValid (span : SourceSpan) :
    (Expr.unit span).GrammarValid := by
  simp [Expr.GrammarValid, Expr.allExpressions,
    Expr.LocallyGrammarValid]

private theorem exprIntegerGrammarValid (literal : IntegerLiteral) :
    (Expr.integer literal).GrammarValid := by
  simp [Expr.GrammarValid, Expr.allExpressions,
    Expr.LocallyGrammarValid]

private theorem exprNameGrammarValid (name : Name) :
    (Expr.name name).GrammarValid := by
  simp [Expr.GrammarValid, Expr.allExpressions,
    Expr.LocallyGrammarValid]

private theorem exprGroupGrammarValid
    (span : SourceSpan)
    (inner : Expr)
    (innerValid : inner.GrammarValid) :
    (Expr.group span inner).GrammarValid := by
  intro expression member
  simp only [Expr.allExpressions, List.mem_cons] at member
  rcases member with rfl | member
  · simp [Expr.LocallyGrammarValid]
  · exact innerValid expression member

private theorem exprCallGrammarValid
    (span : SourceSpan)
    (callee : Name)
    (arguments : List Expr)
    (argumentsValid :
      ∀ argument ∈ arguments, argument.GrammarValid) :
    (Expr.call span callee arguments).GrammarValid := by
  intro expression member
  simp only [Expr.allExpressions, List.mem_cons,
    List.mem_flatMap] at member
  rcases member with rfl | ⟨argument, argumentMember, expressionMember⟩
  · simp [Expr.LocallyGrammarValid]
  · exact argumentsValid argument argumentMember expression expressionMember

private theorem exprUnaryGrammarValid
    (span : SourceSpan)
    (operator : Located UnaryOp)
    (operand : Expr)
    (operandValid : operand.GrammarValid)
    (operandBound : 8 ≤ operand.outerPrecedence) :
    (Expr.unary span operator operand).GrammarValid := by
  intro expression member
  simp only [Expr.allExpressions, List.mem_cons] at member
  rcases member with rfl | member
  · simpa [Expr.LocallyGrammarValid] using operandBound
  · exact operandValid expression member

private theorem exprBinaryGrammarValid
    (span : SourceSpan)
    (operator : Located BinaryOp)
    (left right : Expr)
    (leftValid : left.GrammarValid)
    (rightValid : right.GrammarValid)
    (localValid :
      (Expr.binary span operator left right).LocallyGrammarValid) :
    (Expr.binary span operator left right).GrammarValid := by
  intro expression member
  simp only [Expr.allExpressions, List.mem_cons,
    List.mem_append] at member
  rcases member with (rfl | member) | member
  · exact localValid
  · exact leftValid expression member
  · exact rightValid expression member

private theorem exprConditionalGrammarValid
    (span : SourceSpan)
    (condition thenBranch elseBranch : Expr)
    (conditionValid : condition.GrammarValid)
    (thenValid : thenBranch.GrammarValid)
    (elseValid : elseBranch.GrammarValid) :
    (Expr.ifThenElse span condition thenBranch elseBranch).GrammarValid := by
  intro expression member
  simp only [Expr.allExpressions, List.mem_cons,
    List.mem_append] at member
  rcases member with ((rfl | member) | member) | member
  · simp [Expr.LocallyGrammarValid]
  · exact conditionValid expression member
  · exact thenValid expression member
  · exact elseValid expression member

private theorem exprConditionalGrammarProperty
    (ifToken thenToken elseToken : Token)
    (afterIf afterThen afterElse remaining : List Token)
    (condition thenBranch elseBranch : Expr)
    (_ifKind : ifToken.kind = .keywordIf)
    (_conditionParse :
      ExprParses 0 afterIf condition (thenToken :: afterThen))
    (_thenKind : thenToken.kind = .identifier "then")
    (_thenParse :
      ExprParses 0 afterThen thenBranch (elseToken :: afterElse))
    (_elseKind : elseToken.kind = .keywordElse)
    (_elseParse :
      ExprParses 0 afterElse elseBranch remaining)
    (conditionIH :
      ExprGrammarProperty 0 afterIf condition (thenToken :: afterThen))
    (thenIH :
      ExprGrammarProperty 0 afterThen thenBranch (elseToken :: afterElse))
    (elseIH :
      ExprGrammarProperty 0 afterElse elseBranch remaining) :
    ExprGrammarProperty 0 (ifToken :: afterIf)
      (.ifThenElse
        (SourceSpan.cover ifToken.span elseBranch.span)
        condition thenBranch elseBranch)
      remaining := by
  refine ⟨?_, elseIH.2.1, ?_⟩
  · exact exprConditionalGrammarValid _ condition thenBranch elseBranch
      conditionIH.1 thenIH.1 elseIH.1
  · intro _
    simp [Expr.outerPrecedence]

private theorem exprOrdinaryGrammarProperty
    (minimum : Nat)
    (input afterPrefix remaining : List Token)
    (initial result : Expr)
    (_prefixParse : PrefixParses input initial afterPrefix)
    (_infixParse :
      InfixParses minimum initial afterPrefix result remaining)
    (prefixIH : PrefixGrammarProperty input initial afterPrefix)
    (infixIH :
      InfixGrammarProperty minimum initial afterPrefix result remaining) :
    ExprGrammarProperty minimum input result remaining := by
  have admissible : InfixAdmissible initial afterPrefix := by
    intro token tail operator precedence associativity inputEq binding
    have precedenceLt := binaryBinding_precedence_lt_eight binding
    have outerBound := prefixIH.2
    cases associativity <;> simp only
    · exact Nat.le_trans (Nat.le_of_lt precedenceLt) outerBound
    · exact Nat.lt_of_lt_of_le precedenceLt outerBound
  rcases infixIH prefixIH.1 admissible with
    ⟨valid, blocked, preservesMinimum⟩
  refine ⟨valid, blocked, ?_⟩
  intro minimumLe
  exact preservesMinimum (Nat.le_trans minimumLe prefixIH.2)

private theorem prefixNotGrammarProperty
    (operatorToken : Token)
    (afterOperator remaining : List Token)
    (operand : Expr)
    (_operatorKind : operatorToken.kind = .bang)
    (_operandParse : PrefixParses afterOperator operand remaining)
    (operandIH : PrefixGrammarProperty afterOperator operand remaining) :
    PrefixGrammarProperty (operatorToken :: afterOperator)
      (.unary
        (SourceSpan.cover operatorToken.span operand.span)
        { value := .not, span := operatorToken.span }
        operand)
      remaining := by
  constructor
  · exact exprUnaryGrammarValid _ _ operand operandIH.1 operandIH.2
  · simp [Expr.outerPrecedence]

private theorem prefixUnitGrammarProperty
    (left right : Token)
    (remaining : List Token)
    (_leftKind : left.kind = .leftParen)
    (_rightKind : right.kind = .rightParen) :
    PrefixGrammarProperty (left :: right :: remaining)
      (.unit (SourceSpan.cover left.span right.span)) remaining := by
  exact ⟨exprUnitGrammarValid _, by simp [Expr.outerPrecedence]⟩

private theorem prefixGroupGrammarProperty
    (left right : Token)
    (afterLeft remaining : List Token)
    (inner : Expr)
    (_leftKind : left.kind = .leftParen)
    (_innerParse : ExprParses 0 afterLeft inner (right :: remaining))
    (_rightKind : right.kind = .rightParen)
    (innerIH :
      ExprGrammarProperty 0 afterLeft inner (right :: remaining)) :
    PrefixGrammarProperty (left :: afterLeft)
      (.group (SourceSpan.cover left.span right.span) inner) remaining := by
  constructor
  · exact exprGroupGrammarValid _ inner innerIH.1
  · simp [Expr.outerPrecedence]

private theorem prefixDecimalGrammarProperty
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (_kind : token.kind = .decimal digits) :
    PrefixGrammarProperty (token :: remaining)
      (.integer { base := .decimal, digits, span := token.span })
      remaining := by
  exact ⟨exprIntegerGrammarValid _, by simp [Expr.outerPrecedence]⟩

private theorem prefixHexadecimalGrammarProperty
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (_kind : token.kind = .hexadecimal digits) :
    PrefixGrammarProperty (token :: remaining)
      (.integer { base := .hexadecimal, digits, span := token.span })
      remaining := by
  exact ⟨exprIntegerGrammarValid _, by simp [Expr.outerPrecedence]⟩

private theorem prefixNameGrammarProperty
    (token : Token)
    (text : String)
    (remaining : List Token)
    (_kind : token.kind = .identifier text)
    (_notCall : HeadKindNe .leftParen remaining) :
    PrefixGrammarProperty (token :: remaining)
      (.name { value := text, span := token.span }) remaining := by
  exact ⟨exprNameGrammarValid _, by simp [Expr.outerPrecedence]⟩

private theorem prefixCallGrammarProperty
    (identifier left right : Token)
    (text : String)
    (afterLeft remaining : List Token)
    (arguments : List Expr)
    (_identifierKind : identifier.kind = .identifier text)
    (_leftKind : left.kind = .leftParen)
    (_argumentsParse :
      ArgumentsParse afterLeft arguments right remaining)
    (argumentsIH :
      ArgumentsGrammarProperty afterLeft arguments right remaining) :
    PrefixGrammarProperty (identifier :: left :: afterLeft)
      (.call
        (SourceSpan.cover identifier.span right.span)
        { value := text, span := identifier.span }
        arguments)
      remaining := by
  constructor
  · exact exprCallGrammarValid _ _ arguments argumentsIH
  · simp [Expr.outerPrecedence]

private theorem binaryGrammarValidOfLeftBinding
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    (binding : BinaryBinding kind operator precedence .left)
    (span operatorSpan : SourceSpan)
    (left right : Expr)
    (leftValid : left.GrammarValid)
    (rightValid : right.GrammarValid)
    (leftBound : precedence ≤ left.outerPrecedence)
    (rightBound : precedence < right.outerPrecedence) :
    (Expr.binary span { value := operator, span := operatorSpan }
      left right).GrammarValid := by
  apply exprBinaryGrammarValid _ _ left right leftValid rightValid
  cases binding <;>
    simpa [Expr.LocallyGrammarValid, Expr.outerPrecedence,
      BinaryOp.associativity, BinaryOp.precedence] using
      And.intro leftBound rightBound

private theorem binaryGrammarValidOfNonAssociativeBinding
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    (binding :
      BinaryBinding kind operator precedence .nonAssociative)
    (span operatorSpan : SourceSpan)
    (left right : Expr)
    (leftValid : left.GrammarValid)
    (rightValid : right.GrammarValid)
    (leftBound : precedence < left.outerPrecedence)
    (rightBound : precedence < right.outerPrecedence) :
    (Expr.binary span { value := operator, span := operatorSpan }
      left right).GrammarValid := by
  apply exprBinaryGrammarValid _ _ left right leftValid rightValid
  cases binding <;>
    simpa [Expr.LocallyGrammarValid, Expr.outerPrecedence,
      BinaryOp.associativity, BinaryOp.precedence] using
      And.intro leftBound rightBound

private theorem infixStopGrammarProperty
    (minimum : Nat)
    (left : Expr)
    (tokens : List Token)
    (blocked : InfixBlocked minimum tokens) :
    InfixGrammarProperty minimum left tokens left tokens := by
  intro leftValid _
  exact ⟨leftValid, blocked, fun minimumLe => minimumLe⟩

private theorem infixLeftStepGrammarProperty
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
      ExprGrammarProperty (precedence + 1) afterOperator right afterRight)
    (tailIH :
      InfixGrammarProperty minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixGrammarProperty minimum left (operatorToken :: afterOperator)
      result remaining := by
  intro leftValid admissible
  have leftBound :=
    admissible operatorToken afterOperator operator precedence .left rfl
      binding
  have bindingPrecedence := binaryBinding_precedence_eq binding
  have rightBound := rightIH.2.2 (by
    have precedenceLt := binaryBinding_precedence_lt_eight binding
    omega)
  have binaryValid :=
    binaryGrammarValidOfLeftBinding binding
      (SourceSpan.cover left.span right.span) operatorToken.span left right
      leftValid rightIH.1 leftBound (by omega)
  have tailAdmissible :
      InfixAdmissible
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight := by
    intro nextToken nextTail nextOperator nextPrecedence nextAssociativity
      inputEq nextBinding
    have nextLt :=
      rightIH.2.1 nextToken nextTail nextOperator nextPrecedence
        nextAssociativity inputEq nextBinding
    cases nextAssociativity with
    | left =>
        simp only [Expr.outerPrecedence, bindingPrecedence]
        omega
    | nonAssociative =>
        have nextBound : nextPrecedence < precedence :=
          nonAssociative_precedence_lt_of_left_binding
            binding nextBinding (by omega)
        simpa [Expr.outerPrecedence, bindingPrecedence] using nextBound
  rcases tailIH binaryValid tailAdmissible with
    ⟨resultValid, blocked, resultBound⟩
  exact ⟨resultValid, blocked, fun _ =>
    resultBound (by
      simpa [Expr.outerPrecedence, bindingPrecedence] using eligible)⟩

private theorem infixNonAssociativeStepGrammarProperty
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding :
      BinaryBinding operatorToken.kind operator precedence
        .nonAssociative)
    (eligible : minimum ≤ precedence)
    (_rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (notRepeated : HeadPrecedenceNe precedence afterRight)
    (_tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH :
      ExprGrammarProperty (precedence + 1) afterOperator right afterRight)
    (tailIH :
      InfixGrammarProperty minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining) :
    InfixGrammarProperty minimum left (operatorToken :: afterOperator)
      result remaining := by
  intro leftValid admissible
  have leftBound :=
    admissible operatorToken afterOperator operator precedence
      .nonAssociative rfl binding
  have bindingPrecedence := binaryBinding_precedence_eq binding
  have rightBound := rightIH.2.2 (by
    have precedenceLt := binaryBinding_precedence_lt_eight binding
    omega)
  have binaryValid :=
    binaryGrammarValidOfNonAssociativeBinding binding
      (SourceSpan.cover left.span right.span) operatorToken.span left right
      leftValid rightIH.1 leftBound (by omega)
  have tailAdmissible :
      InfixAdmissible
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight := by
    intro nextToken nextTail nextOperator nextPrecedence nextAssociativity
      inputEq nextBinding
    have nextLt :=
      rightIH.2.1 nextToken nextTail nextOperator nextPrecedence
        nextAssociativity inputEq nextBinding
    have nextNe :=
      notRepeated nextToken nextTail nextOperator nextPrecedence
        nextAssociativity inputEq nextBinding
    cases nextAssociativity <;>
      simp only [Expr.outerPrecedence, bindingPrecedence] <;>
      omega
  rcases tailIH binaryValid tailAdmissible with
    ⟨resultValid, blocked, resultBound⟩
  exact ⟨resultValid, blocked, fun _ =>
    resultBound (by
      simpa [Expr.outerPrecedence, bindingPrecedence] using eligible)⟩

private theorem argumentsEmptyGrammarProperty
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentsGrammarProperty (right :: remaining) [] right remaining := by
  simp [ArgumentsGrammarProperty]

private theorem argumentsNonemptyGrammarProperty
    (input afterFirst remaining : List Token)
    (first : Expr)
    (tail : List Expr)
    (right : Token)
    (_firstParse : ExprParses 0 input first afterFirst)
    (_tailParse :
      ArgumentTailParses afterFirst tail right remaining)
    (firstIH : ExprGrammarProperty 0 input first afterFirst)
    (tailIH :
      ArgumentTailGrammarProperty afterFirst tail right remaining) :
    ArgumentsGrammarProperty input (first :: tail) right remaining := by
  intro argument member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact firstIH.1
  · exact tailIH argument member

private theorem argumentTailDoneGrammarProperty
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentTailGrammarProperty (right :: remaining) [] right remaining := by
  simp [ArgumentTailGrammarProperty]

private theorem argumentTailMoreGrammarProperty
    (comma right : Token)
    (afterComma afterNext remaining : List Token)
    (next : Expr)
    (tail : List Expr)
    (_commaKind : comma.kind = .comma)
    (_nextParse : ExprParses 0 afterComma next afterNext)
    (_tailParse :
      ArgumentTailParses afterNext tail right remaining)
    (nextIH : ExprGrammarProperty 0 afterComma next afterNext)
    (tailIH :
      ArgumentTailGrammarProperty afterNext tail right remaining) :
    ArgumentTailGrammarProperty (comma :: afterComma)
      (next :: tail) right remaining := by
  intro argument member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact nextIH.1
  · exact tailIH argument member

private theorem exprParsesGrammarProperty
    {minimum : Nat}
    {input remaining : List Token}
    {expression : Expr}
    (derivation : ExprParses minimum input expression remaining) :
    ExprGrammarProperty minimum input expression remaining :=
  ExprParses.rec
    (motive_1 := fun minimum input expression remaining _ =>
      ExprGrammarProperty minimum input expression remaining)
    (motive_2 := fun input expression remaining _ =>
      PrefixGrammarProperty input expression remaining)
    (motive_3 := fun minimum left input expression remaining _ =>
      InfixGrammarProperty minimum left input expression remaining)
    (motive_4 := fun input arguments right remaining _ =>
      ArgumentsGrammarProperty input arguments right remaining)
    (motive_5 := fun input arguments right remaining _ =>
      ArgumentTailGrammarProperty input arguments right remaining)
    exprConditionalGrammarProperty
    exprOrdinaryGrammarProperty
    prefixNotGrammarProperty
    prefixUnitGrammarProperty
    prefixGroupGrammarProperty
    prefixDecimalGrammarProperty
    prefixHexadecimalGrammarProperty
    prefixNameGrammarProperty
    prefixCallGrammarProperty
    infixStopGrammarProperty
    infixLeftStepGrammarProperty
    infixNonAssociativeStepGrammarProperty
    argumentsEmptyGrammarProperty
    argumentsNonemptyGrammarProperty
    argumentTailDoneGrammarProperty
    argumentTailMoreGrammarProperty
    derivation

namespace ExprParses

theorem grammarValid
    {minimum : Nat}
    {input remaining : List Token}
    {expression : Expr}
    (derivation : ExprParses minimum input expression remaining) :
    expression.GrammarValid :=
  (exprParsesGrammarProperty derivation).1

end ExprParses

namespace TypeParses

theorem grammarValid
    {input remaining : List Token}
    {type : TypeSyntax}
    (derivation : TypeParses input type remaining) :
    type.GrammarValid := by
  cases derivation <;> simp [TypeSyntax.GrammarValid]

end TypeParses

namespace LetParses

theorem grammarValid
    {input remaining : List Token}
    {statement : LetStatement}
    (derivation : LetParses input statement remaining) :
    statement.GrammarValid := by
  cases derivation with
  | intro _ _ _ _ _ _ _ _ _ type value _ _ _ typeParse _ valueParse _ =>
      exact ⟨typeParse.grammarValid, valueParse.grammarValid⟩

end LetParses

namespace BindingsParse

theorem grammarValid
    {input remaining : List Token}
    {bindings : List LetStatement}
    (derivation : BindingsParse input bindings remaining) :
    ∀ binding ∈ bindings, binding.GrammarValid := by
  induction derivation with
  | done => simp
  | more _ _ _ binding bindings bindingParse _ tailIH =>
      intro candidate member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact bindingParse.grammarValid
      · exact tailIH candidate member

end BindingsParse

namespace ReturnParses

theorem grammarValid
    {input remaining : List Token}
    {statement : ReturnStatement}
    (derivation : ReturnParses input statement remaining) :
    statement.GrammarValid := by
  cases derivation with
  | intro _ _ _ _ value _ valueParse _ =>
      exact valueParse.grammarValid

end ReturnParses

namespace FunctionParses

theorem grammarValid
    {input remaining : List Token}
    {declaration : FunctionDecl}
    (derivation : FunctionParses input declaration remaining) :
    declaration.GrammarValid := by
  cases derivation
  exact ⟨TypeParses.grammarValid (by assumption),
    BindingsParse.grammarValid (by assumption),
    ReturnParses.grammarValid (by assumption)⟩

end FunctionParses

namespace FileParses

theorem grammarValid
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed) :
    parsed.GrammarValid := by
  cases derivation with
  | intro _ _ _ functionParse =>
      exact functionParse.grammarValid

end FileParses

private def TokensValidFor
    (file : SourceFile)
    (tokens : List Token) : Prop :=
  ∀ token ∈ tokens, token.ValidFor file

private abbrev TokensStartWith
    (span : SourceSpan)
    (tokens : List Token) : Prop :=
  ExpectedToken.FirstSatisfies (.starts span) tokens

private abbrev TokensEndWith
    (span : SourceSpan)
    (tokens : List Token) : Prop :=
  ExpectedToken.LastSatisfies (.ends span) tokens

private theorem tokensValidFor_tail
    {file : SourceFile}
    {head : Token}
    {tail : List Token}
    (valid : TokensValidFor file (head :: tail)) :
    TokensValidFor file tail := by
  intro token member
  exact valid token (by simp [member])

private theorem tokenSpan_source_eq
    {file : SourceFile}
    {token : Token}
    (valid : token.ValidFor file) :
    token.span.source = file.path :=
  valid.2.1.1.1

private theorem tokenSpan_sources_eq
    {file : SourceFile}
    {first second : Token}
    (firstValid : first.ValidFor file)
    (secondValid : second.ValidFor file) :
    first.span.source = second.span.source :=
  (tokenSpan_source_eq firstValid).trans
    (tokenSpan_source_eq secondValid).symm

private theorem token_starts_self (token : Token) :
    TokensStartWith token.span [token] := by
  simp [TokensStartWith, ExpectedToken.FirstSatisfies,
    SpanConstraint.Holds]

private theorem token_ends_self (token : Token) :
    TokensEndWith token.span [token] := by
  simp [TokensEndWith, ExpectedToken.LastSatisfies,
    SpanConstraint.Holds]

private theorem tokensValidFor_append_left
    {file : SourceFile}
    {first second : List Token}
    (valid : TokensValidFor file (first ++ second)) :
    TokensValidFor file first := by
  intro token member
  exact valid token (List.mem_append_left second member)

private theorem tokensValidFor_append_right
    {file : SourceFile}
    {first second : List Token}
    (valid : TokensValidFor file (first ++ second)) :
    TokensValidFor file second := by
  intro token member
  exact valid token (List.mem_append_right first member)

private theorem tokensValidFor_append
    {file : SourceFile}
    {first second : List Token}
    (firstValid : TokensValidFor file first)
    (secondValid : TokensValidFor file second) :
    TokensValidFor file (first ++ second) := by
  intro token member
  simp only [List.mem_append] at member
  rcases member with member | member
  · exact firstValid token member
  · exact secondValid token member

private theorem tokensValidFor_singleton
    {file : SourceFile}
    {token : Token}
    (valid : token.ValidFor file) :
    TokensValidFor file [token] := by
  intro candidate member
  simp only [List.mem_singleton] at member
  subst candidate
  exact valid

private theorem span_source_eq_of_tokensStartWith
    {file : SourceFile}
    {span : SourceSpan}
    {tokens : List Token}
    (valid : TokensValidFor file tokens)
    (starts : TokensStartWith span tokens) :
    span.source = file.path := by
  cases tokens with
  | nil => contradiction
  | cons first rest =>
      have firstValid := valid first (by simp)
      exact starts.1.symm.trans firstValid.2.1.1.1

private theorem tokensStartWith_append
    {span : SourceSpan}
    {first second : List Token}
    (starts : TokensStartWith span first) :
    TokensStartWith span (first ++ second) := by
  cases first with
  | nil => contradiction
  | cons head tail => exact starts

private theorem tokensEndWith_append
    {span : SourceSpan}
    (first : List Token)
    {second : List Token}
    (ends : TokensEndWith span second) :
    TokensEndWith span (first ++ second) := by
  induction first with
  | nil => exact ends
  | cons head tail inductionHypothesis =>
      cases tail <;> cases second <;>
        simp_all [TokensEndWith, ExpectedToken.LastSatisfies]

private theorem tokensStartWith_cover
    {firstSpan lastSpan : SourceSpan}
    {first second : List Token}
    (starts : TokensStartWith firstSpan first) :
    TokensStartWith (SourceSpan.cover firstSpan lastSpan)
      (first ++ second) := by
  cases first with
  | nil => contradiction
  | cons head tail =>
      simpa [TokensStartWith, ExpectedToken.FirstSatisfies,
        SpanConstraint.Holds, SourceSpan.cover] using starts

private theorem tokensEndWith_cover
    {firstSpan lastSpan : SourceSpan}
    (first : List Token)
    {last : List Token}
    (sourceEq : firstSpan.source = lastSpan.source)
    (ends : TokensEndWith lastSpan last) :
    TokensEndWith (SourceSpan.cover firstSpan lastSpan)
      (first ++ last) := by
  apply tokensEndWith_append first
  induction last with
  | nil => contradiction
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil =>
          simpa [TokensEndWith, ExpectedToken.LastSatisfies,
            SpanConstraint.Holds, SourceSpan.cover, sourceEq] using ends
      | cons second rest =>
          exact inductionHypothesis ends

private abbrev TokensOrdered (tokens : List Token) : Prop :=
  Lexed.SpansOrdered (tokens.map (·.span))

private theorem tokensOrdered_tail
    {head : Token}
    {tail : List Token}
    (ordered : TokensOrdered (head :: tail)) :
    TokensOrdered tail := by
  cases tail with
  | nil => simp [TokensOrdered, Lexed.SpansOrdered]
  | cons second rest =>
      exact ordered.2

private theorem tokensOrdered_append_right
    (first : List Token)
    {second : List Token}
    (ordered : TokensOrdered (first ++ second)) :
    TokensOrdered second := by
  induction first with
  | nil => exact ordered
  | cons head tail inductionHypothesis =>
      exact inductionHypothesis (tokensOrdered_tail ordered)

private theorem tokensOrdered_append_left
    {first second : List Token}
    (ordered : TokensOrdered (first ++ second)) :
    TokensOrdered first := by
  induction first with
  | nil => simp [TokensOrdered, Lexed.SpansOrdered]
  | cons head tail inductionHypothesis =>
      cases tail with
      | nil => simp [TokensOrdered, Lexed.SpansOrdered]
      | cons next rest =>
          refine ⟨?_, inductionHypothesis (tokensOrdered_tail ordered)⟩
          exact ordered.1

private theorem spanStart_le_tokenStart_of_mem
    {file : SourceFile}
    {span : SourceSpan}
    {tokens : List Token}
    (valid : TokensValidFor file tokens)
    (ordered : TokensOrdered tokens)
    (starts : TokensStartWith span tokens)
    {token : Token}
    (member : token ∈ tokens) :
    span.startByte ≤ token.span.startByte := by
  induction tokens generalizing span token with
  | nil => contradiction
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at member
          subst token
          exact Nat.le_of_eq starts.2.symm
      | cons second rest =>
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · exact Nat.le_of_eq starts.2.symm
          · have firstValid := valid first (by simp)
            exact Nat.le_trans
              (Nat.le_trans
                (Nat.le_of_eq starts.2.symm)
                firstValid.2.1.1.2)
              (Nat.le_trans ordered.1
                (inductionHypothesis
                  (tokensValidFor_tail valid)
                  (tokensOrdered_tail ordered)
                  (token_starts_self second)
                  (by simpa using member)))

private theorem tokenEnd_le_spanEnd_of_mem
    {file : SourceFile}
    {span : SourceSpan}
    {tokens : List Token}
    (valid : TokensValidFor file tokens)
    (ordered : TokensOrdered tokens)
    (ends : TokensEndWith span tokens)
    {token : Token}
    (member : token ∈ tokens) :
    token.span.endByte ≤ span.endByte := by
  induction tokens generalizing span token with
  | nil => contradiction
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          simp only [List.mem_singleton] at member
          subst token
          exact Nat.le_of_eq ends.2
      | cons second rest =>
          simp only [List.mem_cons] at member
          rcases member with rfl | member
          · have secondValid := valid second (by simp)
            exact Nat.le_trans ordered.1
              (Nat.le_trans secondValid.2.1.1.2
                (inductionHypothesis
                  (tokensValidFor_tail valid)
                  (tokensOrdered_tail ordered)
                  ends (by simp)))
          · exact inductionHypothesis
              (tokensValidFor_tail valid)
              (tokensOrdered_tail ordered)
              ends (by simpa using member)

private theorem spanEnd_le_fileEnd_of_tokensEndWith
    {file : SourceFile}
    {span : SourceSpan}
    {tokens : List Token}
    (valid : TokensValidFor file tokens)
    (ends : TokensEndWith span tokens) :
    span.endByte ≤ file.content.utf8ByteSize := by
  induction tokens with
  | nil => contradiction
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          have firstValid := valid first (by simp)
          rw [← ends.2]
          exact firstValid.2.1.2
      | cons second rest =>
          exact inductionHypothesis (tokensValidFor_tail valid) ends

private theorem spanValidFor_of_delimitedTokens
    {file : SourceFile}
    {span : SourceSpan}
    {tokens : List Token}
    (valid : TokensValidFor file tokens)
    (ordered : TokensOrdered tokens)
    (starts : TokensStartWith span tokens)
    (ends : TokensEndWith span tokens) :
    span.ValidFor file := by
  cases tokens with
  | nil => contradiction
  | cons first rest =>
      have firstValid := valid first (by simp)
      refine ⟨⟨span_source_eq_of_tokensStartWith valid starts, ?_⟩,
        spanEnd_le_fileEnd_of_tokensEndWith valid ends⟩
      exact Nat.le_trans (Nat.le_of_eq starts.2.symm)
        (Nat.le_trans firstValid.2.1.1.2
          (tokenEnd_le_spanEnd_of_mem valid ordered ends (by simp)))

private theorem innerSpanEnd_le_outerSpanEnd_of_subset
    {file : SourceFile}
    {outer inner : SourceSpan}
    {outerTokens innerTokens : List Token}
    (outerValid : TokensValidFor file outerTokens)
    (outerOrdered : TokensOrdered outerTokens)
    (outerEnds : TokensEndWith outer outerTokens)
    (innerEnds : TokensEndWith inner innerTokens)
    (subset : ∀ token ∈ innerTokens, token ∈ outerTokens) :
    inner.endByte ≤ outer.endByte := by
  induction innerTokens generalizing inner with
  | nil => contradiction
  | cons first tail inductionHypothesis =>
      cases tail with
      | nil =>
          exact Nat.le_trans (Nat.le_of_eq innerEnds.2.symm)
            (tokenEnd_le_spanEnd_of_mem outerValid outerOrdered outerEnds
              (subset first (by simp)))
      | cons second rest =>
          exact inductionHypothesis innerEnds
            (fun token member => subset token (by simp [member]))

private theorem spanContains_of_delimitedSubset
    {file : SourceFile}
    {outer inner : SourceSpan}
    {outerTokens innerTokens : List Token}
    (outerValid : TokensValidFor file outerTokens)
    (outerOrdered : TokensOrdered outerTokens)
    (outerStarts : TokensStartWith outer outerTokens)
    (outerEnds : TokensEndWith outer outerTokens)
    (innerValid : TokensValidFor file innerTokens)
    (innerOrdered : TokensOrdered innerTokens)
    (innerStarts : TokensStartWith inner innerTokens)
    (innerEnds : TokensEndWith inner innerTokens)
    (subset : ∀ token ∈ innerTokens, token ∈ outerTokens) :
    outer.Contains inner := by
  have outerSpanValid := spanValidFor_of_delimitedTokens
    outerValid outerOrdered outerStarts outerEnds
  have innerSpanValid := spanValidFor_of_delimitedTokens
    innerValid innerOrdered innerStarts innerEnds
  cases innerTokens with
  | nil => contradiction
  | cons first rest =>
      have firstMember : first ∈ outerTokens := subset first (by simp)
      refine ⟨⟨outerSpanValid.1.1.trans innerSpanValid.1.1.symm, ?_⟩,
        ⟨innerSpanValid.1.2, ?_⟩⟩
      · exact Nat.le_trans
          (spanStart_le_tokenStart_of_mem outerValid outerOrdered
            outerStarts firstMember)
          (Nat.le_of_eq innerStarts.2)
      · exact innerSpanEnd_le_outerSpanEnd_of_subset outerValid
          outerOrdered outerEnds innerEnds subset

private theorem exprUnitValidFor
    {file : SourceFile}
    {span : SourceSpan}
    (spanValid : span.ValidFor file) :
    (Expr.unit span).ValidFor file := by
  simp [Expr.ValidFor, Expr.allSpans, Expr.containments, spanValid]

private theorem exprIntegerValidFor
    {file : SourceFile}
    {literal : IntegerLiteral}
    (spanValid : literal.span.ValidFor file) :
    (Expr.integer literal).ValidFor file := by
  simp [Expr.ValidFor, Expr.allSpans, Expr.containments, spanValid]

private theorem exprNameValidFor
    {file : SourceFile}
    {name : Name}
    (spanValid : name.span.ValidFor file) :
    (Expr.name name).ValidFor file := by
  simp [Expr.ValidFor, Expr.allSpans, Expr.containments, spanValid]

private theorem exprGroupValidFor
    {file : SourceFile}
    {span : SourceSpan}
    {inner : Expr}
    (spanValid : span.ValidFor file)
    (innerValid : inner.ValidFor file)
    (containsInner : span.Contains inner.span) :
    (Expr.group span inner).ValidFor file := by
  refine ⟨?_, ?_⟩
  · intro candidate member
    simp only [Expr.allSpans, List.mem_cons] at member
    rcases member with rfl | member
    · exact spanValid
    · exact innerValid.1 candidate member
  · intro containment member
    simp only [Expr.containments, List.mem_cons] at member
    rcases member with rfl | member
    · exact containsInner
    · exact innerValid.2 containment member

private theorem exprCallValidFor
    {file : SourceFile}
    {span : SourceSpan}
    {callee : Name}
    {arguments : List Expr}
    (spanValid : span.ValidFor file)
    (calleeValid : callee.span.ValidFor file)
    (containsCallee : span.Contains callee.span)
    (argumentsValid :
      ∀ argument ∈ arguments, argument.ValidFor file)
    (containsArguments :
      ∀ argument ∈ arguments, span.Contains argument.span) :
    (Expr.call span callee arguments).ValidFor file := by
  refine ⟨?_, ?_⟩
  · intro candidate member
    simp only [Expr.allSpans, List.mem_cons, List.mem_flatMap] at member
    rcases member with rfl | rfl |
      ⟨argument, argumentMember, candidateMember⟩
    · exact spanValid
    · exact calleeValid
    · exact (argumentsValid argument argumentMember).1
        candidate candidateMember
  · intro containment member
    simp only [Expr.containments, List.mem_cons, List.mem_append,
      List.mem_map, List.mem_flatMap] at member
    rcases member with
      (rfl | ⟨argument, argumentMember, rfl⟩) |
      ⟨argument, argumentMember, containmentMember⟩
    · exact containsCallee
    · exact containsArguments argument argumentMember
    · exact (argumentsValid argument argumentMember).2
        containment containmentMember

private theorem exprUnaryValidFor
    {file : SourceFile}
    {span : SourceSpan}
    {operator : Located UnaryOp}
    {operand : Expr}
    (spanValid : span.ValidFor file)
    (operatorValid : operator.span.ValidFor file)
    (operandValid : operand.ValidFor file)
    (containsOperator : span.Contains operator.span)
    (containsOperand : span.Contains operand.span) :
    (Expr.unary span operator operand).ValidFor file := by
  refine ⟨?_, ?_⟩
  · intro candidate member
    simp only [Expr.allSpans, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact spanValid
    · exact operatorValid
    · exact operandValid.1 candidate member
  · intro containment member
    simp only [Expr.containments, List.mem_cons] at member
    rcases member with rfl | rfl | member
    · exact containsOperator
    · exact containsOperand
    · exact operandValid.2 containment member

private theorem exprBinaryValidFor
    {file : SourceFile}
    {span : SourceSpan}
    {operator : Located BinaryOp}
    {left right : Expr}
    (spanValid : span.ValidFor file)
    (operatorValid : operator.span.ValidFor file)
    (leftValid : left.ValidFor file)
    (rightValid : right.ValidFor file)
    (containsOperator : span.Contains operator.span)
    (containsLeft : span.Contains left.span)
    (containsRight : span.Contains right.span) :
    (Expr.binary span operator left right).ValidFor file := by
  refine ⟨?_, ?_⟩
  · intro candidate member
    simp only [Expr.allSpans, List.mem_cons, List.mem_append] at member
    rcases member with (rfl | rfl | member) | member
    · exact spanValid
    · exact operatorValid
    · exact leftValid.1 candidate member
    · exact rightValid.1 candidate member
  · intro containment member
    simp only [Expr.containments, List.mem_cons, List.mem_append] at member
    rcases member with (rfl | rfl | rfl | member) | member
    · exact containsOperator
    · exact containsLeft
    · exact containsRight
    · exact leftValid.2 containment member
    · exact rightValid.2 containment member

private theorem exprConditionalValidFor
    {file : SourceFile}
    {span : SourceSpan}
    {condition thenBranch elseBranch : Expr}
    (spanValid : span.ValidFor file)
    (conditionValid : condition.ValidFor file)
    (thenValid : thenBranch.ValidFor file)
    (elseValid : elseBranch.ValidFor file)
    (containsCondition : span.Contains condition.span)
    (containsThen : span.Contains thenBranch.span)
    (containsElse : span.Contains elseBranch.span) :
    (Expr.ifThenElse span condition thenBranch elseBranch).ValidFor file := by
  refine ⟨?_, ?_⟩
  · intro candidate member
    simp only [Expr.allSpans, List.mem_cons, List.mem_append] at member
    rcases member with ((rfl | member) | member) | member
    · exact spanValid
    · exact conditionValid.1 candidate member
    · exact thenValid.1 candidate member
    · exact elseValid.1 candidate member
  · intro containment member
    simp only [Expr.containments, List.mem_cons, List.mem_append] at member
    rcases member with ((rfl | rfl | rfl | member) | member) | member
    · exact containsCondition
    · exact containsThen
    · exact containsElse
    · exact conditionValid.2 containment member
    · exact thenValid.2 containment member
    · exact elseValid.2 containment member

private theorem expectedTokenPlain_matches
    {kind : TokenKind}
    {token : Token}
    (kindEq : token.kind = kind) :
    (ExpectedToken.plain kind).Matches token := by
  simp [ExpectedToken.plain, ExpectedToken.Matches, kindEq]

private theorem expectedTokenExact_matches
    {kind : TokenKind}
    {token : Token}
    (kindEq : token.kind = kind) :
    (ExpectedToken.exact kind token.span).Matches token := by
  simp [ExpectedToken.exact, ExpectedToken.Matches,
    SpanConstraint.Holds, kindEq]

private def argumentTailExpectedTokens
    (arguments : List Expr) : List ExpectedToken :=
  arguments.flatMap fun argument =>
    ExpectedToken.plain .comma :: argument.expectedTokens

private def argumentsExpectedTokens :
    List Expr → List ExpectedToken
  | [] => []
  | first :: rest =>
      first.expectedTokens ++ argumentTailExpectedTokens rest

private theorem call_expectedTokens_eq
    (span : SourceSpan)
    (callee : Name)
    (arguments : List Expr) :
    (Expr.call span callee arguments).expectedTokens =
      ExpectedToken.enclose span
        (ExpectedToken.exact (.identifier callee.value) callee.span ::
          ExpectedToken.plain .leftParen ::
          argumentsExpectedTokens arguments ++
          [ExpectedToken.plain .rightParen]) := by
  cases arguments with
  | nil =>
      simpa [argumentsExpectedTokens] using
        Expr.expectedTokens_call_nil span callee
  | cons first rest =>
      simpa [argumentsExpectedTokens, argumentTailExpectedTokens] using
        Expr.expectedTokens_call_cons span callee first rest

private def ExprCorrespondenceProperty
    (file : SourceFile)
    (_minimum : Nat)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches expression.expectedTokens consumed ∧
      TokensStartWith expression.span consumed ∧
      TokensEndWith expression.span consumed

private def PrefixCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches expression.expectedTokens consumed ∧
      TokensStartWith expression.span consumed ∧
      TokensEndWith expression.span consumed

private def InfixCorrespondenceProperty
    (file : SourceFile)
    (_minimum : Nat)
    (left : Expr)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  ∀ leftTokens,
    ExpectedToken.ListMatches left.expectedTokens leftTokens →
    TokensStartWith left.span leftTokens →
    TokensEndWith left.span leftTokens →
    TokensValidFor file leftTokens →
    TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches expression.expectedTokens
        (leftTokens ++ consumed) ∧
      TokensStartWith expression.span (leftTokens ++ consumed) ∧
      TokensEndWith expression.span (leftTokens ++ consumed)

private def ArgumentsCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (arguments : List Expr)
    (right : Token)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ right :: remaining ∧
      ExpectedToken.ListMatches
        (argumentsExpectedTokens arguments) consumed

private def ArgumentTailCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (arguments : List Expr)
    (right : Token)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ right :: remaining ∧
      ExpectedToken.ListMatches
        (argumentTailExpectedTokens arguments) consumed

private theorem argumentsEmptyCorrespondenceProperty
    (file : SourceFile)
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentsCorrespondenceProperty file
      (right :: remaining) [] right remaining := by
  intro _
  exact ⟨[], rfl, .nil⟩

private theorem argumentsNonemptyCorrespondenceProperty
    (file : SourceFile)
    (input afterFirst remaining : List Token)
    (first : Expr)
    (tail : List Expr)
    (right : Token)
    (_firstParse : ExprParses 0 input first afterFirst)
    (_tailParse :
      ArgumentTailParses afterFirst tail right remaining)
    (firstIH :
      ExprCorrespondenceProperty file 0 input first afterFirst)
    (tailIH :
      ArgumentTailCorrespondenceProperty file
        afterFirst tail right remaining) :
    ArgumentsCorrespondenceProperty file input
      (first :: tail) right remaining := by
  intro valid
  rcases firstIH valid with
    ⟨firstTokens, inputEq, firstMatch, _, _⟩
  rw [inputEq] at valid
  have afterFirstValid := tokensValidFor_append_right valid
  rcases tailIH afterFirstValid with
    ⟨tailTokens, afterFirstEq, tailMatch⟩
  refine ⟨firstTokens ++ tailTokens, ?_, ?_⟩
  · rw [inputEq, afterFirstEq, List.append_assoc]
  · simpa [argumentsExpectedTokens] using
      ExpectedToken.ListMatches.append firstMatch tailMatch

private theorem argumentTailDoneCorrespondenceProperty
    (file : SourceFile)
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentTailCorrespondenceProperty file
      (right :: remaining) [] right remaining := by
  intro _
  exact ⟨[], rfl, .nil⟩

private theorem argumentTailMoreCorrespondenceProperty
    (file : SourceFile)
    (comma right : Token)
    (afterComma afterNext remaining : List Token)
    (next : Expr)
    (tail : List Expr)
    (commaKind : comma.kind = .comma)
    (_nextParse : ExprParses 0 afterComma next afterNext)
    (_tailParse :
      ArgumentTailParses afterNext tail right remaining)
    (nextIH :
      ExprCorrespondenceProperty file 0 afterComma next afterNext)
    (tailIH :
      ArgumentTailCorrespondenceProperty file
        afterNext tail right remaining) :
    ArgumentTailCorrespondenceProperty file
      (comma :: afterComma) (next :: tail) right remaining := by
  intro valid
  have afterCommaValid := tokensValidFor_tail valid
  rcases nextIH afterCommaValid with
    ⟨nextTokens, afterCommaEq, nextMatch, _, _⟩
  rw [afterCommaEq] at afterCommaValid
  have afterNextValid := tokensValidFor_append_right afterCommaValid
  rcases tailIH afterNextValid with
    ⟨tailTokens, afterNextEq, tailMatch⟩
  refine ⟨comma :: nextTokens ++ tailTokens, ?_, ?_⟩
  · simp only [List.cons_append]
    rw [afterCommaEq, afterNextEq, List.append_assoc]
  · simp only [argumentTailExpectedTokens, List.flatMap_cons]
    exact .cons (expectedTokenPlain_matches commaKind)
      (ExpectedToken.ListMatches.append nextMatch tailMatch)

private theorem argumentTail_rightKind
    {input remaining : List Token}
    {arguments : List Expr}
    {right : Token} :
    ArgumentTailParses input arguments right remaining →
      right.kind = .rightParen
  | .done _ _ kind => kind
  | .more _ _ _ _ _ _ _ _ _ tail => argumentTail_rightKind tail

private theorem arguments_rightKind
    {input remaining : List Token}
    {arguments : List Expr}
    {right : Token} :
    ArgumentsParse input arguments right remaining →
      right.kind = .rightParen
  | .empty _ _ kind => kind
  | .nonempty _ _ _ _ _ _ _ tail => argumentTail_rightKind tail

private theorem prefixNotCorrespondenceProperty
    (file : SourceFile)
    (operatorToken : Token)
    (afterOperator remaining : List Token)
    (operand : Expr)
    (operatorKind : operatorToken.kind = .bang)
    (_operandParse : PrefixParses afterOperator operand remaining)
    (operandIH : PrefixCorrespondenceProperty file
      afterOperator operand remaining) :
    PrefixCorrespondenceProperty file (operatorToken :: afterOperator)
      (.unary
        (SourceSpan.cover operatorToken.span operand.span)
        { value := .not, span := operatorToken.span }
        operand)
      remaining := by
  intro valid
  have operatorValid := valid operatorToken (by simp)
  have afterOperatorValid := tokensValidFor_tail valid
  rcases operandIH afterOperatorValid with
    ⟨operandTokens, afterOperatorEq, operandMatch,
      operandStarts, operandEnds⟩
  rw [afterOperatorEq] at afterOperatorValid
  have operandTokensValid :=
    tokensValidFor_append_left afterOperatorValid
  have sourceEq : operatorToken.span.source = operand.span.source :=
    (tokenSpan_source_eq operatorValid).trans
      (span_source_eq_of_tokensStartWith
        operandTokensValid operandStarts).symm
  let consumed := operatorToken :: operandTokens
  have rawMatch :
      ExpectedToken.ListMatches
        (ExpectedToken.exact .bang operatorToken.span ::
          operand.expectedTokens)
        consumed :=
    .cons (expectedTokenExact_matches operatorKind) operandMatch
  have starts :
      TokensStartWith
        (SourceSpan.cover operatorToken.span operand.span) consumed := by
    simpa [consumed] using
      tokensStartWith_cover
        (second := operandTokens) (token_starts_self operatorToken)
  have ends :
      TokensEndWith
        (SourceSpan.cover operatorToken.span operand.span) consumed := by
    simpa [consumed] using
      tokensEndWith_cover [operatorToken] sourceEq operandEnds
  refine ⟨consumed, ?_, ?_, starts, ends⟩
  · simp [consumed, afterOperatorEq]
  · simpa [Expr.expectedTokens, UnaryOp.tokenKind] using
      ExpectedToken.ListMatches.enclose rawMatch starts ends

private theorem prefixUnitCorrespondenceProperty
    (file : SourceFile)
    (left right : Token)
    (remaining : List Token)
    (leftKind : left.kind = .leftParen)
    (rightKind : right.kind = .rightParen) :
    PrefixCorrespondenceProperty file (left :: right :: remaining)
      (.unit (SourceSpan.cover left.span right.span)) remaining := by
  intro valid
  have leftValid := valid left (by simp)
  have rightValid := valid right (by simp)
  have sourceEq := tokenSpan_sources_eq leftValid rightValid
  have starts : TokensStartWith
      (SourceSpan.cover left.span right.span) [left, right] :=
    tokensStartWith_cover (lastSpan := right.span)
      (second := [right]) (token_starts_self left)
  have ends : TokensEndWith
      (SourceSpan.cover left.span right.span) [left, right] :=
    tokensEndWith_cover [left] sourceEq (token_ends_self right)
  refine ⟨[left, right], rfl, ?_, starts, ends⟩
  simpa [Expr.expectedTokens] using
    ExpectedToken.ListMatches.enclose
      (.cons (expectedTokenPlain_matches leftKind)
        (.cons (expectedTokenPlain_matches rightKind) .nil)) starts ends

private theorem prefixGroupCorrespondenceProperty
    (file : SourceFile)
    (left right : Token)
    (afterLeft remaining : List Token)
    (inner : Expr)
    (leftKind : left.kind = .leftParen)
    (_innerParse : ExprParses 0 afterLeft inner (right :: remaining))
    (rightKind : right.kind = .rightParen)
    (innerIH : ExprCorrespondenceProperty file 0 afterLeft inner
      (right :: remaining)) :
    PrefixCorrespondenceProperty file (left :: afterLeft)
      (.group (SourceSpan.cover left.span right.span) inner) remaining := by
  intro valid
  have leftValid := valid left (by simp)
  have afterLeftValid := tokensValidFor_tail valid
  rcases innerIH afterLeftValid with
    ⟨innerTokens, afterLeftEq, innerMatch, _, _⟩
  rw [afterLeftEq] at afterLeftValid
  have rightValid := afterLeftValid right (by simp)
  have sourceEq := tokenSpan_sources_eq leftValid rightValid
  let consumed := left :: innerTokens ++ [right]
  have starts :
      TokensStartWith (SourceSpan.cover left.span right.span) consumed := by
    simpa [consumed] using
      tokensStartWith_cover
        (second := innerTokens ++ [right]) (token_starts_self left)
  have ends :
      TokensEndWith (SourceSpan.cover left.span right.span) consumed := by
    simpa [consumed] using
      tokensEndWith_cover (left :: innerTokens) sourceEq
        (token_ends_self right)
  refine ⟨consumed, ?_, ?_, starts, ends⟩
  · simp [consumed, afterLeftEq, List.append_assoc]
  · simpa [consumed, Expr.expectedTokens] using
      ExpectedToken.ListMatches.enclose
        (.cons (expectedTokenPlain_matches leftKind)
          (ExpectedToken.ListMatches.append innerMatch
            (.cons (expectedTokenPlain_matches rightKind) .nil)))
        starts ends

private theorem prefixDecimalCorrespondenceProperty
    (file : SourceFile)
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (kind : token.kind = .decimal digits) :
    PrefixCorrespondenceProperty file (token :: remaining)
      (.integer { base := .decimal, digits, span := token.span })
      remaining := by
  intro _
  refine ⟨[token], rfl, ?_, token_starts_self token,
    token_ends_self token⟩
  simpa [Expr.expectedTokens] using
    ExpectedToken.ListMatches.cons
      (expectedTokenExact_matches kind) ExpectedToken.ListMatches.nil

private theorem prefixHexadecimalCorrespondenceProperty
    (file : SourceFile)
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (kind : token.kind = .hexadecimal digits) :
    PrefixCorrespondenceProperty file (token :: remaining)
      (.integer { base := .hexadecimal, digits, span := token.span })
      remaining := by
  intro _
  refine ⟨[token], rfl, ?_, token_starts_self token,
    token_ends_self token⟩
  simpa [Expr.expectedTokens] using
    ExpectedToken.ListMatches.cons
      (expectedTokenExact_matches kind) ExpectedToken.ListMatches.nil

private theorem prefixNameCorrespondenceProperty
    (file : SourceFile)
    (token : Token)
    (text : String)
    (remaining : List Token)
    (kind : token.kind = .identifier text)
    (_notCall : HeadKindNe .leftParen remaining) :
    PrefixCorrespondenceProperty file (token :: remaining)
      (.name { value := text, span := token.span }) remaining := by
  intro _
  refine ⟨[token], rfl, ?_, token_starts_self token,
    token_ends_self token⟩
  simpa [Expr.expectedTokens] using
    ExpectedToken.ListMatches.cons
      (expectedTokenExact_matches kind) ExpectedToken.ListMatches.nil

private theorem prefixCallCorrespondenceProperty
    (file : SourceFile)
    (identifier left right : Token)
    (text : String)
    (afterLeft remaining : List Token)
    (arguments : List Expr)
    (identifierKind : identifier.kind = .identifier text)
    (leftKind : left.kind = .leftParen)
    (_argumentsParse : ArgumentsParse afterLeft arguments right remaining)
    (argumentsIH : ArgumentsCorrespondenceProperty file
      afterLeft arguments right remaining) :
    PrefixCorrespondenceProperty file (identifier :: left :: afterLeft)
      (.call
        (SourceSpan.cover identifier.span right.span)
        { value := text, span := identifier.span }
        arguments)
      remaining := by
  intro valid
  have identifierValid := valid identifier (by simp)
  have afterLeftValid := tokensValidFor_tail (tokensValidFor_tail valid)
  rcases argumentsIH afterLeftValid with
    ⟨argumentTokens, afterLeftEq, argumentMatch⟩
  rw [afterLeftEq] at afterLeftValid
  have rightValid := afterLeftValid right (by simp)
  have rightKind := arguments_rightKind _argumentsParse
  have sourceEq := tokenSpan_sources_eq identifierValid rightValid
  let consumed := identifier :: left :: argumentTokens ++ [right]
  have starts : TokensStartWith
      (SourceSpan.cover identifier.span right.span) consumed := by
    simpa [consumed] using
      tokensStartWith_cover
        (second := left :: argumentTokens ++ [right])
        (token_starts_self identifier)
  have ends : TokensEndWith
      (SourceSpan.cover identifier.span right.span) consumed := by
    simpa [consumed] using
      tokensEndWith_cover (identifier :: left :: argumentTokens)
        sourceEq (token_ends_self right)
  refine ⟨consumed, ?_, ?_, starts, ends⟩
  · simp [consumed, afterLeftEq, List.append_assoc]
  · rw [call_expectedTokens_eq]
    apply ExpectedToken.ListMatches.enclose
    · exact .cons (expectedTokenExact_matches identifierKind)
        (.cons (expectedTokenPlain_matches leftKind)
          (ExpectedToken.ListMatches.append argumentMatch
            (.cons (expectedTokenPlain_matches rightKind) .nil)))
    · exact starts
    · exact ends

private theorem infixStopCorrespondenceProperty
    (file : SourceFile)
    (minimum : Nat)
    (left : Expr)
    (tokens : List Token)
    (_blocked : InfixBlocked minimum tokens) :
    InfixCorrespondenceProperty file minimum left tokens left tokens := by
  intro leftTokens leftMatch leftStarts leftEnds _ _
  exact ⟨[], rfl, by simpa, by simpa, by simpa⟩

private theorem infixLeftStepCorrespondenceProperty
    (file : SourceFile)
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding :
      BinaryBinding operatorToken.kind operator precedence .left)
    (_eligible : minimum ≤ precedence)
    (_rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (_tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH : ExprCorrespondenceProperty file (precedence + 1)
      afterOperator right afterRight)
    (tailIH : InfixCorrespondenceProperty file minimum
      (.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right)
      afterRight result remaining) :
    InfixCorrespondenceProperty file minimum left
      (operatorToken :: afterOperator) result remaining := by
  intro leftTokens leftMatch leftStarts leftEnds leftValid inputValid
  have operatorValid := inputValid operatorToken (by simp)
  have afterOperatorValid := tokensValidFor_tail inputValid
  rcases rightIH afterOperatorValid with
    ⟨rightTokens, afterOperatorEq, rightMatch, rightStarts, rightEnds⟩
  rw [afterOperatorEq] at afterOperatorValid
  have rightTokensValid :=
    tokensValidFor_append_left afterOperatorValid
  have afterRightValid :=
    tokensValidFor_append_right afterOperatorValid
  have sourceEq : left.span.source = right.span.source :=
    (span_source_eq_of_tokensStartWith leftValid leftStarts).trans
      (span_source_eq_of_tokensStartWith
        rightTokensValid rightStarts).symm
  have operatorKind : operatorToken.kind = operator.tokenKind :=
    binaryBinding_kind_eq binding
  let binaryTokens := leftTokens ++ operatorToken :: rightTokens
  have binaryMatch : ExpectedToken.ListMatches
      (Expr.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right).expectedTokens binaryTokens := by
    have rawMatch := ExpectedToken.ListMatches.append leftMatch
      (.cons (expectedTokenExact_matches operatorKind) rightMatch)
    have starts : TokensStartWith
        (SourceSpan.cover left.span right.span) binaryTokens := by
      simpa [binaryTokens] using
        tokensStartWith_cover
          (second := operatorToken :: rightTokens) leftStarts
    have ends : TokensEndWith
        (SourceSpan.cover left.span right.span) binaryTokens := by
      simpa [binaryTokens, List.append_assoc] using
        tokensEndWith_cover (leftTokens ++ [operatorToken])
          sourceEq rightEnds
    simpa [binaryTokens, Expr.expectedTokens] using
      ExpectedToken.ListMatches.enclose rawMatch starts ends
  have binaryStarts : TokensStartWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens] using
      tokensStartWith_cover
        (second := operatorToken :: rightTokens) leftStarts
  have binaryEnds : TokensEndWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens, List.append_assoc] using
      tokensEndWith_cover (leftTokens ++ [operatorToken])
        sourceEq rightEnds
  have binaryValid : TokensValidFor file binaryTokens := by
    simp only [binaryTokens]
    exact tokensValidFor_append leftValid
      (by
        intro token member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact operatorValid
        · exact rightTokensValid token member)
  rcases tailIH binaryTokens binaryMatch binaryStarts binaryEnds
      binaryValid afterRightValid with
    ⟨tailTokens, afterRightEq, resultMatch, resultStarts, resultEnds⟩
  refine ⟨operatorToken :: rightTokens ++ tailTokens, ?_, ?_, ?_, ?_⟩
  · simp only [List.cons_append]
    rw [afterOperatorEq, afterRightEq, List.append_assoc]
  · simpa [binaryTokens, List.append_assoc] using resultMatch
  · simpa [binaryTokens, List.append_assoc] using resultStarts
  · simpa [binaryTokens, List.append_assoc] using resultEnds

private theorem infixNonAssociativeStepCorrespondenceProperty
    (file : SourceFile)
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding :
      BinaryBinding operatorToken.kind operator precedence
        .nonAssociative)
    (_eligible : minimum ≤ precedence)
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
    (rightIH : ExprCorrespondenceProperty file (precedence + 1)
      afterOperator right afterRight)
    (tailIH : InfixCorrespondenceProperty file minimum
      (.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right)
      afterRight result remaining) :
    InfixCorrespondenceProperty file minimum left
      (operatorToken :: afterOperator) result remaining := by
  intro leftTokens leftMatch leftStarts leftEnds leftValid inputValid
  have operatorValid := inputValid operatorToken (by simp)
  have afterOperatorValid := tokensValidFor_tail inputValid
  rcases rightIH afterOperatorValid with
    ⟨rightTokens, afterOperatorEq, rightMatch, rightStarts, rightEnds⟩
  rw [afterOperatorEq] at afterOperatorValid
  have rightTokensValid :=
    tokensValidFor_append_left afterOperatorValid
  have afterRightValid :=
    tokensValidFor_append_right afterOperatorValid
  have sourceEq : left.span.source = right.span.source :=
    (span_source_eq_of_tokensStartWith leftValid leftStarts).trans
      (span_source_eq_of_tokensStartWith
        rightTokensValid rightStarts).symm
  have operatorKind : operatorToken.kind = operator.tokenKind :=
    binaryBinding_kind_eq binding
  let binaryTokens := leftTokens ++ operatorToken :: rightTokens
  have binaryStarts : TokensStartWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens] using
      tokensStartWith_cover
        (second := operatorToken :: rightTokens) leftStarts
  have binaryEnds : TokensEndWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens, List.append_assoc] using
      tokensEndWith_cover (leftTokens ++ [operatorToken])
        sourceEq rightEnds
  have binaryMatch : ExpectedToken.ListMatches
      (Expr.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right).expectedTokens binaryTokens := by
    have rawMatch := ExpectedToken.ListMatches.append leftMatch
      (.cons (expectedTokenExact_matches operatorKind) rightMatch)
    simpa [binaryTokens, Expr.expectedTokens] using
      ExpectedToken.ListMatches.enclose rawMatch binaryStarts binaryEnds
  have binaryValid : TokensValidFor file binaryTokens := by
    simp only [binaryTokens]
    exact tokensValidFor_append leftValid
      (by
        intro token member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact operatorValid
        · exact rightTokensValid token member)
  rcases tailIH binaryTokens binaryMatch binaryStarts binaryEnds
      binaryValid afterRightValid with
    ⟨tailTokens, afterRightEq, resultMatch, resultStarts, resultEnds⟩
  refine ⟨operatorToken :: rightTokens ++ tailTokens, ?_, ?_, ?_, ?_⟩
  · simp only [List.cons_append]
    rw [afterOperatorEq, afterRightEq, List.append_assoc]
  · simpa [binaryTokens, List.append_assoc] using resultMatch
  · simpa [binaryTokens, List.append_assoc] using resultStarts
  · simpa [binaryTokens, List.append_assoc] using resultEnds

private theorem exprOrdinaryCorrespondenceProperty
    (file : SourceFile)
    (minimum : Nat)
    (input afterPrefix remaining : List Token)
    (initial result : Expr)
    (_prefixParse : PrefixParses input initial afterPrefix)
    (_infixParse :
      InfixParses minimum initial afterPrefix result remaining)
    (prefixIH :
      PrefixCorrespondenceProperty file input initial afterPrefix)
    (infixIH : InfixCorrespondenceProperty file minimum initial
      afterPrefix result remaining) :
    ExprCorrespondenceProperty file minimum input result remaining := by
  intro valid
  rcases prefixIH valid with
    ⟨initialTokens, inputEq, initialMatch, initialStarts, initialEnds⟩
  rw [inputEq] at valid
  have initialValid := tokensValidFor_append_left valid
  have afterPrefixValid := tokensValidFor_append_right valid
  rcases infixIH initialTokens initialMatch initialStarts initialEnds
      initialValid afterPrefixValid with
    ⟨tailTokens, afterPrefixEq, resultMatch, resultStarts, resultEnds⟩
  refine ⟨initialTokens ++ tailTokens, ?_, resultMatch,
    resultStarts, resultEnds⟩
  rw [inputEq, afterPrefixEq, List.append_assoc]

private theorem exprConditionalCorrespondenceProperty
    (file : SourceFile)
    (ifToken thenToken elseToken : Token)
    (afterIf afterThen afterElse remaining : List Token)
    (condition thenBranch elseBranch : Expr)
    (ifKind : ifToken.kind = .keywordIf)
    (_conditionParse :
      ExprParses 0 afterIf condition (thenToken :: afterThen))
    (thenKind : thenToken.kind = .identifier "then")
    (_thenParse :
      ExprParses 0 afterThen thenBranch (elseToken :: afterElse))
    (elseKind : elseToken.kind = .keywordElse)
    (_elseParse : ExprParses 0 afterElse elseBranch remaining)
    (conditionIH : ExprCorrespondenceProperty file 0 afterIf condition
      (thenToken :: afterThen))
    (thenIH : ExprCorrespondenceProperty file 0 afterThen thenBranch
      (elseToken :: afterElse))
    (elseIH : ExprCorrespondenceProperty file 0 afterElse elseBranch
      remaining) :
    ExprCorrespondenceProperty file 0 (ifToken :: afterIf)
      (.ifThenElse
        (SourceSpan.cover ifToken.span elseBranch.span)
        condition thenBranch elseBranch)
      remaining := by
  intro valid
  have ifValid := valid ifToken (by simp)
  have afterIfValid := tokensValidFor_tail valid
  rcases conditionIH afterIfValid with
    ⟨conditionTokens, afterIfEq, conditionMatch, _, _⟩
  rw [afterIfEq] at afterIfValid
  have thenTokenValid := afterIfValid thenToken (by simp)
  have afterThenValid := tokensValidFor_tail
    (tokensValidFor_append_right afterIfValid)
  rcases thenIH afterThenValid with
    ⟨thenTokens, afterThenEq, thenMatch, _, _⟩
  rw [afterThenEq] at afterThenValid
  have elseTokenValid := afterThenValid elseToken (by simp)
  have afterElseValid := tokensValidFor_tail
    (tokensValidFor_append_right afterThenValid)
  rcases elseIH afterElseValid with
    ⟨elseTokens, afterElseEq, elseMatch, elseStarts, elseEnds⟩
  rw [afterElseEq] at afterElseValid
  have elseTokensValid := tokensValidFor_append_left afterElseValid
  have sourceEq : ifToken.span.source = elseBranch.span.source :=
    (tokenSpan_source_eq ifValid).trans
      (span_source_eq_of_tokensStartWith
        elseTokensValid elseStarts).symm
  let consumed :=
    ifToken :: conditionTokens ++
      thenToken :: thenTokens ++ elseToken :: elseTokens
  have starts : TokensStartWith
      (SourceSpan.cover ifToken.span elseBranch.span) consumed := by
    simpa [consumed] using
      tokensStartWith_cover
        (second := conditionTokens ++ thenToken :: thenTokens ++
          elseToken :: elseTokens)
        (token_starts_self ifToken)
  have ends : TokensEndWith
      (SourceSpan.cover ifToken.span elseBranch.span) consumed := by
    simpa [consumed, List.append_assoc] using
      tokensEndWith_cover
        (ifToken :: conditionTokens ++
          thenToken :: thenTokens ++ [elseToken])
        sourceEq elseEnds
  have rawMatch : ExpectedToken.ListMatches
      (ExpectedToken.plain .keywordIf ::
        condition.expectedTokens ++
        ExpectedToken.plain (.identifier "then") ::
        thenBranch.expectedTokens ++
        ExpectedToken.plain .keywordElse ::
        elseBranch.expectedTokens)
      consumed := by
    simp only [consumed]
    have throughThen :=
      ExpectedToken.ListMatches.append conditionMatch
        (.cons (expectedTokenPlain_matches thenKind) thenMatch)
    exact .cons (expectedTokenPlain_matches ifKind)
      (ExpectedToken.ListMatches.append throughThen
        (.cons (expectedTokenPlain_matches elseKind) elseMatch))
  refine ⟨consumed, ?_, ?_, starts, ends⟩
  · simp only [consumed, List.cons_append]
    rw [afterIfEq, afterThenEq, afterElseEq]
    simp [List.append_assoc]
  · simpa [Expr.expectedTokens] using
      ExpectedToken.ListMatches.enclose rawMatch starts ends

private theorem exprParsesCorrespondenceProperty
    (file : SourceFile)
    {minimum : Nat}
    {input remaining : List Token}
    {expression : Expr}
    (derivation : ExprParses minimum input expression remaining) :
    ExprCorrespondenceProperty file minimum input expression remaining :=
  ExprParses.rec
    (motive_1 := fun minimum input expression remaining _ =>
      ExprCorrespondenceProperty file minimum input expression remaining)
    (motive_2 := fun input expression remaining _ =>
      PrefixCorrespondenceProperty file input expression remaining)
    (motive_3 := fun minimum left input expression remaining _ =>
      InfixCorrespondenceProperty file minimum left input expression remaining)
    (motive_4 := fun input arguments right remaining _ =>
      ArgumentsCorrespondenceProperty file input arguments right remaining)
    (motive_5 := fun input arguments right remaining _ =>
      ArgumentTailCorrespondenceProperty file
        input arguments right remaining)
    (exprConditionalCorrespondenceProperty file)
    (exprOrdinaryCorrespondenceProperty file)
    (prefixNotCorrespondenceProperty file)
    (prefixUnitCorrespondenceProperty file)
    (prefixGroupCorrespondenceProperty file)
    (prefixDecimalCorrespondenceProperty file)
    (prefixHexadecimalCorrespondenceProperty file)
    (prefixNameCorrespondenceProperty file)
    (prefixCallCorrespondenceProperty file)
    (infixStopCorrespondenceProperty file)
    (infixLeftStepCorrespondenceProperty file)
    (infixNonAssociativeStepCorrespondenceProperty file)
    (argumentsEmptyCorrespondenceProperty file)
    (argumentsNonemptyCorrespondenceProperty file)
    (argumentTailDoneCorrespondenceProperty file)
    (argumentTailMoreCorrespondenceProperty file)
    derivation

private theorem prefixParsesCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {expression : Expr}
    (derivation : PrefixParses input expression remaining) :
    PrefixCorrespondenceProperty file input expression remaining :=
  PrefixParses.rec
    (motive_1 := fun minimum input expression remaining _ =>
      ExprCorrespondenceProperty file minimum input expression remaining)
    (motive_2 := fun input expression remaining _ =>
      PrefixCorrespondenceProperty file input expression remaining)
    (motive_3 := fun minimum left input expression remaining _ =>
      InfixCorrespondenceProperty file minimum left input expression remaining)
    (motive_4 := fun input arguments right remaining _ =>
      ArgumentsCorrespondenceProperty file input arguments right remaining)
    (motive_5 := fun input arguments right remaining _ =>
      ArgumentTailCorrespondenceProperty file
        input arguments right remaining)
    (exprConditionalCorrespondenceProperty file)
    (exprOrdinaryCorrespondenceProperty file)
    (prefixNotCorrespondenceProperty file)
    (prefixUnitCorrespondenceProperty file)
    (prefixGroupCorrespondenceProperty file)
    (prefixDecimalCorrespondenceProperty file)
    (prefixHexadecimalCorrespondenceProperty file)
    (prefixNameCorrespondenceProperty file)
    (prefixCallCorrespondenceProperty file)
    (infixStopCorrespondenceProperty file)
    (infixLeftStepCorrespondenceProperty file)
    (infixNonAssociativeStepCorrespondenceProperty file)
    (argumentsEmptyCorrespondenceProperty file)
    (argumentsNonemptyCorrespondenceProperty file)
    (argumentTailDoneCorrespondenceProperty file)
    (argumentTailMoreCorrespondenceProperty file)
    derivation

private def ExprValidityProperty
    (file : SourceFile)
    (_minimum : Nat)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith expression.span consumed ∧
      TokensEndWith expression.span consumed ∧
      expression.ValidFor file

private def PrefixValidityProperty
    (file : SourceFile)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith expression.span consumed ∧
      TokensEndWith expression.span consumed ∧
      expression.ValidFor file

private def InfixValidityProperty
    (file : SourceFile)
    (_minimum : Nat)
    (left : Expr)
    (input : List Token)
    (expression : Expr)
    (remaining : List Token) : Prop :=
  ∀ leftTokens,
    TokensStartWith left.span leftTokens →
    TokensEndWith left.span leftTokens →
    left.ValidFor file →
    TokensValidFor file leftTokens →
    TokensOrdered leftTokens →
    TokensValidFor file input →
    TokensOrdered input →
    TokensOrdered (leftTokens ++ input) →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith expression.span (leftTokens ++ consumed) ∧
      TokensEndWith expression.span (leftTokens ++ consumed) ∧
      expression.ValidFor file

private def ArgumentsValidityProperty
    (file : SourceFile)
    (input : List Token)
    (arguments : List Expr)
    (right : Token)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ right :: remaining ∧
      ∀ argument ∈ arguments,
        argument.ValidFor file ∧
        ∃ argumentTokens,
          TokensStartWith argument.span argumentTokens ∧
          TokensEndWith argument.span argumentTokens ∧
          TokensValidFor file argumentTokens ∧
          TokensOrdered argumentTokens ∧
          ∀ token ∈ argumentTokens, token ∈ consumed

private def ArgumentTailValidityProperty
    (file : SourceFile)
    (input : List Token)
    (arguments : List Expr)
    (right : Token)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ right :: remaining ∧
      ∀ argument ∈ arguments,
        argument.ValidFor file ∧
        ∃ argumentTokens,
          TokensStartWith argument.span argumentTokens ∧
          TokensEndWith argument.span argumentTokens ∧
          TokensValidFor file argumentTokens ∧
          TokensOrdered argumentTokens ∧
          ∀ token ∈ argumentTokens, token ∈ consumed

private theorem argumentsEmptyValidityProperty
    (file : SourceFile)
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentsValidityProperty file
      (right :: remaining) [] right remaining := by
  intro _ _
  exact ⟨[], rfl, by simp⟩

private theorem argumentsNonemptyValidityProperty
    (file : SourceFile)
    (input afterFirst remaining : List Token)
    (first : Expr)
    (tail : List Expr)
    (right : Token)
    (_firstParse : ExprParses 0 input first afterFirst)
    (_tailParse : ArgumentTailParses afterFirst tail right remaining)
    (firstIH : ExprValidityProperty file 0 input first afterFirst)
    (tailIH : ArgumentTailValidityProperty file
      afterFirst tail right remaining) :
    ArgumentsValidityProperty file input (first :: tail) right remaining := by
  intro valid ordered
  rcases firstIH valid ordered with
    ⟨firstTokens, inputEq, firstStarts, firstEnds, firstValid⟩
  rw [inputEq] at valid ordered
  have firstTokensValid := tokensValidFor_append_left valid
  have firstTokensOrdered := tokensOrdered_append_left ordered
  have afterFirstValid := tokensValidFor_append_right valid
  have afterFirstOrdered := tokensOrdered_append_right firstTokens ordered
  rcases tailIH afterFirstValid afterFirstOrdered with
    ⟨tailTokens, afterFirstEq, tailEvidence⟩
  refine ⟨firstTokens ++ tailTokens, ?_, ?_⟩
  · rw [inputEq, afterFirstEq, List.append_assoc]
  · intro argument member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨firstValid, firstTokens, firstStarts, firstEnds,
        firstTokensValid, firstTokensOrdered,
        fun token tokenMember => List.mem_append_left _ tokenMember⟩
    · rcases tailEvidence argument member with
        ⟨argumentValid, argumentTokens, starts, ends,
          argumentTokensValid, argumentTokensOrdered, subset⟩
      exact ⟨argumentValid, argumentTokens, starts, ends,
        argumentTokensValid, argumentTokensOrdered,
        fun token tokenMember =>
          List.mem_append_right firstTokens (subset token tokenMember)⟩

private theorem argumentTailDoneValidityProperty
    (file : SourceFile)
    (right : Token)
    (remaining : List Token)
    (_rightKind : right.kind = .rightParen) :
    ArgumentTailValidityProperty file
      (right :: remaining) [] right remaining := by
  intro _ _
  exact ⟨[], rfl, by simp⟩

private theorem argumentTailMoreValidityProperty
    (file : SourceFile)
    (comma right : Token)
    (afterComma afterNext remaining : List Token)
    (next : Expr)
    (tail : List Expr)
    (_commaKind : comma.kind = .comma)
    (_nextParse : ExprParses 0 afterComma next afterNext)
    (_tailParse : ArgumentTailParses afterNext tail right remaining)
    (nextIH : ExprValidityProperty file 0 afterComma next afterNext)
    (tailIH : ArgumentTailValidityProperty file
      afterNext tail right remaining) :
    ArgumentTailValidityProperty file (comma :: afterComma)
      (next :: tail) right remaining := by
  intro valid ordered
  have afterCommaValid := tokensValidFor_tail valid
  have afterCommaOrdered := tokensOrdered_tail ordered
  rcases nextIH afterCommaValid afterCommaOrdered with
    ⟨nextTokens, afterCommaEq, nextStarts, nextEnds, nextValid⟩
  rw [afterCommaEq] at afterCommaValid afterCommaOrdered
  have nextTokensValid := tokensValidFor_append_left afterCommaValid
  have nextTokensOrdered := tokensOrdered_append_left afterCommaOrdered
  have afterNextValid := tokensValidFor_append_right afterCommaValid
  have afterNextOrdered :=
    tokensOrdered_append_right nextTokens afterCommaOrdered
  rcases tailIH afterNextValid afterNextOrdered with
    ⟨tailTokens, afterNextEq, tailEvidence⟩
  refine ⟨comma :: nextTokens ++ tailTokens, ?_, ?_⟩
  · simp only [List.cons_append]
    rw [afterCommaEq, afterNextEq, List.append_assoc]
  · intro argument member
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact ⟨nextValid, nextTokens, nextStarts, nextEnds,
        nextTokensValid, nextTokensOrdered,
        fun token tokenMember => by
          simp [tokenMember]⟩
    · rcases tailEvidence argument member with
        ⟨argumentValid, argumentTokens, starts, ends,
          argumentTokensValid, argumentTokensOrdered, subset⟩
      exact ⟨argumentValid, argumentTokens, starts, ends,
        argumentTokensValid, argumentTokensOrdered,
        fun token tokenMember => by
          simp [subset token tokenMember]⟩

private theorem prefixNotValidityProperty
    (file : SourceFile)
    (operatorToken : Token)
    (afterOperator remaining : List Token)
    (operand : Expr)
    (_operatorKind : operatorToken.kind = .bang)
    (_operandParse : PrefixParses afterOperator operand remaining)
    (operandIH : PrefixValidityProperty file
      afterOperator operand remaining) :
    PrefixValidityProperty file (operatorToken :: afterOperator)
      (.unary
        (SourceSpan.cover operatorToken.span operand.span)
        { value := .not, span := operatorToken.span }
        operand)
      remaining := by
  intro valid ordered
  have operatorValid := valid operatorToken (by simp)
  have afterOperatorValid := tokensValidFor_tail valid
  have afterOperatorOrdered := tokensOrdered_tail ordered
  rcases operandIH afterOperatorValid afterOperatorOrdered with
    ⟨operandTokens, afterOperatorEq, operandStarts, operandEnds,
      operandValid⟩
  rw [afterOperatorEq] at afterOperatorValid afterOperatorOrdered
  have operandTokensValid :=
    tokensValidFor_append_left afterOperatorValid
  have operandTokensOrdered :=
    tokensOrdered_append_left afterOperatorOrdered
  have sourceEq : operatorToken.span.source = operand.span.source :=
    (tokenSpan_source_eq operatorValid).trans
      (span_source_eq_of_tokensStartWith
        operandTokensValid operandStarts).symm
  let consumed := operatorToken :: operandTokens
  have starts : TokensStartWith
      (SourceSpan.cover operatorToken.span operand.span) consumed := by
    simpa [consumed] using
      tokensStartWith_cover (second := operandTokens)
        (token_starts_self operatorToken)
  have ends : TokensEndWith
      (SourceSpan.cover operatorToken.span operand.span) consumed := by
    simpa [consumed] using
      tokensEndWith_cover [operatorToken] sourceEq operandEnds
  have inputEq : operatorToken :: afterOperator = consumed ++ remaining := by
    simp [consumed, afterOperatorEq]
  rw [inputEq] at valid ordered
  have consumedValid := tokensValidFor_append_left valid
  have consumedOrdered := tokensOrdered_append_left ordered
  have spanValid := spanValidFor_of_delimitedTokens
    consumedValid consumedOrdered starts ends
  have containsOperator := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    (tokensValidFor_singleton operatorValid)
    (by simp [TokensOrdered, Lexed.SpansOrdered])
    (token_starts_self operatorToken) (token_ends_self operatorToken)
    (fun token member => by
      simp only [List.mem_singleton] at member
      subst token
      simp [consumed])
  have containsOperand := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    operandTokensValid operandTokensOrdered operandStarts operandEnds
    (fun token member => by simp [consumed, member])
  exact ⟨consumed, inputEq,
    starts, ends,
    exprUnaryValidFor spanValid operatorValid.2.1 operandValid
      containsOperator containsOperand⟩

private theorem prefixUnitValidityProperty
    (file : SourceFile)
    (left right : Token)
    (remaining : List Token)
    (_leftKind : left.kind = .leftParen)
    (_rightKind : right.kind = .rightParen) :
    PrefixValidityProperty file (left :: right :: remaining)
      (.unit (SourceSpan.cover left.span right.span)) remaining := by
  intro valid ordered
  have leftValid := valid left (by simp)
  have rightValid := valid right (by simp)
  have sourceEq := tokenSpan_sources_eq leftValid rightValid
  have starts : TokensStartWith
      (SourceSpan.cover left.span right.span) [left, right] :=
    tokensStartWith_cover (lastSpan := right.span)
      (second := [right]) (token_starts_self left)
  have ends : TokensEndWith
      (SourceSpan.cover left.span right.span) [left, right] :=
    tokensEndWith_cover [left] sourceEq (token_ends_self right)
  have consumedValid := tokensValidFor_append_left
    (first := [left, right]) (second := remaining) valid
  have consumedOrdered := tokensOrdered_append_left
    (first := [left, right]) (second := remaining) ordered
  exact ⟨[left, right], rfl, starts, ends,
    exprUnitValidFor
      (spanValidFor_of_delimitedTokens consumedValid consumedOrdered
        starts ends)⟩

private theorem prefixGroupValidityProperty
    (file : SourceFile)
    (left right : Token)
    (afterLeft remaining : List Token)
    (inner : Expr)
    (_leftKind : left.kind = .leftParen)
    (_innerParse : ExprParses 0 afterLeft inner (right :: remaining))
    (_rightKind : right.kind = .rightParen)
    (innerIH : ExprValidityProperty file 0 afterLeft inner
      (right :: remaining)) :
    PrefixValidityProperty file (left :: afterLeft)
      (.group (SourceSpan.cover left.span right.span) inner) remaining := by
  intro valid ordered
  have leftValid := valid left (by simp)
  have afterLeftValid := tokensValidFor_tail valid
  have afterLeftOrdered := tokensOrdered_tail ordered
  rcases innerIH afterLeftValid afterLeftOrdered with
    ⟨innerTokens, afterLeftEq, innerStarts, innerEnds, innerValid⟩
  rw [afterLeftEq] at afterLeftValid afterLeftOrdered
  have innerTokensValid := tokensValidFor_append_left afterLeftValid
  have innerTokensOrdered := tokensOrdered_append_left afterLeftOrdered
  have rightValid := afterLeftValid right (by simp)
  have sourceEq := tokenSpan_sources_eq leftValid rightValid
  let consumed := left :: innerTokens ++ [right]
  have starts : TokensStartWith
      (SourceSpan.cover left.span right.span) consumed := by
    simpa [consumed] using tokensStartWith_cover
      (second := innerTokens ++ [right]) (token_starts_self left)
  have ends : TokensEndWith
      (SourceSpan.cover left.span right.span) consumed := by
    simpa [consumed] using tokensEndWith_cover
      (left :: innerTokens) sourceEq (token_ends_self right)
  have inputEq : left :: afterLeft = consumed ++ remaining := by
    simp [consumed, afterLeftEq, List.append_assoc]
  rw [inputEq] at valid ordered
  have consumedValid := tokensValidFor_append_left valid
  have consumedOrdered := tokensOrdered_append_left ordered
  have containsInner := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    innerTokensValid innerTokensOrdered innerStarts innerEnds
    (fun token member => by simp [consumed, member])
  exact ⟨consumed, inputEq, starts, ends,
    exprGroupValidFor
      (spanValidFor_of_delimitedTokens consumedValid consumedOrdered
        starts ends)
      innerValid containsInner⟩

private theorem prefixDecimalValidityProperty
    (file : SourceFile)
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (_kind : token.kind = .decimal digits) :
    PrefixValidityProperty file (token :: remaining)
      (.integer { base := .decimal, digits, span := token.span })
      remaining := by
  intro valid _
  exact ⟨[token], rfl, token_starts_self token, token_ends_self token,
    exprIntegerValidFor (valid token (by simp)).2.1⟩

private theorem prefixHexadecimalValidityProperty
    (file : SourceFile)
    (token : Token)
    (digits : String)
    (remaining : List Token)
    (_kind : token.kind = .hexadecimal digits) :
    PrefixValidityProperty file (token :: remaining)
      (.integer { base := .hexadecimal, digits, span := token.span })
      remaining := by
  intro valid _
  exact ⟨[token], rfl, token_starts_self token, token_ends_self token,
    exprIntegerValidFor (valid token (by simp)).2.1⟩

private theorem prefixNameValidityProperty
    (file : SourceFile)
    (token : Token)
    (text : String)
    (remaining : List Token)
    (_kind : token.kind = .identifier text)
    (_notCall : HeadKindNe .leftParen remaining) :
    PrefixValidityProperty file (token :: remaining)
      (.name { value := text, span := token.span }) remaining := by
  intro valid _
  exact ⟨[token], rfl, token_starts_self token, token_ends_self token,
    exprNameValidFor (valid token (by simp)).2.1⟩

private theorem prefixCallValidityProperty
    (file : SourceFile)
    (identifier left right : Token)
    (text : String)
    (afterLeft remaining : List Token)
    (arguments : List Expr)
    (_identifierKind : identifier.kind = .identifier text)
    (_leftKind : left.kind = .leftParen)
    (_argumentsParse : ArgumentsParse afterLeft arguments right remaining)
    (argumentsIH : ArgumentsValidityProperty file
      afterLeft arguments right remaining) :
    PrefixValidityProperty file (identifier :: left :: afterLeft)
      (.call
        (SourceSpan.cover identifier.span right.span)
        { value := text, span := identifier.span }
        arguments)
      remaining := by
  intro valid ordered
  have identifierValid := valid identifier (by simp)
  have afterLeftValid := tokensValidFor_tail (tokensValidFor_tail valid)
  have afterLeftOrdered := tokensOrdered_tail (tokensOrdered_tail ordered)
  rcases argumentsIH afterLeftValid afterLeftOrdered with
    ⟨argumentTokens, afterLeftEq, argumentEvidence⟩
  rw [afterLeftEq] at afterLeftValid afterLeftOrdered
  have argumentTokensValid := tokensValidFor_append_left afterLeftValid
  have rightValid := afterLeftValid right (by simp)
  have sourceEq := tokenSpan_sources_eq identifierValid rightValid
  let consumed := identifier :: left :: argumentTokens ++ [right]
  have starts : TokensStartWith
      (SourceSpan.cover identifier.span right.span) consumed := by
    simpa [consumed] using tokensStartWith_cover
      (second := left :: argumentTokens ++ [right])
      (token_starts_self identifier)
  have ends : TokensEndWith
      (SourceSpan.cover identifier.span right.span) consumed := by
    simpa [consumed] using tokensEndWith_cover
      (identifier :: left :: argumentTokens) sourceEq
      (token_ends_self right)
  have inputEq : identifier :: left :: afterLeft = consumed ++ remaining := by
    simp [consumed, afterLeftEq, List.append_assoc]
  rw [inputEq] at valid ordered
  have consumedValid := tokensValidFor_append_left valid
  have consumedOrdered := tokensOrdered_append_left ordered
  have containsCallee := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    (tokensValidFor_singleton identifierValid)
    (by simp [TokensOrdered, Lexed.SpansOrdered])
    (token_starts_self identifier) (token_ends_self identifier)
    (fun token member => by
      simp only [List.mem_singleton] at member
      subst token
      simp [consumed])
  have argumentsValid :
      ∀ argument ∈ arguments, argument.ValidFor file :=
    fun argument member => (argumentEvidence argument member).1
  have containsArguments :
      ∀ argument ∈ arguments,
        (SourceSpan.cover identifier.span right.span).Contains
          argument.span := by
    intro argument member
    rcases argumentEvidence argument member with
      ⟨_, tokens, argumentStarts, argumentEnds,
        tokensValid, tokensOrdered, subset⟩
    exact spanContains_of_delimitedSubset
      consumedValid consumedOrdered starts ends
      tokensValid tokensOrdered argumentStarts argumentEnds
      (fun token tokenMember => by
        simp [consumed, subset token tokenMember])
  exact ⟨consumed, inputEq, starts, ends,
    exprCallValidFor
      (spanValidFor_of_delimitedTokens consumedValid consumedOrdered
        starts ends)
      identifierValid.2.1 containsCallee argumentsValid containsArguments⟩

private theorem infixStopValidityProperty
    (file : SourceFile)
    (minimum : Nat)
    (left : Expr)
    (tokens : List Token)
    (_blocked : InfixBlocked minimum tokens) :
    InfixValidityProperty file minimum left tokens left tokens := by
  intro leftTokens leftStarts leftEnds leftValid _ _ _ _ _
  exact ⟨[], rfl, by simpa, by simpa, leftValid⟩

private theorem infixStepValidityCore
    (file : SourceFile)
    (minimum precedence : Nat)
    (associativity : Associativity)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding : BinaryBinding operatorToken.kind operator precedence
      associativity)
    (_rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (_tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH : ExprValidityProperty file (precedence + 1)
      afterOperator right afterRight)
    (tailIH : InfixValidityProperty file minimum
      (.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right)
      afterRight result remaining) :
    InfixValidityProperty file minimum left
      (operatorToken :: afterOperator) result remaining := by
  intro leftTokens leftStarts leftEnds leftAstValid leftValid leftOrdered
    inputValid inputOrdered combinedOrdered
  have operatorValid := inputValid operatorToken (by simp)
  have afterOperatorValid := tokensValidFor_tail inputValid
  have afterOperatorOrdered := tokensOrdered_tail inputOrdered
  rcases rightIH afterOperatorValid afterOperatorOrdered with
    ⟨rightTokens, afterOperatorEq, rightStarts, rightEnds, rightAstValid⟩
  rw [afterOperatorEq] at afterOperatorValid afterOperatorOrdered
  have rightValid := tokensValidFor_append_left afterOperatorValid
  have rightOrdered := tokensOrdered_append_left afterOperatorOrdered
  have afterRightValid := tokensValidFor_append_right afterOperatorValid
  have afterRightOrdered :=
    tokensOrdered_append_right rightTokens afterOperatorOrdered
  have sourceEq : left.span.source = right.span.source :=
    (span_source_eq_of_tokensStartWith leftValid leftStarts).trans
      (span_source_eq_of_tokensStartWith rightValid rightStarts).symm
  let binaryTokens := leftTokens ++ operatorToken :: rightTokens
  have binaryStarts : TokensStartWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens] using tokensStartWith_cover
      (second := operatorToken :: rightTokens) leftStarts
  have binaryEnds : TokensEndWith
      (SourceSpan.cover left.span right.span) binaryTokens := by
    simpa [binaryTokens, List.append_assoc] using
      tokensEndWith_cover (leftTokens ++ [operatorToken])
        sourceEq rightEnds
  have binaryValid : TokensValidFor file binaryTokens := by
    simp only [binaryTokens]
    exact tokensValidFor_append leftValid
      (by
        intro token member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact operatorValid
        · exact rightValid token member)
  have binaryAndRestOrdered :
      TokensOrdered (binaryTokens ++ afterRight) := by
    rw [afterOperatorEq] at combinedOrdered
    simpa [binaryTokens, List.append_assoc] using combinedOrdered
  have binaryOrdered :=
    tokensOrdered_append_left binaryAndRestOrdered
  have containsLeft := spanContains_of_delimitedSubset
    binaryValid binaryOrdered binaryStarts binaryEnds
    leftValid leftOrdered leftStarts leftEnds
    (fun token member => by simp [binaryTokens, member])
  have containsRight := spanContains_of_delimitedSubset
    binaryValid binaryOrdered binaryStarts binaryEnds
    rightValid rightOrdered rightStarts rightEnds
    (fun token member => by simp [binaryTokens, member])
  have containsOperator := spanContains_of_delimitedSubset
    binaryValid binaryOrdered binaryStarts binaryEnds
    (tokensValidFor_singleton operatorValid)
    (by simp [TokensOrdered, Lexed.SpansOrdered])
    (token_starts_self operatorToken) (token_ends_self operatorToken)
    (fun token member => by
      simp only [List.mem_singleton] at member
      subst token
      simp [binaryTokens])
  have binaryAstValid :
      (Expr.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right).ValidFor file := exprBinaryValidFor
    (spanValidFor_of_delimitedTokens binaryValid binaryOrdered
      binaryStarts binaryEnds)
    operatorValid.2.1 leftAstValid rightAstValid containsOperator
    containsLeft containsRight
  rcases tailIH binaryTokens binaryStarts binaryEnds binaryAstValid
      binaryValid binaryOrdered afterRightValid afterRightOrdered
      binaryAndRestOrdered with
    ⟨tailTokens, afterRightEq, resultStarts, resultEnds, resultValid⟩
  refine ⟨operatorToken :: rightTokens ++ tailTokens, ?_, ?_, ?_,
    resultValid⟩
  · simp only [List.cons_append]
    rw [afterOperatorEq, afterRightEq, List.append_assoc]
  · simpa [binaryTokens, List.append_assoc] using resultStarts
  · simpa [binaryTokens, List.append_assoc] using resultEnds

private theorem infixLeftStepValidityProperty
    (file : SourceFile)
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding : BinaryBinding operatorToken.kind operator precedence .left)
    (_eligible : minimum ≤ precedence)
    (rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH : ExprValidityProperty file (precedence + 1)
      afterOperator right afterRight)
    (tailIH : InfixValidityProperty file minimum
      (.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right)
      afterRight result remaining) :
    InfixValidityProperty file minimum left
      (operatorToken :: afterOperator) result remaining :=
  infixStepValidityCore file minimum precedence .left left right result
    operatorToken operator afterOperator afterRight remaining binding
    rightParse tailParse rightIH tailIH

private theorem infixNonAssociativeStepValidityProperty
    (file : SourceFile)
    (minimum precedence : Nat)
    (left right result : Expr)
    (operatorToken : Token)
    (operator : BinaryOp)
    (afterOperator afterRight remaining : List Token)
    (binding : BinaryBinding operatorToken.kind operator precedence
      .nonAssociative)
    (_eligible : minimum ≤ precedence)
    (rightParse :
      ExprParses (precedence + 1) afterOperator right afterRight)
    (_notRepeated : HeadPrecedenceNe precedence afterRight)
    (tailParse :
      InfixParses minimum
        (.binary
          (SourceSpan.cover left.span right.span)
          { value := operator, span := operatorToken.span }
          left right)
        afterRight result remaining)
    (rightIH : ExprValidityProperty file (precedence + 1)
      afterOperator right afterRight)
    (tailIH : InfixValidityProperty file minimum
      (.binary
        (SourceSpan.cover left.span right.span)
        { value := operator, span := operatorToken.span }
        left right)
      afterRight result remaining) :
    InfixValidityProperty file minimum left
      (operatorToken :: afterOperator) result remaining :=
  infixStepValidityCore file minimum precedence .nonAssociative
    left right result operatorToken operator afterOperator afterRight remaining
    binding rightParse tailParse rightIH tailIH

private theorem exprOrdinaryValidityProperty
    (file : SourceFile)
    (minimum : Nat)
    (input afterPrefix remaining : List Token)
    (initial result : Expr)
    (_prefixParse : PrefixParses input initial afterPrefix)
    (_infixParse :
      InfixParses minimum initial afterPrefix result remaining)
    (prefixIH : PrefixValidityProperty file input initial afterPrefix)
    (infixIH : InfixValidityProperty file minimum initial
      afterPrefix result remaining) :
    ExprValidityProperty file minimum input result remaining := by
  intro valid ordered
  rcases prefixIH valid ordered with
    ⟨initialTokens, inputEq, initialStarts, initialEnds, initialAstValid⟩
  rw [inputEq] at valid ordered
  have initialValid := tokensValidFor_append_left valid
  have initialOrdered := tokensOrdered_append_left ordered
  have afterPrefixValid := tokensValidFor_append_right valid
  have afterPrefixOrdered :=
    tokensOrdered_append_right initialTokens ordered
  rcases infixIH initialTokens initialStarts initialEnds initialAstValid
      initialValid initialOrdered afterPrefixValid afterPrefixOrdered ordered with
    ⟨tailTokens, afterPrefixEq, resultStarts, resultEnds, resultValid⟩
  exact ⟨initialTokens ++ tailTokens,
    by rw [inputEq, afterPrefixEq, List.append_assoc],
    resultStarts, resultEnds, resultValid⟩

private theorem exprConditionalValidityProperty
    (file : SourceFile)
    (ifToken thenToken elseToken : Token)
    (afterIf afterThen afterElse remaining : List Token)
    (condition thenBranch elseBranch : Expr)
    (_ifKind : ifToken.kind = .keywordIf)
    (_conditionParse :
      ExprParses 0 afterIf condition (thenToken :: afterThen))
    (_thenKind : thenToken.kind = .identifier "then")
    (_thenParse :
      ExprParses 0 afterThen thenBranch (elseToken :: afterElse))
    (_elseKind : elseToken.kind = .keywordElse)
    (_elseParse : ExprParses 0 afterElse elseBranch remaining)
    (conditionIH : ExprValidityProperty file 0 afterIf condition
      (thenToken :: afterThen))
    (thenIH : ExprValidityProperty file 0 afterThen thenBranch
      (elseToken :: afterElse))
    (elseIH : ExprValidityProperty file 0 afterElse elseBranch remaining) :
    ExprValidityProperty file 0 (ifToken :: afterIf)
      (.ifThenElse
        (SourceSpan.cover ifToken.span elseBranch.span)
        condition thenBranch elseBranch)
      remaining := by
  intro valid ordered
  have ifValid := valid ifToken (by simp)
  have afterIfValid := tokensValidFor_tail valid
  have afterIfOrdered := tokensOrdered_tail ordered
  rcases conditionIH afterIfValid afterIfOrdered with
    ⟨conditionTokens, afterIfEq, conditionStarts, conditionEnds,
      conditionValid⟩
  rw [afterIfEq] at afterIfValid afterIfOrdered
  have conditionTokensValid := tokensValidFor_append_left afterIfValid
  have conditionTokensOrdered := tokensOrdered_append_left afterIfOrdered
  have afterThenValid := tokensValidFor_tail
    (tokensValidFor_append_right afterIfValid)
  have afterThenOrdered := tokensOrdered_tail
    (tokensOrdered_append_right conditionTokens afterIfOrdered)
  rcases thenIH afterThenValid afterThenOrdered with
    ⟨thenTokens, afterThenEq, thenStarts, thenEnds, thenValid⟩
  rw [afterThenEq] at afterThenValid afterThenOrdered
  have thenTokensValid := tokensValidFor_append_left afterThenValid
  have thenTokensOrdered := tokensOrdered_append_left afterThenOrdered
  have afterElseValid := tokensValidFor_tail
    (tokensValidFor_append_right afterThenValid)
  have afterElseOrdered := tokensOrdered_tail
    (tokensOrdered_append_right thenTokens afterThenOrdered)
  rcases elseIH afterElseValid afterElseOrdered with
    ⟨elseTokens, afterElseEq, elseStarts, elseEnds, elseValid⟩
  rw [afterElseEq] at afterElseValid afterElseOrdered
  have elseTokensValid := tokensValidFor_append_left afterElseValid
  have elseTokensOrdered := tokensOrdered_append_left afterElseOrdered
  have sourceEq : ifToken.span.source = elseBranch.span.source :=
    (tokenSpan_source_eq ifValid).trans
      (span_source_eq_of_tokensStartWith
        elseTokensValid elseStarts).symm
  let consumed :=
    ifToken :: conditionTokens ++
      thenToken :: thenTokens ++ elseToken :: elseTokens
  have starts : TokensStartWith
      (SourceSpan.cover ifToken.span elseBranch.span) consumed := by
    simpa [consumed] using tokensStartWith_cover
      (second := conditionTokens ++ thenToken :: thenTokens ++
        elseToken :: elseTokens)
      (token_starts_self ifToken)
  have ends : TokensEndWith
      (SourceSpan.cover ifToken.span elseBranch.span) consumed := by
    simpa [consumed, List.append_assoc] using tokensEndWith_cover
      (ifToken :: conditionTokens ++ thenToken :: thenTokens ++ [elseToken])
      sourceEq elseEnds
  have inputEq : ifToken :: afterIf = consumed ++ remaining := by
    simp only [consumed, List.cons_append]
    rw [afterIfEq, afterThenEq, afterElseEq]
    simp [List.append_assoc]
  rw [inputEq] at valid ordered
  have consumedValid := tokensValidFor_append_left valid
  have consumedOrdered := tokensOrdered_append_left ordered
  have containsCondition := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    conditionTokensValid conditionTokensOrdered conditionStarts conditionEnds
    (fun token member => by simp [consumed, member])
  have containsThen := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    thenTokensValid thenTokensOrdered thenStarts thenEnds
    (fun token member => by simp [consumed, member])
  have containsElse := spanContains_of_delimitedSubset
    consumedValid consumedOrdered starts ends
    elseTokensValid elseTokensOrdered elseStarts elseEnds
    (fun token member => by simp [consumed, member])
  exact ⟨consumed, inputEq, starts, ends,
    exprConditionalValidFor
      (spanValidFor_of_delimitedTokens consumedValid consumedOrdered
        starts ends)
      conditionValid thenValid elseValid containsCondition containsThen
      containsElse⟩

private theorem exprParsesValidityProperty
    (file : SourceFile)
    {minimum : Nat}
    {input remaining : List Token}
    {expression : Expr}
    (derivation : ExprParses minimum input expression remaining) :
    ExprValidityProperty file minimum input expression remaining :=
  ExprParses.rec
    (motive_1 := fun minimum input expression remaining _ =>
      ExprValidityProperty file minimum input expression remaining)
    (motive_2 := fun input expression remaining _ =>
      PrefixValidityProperty file input expression remaining)
    (motive_3 := fun minimum left input expression remaining _ =>
      InfixValidityProperty file minimum left input expression remaining)
    (motive_4 := fun input arguments right remaining _ =>
      ArgumentsValidityProperty file input arguments right remaining)
    (motive_5 := fun input arguments right remaining _ =>
      ArgumentTailValidityProperty file input arguments right remaining)
    (exprConditionalValidityProperty file)
    (exprOrdinaryValidityProperty file)
    (prefixNotValidityProperty file)
    (prefixUnitValidityProperty file)
    (prefixGroupValidityProperty file)
    (prefixDecimalValidityProperty file)
    (prefixHexadecimalValidityProperty file)
    (prefixNameValidityProperty file)
    (prefixCallValidityProperty file)
    (infixStopValidityProperty file)
    (infixLeftStepValidityProperty file)
    (infixNonAssociativeStepValidityProperty file)
    (argumentsEmptyValidityProperty file)
    (argumentsNonemptyValidityProperty file)
    (argumentTailDoneValidityProperty file)
    (argumentTailMoreValidityProperty file)
    derivation

private def TypeValidityProperty
    (file : SourceFile)
    (input : List Token)
    (type : TypeSyntax)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith type.span consumed ∧
      TokensEndWith type.span consumed ∧
      type.ValidFor file

private theorem typeParsesValidityProperty
    (file : SourceFile)
    {input remaining : List Token}
    {type : TypeSyntax}
    (derivation : TypeParses input type remaining) :
    TypeValidityProperty file input type remaining := by
  cases derivation with
  | unit left right remaining _ _ =>
      intro valid ordered
      have leftValid := valid left (by simp)
      have rightValid := valid right (by simp)
      have sourceEq := tokenSpan_sources_eq leftValid rightValid
      have starts : TokensStartWith
          (SourceSpan.cover left.span right.span) [left, right] :=
        tokensStartWith_cover (lastSpan := right.span)
          (second := [right]) (token_starts_self left)
      have ends : TokensEndWith
          (SourceSpan.cover left.span right.span) [left, right] :=
        tokensEndWith_cover [left] sourceEq (token_ends_self right)
      have consumedValid := tokensValidFor_append_left
        (first := [left, right]) (second := remaining) valid
      have consumedOrdered := tokensOrdered_append_left
        (first := [left, right]) (second := remaining) ordered
      exact ⟨[left, right], rfl, starts, ends,
        spanValidFor_of_delimitedTokens consumedValid consumedOrdered
          starts ends⟩
  | bool token remaining _ =>
      intro valid _
      exact ⟨[token], rfl, token_starts_self token, token_ends_self token,
        (valid token (by simp)).2.1⟩
  | word token remaining _ =>
      intro valid _
      exact ⟨[token], rfl, token_starts_self token, token_ends_self token,
        (valid token (by simp)).2.1⟩

private def LetValidityProperty
    (file : SourceFile)
    (input : List Token)
    (statement : LetStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith statement.span consumed ∧
      TokensEndWith statement.span consumed ∧
      statement.ValidFor file

private theorem letParsesValidityProperty
    (file : SourceFile)
    {input remaining : List Token}
    {statement : LetStatement}
    (derivation : LetParses input statement remaining) :
    LetValidityProperty file input statement remaining := by
  cases derivation with
  | intro letToken nameToken colonToken equalToken semicolonToken nameText
      afterColon afterEqual remaining type value _ _ _ typeParse _ valueParse _ =>
      intro valid ordered
      have letValid := valid letToken (by simp)
      have nameValid := valid nameToken (by simp)
      have afterColonValid :=
        tokensValidFor_tail (tokensValidFor_tail (tokensValidFor_tail valid))
      have afterColonOrdered :=
        tokensOrdered_tail (tokensOrdered_tail (tokensOrdered_tail ordered))
      rcases typeParsesValidityProperty file typeParse
          afterColonValid afterColonOrdered with
        ⟨typeTokens, afterColonEq, typeStarts, typeEnds, typeValid⟩
      rw [afterColonEq] at afterColonValid afterColonOrdered
      have typeTokensValid := tokensValidFor_append_left afterColonValid
      have typeTokensOrdered := tokensOrdered_append_left afterColonOrdered
      have afterEqualValid := tokensValidFor_tail
        (tokensValidFor_append_right afterColonValid)
      have afterEqualOrdered := tokensOrdered_tail
        (tokensOrdered_append_right typeTokens afterColonOrdered)
      rcases exprParsesValidityProperty file valueParse
          afterEqualValid afterEqualOrdered with
        ⟨valueTokens, afterEqualEq, valueStarts, valueEnds, valueValid⟩
      rw [afterEqualEq] at afterEqualValid afterEqualOrdered
      have valueTokensValid := tokensValidFor_append_left afterEqualValid
      have valueTokensOrdered := tokensOrdered_append_left afterEqualOrdered
      have semicolonValid := afterEqualValid semicolonToken (by simp)
      have sourceEq := tokenSpan_sources_eq letValid semicolonValid
      let consumed :=
        letToken :: nameToken :: colonToken :: typeTokens ++
          equalToken :: valueTokens ++ [semicolonToken]
      have starts : TokensStartWith
          (SourceSpan.cover letToken.span semicolonToken.span) consumed := by
        simpa [consumed] using tokensStartWith_cover
          (second := nameToken :: colonToken :: typeTokens ++
            equalToken :: valueTokens ++ [semicolonToken])
          (token_starts_self letToken)
      have ends : TokensEndWith
          (SourceSpan.cover letToken.span semicolonToken.span) consumed := by
        simpa [consumed, List.append_assoc] using tokensEndWith_cover
          (letToken :: nameToken :: colonToken :: typeTokens ++
            equalToken :: valueTokens)
          sourceEq (token_ends_self semicolonToken)
      have inputEq :
          letToken :: nameToken :: colonToken :: afterColon =
            consumed ++ remaining := by
        simp only [consumed, List.cons_append]
        rw [afterColonEq, afterEqualEq]
        simp [List.append_assoc]
      rw [inputEq] at valid ordered
      have consumedValid := tokensValidFor_append_left valid
      have consumedOrdered := tokensOrdered_append_left ordered
      have containsName := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        (tokensValidFor_singleton nameValid)
        (by simp [TokensOrdered, Lexed.SpansOrdered])
        (token_starts_self nameToken) (token_ends_self nameToken)
        (fun token member => by
          simp only [List.mem_singleton] at member
          subst token
          simp [consumed])
      have containsType := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        typeTokensValid typeTokensOrdered typeStarts typeEnds
        (fun token member => by simp [consumed, member])
      have containsValue := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        valueTokensValid valueTokensOrdered valueStarts valueEnds
        (fun token member => by simp [consumed, member])
      exact ⟨consumed, inputEq, starts, ends,
        ⟨spanValidFor_of_delimitedTokens consumedValid consumedOrdered
            starts ends,
          nameValid.2.1,
          containsName,
          containsType,
          containsValue,
          typeValid,
          valueValid⟩⟩
private def TypeCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (type : TypeSyntax)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches type.expectedTokens consumed ∧
      TokensStartWith type.span consumed ∧
      TokensEndWith type.span consumed

private theorem typeParsesCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {type : TypeSyntax}
    (derivation : TypeParses input type remaining) :
    TypeCorrespondenceProperty file input type remaining := by
  cases derivation with
  | unit left right remaining leftKind rightKind =>
      intro valid
      have leftValid := valid left (by simp)
      have rightValid := valid right (by simp)
      have sourceEq := tokenSpan_sources_eq leftValid rightValid
      have starts : TokensStartWith
          (SourceSpan.cover left.span right.span) [left, right] :=
        tokensStartWith_cover (lastSpan := right.span)
          (second := [right]) (token_starts_self left)
      have ends : TokensEndWith
          (SourceSpan.cover left.span right.span) [left, right] :=
        tokensEndWith_cover [left] sourceEq (token_ends_self right)
      refine ⟨[left, right], rfl, ?_, starts, ends⟩
      simpa [TypeSyntax.expectedTokens] using
        ExpectedToken.ListMatches.enclose
          (.cons (expectedTokenPlain_matches leftKind)
            (.cons (expectedTokenPlain_matches rightKind) .nil))
          starts ends
  | bool token remaining kind =>
      intro _
      refine ⟨[token], rfl, ?_, token_starts_self token,
        token_ends_self token⟩
      simpa [TypeSyntax.expectedTokens] using
        ExpectedToken.ListMatches.cons
          (expectedTokenExact_matches kind) ExpectedToken.ListMatches.nil
  | word token remaining kind =>
      intro _
      refine ⟨[token], rfl, ?_, token_starts_self token,
        token_ends_self token⟩
      simpa [TypeSyntax.expectedTokens] using
        ExpectedToken.ListMatches.cons
          (expectedTokenExact_matches kind) ExpectedToken.ListMatches.nil

private def LetCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (statement : LetStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches statement.expectedTokens consumed ∧
      TokensStartWith statement.span consumed ∧
      TokensEndWith statement.span consumed

private theorem letParsesCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {statement : LetStatement}
    (derivation : LetParses input statement remaining) :
    LetCorrespondenceProperty file input statement remaining := by
  cases derivation with
  | intro letToken nameToken colonToken equalToken semicolonToken nameText
      afterColon afterEqual remaining type value letKind nameKind colonKind
      typeParse equalKind valueParse semicolonKind =>
      intro valid
      have letValid := valid letToken (by simp)
      have afterColonValid :=
        tokensValidFor_tail (tokensValidFor_tail (tokensValidFor_tail valid))
      rcases typeParsesCorrespondenceProperty file typeParse
          afterColonValid with
        ⟨typeTokens, afterColonEq, typeMatch, _, _⟩
      rw [afterColonEq] at afterColonValid
      have afterEqualValid := tokensValidFor_tail
        (tokensValidFor_append_right afterColonValid)
      rcases exprParsesCorrespondenceProperty file valueParse
          afterEqualValid with
        ⟨valueTokens, afterEqualEq, valueMatch, _, _⟩
      rw [afterEqualEq] at afterEqualValid
      have semicolonValid := afterEqualValid semicolonToken (by simp)
      have sourceEq := tokenSpan_sources_eq letValid semicolonValid
      let consumed :=
        letToken :: nameToken :: colonToken :: typeTokens ++
          equalToken :: valueTokens ++ [semicolonToken]
      have starts : TokensStartWith
          (SourceSpan.cover letToken.span semicolonToken.span) consumed := by
        simpa [consumed] using
          tokensStartWith_cover
            (second := nameToken :: colonToken :: typeTokens ++
              equalToken :: valueTokens ++ [semicolonToken])
            (token_starts_self letToken)
      have ends : TokensEndWith
          (SourceSpan.cover letToken.span semicolonToken.span) consumed := by
        simpa [consumed, List.append_assoc] using
          tokensEndWith_cover
            (letToken :: nameToken :: colonToken :: typeTokens ++
              equalToken :: valueTokens)
            sourceEq (token_ends_self semicolonToken)
      have rawMatch : ExpectedToken.ListMatches
          (ExpectedToken.plain .keywordLet ::
            ExpectedToken.exact (.identifier nameText) nameToken.span ::
            ExpectedToken.plain .colon ::
            type.expectedTokens ++
            ExpectedToken.plain .equal ::
            value.expectedTokens ++
            [ExpectedToken.plain .semicolon])
          consumed := by
        simp only [consumed]
        exact .cons (expectedTokenPlain_matches letKind)
          (.cons (expectedTokenExact_matches nameKind)
            (.cons (expectedTokenPlain_matches colonKind)
              (ExpectedToken.ListMatches.append
                (ExpectedToken.ListMatches.append typeMatch
                  (.cons (expectedTokenPlain_matches equalKind) valueMatch))
                (.cons (expectedTokenPlain_matches semicolonKind) .nil))))
      refine ⟨consumed, ?_, ?_, starts, ends⟩
      · simp only [consumed, List.cons_append]
        rw [afterColonEq, afterEqualEq]
        simp [List.append_assoc]
      · simpa [LetStatement.expectedTokens] using
          ExpectedToken.ListMatches.enclose rawMatch starts ends

private def BindingsCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (bindings : List LetStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches
        (bindings.flatMap LetStatement.expectedTokens) consumed

private theorem bindingsParseCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {bindings : List LetStatement}
    (derivation : BindingsParse input bindings remaining) :
    BindingsCorrespondenceProperty file input bindings remaining := by
  induction derivation with
  | done =>
      intro _
      exact ⟨[], rfl, .nil⟩
  | more input afterBinding remaining binding bindings bindingParse
      tailParse tailIH =>
      intro valid
      rcases letParsesCorrespondenceProperty file bindingParse valid with
        ⟨bindingTokens, inputEq, bindingMatch, _, _⟩
      rw [inputEq] at valid
      have afterBindingValid := tokensValidFor_append_right valid
      rcases tailIH afterBindingValid with
        ⟨tailTokens, afterBindingEq, tailMatch⟩
      refine ⟨bindingTokens ++ tailTokens, ?_, ?_⟩
      · rw [inputEq, afterBindingEq, List.append_assoc]
      · simpa using
          ExpectedToken.ListMatches.append bindingMatch tailMatch

private def ReturnCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (statement : ReturnStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches statement.expectedTokens consumed ∧
      TokensStartWith statement.span consumed ∧
      TokensEndWith statement.span consumed

private theorem returnParsesCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {statement : ReturnStatement}
    (derivation : ReturnParses input statement remaining) :
    ReturnCorrespondenceProperty file input statement remaining := by
  cases derivation with
  | intro returnToken semicolonToken afterReturn remaining value returnKind
      valueParse semicolonKind =>
      intro valid
      have returnValid := valid returnToken (by simp)
      have afterReturnValid := tokensValidFor_tail valid
      rcases exprParsesCorrespondenceProperty file valueParse
          afterReturnValid with
        ⟨valueTokens, afterReturnEq, valueMatch, _, _⟩
      rw [afterReturnEq] at afterReturnValid
      have semicolonValid := afterReturnValid semicolonToken (by simp)
      have sourceEq := tokenSpan_sources_eq returnValid semicolonValid
      let consumed := returnToken :: valueTokens ++ [semicolonToken]
      have starts : TokensStartWith
          (SourceSpan.cover returnToken.span semicolonToken.span) consumed := by
        simpa [consumed] using
          tokensStartWith_cover
            (second := valueTokens ++ [semicolonToken])
            (token_starts_self returnToken)
      have ends : TokensEndWith
          (SourceSpan.cover returnToken.span semicolonToken.span) consumed := by
        simpa [consumed, List.append_assoc] using
          tokensEndWith_cover (returnToken :: valueTokens)
            sourceEq (token_ends_self semicolonToken)
      have rawMatch : ExpectedToken.ListMatches
          (ExpectedToken.plain .keywordReturn ::
            value.expectedTokens ++ [ExpectedToken.plain .semicolon])
          consumed := by
        simp only [consumed]
        exact .cons (expectedTokenPlain_matches returnKind)
          (ExpectedToken.ListMatches.append valueMatch
            (.cons (expectedTokenPlain_matches semicolonKind) .nil))
      refine ⟨consumed, ?_, ?_, starts, ends⟩
      · simp [consumed, afterReturnEq, List.append_assoc]
      · simpa [ReturnStatement.expectedTokens] using
          ExpectedToken.ListMatches.enclose rawMatch starts ends

private def FunctionCorrespondenceProperty
    (file : SourceFile)
    (input : List Token)
    (declaration : FunctionDecl)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ExpectedToken.ListMatches declaration.expectedTokens consumed ∧
      TokensStartWith declaration.span consumed ∧
      TokensEndWith declaration.span consumed

private theorem functionParsesCorrespondenceProperty
    (file : SourceFile)
    {input remaining : List Token}
    {declaration : FunctionDecl}
    (derivation : FunctionParses input declaration remaining) :
    FunctionCorrespondenceProperty file input declaration remaining := by
  cases derivation with
  | intro functionToken nameToken leftParen rightParen arrow leftBrace
      rightBrace nameText afterArrow afterLeftBrace afterBindings afterResult
      remaining returnType bindings result functionKind nameKind leftParenKind
      rightParenKind arrowKind typeParse leftBraceKind bindingsParse
      resultParse rightBraceKind =>
      intro valid
      have functionValid := valid functionToken (by simp)
      have afterArrowValid :=
        tokensValidFor_tail (tokensValidFor_tail (tokensValidFor_tail
          (tokensValidFor_tail (tokensValidFor_tail valid))))
      rcases typeParsesCorrespondenceProperty file typeParse
          afterArrowValid with
        ⟨typeTokens, afterArrowEq, typeMatch, _, _⟩
      rw [afterArrowEq] at afterArrowValid
      have afterLeftBraceValid := tokensValidFor_tail
        (tokensValidFor_append_right afterArrowValid)
      rcases bindingsParseCorrespondenceProperty file bindingsParse
          afterLeftBraceValid with
        ⟨bindingTokens, afterLeftBraceEq, bindingsMatch⟩
      rw [afterLeftBraceEq] at afterLeftBraceValid
      have afterBindingsValid :=
        tokensValidFor_append_right afterLeftBraceValid
      rcases returnParsesCorrespondenceProperty file resultParse
          afterBindingsValid with
        ⟨resultTokens, afterBindingsEq, resultMatch, _, _⟩
      rw [afterBindingsEq] at afterBindingsValid
      have rightBraceValid := afterBindingsValid rightBrace (by simp)
      have sourceEq := tokenSpan_sources_eq functionValid rightBraceValid
      let consumed :=
        functionToken :: nameToken :: leftParen :: rightParen :: arrow ::
          typeTokens ++ leftBrace :: bindingTokens ++
          resultTokens ++ [rightBrace]
      have starts : TokensStartWith
          (SourceSpan.cover functionToken.span rightBrace.span) consumed := by
        simpa [consumed] using
          tokensStartWith_cover
            (second := nameToken :: leftParen :: rightParen :: arrow ::
              typeTokens ++ leftBrace :: bindingTokens ++
              resultTokens ++ [rightBrace])
            (token_starts_self functionToken)
      have ends : TokensEndWith
          (SourceSpan.cover functionToken.span rightBrace.span) consumed := by
        simpa [consumed, List.append_assoc] using
          tokensEndWith_cover
            (functionToken :: nameToken :: leftParen :: rightParen ::
              arrow :: typeTokens ++ leftBrace :: bindingTokens ++
              resultTokens)
            sourceEq (token_ends_self rightBrace)
      have rawMatch : ExpectedToken.ListMatches
          (ExpectedToken.plain .keywordFunction ::
            ExpectedToken.exact (.identifier nameText) nameToken.span ::
            ExpectedToken.plain .leftParen ::
            ExpectedToken.plain .rightParen ::
            ExpectedToken.plain .arrow ::
            returnType.expectedTokens ++
            ExpectedToken.plain .leftBrace ::
            bindings.flatMap LetStatement.expectedTokens ++
            result.expectedTokens ++
            [ExpectedToken.plain .rightBrace])
          consumed := by
        simp only [consumed]
        exact .cons (expectedTokenPlain_matches functionKind)
          (.cons (expectedTokenExact_matches nameKind)
            (.cons (expectedTokenPlain_matches leftParenKind)
              (.cons (expectedTokenPlain_matches rightParenKind)
                (.cons (expectedTokenPlain_matches arrowKind)
                  (ExpectedToken.ListMatches.append
                    (ExpectedToken.ListMatches.append
                      (ExpectedToken.ListMatches.append typeMatch
                        (.cons
                          (expectedTokenPlain_matches leftBraceKind)
                          bindingsMatch))
                      resultMatch)
                    (.cons (expectedTokenPlain_matches rightBraceKind)
                      .nil))))))
      refine ⟨consumed, ?_, ?_, starts, ends⟩
      · simp only [consumed, List.cons_append]
        rw [afterArrowEq, afterLeftBraceEq, afterBindingsEq]
        simp [List.append_assoc]
      · simpa [FunctionDecl.expectedTokens] using
          ExpectedToken.ListMatches.enclose rawMatch starts ends

private def BindingsValidityProperty
    (file : SourceFile)
    (input : List Token)
    (bindings : List LetStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      ∀ binding ∈ bindings,
        binding.ValidFor file ∧
        ∃ bindingTokens,
          TokensStartWith binding.span bindingTokens ∧
          TokensEndWith binding.span bindingTokens ∧
          TokensValidFor file bindingTokens ∧
          TokensOrdered bindingTokens ∧
          ∀ token ∈ bindingTokens, token ∈ consumed

private theorem bindingsParseValidityProperty
    (file : SourceFile)
    {input remaining : List Token}
    {bindings : List LetStatement}
    (derivation : BindingsParse input bindings remaining) :
    BindingsValidityProperty file input bindings remaining := by
  induction derivation with
  | done =>
      intro _ _
      exact ⟨[], rfl, by simp⟩
  | more input afterBinding remaining binding bindings bindingParse
      tailParse tailIH =>
      intro valid ordered
      rcases letParsesValidityProperty file bindingParse valid ordered with
        ⟨bindingTokens, inputEq, bindingStarts, bindingEnds, bindingValid⟩
      rw [inputEq] at valid ordered
      have bindingTokensValid := tokensValidFor_append_left valid
      have bindingTokensOrdered := tokensOrdered_append_left ordered
      have afterBindingValid := tokensValidFor_append_right valid
      have afterBindingOrdered :=
        tokensOrdered_append_right bindingTokens ordered
      rcases tailIH afterBindingValid afterBindingOrdered with
        ⟨tailTokens, afterBindingEq, tailEvidence⟩
      refine ⟨bindingTokens ++ tailTokens, ?_, ?_⟩
      · rw [inputEq, afterBindingEq, List.append_assoc]
      · intro candidate member
        simp only [List.mem_cons] at member
        rcases member with rfl | member
        · exact ⟨bindingValid, bindingTokens, bindingStarts, bindingEnds,
            bindingTokensValid, bindingTokensOrdered,
            fun token tokenMember =>
              List.mem_append_left _ tokenMember⟩
        · rcases tailEvidence candidate member with
            ⟨candidateValid, candidateTokens, starts, ends,
              candidateTokensValid, candidateTokensOrdered, subset⟩
          exact ⟨candidateValid, candidateTokens, starts, ends,
            candidateTokensValid, candidateTokensOrdered,
            fun token tokenMember =>
              List.mem_append_right bindingTokens
                (subset token tokenMember)⟩

private def ReturnValidityProperty
    (file : SourceFile)
    (input : List Token)
    (statement : ReturnStatement)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith statement.span consumed ∧
      TokensEndWith statement.span consumed ∧
      statement.ValidFor file

private theorem returnParsesValidityProperty
    (file : SourceFile)
    {input remaining : List Token}
    {statement : ReturnStatement}
    (derivation : ReturnParses input statement remaining) :
    ReturnValidityProperty file input statement remaining := by
  cases derivation with
  | intro returnToken semicolonToken afterReturn remaining value _
      valueParse _ =>
      intro valid ordered
      have returnValid := valid returnToken (by simp)
      have afterReturnValid := tokensValidFor_tail valid
      have afterReturnOrdered := tokensOrdered_tail ordered
      rcases exprParsesValidityProperty file valueParse
          afterReturnValid afterReturnOrdered with
        ⟨valueTokens, afterReturnEq, valueStarts, valueEnds, valueValid⟩
      rw [afterReturnEq] at afterReturnValid afterReturnOrdered
      have valueTokensValid := tokensValidFor_append_left afterReturnValid
      have valueTokensOrdered := tokensOrdered_append_left afterReturnOrdered
      have semicolonValid := afterReturnValid semicolonToken (by simp)
      have sourceEq := tokenSpan_sources_eq returnValid semicolonValid
      let consumed := returnToken :: valueTokens ++ [semicolonToken]
      have starts : TokensStartWith
          (SourceSpan.cover returnToken.span semicolonToken.span) consumed := by
        simpa [consumed] using tokensStartWith_cover
          (second := valueTokens ++ [semicolonToken])
          (token_starts_self returnToken)
      have ends : TokensEndWith
          (SourceSpan.cover returnToken.span semicolonToken.span) consumed := by
        simpa [consumed] using tokensEndWith_cover
          (returnToken :: valueTokens) sourceEq
          (token_ends_self semicolonToken)
      have inputEq : returnToken :: afterReturn = consumed ++ remaining := by
        simp [consumed, afterReturnEq, List.append_assoc]
      rw [inputEq] at valid ordered
      have consumedValid := tokensValidFor_append_left valid
      have consumedOrdered := tokensOrdered_append_left ordered
      have containsValue := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        valueTokensValid valueTokensOrdered valueStarts valueEnds
        (fun token member => by simp [consumed, member])
      exact ⟨consumed, inputEq, starts, ends,
        ⟨spanValidFor_of_delimitedTokens consumedValid consumedOrdered
            starts ends,
          containsValue,
          valueValid⟩⟩

private def FunctionValidityProperty
    (file : SourceFile)
    (input : List Token)
    (declaration : FunctionDecl)
    (remaining : List Token) : Prop :=
  TokensValidFor file input →
    TokensOrdered input →
    ∃ consumed,
      input = consumed ++ remaining ∧
      TokensStartWith declaration.span consumed ∧
      TokensEndWith declaration.span consumed ∧
      declaration.ValidFor file

private theorem functionParsesValidityProperty
    (file : SourceFile)
    {input remaining : List Token}
    {declaration : FunctionDecl}
    (derivation : FunctionParses input declaration remaining) :
    FunctionValidityProperty file input declaration remaining := by
  cases derivation with
  | intro functionToken nameToken leftParen rightParen arrow leftBrace
      rightBrace nameText afterArrow afterLeftBrace afterBindings afterResult
      _ returnType bindings result _ _ _ _ _ typeParse _ bindingsParse
      resultParse _ =>
      intro valid ordered
      have functionValid := valid functionToken (by simp)
      have nameValid := valid nameToken (by simp)
      have afterArrowValid :=
        tokensValidFor_tail (tokensValidFor_tail (tokensValidFor_tail
          (tokensValidFor_tail (tokensValidFor_tail valid))))
      have afterArrowOrdered :=
        tokensOrdered_tail (tokensOrdered_tail (tokensOrdered_tail
          (tokensOrdered_tail (tokensOrdered_tail ordered))))
      rcases typeParsesValidityProperty file typeParse
          afterArrowValid afterArrowOrdered with
        ⟨typeTokens, afterArrowEq, typeStarts, typeEnds, typeValid⟩
      rw [afterArrowEq] at afterArrowValid afterArrowOrdered
      have typeTokensValid := tokensValidFor_append_left afterArrowValid
      have typeTokensOrdered := tokensOrdered_append_left afterArrowOrdered
      have afterLeftBraceValid := tokensValidFor_tail
        (tokensValidFor_append_right afterArrowValid)
      have afterLeftBraceOrdered := tokensOrdered_tail
        (tokensOrdered_append_right typeTokens afterArrowOrdered)
      rcases bindingsParseValidityProperty file bindingsParse
          afterLeftBraceValid afterLeftBraceOrdered with
        ⟨bindingTokens, afterLeftBraceEq, bindingEvidence⟩
      rw [afterLeftBraceEq] at afterLeftBraceValid afterLeftBraceOrdered
      have bindingTokensValid :=
        tokensValidFor_append_left afterLeftBraceValid
      have afterBindingsValid :=
        tokensValidFor_append_right afterLeftBraceValid
      have afterBindingsOrdered :=
        tokensOrdered_append_right bindingTokens afterLeftBraceOrdered
      rcases returnParsesValidityProperty file resultParse
          afterBindingsValid afterBindingsOrdered with
        ⟨resultTokens, afterBindingsEq, resultStarts, resultEnds, resultValid⟩
      rw [afterBindingsEq] at afterBindingsValid afterBindingsOrdered
      have resultTokensValid := tokensValidFor_append_left afterBindingsValid
      have resultTokensOrdered := tokensOrdered_append_left afterBindingsOrdered
      have rightBraceValid := afterBindingsValid rightBrace (by simp)
      have sourceEq := tokenSpan_sources_eq functionValid rightBraceValid
      let consumed :=
        functionToken :: nameToken :: leftParen :: rightParen :: arrow ::
          typeTokens ++ leftBrace :: bindingTokens ++
          resultTokens ++ [rightBrace]
      have starts : TokensStartWith
          (SourceSpan.cover functionToken.span rightBrace.span) consumed := by
        simpa [consumed] using tokensStartWith_cover
          (second := nameToken :: leftParen :: rightParen :: arrow ::
            typeTokens ++ leftBrace :: bindingTokens ++
            resultTokens ++ [rightBrace])
          (token_starts_self functionToken)
      have ends : TokensEndWith
          (SourceSpan.cover functionToken.span rightBrace.span) consumed := by
        simpa [consumed, List.append_assoc] using tokensEndWith_cover
          (functionToken :: nameToken :: leftParen :: rightParen :: arrow ::
            typeTokens ++ leftBrace :: bindingTokens ++ resultTokens)
          sourceEq (token_ends_self rightBrace)
      have inputEq :
          functionToken :: nameToken :: leftParen :: rightParen :: arrow ::
            afterArrow = consumed ++ remaining := by
        simp only [consumed, List.cons_append]
        rw [afterArrowEq, afterLeftBraceEq, afterBindingsEq]
        simp [List.append_assoc]
      rw [inputEq] at valid ordered
      have consumedValid := tokensValidFor_append_left valid
      have consumedOrdered := tokensOrdered_append_left ordered
      have containsName := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        (tokensValidFor_singleton nameValid)
        (by simp [TokensOrdered, Lexed.SpansOrdered])
        (token_starts_self nameToken) (token_ends_self nameToken)
        (fun token member => by
          simp only [List.mem_singleton] at member
          subst token
          simp [consumed])
      have containsType := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        typeTokensValid typeTokensOrdered typeStarts typeEnds
        (fun token member => by simp [consumed, member])
      have containsBindings :
          ∀ binding ∈ bindings,
            (SourceSpan.cover functionToken.span rightBrace.span).Contains
                binding.span ∧
              binding.ValidFor file := by
        intro binding member
        rcases bindingEvidence binding member with
          ⟨bindingValid, tokens, bindingStarts, bindingEnds,
            tokensValid, tokensOrdered, subset⟩
        exact ⟨spanContains_of_delimitedSubset
          consumedValid consumedOrdered starts ends
          tokensValid tokensOrdered bindingStarts bindingEnds
          (fun token tokenMember => by
            simp [consumed, subset token tokenMember]), bindingValid⟩
      have containsResult := spanContains_of_delimitedSubset
        consumedValid consumedOrdered starts ends
        resultTokensValid resultTokensOrdered resultStarts resultEnds
        (fun token member => by simp [consumed, member])
      exact ⟨consumed, inputEq, starts, ends,
        ⟨spanValidFor_of_delimitedTokens consumedValid consumedOrdered
            starts ends,
          nameValid.2.1,
          containsName,
          containsType,
          typeValid,
          containsBindings,
          containsResult,
          resultValid⟩⟩

namespace FileParses

theorem correspondsTo_of_tokensValid
    (file : SourceFile)
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed)
    (tokensValid : ∀ token ∈ lexed.tokens, token.ValidFor file) :
    parsed.CorrespondsTo lexed := by
  cases derivation with
  | intro tokens comments declaration functionParse =>
      rcases functionParsesCorrespondenceProperty file functionParse
          tokensValid with
        ⟨consumed, tokensEq, functionMatch, starts, ends⟩
      simp only [List.append_nil] at tokensEq
      subst consumed
      have fileMatch : ExpectedToken.ListMatches
          ({
            span := declaration.span
            function := declaration
            comments
          } : ParsedFile).expectedTokens tokens := by
        simpa [ParsedFile.expectedTokens] using
          ExpectedToken.ListMatches.enclose functionMatch starts ends
      exact ⟨fileMatch.length_eq, fileMatch.zipped_matches, rfl⟩

theorem validFor_of_lexedValid
    (file : SourceFile)
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed)
    (lexedValid : lexed.ValidFor file) :
    parsed.ValidFor file := by
  cases derivation with
  | intro tokens comments declaration functionParse =>
      rcases functionParsesValidityProperty file functionParse
          lexedValid.1 lexedValid.2.2.1 with
        ⟨consumed, tokensEq, _, _, declarationValid⟩
      simp only [List.append_nil] at tokensEq
      subst consumed
      exact ⟨declarationValid.1,
        by
          simp [SourceSpan.Contains, declarationValid.1.1],
        declarationValid,
        lexedValid.2.1⟩

/-- Independent lexical and grammatical derivations imply full conformance. -/
theorem conformsTo_of_lexes
    (file : SourceFile)
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed)
    (lexes : LexicalGrammar.Lexes file lexed) :
    parsed.ConformsTo file lexed := by
  exact ⟨validFor_of_lexedValid file derivation lexes.1,
    correspondsTo_of_tokensValid file derivation lexes.1.1,
    derivation.grammarValid⟩

end FileParses

end Solcore.Surface
