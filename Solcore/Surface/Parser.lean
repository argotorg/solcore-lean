import Solcore.Surface.Lexer
import Solcore.Surface.Grammar

set_option autoImplicit false

namespace Solcore.Surface

inductive ParseExpectation where
  | token (kind : TokenKind)
  | identifier
  | type
  | expression
  | argumentOrRightParen
  | commaOrRightParen
  | bindingOrReturn
  | endOfFile
  deriving Repr, BEq, DecidableEq

inductive ParseErrorKind where
  | expected (expectation : ParseExpectation) (found : Option TokenKind)
  | nonAssociative (operator : BinaryOp)
  deriving Repr, BEq, DecidableEq

structure ParseError where
  code : String
  span : SourceSpan
  kind : ParseErrorKind
  deriving Repr, BEq, DecidableEq

inductive ParserPhase where
  | expression
  | prefix
  | arguments
  | argumentTail
  | infix
  | bindings
  deriving Repr, BEq, DecidableEq

inductive ParserInvariant where
  | fuelExhausted (phase : ParserPhase) (span : SourceSpan)
  | invalidInput (lexed : Lexed)
  | invalidOutput (parsed : ParsedFile)
  deriving Repr, BEq

inductive ParseFailure where
  | source (error : ParseError)
  | internal (invariant : ParserInvariant)
  deriving Repr, BEq

inductive FrontendInvariant where
  | lexer (invariant : LexerInvariant)
  | parser (invariant : ParserInvariant)
  deriving Repr, BEq

inductive FrontendError where
  | lexical (error : LexError)
  | syntactic (error : ParseError)
  | internal (invariant : FrontendInvariant)
  deriving Repr, BEq

namespace Parser

private def eofSpan (file : SourceFile) : SourceSpan := {
  source := file.path
  startByte := file.content.utf8ByteSize
  endByte := file.content.utf8ByteSize
}

private def errorSpan (file : SourceFile) : List Token → SourceSpan
  | token :: _ => token.span
  | [] => eofSpan file

private def expected
    (file : SourceFile)
    (expectation : ParseExpectation)
    (tokens : List Token) : ParseError := {
  code := "SP0001"
  span := errorSpan file tokens
  kind := .expected expectation (tokens.head?.map (·.kind))
}

private def nonAssociative (token : Token) (operator : BinaryOp) : ParseError := {
  code := "SP0002"
  span := token.span
  kind := .nonAssociative operator
}

private structure ExpectedKindResult
    (kind : TokenKind)
    (input : List Token) where
  token : Token
  remaining : List Token
  inputEq : input = token :: remaining
  kindEq : token.kind = kind

private theorem ExpectedKindResult.castInput
    {kind : TokenKind}
    {input : List Token}
    (result : ExpectedKindResult kind input)
    (motive : List Token → Prop)
    (proof : motive (result.token :: result.remaining)) :
    motive input :=
  result.inputEq.symm ▸ proof

private def expectKind
    (file : SourceFile)
    (kind : TokenKind) :
    (input : List Token) →
      Except ParseFailure (ExpectedKindResult kind input)
  | token :: rest =>
      if kindMatches : decide (token.kind = kind) then
        .ok {
          token
          remaining := rest
          inputEq := rfl
          kindEq := of_decide_eq_true kindMatches
        }
      else
        .error (.source (expected file (.token kind) (token :: rest)))
  | [] =>
      .error (.source (expected file (.token kind) []))

private structure IdentifierResult (input : List Token) where
  token : Token
  text : String
  remaining : List Token
  inputEq : input = token :: remaining
  kindEq : token.kind = .identifier text

private theorem IdentifierResult.castInput
    {input : List Token}
    (result : IdentifierResult input)
    (motive : List Token → Prop)
    (proof : motive (result.token :: result.remaining)) :
    motive input :=
  result.inputEq.symm ▸ proof

private def expectIdentifier
    (file : SourceFile) :
    (input : List Token) → Except ParseFailure (IdentifierResult input)
  | { kind := .identifier text, span } :: rest =>
      .ok {
        token := { kind := .identifier text, span }
        text
        remaining := rest
        inputEq := rfl
        kindEq := rfl
      }
  | tokens =>
      .error (.source (expected file .identifier tokens))

private def expectContextual
    (file : SourceFile)
    (text : String) :
    (input : List Token) →
      Except ParseFailure (ExpectedKindResult (.identifier text) input)
  | { kind := .identifier actual, span } :: rest =>
      if textMatches : decide (actual = text) then
        .ok {
          token := { kind := .identifier actual, span }
          remaining := rest
          inputEq := rfl
          kindEq := congrArg TokenKind.identifier
            (of_decide_eq_true textMatches)
        }
      else
        .error (.source
          (expected file (.token (.identifier text))
            ({ kind := .identifier actual, span } :: rest)))
  | tokens =>
      .error (.source (expected file (.token (.identifier text)) tokens))

private structure TypeResult (input : List Token) where
  type : TypeSyntax
  remaining : List Token
  parses : TypeParses input type remaining

private theorem namedTypeParses
    (token : Token)
    (text : String)
    (rest : List Token)
    (kindEq : token.kind = .identifier text)
    (valid : text == "bool" || text == "word") :
    TypeParses
      (token :: rest)
      (.named { value := text, span := token.span })
      rest := by
  simp only [Bool.or_eq_true, beq_iff_eq] at valid
  rcases valid with boolEq | wordEq
  · subst text
    exact .bool token rest kindEq
  · subst text
    exact .word token rest kindEq

private def parseType
    (file : SourceFile) :
    (input : List Token) → Except ParseFailure (TypeResult input)
  | { kind := .leftParen, span := leftSpan } ::
      { kind := .rightParen, span := rightSpan } :: rest =>
      let left : Token := { kind := .leftParen, span := leftSpan }
      let right : Token := { kind := .rightParen, span := rightSpan }
      .ok {
        type := .unit (SourceSpan.cover left.span right.span)
        remaining := rest
        parses := .unit left right rest rfl rfl
      }
  | { kind := .identifier text, span } :: rest =>
      let token : Token := { kind := .identifier text, span }
      if valid : text == "bool" || text == "word" then
        .ok {
          type := .named { value := text, span := token.span }
          remaining := rest
          parses := namedTypeParses token text rest rfl valid
        }
      else
        .error (.source (expected file .type (token :: rest)))
  | tokens =>
      .error (.source (expected file .type tokens))

private def exhausted
    {α : Type}
    (file : SourceFile)
    (phase : ParserPhase)
    (tokens : List Token) : Except ParseFailure α :=
  .error (.internal (.fuelExhausted phase (errorSpan file tokens)))

private structure BinaryInfo (kind : TokenKind) where
  operator : BinaryOp
  precedence : Nat
  associativity : Associativity
  binding : BinaryBinding kind operator precedence associativity

private def binaryInfo : (kind : TokenKind) → Option (BinaryInfo kind)
  | .equalEqual => some ⟨.eq, 1, .nonAssociative, .eq⟩
  | .bangEqual => some ⟨.ne, 1, .nonAssociative, .ne⟩
  | .less => some ⟨.lt, 2, .nonAssociative, .lt⟩
  | .greater => some ⟨.gt, 2, .nonAssociative, .gt⟩
  | .lessEqual => some ⟨.le, 2, .nonAssociative, .le⟩
  | .greaterEqual => some ⟨.ge, 2, .nonAssociative, .ge⟩
  | .pipe => some ⟨.bitOr, 3, .left, .bitOr⟩
  | .caret => some ⟨.bitXor, 4, .left, .bitXor⟩
  | .ampersand => some ⟨.bitAnd, 5, .left, .bitAnd⟩
  | .plus => some ⟨.add, 6, .left, .add⟩
  | .minus => some ⟨.sub, 6, .left, .sub⟩
  | .star => some ⟨.mul, 7, .left, .mul⟩
  | .slash => some ⟨.div, 7, .left, .div⟩
  | .percent => some ⟨.mod, 7, .left, .mod⟩
  | _ => none

private structure BinaryHead (input : List Token) where
  token : Token
  remaining : List Token
  inputEq : input = token :: remaining
  info : BinaryInfo token.kind

private def peekBinary :
    (input : List Token) → Option (BinaryHead input)
  | token :: remaining =>
      (binaryInfo token.kind).map fun info => {
        token
        remaining
        inputEq := rfl
        info
      }
  | [] => none

private theorem BinaryHead.infix
    {input : List Token}
    (head : BinaryHead input)
    {minimum : Nat}
    {left result : Expr}
    {remaining : List Token}
    (derivation :
      InfixParses minimum left
        (head.token :: head.remaining) result remaining) :
    InfixParses minimum left input result remaining := by
  exact head.inputEq.symm ▸ derivation

private theorem binaryBinding_unique
    {kind : TokenKind}
    {leftOperator rightOperator : BinaryOp}
    {leftPrecedence rightPrecedence : Nat}
    {leftAssociativity rightAssociativity : Associativity}
    (left :
      BinaryBinding kind leftOperator leftPrecedence leftAssociativity)
    (right :
      BinaryBinding kind rightOperator rightPrecedence rightAssociativity) :
    leftOperator = rightOperator ∧
      leftPrecedence = rightPrecedence ∧
      leftAssociativity = rightAssociativity := by
  cases left <;> cases right <;> simp

private theorem binaryInfoOfBinding
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    {associativity : Associativity}
    (binding : BinaryBinding kind operator precedence associativity) :
    ∃ info, binaryInfo kind = some info := by
  cases binding <;> simp [binaryInfo]

private theorem infixBlockedOfNoBinary
    (minimum : Nat)
    (tokens : List Token)
    (noneAtHead : peekBinary tokens = none) :
    InfixBlocked minimum tokens := by
  intro token tail operator precedence associativity inputEq binding
  subst tokens
  obtain ⟨info, infoEq⟩ := binaryInfoOfBinding binding
  simp [peekBinary, infoEq] at noneAtHead

private theorem infixBlockedOfLowerPrecedence
    {tokens : List Token}
    (minimum : Nat)
    (head : BinaryHead tokens)
    (lower : head.info.precedence < minimum) :
    InfixBlocked minimum tokens := by
  intro token tail operator precedence associativity inputEq binding
  rw [head.inputEq] at inputEq
  injection inputEq with tokenEq tailEq
  subst token
  have unique := binaryBinding_unique head.info.binding binding
  simpa [unique.2.1] using lower

private theorem headPrecedenceNeOfNoBinary
    (precedence : Nat)
    (tokens : List Token)
    (noneAtHead : peekBinary tokens = none) :
    HeadPrecedenceNe precedence tokens := by
  intro token tail operator actual associativity inputEq binding
  subst tokens
  obtain ⟨info, infoEq⟩ := binaryInfoOfBinding binding
  simp [peekBinary, infoEq] at noneAtHead

private theorem headPrecedenceNeOfDifferentBinary
    {tokens : List Token}
    (precedence : Nat)
    (head : BinaryHead tokens)
    (different : head.info.precedence ≠ precedence) :
    HeadPrecedenceNe precedence tokens := by
  intro token tail operator actual associativity inputEq binding
  rw [head.inputEq] at inputEq
  injection inputEq with tokenEq tailEq
  subst token
  have unique := binaryBinding_unique head.info.binding binding
  intro actualEq
  exact different (unique.2.1.trans actualEq)

private theorem headKindNeNil (kind : TokenKind) :
    HeadKindNe kind [] := by
  intro token tail inputEq
  simp at inputEq

private theorem headKindNeCons
    (kind : TokenKind)
    (token : Token)
    (tail : List Token)
    (different : token.kind ≠ kind) :
    HeadKindNe kind (token :: tail) := by
  intro actual actualTail inputEq
  injection inputEq with tokenEq tailEq
  subst actual
  exact different

private structure ExpressionResult
    (minimum : Nat)
    (input : List Token) where
  expression : Expr
  remaining : List Token
  parses : ExprParses minimum input expression remaining

private structure PrefixResult (input : List Token) where
  expression : Expr
  remaining : List Token
  parses : PrefixParses input expression remaining

private structure InfixResult
    (minimum : Nat)
    (left : Expr)
    (input : List Token) where
  expression : Expr
  remaining : List Token
  parses : InfixParses minimum left input expression remaining

private structure ArgumentsResult (input : List Token) where
  arguments : List Expr
  right : Token
  remaining : List Token
  parses : ArgumentsParse input arguments right remaining

private structure ArgumentTailResult (input : List Token) where
  arguments : List Expr
  right : Token
  remaining : List Token
  parses : ArgumentTailParses input arguments right remaining

private theorem exprParses_remaining_length_lt
    {minimum : Nat}
    {input remaining : List Token}
    {expression : Expr}
    (derivation :
      ExprParses minimum input expression remaining) :
    remaining.length < input.length := by
  exact ExprParses.rec
    (motive_1 := fun _ input _ remaining _ =>
      remaining.length < input.length)
    (motive_2 := fun input _ remaining _ =>
      remaining.length < input.length)
    (motive_3 := fun _ _ input _ remaining _ =>
      remaining.length ≤ input.length)
    (motive_4 := fun input _ _ remaining _ =>
      remaining.length < input.length)
    (motive_5 := fun input _ _ remaining _ =>
      remaining.length < input.length)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    (by
      intros
      try simp only [List.length_cons] at *
      all_goals omega)
    derivation

private theorem binaryBinding_precedence_lt_eight
    {kind : TokenKind}
    {operator : BinaryOp}
    {precedence : Nat}
    {associativity : Associativity}
    (binding :
      BinaryBinding kind operator precedence associativity) :
    precedence < 8 := by
  cases binding <;> omega

private theorem infixBlockedAtEight (tokens : List Token) :
    InfixBlocked 8 tokens := by
  intro _ _ _ precedence _ _ binding
  exact binaryBinding_precedence_lt_eight binding

private theorem prefixParses_remaining_length_lt
    {input remaining : List Token}
    {expression : Expr}
    (derivation : PrefixParses input expression remaining) :
    remaining.length < input.length :=
  exprParses_remaining_length_lt
    (.ordinary
      8
      input
      remaining
      remaining
      expression
      expression
      derivation
      (.stop 8 expression remaining (infixBlockedAtEight remaining)))

mutual

private def parseExpressionFuel
    (file : SourceFile) :
    (fuel : Nat) → (minimum : Nat) → (input : List Token) →
      Except ParseFailure (ExpressionResult minimum input)
  | 0, _, tokens =>
      exhausted file .expression tokens
  | fuel + 1, minimumPrecedence, tokens =>
      match tokens with
      | { kind := .keywordIf, span := ifSpan } :: afterIf =>
          let ifToken : Token := { kind := .keywordIf, span := ifSpan }
          if minimumIsZero : minimumPrecedence == 0 then do
            have minimumEq : minimumPrecedence = 0 :=
              beq_iff_eq.mp minimumIsZero
            let condition ←
              parseExpressionFuel file fuel 0 afterIf
            let thenToken ←
              expectContextual file "then" condition.remaining
            let thenBranch ←
              parseExpressionFuel file fuel 0 thenToken.remaining
            let elseToken ←
              expectKind file .keywordElse thenBranch.remaining
            let elseBranch ←
              parseExpressionFuel file fuel 0 elseToken.remaining
            have conditionParse :
                ExprParses 0 afterIf condition.expression
                  (thenToken.token :: thenToken.remaining) := by
              simpa only [thenToken.inputEq] using condition.parses
            have thenParse :
                ExprParses 0 thenToken.remaining thenBranch.expression
                  (elseToken.token :: elseToken.remaining) := by
              simpa only [elseToken.inputEq] using thenBranch.parses
            .ok {
              expression := .ifThenElse
                (SourceSpan.cover ifToken.span elseBranch.expression.span)
                condition.expression
                thenBranch.expression
                elseBranch.expression
              remaining := elseBranch.remaining
              parses := minimumEq.symm ▸
                (.conditional
                  ifToken
                  thenToken.token
                  elseToken.token
                  afterIf
                  thenToken.remaining
                  elseToken.remaining
                  elseBranch.remaining
                  condition.expression
                  thenBranch.expression
                  elseBranch.expression
                  rfl
                  conditionParse
                  thenToken.kindEq
                  thenParse
                  elseToken.kindEq
                  elseBranch.parses)
            }
          else do
            let prefixResult ← parsePrefixFuel file fuel
              ({ kind := .keywordIf, span := ifSpan } :: afterIf)
            let infixResult ← parseInfixFuel file fuel minimumPrecedence
              prefixResult.expression prefixResult.remaining
            .ok {
              expression := infixResult.expression
              remaining := infixResult.remaining
              parses := .ordinary
                minimumPrecedence
                ({ kind := .keywordIf, span := ifSpan } :: afterIf)
                prefixResult.remaining
                infixResult.remaining
                prefixResult.expression
                infixResult.expression
                prefixResult.parses
                infixResult.parses
            }
      | otherTokens => do
          let prefixResult ← parsePrefixFuel file fuel otherTokens
          let infixResult ← parseInfixFuel file fuel minimumPrecedence
            prefixResult.expression prefixResult.remaining
          .ok {
            expression := infixResult.expression
            remaining := infixResult.remaining
            parses := .ordinary
              minimumPrecedence
              otherTokens
              prefixResult.remaining
              infixResult.remaining
              prefixResult.expression
              infixResult.expression
              prefixResult.parses
              infixResult.parses
          }

private def parsePrefixFuel
    (file : SourceFile) :
    (fuel : Nat) → (input : List Token) →
      Except ParseFailure (PrefixResult input)
  | 0, tokens =>
      exhausted file .prefix tokens
  | fuel + 1, tokens =>
      match tokens with
      | { kind := .bang, span := operatorSpan } :: rest =>
          let operator : Token := { kind := .bang, span := operatorSpan }
          do
            let operand ← parsePrefixFuel file fuel rest
            .ok {
              expression := .unary
                (SourceSpan.cover operator.span operand.expression.span)
                { value := .not, span := operator.span }
                operand.expression
              remaining := operand.remaining
              parses := .not operator rest operand.remaining
                operand.expression rfl operand.parses
            }
      | { kind := .leftParen, span := leftSpan } ::
          { kind := .rightParen, span := rightSpan } :: rest =>
          let left : Token := { kind := .leftParen, span := leftSpan }
          let right : Token := { kind := .rightParen, span := rightSpan }
          .ok {
            expression := .unit (SourceSpan.cover left.span right.span)
            remaining := rest
            parses := .unit left right rest rfl rfl
          }
      | { kind := .leftParen, span := leftSpan } :: rest =>
          let left : Token := { kind := .leftParen, span := leftSpan }
          do
            let inner ← parseExpressionFuel file fuel 0 rest
            let right ← expectKind file .rightParen inner.remaining
            have innerParse :
                ExprParses 0 rest inner.expression
                  (right.token :: right.remaining) := by
              simpa only [right.inputEq] using inner.parses
            .ok {
              expression := .group
                (SourceSpan.cover left.span right.token.span)
                inner.expression
              remaining := right.remaining
              parses := .group left right.token rest right.remaining
                inner.expression rfl innerParse right.kindEq
            }
      | { kind := .decimal digits, span } :: rest =>
          let token : Token := { kind := .decimal digits, span }
          .ok {
            expression := .integer {
              base := .decimal
              digits
              span := token.span
            }
            remaining := rest
            parses := .decimal token digits rest rfl
          }
      | { kind := .hexadecimal digits, span } :: rest =>
          let token : Token := { kind := .hexadecimal digits, span }
          .ok {
            expression := .integer {
              base := .hexadecimal
              digits
              span := token.span
            }
            remaining := rest
            parses := .hexadecimal token digits rest rfl
          }
      | { kind := .identifier text, span } :: rest =>
          let identifier : Token := { kind := .identifier text, span }
          let callee : Name := { value := text, span := identifier.span }
          match rest with
          | [] =>
              .ok {
                expression := .name callee
                remaining := []
                parses := .name identifier text [] rfl
                  (headKindNeNil .leftParen)
              }
          | left :: afterLeft =>
              if leftMatches : decide (left.kind = .leftParen) then do
                let arguments ←
                  parseArgumentsFuel file fuel afterLeft
                .ok {
                  expression := .call
                    (SourceSpan.cover identifier.span arguments.right.span)
                    callee
                    arguments.arguments
                  remaining := arguments.remaining
                  parses := .call
                    identifier
                    left
                    arguments.right
                    text
                    afterLeft
                    arguments.remaining
                    arguments.arguments
                    rfl
                    (of_decide_eq_true leftMatches)
                    arguments.parses
                }
              else
                .ok {
                  expression := .name callee
                  remaining := left :: afterLeft
                  parses := .name identifier text (left :: afterLeft) rfl
                    (headKindNeCons .leftParen left afterLeft (by
                      simpa using leftMatches))
                }
      | _ =>
          .error (.source (expected file .expression tokens))

private def parseArgumentsFuel
    (file : SourceFile) :
    (fuel : Nat) → (input : List Token) →
      Except ParseFailure (ArgumentsResult input)
  | 0, tokens =>
      exhausted file .arguments tokens
  | fuel + 1, tokens =>
      match tokens with
      | { kind := .rightParen, span } :: rest =>
          let right : Token := { kind := .rightParen, span }
          .ok {
            arguments := []
            right
            remaining := rest
            parses := .empty right rest rfl
          }
      | otherTokens => do
          let first ← parseExpressionFuel file fuel 0 otherTokens
          let tail ← parseArgumentTailFuel file fuel first.remaining
          .ok {
            arguments := first.expression :: tail.arguments
            right := tail.right
            remaining := tail.remaining
            parses := .nonempty
              otherTokens
              first.remaining
              tail.remaining
              first.expression
              tail.arguments
              tail.right
              first.parses
              tail.parses
          }

private def parseArgumentTailFuel
    (file : SourceFile) :
    (fuel : Nat) → (input : List Token) →
      Except ParseFailure (ArgumentTailResult input)
  | 0, tokens =>
      exhausted file .argumentTail tokens
  | fuel + 1, tokens =>
      match tokens with
      | { kind := .rightParen, span } :: rest =>
          let right : Token := { kind := .rightParen, span }
          .ok {
            arguments := []
            right
            remaining := rest
            parses := .done right rest rfl
          }
      | { kind := .comma, span } :: rest =>
          let comma : Token := { kind := .comma, span }
          do
            let next ← parseExpressionFuel file fuel 0 rest
            let tail ← parseArgumentTailFuel file fuel next.remaining
            .ok {
              arguments := next.expression :: tail.arguments
              right := tail.right
              remaining := tail.remaining
              parses := .more
                comma
                tail.right
                rest
                next.remaining
                tail.remaining
                next.expression
                tail.arguments
                rfl
                next.parses
                tail.parses
            }
      | _ =>
          .error (.source (expected file .commaOrRightParen tokens))

private def parseInfixFuel
    (file : SourceFile) :
    (fuel : Nat) → (minimum : Nat) → (left : Expr) →
      (input : List Token) →
      Except ParseFailure (InfixResult minimum left input)
  | 0, minimumPrecedence, left, tokens =>
      match binaryAtHead : peekBinary tokens with
      | some _ => exhausted file .infix tokens
      | none =>
          .ok {
            expression := left
            remaining := tokens
            parses := .stop minimumPrecedence left tokens
              (infixBlockedOfNoBinary
                minimumPrecedence tokens binaryAtHead)
          }
  | fuel + 1, minimumPrecedence, left, tokens =>
      match binaryAtHead : peekBinary tokens with
      | some head =>
          if lower : head.info.precedence < minimumPrecedence then
            .ok {
              expression := left
              remaining := tokens
              parses := .stop minimumPrecedence left tokens
                (infixBlockedOfLowerPrecedence
                  minimumPrecedence head lower)
            }
          else
            have eligible : minimumPrecedence ≤ head.info.precedence :=
              Nat.le_of_not_gt lower
            do
              let right ← parseExpressionFuel file fuel
                (head.info.precedence + 1) head.remaining
              let expression := .binary
                (SourceSpan.cover left.span right.expression.span)
                {
                  value := head.info.operator
                  span := head.token.span
                }
                left
                right.expression
              match associativityEq : head.info.associativity with
              | .left => do
                  have binding :
                      BinaryBinding head.token.kind
                        head.info.operator head.info.precedence .left := by
                    simpa only [associativityEq] using head.info.binding
                  let tail ← parseInfixFuel file fuel minimumPrecedence
                    expression right.remaining
                  .ok {
                    expression := tail.expression
                    remaining := tail.remaining
                    parses := head.infix
                      (.leftStep
                        minimumPrecedence
                        head.info.precedence
                        left
                        right.expression
                        tail.expression
                        head.token
                        head.info.operator
                        head.remaining
                        right.remaining
                        tail.remaining
                        binding
                        eligible
                        right.parses
                        tail.parses)
                  }
              | .nonAssociative =>
                  have binding :
                      BinaryBinding head.token.kind
                        head.info.operator head.info.precedence
                        .nonAssociative := by
                    simpa only [associativityEq] using head.info.binding
                  match secondAtHead : peekBinary right.remaining with
                  | some second =>
                      if repeated :
                          second.info.precedence == head.info.precedence then
                        .error (.source
                          (nonAssociative
                            second.token second.info.operator))
                      else do
                        let tail ← parseInfixFuel file fuel minimumPrecedence
                          expression right.remaining
                        .ok {
                          expression := tail.expression
                          remaining := tail.remaining
                          parses := head.infix
                            (.nonAssociativeStep
                              minimumPrecedence
                              head.info.precedence
                              left
                              right.expression
                              tail.expression
                              head.token
                              head.info.operator
                              head.remaining
                              right.remaining
                              tail.remaining
                              binding
                              eligible
                              right.parses
                              (headPrecedenceNeOfDifferentBinary
                                head.info.precedence
                                second
                                (by simpa using repeated))
                              tail.parses)
                        }
                  | none => do
                      let tail ← parseInfixFuel file fuel minimumPrecedence
                        expression right.remaining
                      .ok {
                        expression := tail.expression
                        remaining := tail.remaining
                        parses := head.infix
                          (.nonAssociativeStep
                            minimumPrecedence
                            head.info.precedence
                            left
                            right.expression
                            tail.expression
                            head.token
                            head.info.operator
                            head.remaining
                            right.remaining
                            tail.remaining
                            binding
                            eligible
                            right.parses
                            (headPrecedenceNeOfNoBinary
                              head.info.precedence
                              right.remaining
                              secondAtHead)
                            tail.parses)
                      }
      | none =>
          .ok {
            expression := left
            remaining := tokens
            parses := .stop minimumPrecedence left tokens
              (infixBlockedOfNoBinary
                minimumPrecedence tokens binaryAtHead)
          }

end

private def expressionRank (tokens : List Token) : Nat :=
  2 * tokens.length + 2

private def prefixRank (tokens : List Token) : Nat :=
  2 * tokens.length + 1

private def argumentsRank (tokens : List Token) : Nat :=
  2 * tokens.length + 3

private def argumentTailRank (tokens : List Token) : Nat :=
  2 * tokens.length + 1

private def infixRank (tokens : List Token) : Nat :=
  2 * tokens.length + 1

private def NoFuelExhaustion
    {α : Type}
    (result : Except ParseFailure α) : Prop :=
  ∀ phase span,
    result ≠ .error (.internal (.fuelExhausted phase span))

private theorem noFuelExhaustion_ok
    {α : Type}
    (value : α) :
    NoFuelExhaustion (.ok value : Except ParseFailure α) := by
  intro _ _
  simp

private theorem noFuelExhaustion_source
    {α : Type}
    (error : ParseError) :
    NoFuelExhaustion
      (.error (.source error) : Except ParseFailure α) := by
  intro _ _
  simp

private theorem noFuelExhaustion_invalidInput
    {α : Type}
    (lexed : Lexed) :
    NoFuelExhaustion
      (.error (.internal (.invalidInput lexed)) :
        Except ParseFailure α) := by
  intro _ _
  simp

private theorem noFuelExhaustion_invalidOutput
    {α : Type}
    (parsed : ParsedFile) :
    NoFuelExhaustion
      (.error (.internal (.invalidOutput parsed)) :
        Except ParseFailure α) := by
  intro _ _
  simp

private theorem noFuelExhaustion_bind
    {α β : Type}
    {result : Except ParseFailure α}
    {next : α → Except ParseFailure β}
    (resultSafe : NoFuelExhaustion result)
    (nextSafe : ∀ value, NoFuelExhaustion (next value)) :
    NoFuelExhaustion (result >>= next) := by
  intro phase span
  cases result with
  | ok value =>
      exact nextSafe value phase span
  | error failure =>
      cases failure with
      | source error =>
          intro equality
          cases equality
      | internal invariant =>
          cases invariant with
          | fuelExhausted actualPhase actualSpan =>
              exact False.elim
                (resultSafe actualPhase actualSpan rfl)
          | invalidInput lexed =>
              intro equality
              cases equality
          | invalidOutput parsed =>
              intro equality
              cases equality

private theorem expectKind_noFuelExhaustion
    (file : SourceFile)
    (kind : TokenKind)
    (tokens : List Token) :
    NoFuelExhaustion (expectKind file kind tokens) := by
  cases tokens with
  | nil =>
      exact noFuelExhaustion_source _
  | cons token rest =>
      simp only [expectKind]
      split
      · exact noFuelExhaustion_ok _
      · exact noFuelExhaustion_source _

private theorem expectContextual_noFuelExhaustion
    (file : SourceFile)
    (text : String)
    (tokens : List Token) :
    NoFuelExhaustion (expectContextual file text tokens) := by
  cases tokens with
  | nil =>
      exact noFuelExhaustion_source _
  | cons token rest =>
      cases token with
      | mk kind span =>
          cases kind with
          | identifier actual =>
              simp only [expectContextual]
              split
              · exact noFuelExhaustion_ok _
              · exact noFuelExhaustion_source _
          | _ =>
              exact noFuelExhaustion_source _

private structure ExpressionParserFuelSafe (fuel : Nat) : Prop where
  expressionSafe :
    ∀ (file : SourceFile) (minimum : Nat) (tokens : List Token),
      expressionRank tokens ≤ fuel →
      NoFuelExhaustion
        (parseExpressionFuel file fuel minimum tokens)
  prefixSafe :
    ∀ (file : SourceFile) (tokens : List Token),
      prefixRank tokens ≤ fuel →
      NoFuelExhaustion (parsePrefixFuel file fuel tokens)
  argumentsSafe :
    ∀ (file : SourceFile) (tokens : List Token),
      argumentsRank tokens ≤ fuel →
      NoFuelExhaustion (parseArgumentsFuel file fuel tokens)
  argumentTailSafe :
    ∀ (file : SourceFile) (tokens : List Token),
      argumentTailRank tokens ≤ fuel →
      NoFuelExhaustion (parseArgumentTailFuel file fuel tokens)
  infixSafe :
    ∀ (file : SourceFile) (minimum : Nat) (left : Expr)
        (tokens : List Token),
      infixRank tokens ≤ fuel →
      NoFuelExhaustion
        (parseInfixFuel file fuel minimum left tokens)

private theorem expressionParserFuelSafe (fuel : Nat) :
    ExpressionParserFuelSafe fuel := by
  induction fuel with
  | zero =>
      refine {
        expressionSafe := ?_
        prefixSafe := ?_
        argumentsSafe := ?_
        argumentTailSafe := ?_
        infixSafe := ?_
      }
      · intro _ _ tokens sufficient
        simp [expressionRank] at sufficient
      · intro _ tokens sufficient
        simp [prefixRank] at sufficient
      · intro _ tokens sufficient
        simp [argumentsRank] at sufficient
      · intro _ tokens sufficient
        simp [argumentTailRank] at sufficient
      · intro _ _ _ tokens sufficient
        simp [infixRank] at sufficient
  | succ fuel inductionHypothesis =>
      refine {
        expressionSafe := ?_
        prefixSafe := ?_
        argumentsSafe := ?_
        argumentTailSafe := ?_
        infixSafe := ?_
      }
      · intro file minimum tokens sufficient
        simp only [parseExpressionFuel]
        split
        · split
          · apply noFuelExhaustion_bind
            · apply inductionHypothesis.expressionSafe
              simp only [
                expressionRank,
                List.length_cons
              ] at sufficient ⊢
              omega
            · intro condition
              apply noFuelExhaustion_bind
              · exact expectContextual_noFuelExhaustion
                  file "then" condition.remaining
              · intro thenToken
                apply noFuelExhaustion_bind
                · apply inductionHypothesis.expressionSafe
                  have conditionShort :=
                    exprParses_remaining_length_lt condition.parses
                  rw [thenToken.inputEq] at conditionShort
                  simp only [
                    expressionRank,
                    List.length_cons
                  ] at sufficient conditionShort ⊢
                  omega
                · intro thenBranch
                  apply noFuelExhaustion_bind
                  · exact expectKind_noFuelExhaustion
                      file .keywordElse thenBranch.remaining
                  · intro elseToken
                    apply noFuelExhaustion_bind
                    · apply inductionHypothesis.expressionSafe
                      have thenShort :=
                        exprParses_remaining_length_lt
                          thenBranch.parses
                      rw [elseToken.inputEq] at thenShort
                      have conditionShort :=
                        exprParses_remaining_length_lt
                          condition.parses
                      rw [thenToken.inputEq] at conditionShort
                      simp only [
                        expressionRank,
                        List.length_cons
                      ] at sufficient conditionShort thenShort ⊢
                      omega
                    · intro _
                      exact noFuelExhaustion_ok _
          · apply noFuelExhaustion_bind
            · apply inductionHypothesis.prefixSafe
              simp only [
                expressionRank,
                prefixRank
              ] at sufficient ⊢
              omega
            · intro prefixResult
              apply noFuelExhaustion_bind
              · apply inductionHypothesis.infixSafe
                have prefixShort :=
                  prefixParses_remaining_length_lt
                    prefixResult.parses
                simp only [
                  expressionRank,
                  infixRank
                ] at sufficient prefixShort ⊢
                omega
              · intro _
                exact noFuelExhaustion_ok _
        · apply noFuelExhaustion_bind
          · apply inductionHypothesis.prefixSafe
            simp only [
              expressionRank,
              prefixRank
            ] at sufficient ⊢
            omega
          · intro prefixResult
            apply noFuelExhaustion_bind
            · apply inductionHypothesis.infixSafe
              have prefixShort :=
                prefixParses_remaining_length_lt
                  prefixResult.parses
              simp only [
                expressionRank,
                infixRank
              ] at sufficient prefixShort ⊢
              omega
            · intro _
              exact noFuelExhaustion_ok _
      · intro file tokens sufficient
        simp only [parsePrefixFuel]
        split
        · apply noFuelExhaustion_bind
          · apply inductionHypothesis.prefixSafe
            simp only [
              prefixRank,
              List.length_cons
            ] at sufficient ⊢
            omega
          · intro _
            exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_ok _
        · apply noFuelExhaustion_bind
          · apply inductionHypothesis.expressionSafe
            simp only [
              prefixRank,
              expressionRank,
              List.length_cons
            ] at sufficient ⊢
            omega
          · intro inner
            apply noFuelExhaustion_bind
            · exact expectKind_noFuelExhaustion
                file .rightParen inner.remaining
            · intro _
              exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_ok _
        · split
          · exact noFuelExhaustion_ok _
          · split
            · apply noFuelExhaustion_bind
              · apply inductionHypothesis.argumentsSafe
                simp only [
                  prefixRank,
                  argumentsRank,
                  List.length_cons
                ] at sufficient ⊢
                omega
              · intro _
                exact noFuelExhaustion_ok _
            · exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_source _
      · intro file tokens sufficient
        simp only [parseArgumentsFuel]
        split
        · exact noFuelExhaustion_ok _
        · apply noFuelExhaustion_bind
          · apply inductionHypothesis.expressionSafe
            simp only [
              argumentsRank,
              expressionRank
            ] at sufficient ⊢
            omega
          · intro first
            apply noFuelExhaustion_bind
            · apply inductionHypothesis.argumentTailSafe
              have firstShort :=
                exprParses_remaining_length_lt first.parses
              simp only [
                argumentsRank,
                argumentTailRank
              ] at sufficient firstShort ⊢
              omega
            · intro _
              exact noFuelExhaustion_ok _
      · intro file tokens sufficient
        simp only [parseArgumentTailFuel]
        split
        · exact noFuelExhaustion_ok _
        · apply noFuelExhaustion_bind
          · apply inductionHypothesis.expressionSafe
            simp only [
              argumentTailRank,
              expressionRank,
              List.length_cons
            ] at sufficient ⊢
            omega
          · intro next
            apply noFuelExhaustion_bind
            · apply inductionHypothesis.argumentTailSafe
              have nextShort :=
                exprParses_remaining_length_lt next.parses
              simp only [
                argumentTailRank,
                List.length_cons
              ] at sufficient nextShort ⊢
              omega
            · intro _
              exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_source _
      · intro file minimum left tokens sufficient
        simp only [parseInfixFuel]
        split
        · rename_i head binaryAtHead
          have headLength :
              tokens.length = head.remaining.length + 1 := by
            have equality :=
              congrArg List.length head.inputEq
            simpa only [List.length_cons] using equality
          split
          · exact noFuelExhaustion_ok _
          · apply noFuelExhaustion_bind
            · apply inductionHypothesis.expressionSafe
              simp only [
                infixRank,
                expressionRank
              ] at sufficient ⊢
              omega
            · intro right
              split
              · apply noFuelExhaustion_bind
                · apply inductionHypothesis.infixSafe
                  have rightShort :=
                    exprParses_remaining_length_lt right.parses
                  simp only [
                    infixRank
                  ] at sufficient rightShort ⊢
                  omega
                · intro _
                  exact noFuelExhaustion_ok _
              · split
                · split
                  · exact noFuelExhaustion_source _
                  · apply noFuelExhaustion_bind
                    · apply inductionHypothesis.infixSafe
                      have rightShort :=
                        exprParses_remaining_length_lt right.parses
                      simp only [
                        infixRank
                      ] at sufficient rightShort ⊢
                      omega
                    · intro _
                      exact noFuelExhaustion_ok _
                · apply noFuelExhaustion_bind
                  · apply inductionHypothesis.infixSafe
                    have rightShort :=
                      exprParses_remaining_length_lt right.parses
                    simp only [
                      infixRank
                    ] at sufficient rightShort ⊢
                    omega
                  · intro _
                    exact noFuelExhaustion_ok _
        · exact noFuelExhaustion_ok _

private def expressionFuel (tokens : List Token) : Nat :=
  32 * (tokens.length + 1)

private def parseExpression
    (file : SourceFile)
    (tokens : List Token) :
    Except ParseFailure (ExpressionResult 0 tokens) :=
  parseExpressionFuel file (expressionFuel tokens) 0 tokens

private theorem parseExpression_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (parseExpression file tokens) := by
  apply (expressionParserFuelSafe
    (expressionFuel tokens)).expressionSafe
  simp only [expressionFuel, expressionRank]
  omega

private structure LetResult (input : List Token) where
  statement : LetStatement
  remaining : List Token
  parses : LetParses input statement remaining

private theorem expectIdentifier_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (expectIdentifier file tokens) := by
  intro _ _
  cases tokens with
  | nil =>
      simp [expectIdentifier]
  | cons token rest =>
      cases token with
      | mk kind span =>
          cases kind <;> simp [expectIdentifier]

private theorem parseType_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (parseType file tokens) := by
  intro _ _
  cases tokens with
  | nil =>
      simp [parseType]
  | cons first rest =>
      cases first with
      | mk firstKind firstSpan =>
          cases rest with
          | nil =>
              cases firstKind <;>
                simp [parseType] <;>
                split <;>
                simp
          | cons second tail =>
              cases second with
              | mk secondKind secondSpan =>
                  cases firstKind <;>
                    cases secondKind <;>
                    simp [parseType] <;>
                    split <;>
                    simp

private def parseLet
    (file : SourceFile) :
    (input : List Token) → Except ParseFailure (LetResult input)
  | tokens => do
      let letToken ← expectKind file .keywordLet tokens
      let name ← expectIdentifier file letToken.remaining
      let colon ← expectKind file .colon name.remaining
      let type ← parseType file colon.remaining
      let equal ← expectKind file .equal type.remaining
      let value ← parseExpression file equal.remaining
      let semicolon ← expectKind file .semicolon value.remaining
      have typeParse :
          TypeParses colon.remaining type.type
            (equal.token :: equal.remaining) := by
        simpa only [equal.inputEq] using type.parses
      have valueParse :
          ExprParses 0 equal.remaining value.expression
            (semicolon.token :: semicolon.remaining) := by
        simpa only [semicolon.inputEq] using value.parses
      let statement : LetStatement := {
        span := SourceSpan.cover letToken.token.span semicolon.token.span
        name := {
          value := name.text
          span := name.token.span
        }
        type := type.type
        value := value.expression
      }
      .ok {
        statement
        remaining := semicolon.remaining
        parses := by
          have direct :
              LetParses
                (letToken.token :: name.token :: colon.token ::
                  colon.remaining)
                statement
                semicolon.remaining := .intro
            letToken.token
            name.token
            colon.token
            equal.token
            semicolon.token
            name.text
            colon.remaining
            equal.remaining
            semicolon.remaining
            type.type
            value.expression
            letToken.kindEq
            name.kindEq
            colon.kindEq
            typeParse
            equal.kindEq
            valueParse
            semicolon.kindEq
          exact letToken.castInput
            (fun input =>
              LetParses input statement semicolon.remaining)
            (name.castInput
              (fun afterLet =>
                LetParses
                  (letToken.token :: afterLet)
                  statement
                  semicolon.remaining)
              (colon.castInput
                (fun afterName =>
                  LetParses
                    (letToken.token :: name.token :: afterName)
                    statement
                    semicolon.remaining)
                direct))
      }

private theorem parseLet_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (parseLet file tokens) := by
  simp only [parseLet]
  apply noFuelExhaustion_bind
  · exact expectKind_noFuelExhaustion
      file .keywordLet tokens
  · intro letToken
    apply noFuelExhaustion_bind
    · exact expectIdentifier_noFuelExhaustion
        file letToken.remaining
    · intro name
      apply noFuelExhaustion_bind
      · exact expectKind_noFuelExhaustion
          file .colon name.remaining
      · intro colon
        apply noFuelExhaustion_bind
        · exact parseType_noFuelExhaustion
            file colon.remaining
        · intro type
          apply noFuelExhaustion_bind
          · exact expectKind_noFuelExhaustion
              file .equal type.remaining
          · intro equal
            apply noFuelExhaustion_bind
            · exact parseExpression_noFuelExhaustion
                file equal.remaining
            · intro value
              apply noFuelExhaustion_bind
              · exact expectKind_noFuelExhaustion
                  file .semicolon value.remaining
              · intro _
                exact noFuelExhaustion_ok _

private theorem typeParses_remaining_length_lt
    {input remaining : List Token}
    {type : TypeSyntax}
    (derivation : TypeParses input type remaining) :
    remaining.length < input.length := by
  cases derivation <;> simp <;> omega

private theorem letParses_remaining_length_lt
    {input remaining : List Token}
    {statement : LetStatement}
    (derivation : LetParses input statement remaining) :
    remaining.length < input.length := by
  cases derivation with
  | intro _ _ _ _ _ _ _ _ _ _ _ _ _ _
      typeParse _ valueParse _ =>
      have typeShort :=
        typeParses_remaining_length_lt typeParse
      have valueShort :=
        exprParses_remaining_length_lt valueParse
      simp only [List.length_cons] at typeShort valueShort ⊢
      omega

private structure BindingsResult (input : List Token) where
  bindings : List LetStatement
  remaining : List Token
  parses : BindingsParse input bindings remaining

private def parseBindings
    (file : SourceFile) :
    (fuel : Nat) → (input : List Token) →
      Except ParseFailure (BindingsResult input)
  | 0, tokens =>
      exhausted file .bindings tokens
  | fuel + 1, tokens =>
      match tokens with
      | { kind := .keywordLet, span } :: rest => do
          let binding ← parseLet file
            ({ kind := .keywordLet, span } :: rest)
          let tail ← parseBindings file fuel binding.remaining
          .ok {
            bindings := binding.statement :: tail.bindings
            remaining := tail.remaining
            parses := .more
              ({ kind := .keywordLet, span } :: rest)
              binding.remaining
              tail.remaining
              binding.statement
              tail.bindings
              binding.parses
              tail.parses
          }
      | { kind := .keywordReturn, span } :: rest =>
          let returnToken : Token := { kind := .keywordReturn, span }
          .ok {
            bindings := []
            remaining := returnToken :: rest
            parses := .done returnToken rest rfl
          }
      | _ =>
          .error (.source (expected file .bindingOrReturn tokens))

private theorem parseBindings_noFuelExhaustion
    (file : SourceFile)
    (fuel : Nat)
    (tokens : List Token)
    (sufficient : tokens.length < fuel) :
    NoFuelExhaustion (parseBindings file fuel tokens) := by
  induction fuel generalizing tokens with
  | zero =>
      omega
  | succ fuel inductionHypothesis =>
      simp only [parseBindings]
      split
      · apply noFuelExhaustion_bind
        · exact parseLet_noFuelExhaustion file _
        · intro binding
          apply noFuelExhaustion_bind
          · apply inductionHypothesis
            have bindingShort :=
              letParses_remaining_length_lt binding.parses
            simp only [List.length_cons] at sufficient bindingShort
            omega
          · intro _
            exact noFuelExhaustion_ok _
      · exact noFuelExhaustion_ok _
      · exact noFuelExhaustion_source _

private structure ReturnResult (input : List Token) where
  statement : ReturnStatement
  remaining : List Token
  parses : ReturnParses input statement remaining

private def parseReturn
    (file : SourceFile) :
    (input : List Token) → Except ParseFailure (ReturnResult input)
  | tokens => do
      let returnToken ← expectKind file .keywordReturn tokens
      let value ← parseExpression file returnToken.remaining
      let semicolon ← expectKind file .semicolon value.remaining
      have valueParse :
          ExprParses 0 returnToken.remaining value.expression
            (semicolon.token :: semicolon.remaining) := by
        simpa only [semicolon.inputEq] using value.parses
      let statement : ReturnStatement := {
        span := SourceSpan.cover
          returnToken.token.span semicolon.token.span
        value := value.expression
      }
      .ok {
        statement
        remaining := semicolon.remaining
        parses := by
          have direct :
              ReturnParses
                (returnToken.token :: returnToken.remaining)
                statement
                semicolon.remaining := .intro
            returnToken.token
            semicolon.token
            returnToken.remaining
            semicolon.remaining
            value.expression
            returnToken.kindEq
            valueParse
            semicolon.kindEq
          exact returnToken.castInput
            (fun input =>
              ReturnParses input statement semicolon.remaining)
            direct
      }

private theorem parseReturn_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (parseReturn file tokens) := by
  simp only [parseReturn]
  apply noFuelExhaustion_bind
  · exact expectKind_noFuelExhaustion
      file .keywordReturn tokens
  · intro returnToken
    apply noFuelExhaustion_bind
    · exact parseExpression_noFuelExhaustion
        file returnToken.remaining
    · intro value
      apply noFuelExhaustion_bind
      · exact expectKind_noFuelExhaustion
          file .semicolon value.remaining
      · intro _
        exact noFuelExhaustion_ok _

private structure FunctionResult (input : List Token) where
  declaration : FunctionDecl
  remaining : List Token
  parses : FunctionParses input declaration remaining

private def parseFunction
    (file : SourceFile)
    (tokens : List Token) :
    Except ParseFailure (FunctionResult tokens) := do
  let functionToken ← expectKind file .keywordFunction tokens
  let name ← expectIdentifier file functionToken.remaining
  let leftParen ← expectKind file .leftParen name.remaining
  let rightParen ← expectKind file .rightParen leftParen.remaining
  let arrow ← expectKind file .arrow rightParen.remaining
  let returnType ← parseType file arrow.remaining
  let leftBrace ← expectKind file .leftBrace returnType.remaining
  let bindings ← parseBindings file
    (leftBrace.remaining.length + 1) leftBrace.remaining
  let result ← parseReturn file bindings.remaining
  let rightBrace ← expectKind file .rightBrace result.remaining
  have typeParse :
      TypeParses arrow.remaining returnType.type
        (leftBrace.token :: leftBrace.remaining) := by
    simpa only [leftBrace.inputEq] using returnType.parses
  have resultParse :
      ReturnParses bindings.remaining result.statement
        (rightBrace.token :: rightBrace.remaining) := by
    simpa only [rightBrace.inputEq] using result.parses
  let declaration : FunctionDecl := {
    span := SourceSpan.cover functionToken.token.span rightBrace.token.span
    name := {
      value := name.text
      span := name.token.span
    }
    returnType := returnType.type
    bindings := bindings.bindings
    result := result.statement
  }
  .ok {
    declaration
    remaining := rightBrace.remaining
    parses := by
      have direct :
          FunctionParses
            (functionToken.token :: name.token :: leftParen.token ::
              rightParen.token :: arrow.token :: arrow.remaining)
            declaration
            rightBrace.remaining := .intro
        functionToken.token
        name.token
        leftParen.token
        rightParen.token
        arrow.token
        leftBrace.token
        rightBrace.token
        name.text
        arrow.remaining
        leftBrace.remaining
        bindings.remaining
        rightBrace.remaining
        rightBrace.remaining
        returnType.type
        bindings.bindings
        result.statement
        functionToken.kindEq
        name.kindEq
        leftParen.kindEq
        rightParen.kindEq
        arrow.kindEq
        typeParse
        leftBrace.kindEq
        bindings.parses
        resultParse
        rightBrace.kindEq
      exact functionToken.castInput
        (fun input =>
          FunctionParses input declaration rightBrace.remaining)
        (name.castInput
          (fun afterFunction =>
            FunctionParses
              (functionToken.token :: afterFunction)
              declaration
              rightBrace.remaining)
          (leftParen.castInput
            (fun afterName =>
              FunctionParses
                (functionToken.token :: name.token :: afterName)
                declaration
                rightBrace.remaining)
            (rightParen.castInput
              (fun afterLeftParen =>
                FunctionParses
                  (functionToken.token :: name.token ::
                    leftParen.token :: afterLeftParen)
                  declaration
                  rightBrace.remaining)
              (arrow.castInput
                (fun afterRightParen =>
                  FunctionParses
                    (functionToken.token :: name.token ::
                      leftParen.token :: rightParen.token ::
                      afterRightParen)
                    declaration
                    rightBrace.remaining)
                direct))))
  }

private theorem parseFunction_noFuelExhaustion
    (file : SourceFile)
    (tokens : List Token) :
    NoFuelExhaustion (parseFunction file tokens) := by
  simp only [parseFunction]
  apply noFuelExhaustion_bind
  · exact expectKind_noFuelExhaustion
      file .keywordFunction tokens
  · intro functionToken
    apply noFuelExhaustion_bind
    · exact expectIdentifier_noFuelExhaustion
        file functionToken.remaining
    · intro name
      apply noFuelExhaustion_bind
      · exact expectKind_noFuelExhaustion
          file .leftParen name.remaining
      · intro leftParen
        apply noFuelExhaustion_bind
        · exact expectKind_noFuelExhaustion
            file .rightParen leftParen.remaining
        · intro rightParen
          apply noFuelExhaustion_bind
          · exact expectKind_noFuelExhaustion
              file .arrow rightParen.remaining
          · intro arrow
            apply noFuelExhaustion_bind
            · exact parseType_noFuelExhaustion
                file arrow.remaining
            · intro returnType
              apply noFuelExhaustion_bind
              · exact expectKind_noFuelExhaustion
                  file .leftBrace returnType.remaining
              · intro leftBrace
                apply noFuelExhaustion_bind
                · apply parseBindings_noFuelExhaustion
                  omega
                · intro bindings
                  apply noFuelExhaustion_bind
                  · exact parseReturn_noFuelExhaustion
                      file bindings.remaining
                  · intro result
                    apply noFuelExhaustion_bind
                    · exact expectKind_noFuelExhaustion
                        file .rightBrace result.remaining
                    · intro _
                      exact noFuelExhaustion_ok _

private structure ParsedResult (lexed : Lexed) where
  parsed : ParsedFile
  parses : FileParses lexed parsed

private def parseLexedUncheckedCertified
    (file : SourceFile)
    (lexed : Lexed) : Except ParseFailure (ParsedResult lexed) := do
  let function ← parseFunction file lexed.tokens
  match remainingEq : function.remaining with
  | [] =>
      have functionParse :
          FunctionParses lexed.tokens function.declaration [] := by
        simpa only [remainingEq] using function.parses
      .ok {
        parsed := {
          span := function.declaration.span
          function := function.declaration
          comments := lexed.comments
        }
        parses := .intro
          lexed.tokens
          lexed.comments
          function.declaration
          functionParse
      }
  | _ =>
      .error (.source
        (expected file .endOfFile function.remaining))

private def parseLexedUnchecked
    (file : SourceFile)
    (lexed : Lexed) : Except ParseFailure ParsedFile :=
  match parseLexedUncheckedCertified file lexed with
  | .error failure => .error failure
  | .ok result => .ok result.parsed

private theorem parseLexedUncheckedCertified_noFuelExhaustion
    (file : SourceFile)
    (lexed : Lexed) :
    NoFuelExhaustion
      (parseLexedUncheckedCertified file lexed) := by
  simp only [parseLexedUncheckedCertified]
  apply noFuelExhaustion_bind
  · exact parseFunction_noFuelExhaustion
      file lexed.tokens
  · intro function
    split
    · exact noFuelExhaustion_ok _
    · exact noFuelExhaustion_source _

private theorem parseLexedUnchecked_noFuelExhaustion
    (file : SourceFile)
    (lexed : Lexed) :
    NoFuelExhaustion (parseLexedUnchecked file lexed) := by
  intro phase span
  unfold parseLexedUnchecked
  cases resultEquation :
      parseLexedUncheckedCertified file lexed with
  | ok result =>
      simp
  | error failure =>
      cases failure with
      | source error =>
          simp
      | internal invariant =>
          cases invariant with
          | fuelExhausted actualPhase actualSpan =>
              exact False.elim
                (parseLexedUncheckedCertified_noFuelExhaustion
                  file lexed actualPhase actualSpan resultEquation)
          | invalidInput invalid =>
              simp
          | invalidOutput invalid =>
              simp

private theorem parseLexedUnchecked_success_fileParses
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexedUnchecked file lexed = .ok parsed) :
    FileParses lexed parsed := by
  unfold parseLexedUnchecked at success
  cases certified : parseLexedUncheckedCertified file lexed with
  | error failure =>
      simp [certified] at success
  | ok result =>
      simp [certified] at success
      cases success
      exact result.parses

def parseLexed
    (file : SourceFile)
    (lexed : Lexed) : Except ParseFailure ParsedFile :=
  match Lexer.lex file with
  | .error _ =>
      .error (.internal (.invalidInput lexed))
  | .ok canonical =>
      if decide (canonical = lexed) then
        match parseLexedUnchecked file lexed with
        | .error failure => .error failure
        | .ok parsed =>
            if parsed.conformsTo file lexed then
              .ok parsed
            else
              .error (.internal (.invalidOutput parsed))
      else
        .error (.internal (.invalidInput lexed))

theorem parseLexed_ne_fuel_exhausted
    (file : SourceFile)
    (lexed : Lexed)
    (phase : ParserPhase)
    (span : SourceSpan) :
    parseLexed file lexed ≠
      .error (.internal (.fuelExhausted phase span)) := by
  cases lexing : Lexer.lex file with
  | error failure =>
      simp [parseLexed, lexing]
  | ok canonical =>
      cases canonicality : decide (canonical = lexed) with
      | false =>
          simp [parseLexed, lexing, canonicality]
      | true =>
          cases parsing : parseLexedUnchecked file lexed with
          | error failure =>
              cases failure with
              | source error =>
                  simp [
                    parseLexed,
                    lexing,
                    canonicality,
                    parsing
                  ]
              | internal invariant =>
                  cases invariant with
                  | fuelExhausted actualPhase actualSpan =>
                      exact False.elim
                        (parseLexedUnchecked_noFuelExhaustion
                          file lexed
                          actualPhase actualSpan parsing)
                  | invalidInput invalid =>
                      simp [
                        parseLexed,
                        lexing,
                        canonicality,
                        parsing
                      ]
                  | invalidOutput invalid =>
                      simp [
                        parseLexed,
                        lexing,
                        canonicality,
                        parsing
                      ]
          | ok parsed =>
              cases outputValidity :
                  parsed.conformsTo file lexed with
              | false =>
                  simp [
                    parseLexed,
                    lexing,
                    canonicality,
                    parsing,
                    outputValidity
                  ]
              | true =>
                  simp [
                    parseLexed,
                    lexing,
                    canonicality,
                    parsing,
                    outputValidity
                  ]

theorem parseLexed_success_provenance
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexed file lexed = .ok parsed) :
    Lexer.lex file = .ok lexed ∧
      LexicalGrammar.Lexes file lexed ∧
      parsed.ConformsTo file lexed := by
  unfold parseLexed at success
  cases lexing : Lexer.lex file with
  | error failure =>
      simp [lexing] at success
  | ok canonical =>
      cases canonicality : decide (canonical = lexed) with
      | false =>
          simp [lexing, canonicality] at success
      | true =>
          have canonicalEquals : canonical = lexed :=
            of_decide_eq_true canonicality
          subst canonical
          cases parsing : parseLexedUnchecked file lexed with
          | error failure =>
              simp [lexing, parsing] at success
          | ok parsedResult =>
            cases outputValidity : parsedResult.conformsTo file lexed with
          | false =>
              simp [lexing, parsing, outputValidity] at success
          | true =>
              simp [lexing, parsing, outputValidity] at success
              cases success
              exact ⟨
                rfl,
                Lexer.lex_success_lexes file lexed lexing,
                (ParsedFile.conformsTo_eq_true_iff
                  parsed file lexed).mp outputValidity
              ⟩

theorem parseLexed_success_conforms
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexed file lexed = .ok parsed) :
    lexed.ValidFor file ∧ parsed.ConformsTo file lexed :=
  let provenance :=
    parseLexed_success_provenance file lexed parsed success
  ⟨provenance.2.1.1, provenance.2.2⟩

theorem parseLexed_success_fileParses
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexed file lexed = .ok parsed) :
    FileParses lexed parsed := by
  unfold parseLexed at success
  cases lexing : Lexer.lex file with
  | error failure =>
      simp [lexing] at success
  | ok canonical =>
      cases canonicality : decide (canonical = lexed) with
      | false =>
          simp [lexing, canonicality] at success
      | true =>
          cases parsing : parseLexedUnchecked file lexed with
          | error failure =>
              simp [lexing, canonicality, parsing] at success
          | ok parsedResult =>
              cases outputValidity :
                  parsedResult.conformsTo file lexed with
              | false =>
                  simp [
                    lexing,
                    canonicality,
                    parsing,
                    outputValidity
                  ] at success
              | true =>
                  simp [
                    lexing,
                    canonicality,
                    parsing,
                    outputValidity
                  ] at success
                  cases success
                  exact parseLexedUnchecked_success_fileParses
                    file lexed parsed parsing

def parse (file : SourceFile) : Except FrontendError ParsedFile :=
  match Lexer.lex file with
  | .error (.source error) => .error (.lexical error)
  | .error (.internal invariant) => .error (.internal (.lexer invariant))
  | .ok lexed =>
      match parseLexed file lexed with
      | .error (.source error) => .error (.syntactic error)
      | .error (.internal invariant) =>
          .error (.internal (.parser invariant))
      | .ok parsed => .ok parsed

theorem parse_ne_parser_fuel_exhausted
    (file : SourceFile)
    (phase : ParserPhase)
    (span : SourceSpan) :
    parse file ≠
      .error
        (.internal
          (.parser (.fuelExhausted phase span))) := by
  cases lexing : Lexer.lex file with
  | error failure =>
      cases failure <;>
        simp [parse, lexing]
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error failure =>
          cases failure with
          | source error =>
              simp [parse, lexing, parsing]
          | internal invariant =>
              cases invariant with
              | fuelExhausted actualPhase actualSpan =>
                  exact False.elim
                    (parseLexed_ne_fuel_exhausted
                      file lexed
                      actualPhase actualSpan parsing)
              | invalidInput invalid =>
                  simp [parse, lexing, parsing]
              | invalidOutput invalid =>
                  simp [parse, lexing, parsing]
      | ok parsed =>
          simp [parse, lexing, parsing]

theorem parse_success_valid
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    parsed.ValidFor file := by
  cases lexing : Lexer.lex file with
  | error failure =>
      cases failure <;> simp [parse, lexing] at success
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error failure =>
          cases failure <;> simp [parse, lexing, parsing] at success
      | ok parsedResult =>
          simp [parse, lexing, parsing] at success
          cases success
          exact (parseLexed_success_conforms
            file lexed parsed parsing).2.1

theorem parse_success_fileParses
    (file : SourceFile)
    (parsed : ParsedFile)
    (success : parse file = .ok parsed) :
    ∃ lexed,
      Lexer.lex file = .ok lexed ∧
        FileParses lexed parsed := by
  cases lexing : Lexer.lex file with
  | error failure =>
      cases failure <;> simp [parse, lexing] at success
  | ok lexed =>
      cases parsing : parseLexed file lexed with
      | error failure =>
          cases failure <;> simp [parse, lexing, parsing] at success
      | ok parsedResult =>
          simp [parse, lexing, parsing] at success
          cases success
          exact ⟨
            lexed,
            rfl,
            parseLexed_success_fileParses
              file lexed parsed parsing
          ⟩

end Parser

end Solcore.Surface
