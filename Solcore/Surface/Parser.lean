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

private def expectKind
    (file : SourceFile)
    (kind : TokenKind) :
    List Token → Except ParseFailure (Token × List Token)
  | token :: rest =>
      if token.kind == kind then
        .ok (token, rest)
      else
        .error (.source (expected file (.token kind) (token :: rest)))
  | [] =>
      .error (.source (expected file (.token kind) []))

private def expectIdentifier
    (file : SourceFile) :
    List Token → Except ParseFailure (Name × List Token)
  | { kind := .identifier text, span } :: rest =>
      .ok ({ value := text, span }, rest)
  | tokens =>
      .error (.source (expected file .identifier tokens))

private def expectContextual
    (file : SourceFile)
    (text : String) :
    List Token → Except ParseFailure (Token × List Token)
  | token@{ kind := .identifier actual, .. } :: rest =>
      if actual == text then
        .ok (token, rest)
      else
        .error (.source
          (expected file (.token (.identifier text)) (token :: rest)))
  | tokens =>
      .error (.source (expected file (.token (.identifier text)) tokens))

private def parseType (file : SourceFile) :
    List Token → Except ParseFailure (TypeSyntax × List Token)
  | left@{ kind := .leftParen, .. } ::
      right@{ kind := .rightParen, .. } :: rest =>
      .ok (.unit (SourceSpan.cover left.span right.span), rest)
  | { kind := .identifier text, span } :: rest =>
      if text == "bool" || text == "word" then
        .ok (.named { value := text, span }, rest)
      else
        .error (.source
          (expected file .type ({ kind := .identifier text, span } :: rest)))
  | tokens =>
      .error (.source (expected file .type tokens))

private def exhausted
    {α : Type}
    (file : SourceFile)
    (phase : ParserPhase)
    (tokens : List Token) : Except ParseFailure α :=
  .error (.internal (.fuelExhausted phase (errorSpan file tokens)))

private structure BinaryInfo where
  operator : BinaryOp
  precedence : Nat
  nonAssociative : Bool

private def binaryInfo : TokenKind → Option BinaryInfo
  | .equalEqual => some ⟨.eq, 1, true⟩
  | .bangEqual => some ⟨.ne, 1, true⟩
  | .less => some ⟨.lt, 2, true⟩
  | .greater => some ⟨.gt, 2, true⟩
  | .lessEqual => some ⟨.le, 2, true⟩
  | .greaterEqual => some ⟨.ge, 2, true⟩
  | .pipe => some ⟨.bitOr, 3, false⟩
  | .caret => some ⟨.bitXor, 4, false⟩
  | .ampersand => some ⟨.bitAnd, 5, false⟩
  | .plus => some ⟨.add, 6, false⟩
  | .minus => some ⟨.sub, 6, false⟩
  | .star => some ⟨.mul, 7, false⟩
  | .slash => some ⟨.div, 7, false⟩
  | .percent => some ⟨.mod, 7, false⟩
  | _ => none

private def peekBinary : List Token → Option (Token × BinaryInfo)
  | token :: _ => (binaryInfo token.kind).map fun info => (token, info)
  | [] => none

mutual

private def parseExpressionFuel
    (file : SourceFile) :
    Nat → Nat → List Token → Except ParseFailure (Expr × List Token)
  | 0, _, tokens =>
      exhausted file .expression tokens
  | fuel + 1, minimumPrecedence, tokens =>
      match tokens with
      | ifToken@{ kind := .keywordIf, .. } :: afterIf =>
          if minimumPrecedence == 0 then do
            let (condition, afterCondition) ←
              parseExpressionFuel file fuel 0 afterIf
            let (_, afterThen) ← expectContextual file "then" afterCondition
            let (thenBranch, afterThenBranch) ←
              parseExpressionFuel file fuel 0 afterThen
            let (_, afterElse) ←
              expectKind file .keywordElse afterThenBranch
            let (elseBranch, remaining) ←
              parseExpressionFuel file fuel 0 afterElse
            let expression := .ifThenElse
              (SourceSpan.cover ifToken.span elseBranch.span)
              condition thenBranch elseBranch
            .ok (expression, remaining)
          else do
            let (left, remaining) ← parsePrefixFuel file fuel tokens
            parseInfixFuel file fuel minimumPrecedence left remaining
      | _ => do
          let (left, remaining) ← parsePrefixFuel file fuel tokens
          parseInfixFuel file fuel minimumPrecedence left remaining

private def parsePrefixFuel
    (file : SourceFile) :
    Nat → List Token → Except ParseFailure (Expr × List Token)
  | 0, tokens =>
      exhausted file .prefix tokens
  | fuel + 1, tokens =>
      match tokens with
      | operator@{ kind := .bang, .. } :: rest => do
          let (operand, remaining) ← parsePrefixFuel file fuel rest
          let expression := .unary
            (SourceSpan.cover operator.span operand.span)
            { value := .not, span := operator.span }
            operand
          .ok (expression, remaining)
      | left@{ kind := .leftParen, .. } ::
          right@{ kind := .rightParen, .. } :: rest =>
          .ok (.unit (SourceSpan.cover left.span right.span), rest)
      | left@{ kind := .leftParen, .. } :: rest => do
          let (inner, afterInner) ← parseExpressionFuel file fuel 0 rest
          let (right, remaining) ←
            expectKind file .rightParen afterInner
          .ok (.group (SourceSpan.cover left.span right.span) inner, remaining)
      | { kind := .decimal digits, span } :: rest =>
          .ok (.integer { base := .decimal, digits, span }, rest)
      | { kind := .hexadecimal digits, span } :: rest =>
          .ok (.integer { base := .hexadecimal, digits, span }, rest)
      | { kind := .identifier text, span } :: rest =>
          let callee : Name := { value := text, span }
          match rest with
          | { kind := .leftParen, .. } :: afterLeft => do
              let (arguments, right, remaining) ←
                parseArgumentsFuel file fuel afterLeft
              .ok (.call (SourceSpan.cover span right.span) callee arguments, remaining)
          | _ =>
              .ok (.name callee, rest)
      | _ =>
          .error (.source (expected file .expression tokens))

private def parseArgumentsFuel
    (file : SourceFile) :
    Nat → List Token → Except ParseFailure (List Expr × Token × List Token)
  | 0, tokens =>
      exhausted file .arguments tokens
  | fuel + 1, tokens =>
      match tokens with
      | right@{ kind := .rightParen, .. } :: rest =>
          .ok ([], right, rest)
      | _ => do
          let (first, afterFirst) ← parseExpressionFuel file fuel 0 tokens
          parseArgumentTailFuel file fuel [first] afterFirst

private def parseArgumentTailFuel
    (file : SourceFile) :
    Nat → List Expr → List Token →
      Except ParseFailure (List Expr × Token × List Token)
  | 0, _, tokens =>
      exhausted file .argumentTail tokens
  | fuel + 1, reversed, tokens =>
      match tokens with
      | right@{ kind := .rightParen, .. } :: rest =>
          .ok (reversed.reverse, right, rest)
      | { kind := .comma, .. } :: rest => do
          let (next, afterNext) ← parseExpressionFuel file fuel 0 rest
          parseArgumentTailFuel file fuel (next :: reversed) afterNext
      | _ =>
          .error (.source (expected file .commaOrRightParen tokens))

private def parseInfixFuel
    (file : SourceFile) :
    Nat → Nat → Expr → List Token → Except ParseFailure (Expr × List Token)
  | 0, _, left, tokens =>
      match peekBinary tokens with
      | some _ => exhausted file .infix tokens
      | none => .ok (left, tokens)
  | fuel + 1, minimumPrecedence, left, tokens =>
      match peekBinary tokens with
      | some (operatorToken, info) =>
          if info.precedence < minimumPrecedence then
            .ok (left, tokens)
          else
            match tokens with
            | _ :: afterOperator => do
                let (right, afterRight) ←
                  parseExpressionFuel file fuel (info.precedence + 1) afterOperator
                if info.nonAssociative then
                  match peekBinary afterRight with
                  | some (secondToken, secondInfo) =>
                      if secondInfo.precedence == info.precedence then
                        .error (.source
                          (nonAssociative secondToken secondInfo.operator))
                      else
                        let expression := .binary
                          (SourceSpan.cover left.span right.span)
                          { value := info.operator, span := operatorToken.span }
                          left right
                        parseInfixFuel file fuel minimumPrecedence expression afterRight
                  | none =>
                      let expression := .binary
                        (SourceSpan.cover left.span right.span)
                        { value := info.operator, span := operatorToken.span }
                        left right
                      parseInfixFuel file fuel minimumPrecedence expression afterRight
                else
                  let expression := .binary
                    (SourceSpan.cover left.span right.span)
                    { value := info.operator, span := operatorToken.span }
                    left right
                  parseInfixFuel file fuel minimumPrecedence expression afterRight
            | [] =>
                .ok (left, [])
      | none =>
          .ok (left, tokens)

end

private def expressionFuel (tokens : List Token) : Nat :=
  32 * (tokens.length + 1)

private def parseExpression
    (file : SourceFile)
    (tokens : List Token) : Except ParseFailure (Expr × List Token) :=
  parseExpressionFuel file (expressionFuel tokens) 0 tokens

private def parseLet
    (file : SourceFile) :
    List Token → Except ParseFailure (LetStatement × List Token)
  | tokens => do
      let (letToken, afterLet) ←
        expectKind file .keywordLet tokens
      let (name, afterName) ← expectIdentifier file afterLet
      let (_, afterColon) ← expectKind file .colon afterName
      let (type, afterType) ← parseType file afterColon
      let (_, afterEqual) ← expectKind file .equal afterType
      let (value, afterValue) ← parseExpression file afterEqual
      let (semicolon, remaining) ←
        expectKind file .semicolon afterValue
      .ok ({
        span := SourceSpan.cover letToken.span semicolon.span
        name
        type
        value
      }, remaining)

private def parseBindings
    (file : SourceFile) :
    Nat → List Token → Except ParseFailure (List LetStatement × List Token)
  | 0, tokens =>
      exhausted file .bindings tokens
  | fuel + 1, tokens =>
      match tokens with
      | { kind := .keywordLet, .. } :: _ => do
          let (binding, remaining) ← parseLet file tokens
          let (bindings, afterBindings) ← parseBindings file fuel remaining
          .ok (binding :: bindings, afterBindings)
      | { kind := .keywordReturn, .. } :: _ =>
          .ok ([], tokens)
      | _ =>
          .error (.source (expected file .bindingOrReturn tokens))

private def parseReturn
    (file : SourceFile) :
    List Token → Except ParseFailure (ReturnStatement × List Token)
  | tokens => do
      let (returnToken, afterReturn) ←
        expectKind file .keywordReturn tokens
      let (value, afterValue) ← parseExpression file afterReturn
      let (semicolon, remaining) ←
        expectKind file .semicolon afterValue
      .ok ({
        span := SourceSpan.cover returnToken.span semicolon.span
        value
      }, remaining)

private def parseFunction
    (file : SourceFile)
    (tokens : List Token) : Except ParseFailure (FunctionDecl × List Token) := do
  let (functionToken, afterFunction) ←
    expectKind file .keywordFunction tokens
  let (name, afterName) ← expectIdentifier file afterFunction
  let (_, afterLeftParen) ←
    expectKind file .leftParen afterName
  let (_, afterRightParen) ←
    expectKind file .rightParen afterLeftParen
  let (_, afterArrow) ← expectKind file .arrow afterRightParen
  let (returnType, afterType) ← parseType file afterArrow
  let (_, afterLeftBrace) ←
    expectKind file .leftBrace afterType
  let (bindings, afterBindings) ←
    parseBindings file (afterLeftBrace.length + 1) afterLeftBrace
  let (result, afterResult) ← parseReturn file afterBindings
  let (rightBrace, remaining) ←
    expectKind file .rightBrace afterResult
  .ok ({
    span := SourceSpan.cover functionToken.span rightBrace.span
    name
    returnType
    bindings
    result
  }, remaining)

private def parseLexedUnchecked
    (file : SourceFile)
    (lexed : Lexed) : Except ParseFailure ParsedFile := do
  let (function, remaining) ← parseFunction file lexed.tokens
  match remaining with
  | [] =>
      .ok {
        span := function.span
        function
        comments := lexed.comments
      }
  | _ =>
      .error (.source (expected file .endOfFile remaining))

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

theorem parseLexed_success_provenance
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexed file lexed = .ok parsed) :
    Lexer.lex file = .ok lexed ∧
      lexed.ValidFor file ∧
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
                Lexer.lex_success_valid file lexed lexing,
                (ParsedFile.conformsTo_eq_true_iff
                  parsed file lexed).mp outputValidity
              ⟩

theorem parseLexed_success_conforms
    (file : SourceFile)
    (lexed : Lexed)
    (parsed : ParsedFile)
    (success : parseLexed file lexed = .ok parsed) :
    lexed.ValidFor file ∧ parsed.ConformsTo file lexed :=
  (parseLexed_success_provenance file lexed parsed success).2

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

end Parser

end Solcore.Surface
