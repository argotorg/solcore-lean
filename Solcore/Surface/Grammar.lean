import Solcore.Surface.Syntax

set_option autoImplicit false

namespace Solcore.Surface

inductive Associativity where
  | left
  | nonAssociative
  deriving Repr, BEq, DecidableEq

/--
The declarative binding table for the M2a expression grammar.
-/
inductive BinaryBinding :
    TokenKind → BinaryOp → Nat → Associativity → Prop where
  | eq : BinaryBinding .equalEqual .eq 1 .nonAssociative
  | ne : BinaryBinding .bangEqual .ne 1 .nonAssociative
  | lt : BinaryBinding .less .lt 2 .nonAssociative
  | gt : BinaryBinding .greater .gt 2 .nonAssociative
  | le : BinaryBinding .lessEqual .le 2 .nonAssociative
  | ge : BinaryBinding .greaterEqual .ge 2 .nonAssociative
  | bitOr : BinaryBinding .pipe .bitOr 3 .left
  | bitXor : BinaryBinding .caret .bitXor 4 .left
  | bitAnd : BinaryBinding .ampersand .bitAnd 5 .left
  | add : BinaryBinding .plus .add 6 .left
  | sub : BinaryBinding .minus .sub 6 .left
  | mul : BinaryBinding .star .mul 7 .left
  | div : BinaryBinding .slash .div 7 .left
  | mod : BinaryBinding .percent .mod 7 .left

/-- No operator at the head of `tokens` can bind at `minimum`. -/
def InfixBlocked (minimum : Nat) (tokens : List Token) : Prop :=
  ∀ (token : Token) (tail : List Token) (operator : BinaryOp)
      (precedence : Nat) (associativity : Associativity),
    tokens = token :: tail →
    BinaryBinding token.kind operator precedence associativity →
    precedence < minimum

/-- The head token is not an operator at the specified precedence. -/
def HeadPrecedenceNe (precedence : Nat) (tokens : List Token) : Prop :=
  ∀ (token : Token) (tail : List Token) (operator : BinaryOp)
      (actual : Nat) (associativity : Associativity),
    tokens = token :: tail →
    BinaryBinding token.kind operator actual associativity →
    actual ≠ precedence

/-- The first token, when present, does not have `kind`. -/
def HeadKindNe (kind : TokenKind) (tokens : List Token) : Prop :=
  ∀ (token : Token) (tail : List Token),
    tokens = token :: tail → token.kind ≠ kind

mutual

/--
`ExprParses minimum input expression rest` is the declarative precedence
judgment. It consumes exactly the prefix of `input` before `rest`.
-/
inductive ExprParses :
    Nat → List Token → Expr → List Token → Prop where
  | conditional
      (ifToken thenToken elseToken : Token)
      (afterIf afterThen afterElse remaining : List Token)
      (condition thenBranch elseBranch : Expr)
      (ifKind : ifToken.kind = .keywordIf)
      (conditionParse :
        ExprParses 0 afterIf condition (thenToken :: afterThen))
      (thenKind : thenToken.kind = .identifier "then")
      (thenParse :
        ExprParses 0 afterThen thenBranch (elseToken :: afterElse))
      (elseKind : elseToken.kind = .keywordElse)
      (elseParse :
        ExprParses 0 afterElse elseBranch remaining) :
      ExprParses 0
        (ifToken :: afterIf)
        (.ifThenElse
          (SourceSpan.cover ifToken.span elseBranch.span)
          condition thenBranch elseBranch)
        remaining
  | ordinary
      (minimum : Nat)
      (input afterPrefix remaining : List Token)
      (initial result : Expr)
      (prefixParse : PrefixParses input initial afterPrefix)
      (infixParse :
        InfixParses minimum initial afterPrefix result remaining) :
      ExprParses minimum input result remaining

inductive PrefixParses :
    List Token → Expr → List Token → Prop where
  | not
      (operatorToken : Token)
      (afterOperator remaining : List Token)
      (operand : Expr)
      (operatorKind : operatorToken.kind = .bang)
      (operandParse : PrefixParses afterOperator operand remaining) :
      PrefixParses
        (operatorToken :: afterOperator)
        (.unary
          (SourceSpan.cover operatorToken.span operand.span)
          { value := .not, span := operatorToken.span }
          operand)
        remaining
  | unit
      (left right : Token)
      (remaining : List Token)
      (leftKind : left.kind = .leftParen)
      (rightKind : right.kind = .rightParen) :
      PrefixParses
        (left :: right :: remaining)
        (.unit (SourceSpan.cover left.span right.span))
        remaining
  | group
      (left right : Token)
      (afterLeft remaining : List Token)
      (inner : Expr)
      (leftKind : left.kind = .leftParen)
      (innerParse :
        ExprParses 0 afterLeft inner (right :: remaining))
      (rightKind : right.kind = .rightParen) :
      PrefixParses
        (left :: afterLeft)
        (.group (SourceSpan.cover left.span right.span) inner)
        remaining
  | decimal
      (token : Token)
      (digits : String)
      (remaining : List Token)
      (kind : token.kind = .decimal digits) :
      PrefixParses
        (token :: remaining)
        (.integer { base := .decimal, digits, span := token.span })
        remaining
  | hexadecimal
      (token : Token)
      (digits : String)
      (remaining : List Token)
      (kind : token.kind = .hexadecimal digits) :
      PrefixParses
        (token :: remaining)
        (.integer { base := .hexadecimal, digits, span := token.span })
        remaining
  | name
      (token : Token)
      (text : String)
      (remaining : List Token)
      (kind : token.kind = .identifier text)
      (notCall : HeadKindNe .leftParen remaining) :
      PrefixParses
        (token :: remaining)
        (.name { value := text, span := token.span })
        remaining
  | call
      (identifier left right : Token)
      (text : String)
      (afterLeft remaining : List Token)
      (arguments : List Expr)
      (identifierKind : identifier.kind = .identifier text)
      (leftKind : left.kind = .leftParen)
      (argumentsParse :
        ArgumentsParse afterLeft arguments right remaining) :
      PrefixParses
        (identifier :: left :: afterLeft)
        (.call
          (SourceSpan.cover identifier.span right.span)
          { value := text, span := identifier.span }
          arguments)
        remaining

inductive InfixParses :
    Nat → Expr → List Token → Expr → List Token → Prop where
  | stop
      (minimum : Nat)
      (left : Expr)
      (tokens : List Token)
      (blocked : InfixBlocked minimum tokens) :
      InfixParses minimum left tokens left tokens
  | leftStep
      (minimum precedence : Nat)
      (left right result : Expr)
      (operatorToken : Token)
      (operator : BinaryOp)
      (afterOperator afterRight remaining : List Token)
      (binding :
        BinaryBinding operatorToken.kind operator precedence .left)
      (eligible : minimum ≤ precedence)
      (rightParse :
        ExprParses (precedence + 1) afterOperator right afterRight)
      (tailParse :
        InfixParses minimum
          (.binary
            (SourceSpan.cover left.span right.span)
            { value := operator, span := operatorToken.span }
            left right)
          afterRight result remaining) :
      InfixParses minimum left
        (operatorToken :: afterOperator) result remaining
  | nonAssociativeStep
      (minimum precedence : Nat)
      (left right result : Expr)
      (operatorToken : Token)
      (operator : BinaryOp)
      (afterOperator afterRight remaining : List Token)
      (binding :
        BinaryBinding operatorToken.kind operator precedence .nonAssociative)
      (eligible : minimum ≤ precedence)
      (rightParse :
        ExprParses (precedence + 1) afterOperator right afterRight)
      (notRepeated : HeadPrecedenceNe precedence afterRight)
      (tailParse :
        InfixParses minimum
          (.binary
            (SourceSpan.cover left.span right.span)
            { value := operator, span := operatorToken.span }
            left right)
          afterRight result remaining) :
      InfixParses minimum left
        (operatorToken :: afterOperator) result remaining

inductive ArgumentsParse :
    List Token → List Expr → Token → List Token → Prop where
  | empty
      (right : Token)
      (remaining : List Token)
      (rightKind : right.kind = .rightParen) :
      ArgumentsParse (right :: remaining) [] right remaining
  | nonempty
      (input afterFirst remaining : List Token)
      (first : Expr)
      (tail : List Expr)
      (right : Token)
      (firstParse : ExprParses 0 input first afterFirst)
      (tailParse :
        ArgumentTailParses afterFirst tail right remaining) :
      ArgumentsParse input (first :: tail) right remaining

inductive ArgumentTailParses :
    List Token → List Expr → Token → List Token → Prop where
  | done
      (right : Token)
      (remaining : List Token)
      (rightKind : right.kind = .rightParen) :
      ArgumentTailParses (right :: remaining) [] right remaining
  | more
      (comma right : Token)
      (afterComma afterNext remaining : List Token)
      (next : Expr)
      (tail : List Expr)
      (commaKind : comma.kind = .comma)
      (nextParse : ExprParses 0 afterComma next afterNext)
      (tailParse :
        ArgumentTailParses afterNext tail right remaining) :
      ArgumentTailParses
        (comma :: afterComma) (next :: tail) right remaining

end

inductive TypeParses :
    List Token → TypeSyntax → List Token → Prop where
  | unit
      (left right : Token)
      (remaining : List Token)
      (leftKind : left.kind = .leftParen)
      (rightKind : right.kind = .rightParen) :
      TypeParses
        (left :: right :: remaining)
        (.unit (SourceSpan.cover left.span right.span))
        remaining
  | bool
      (token : Token)
      (remaining : List Token)
      (kind : token.kind = .identifier "bool") :
      TypeParses
        (token :: remaining)
        (.named { value := "bool", span := token.span })
        remaining
  | word
      (token : Token)
      (remaining : List Token)
      (kind : token.kind = .identifier "word") :
      TypeParses
        (token :: remaining)
        (.named { value := "word", span := token.span })
        remaining

inductive LetParses :
    List Token → LetStatement → List Token → Prop where
  | intro
      (letToken nameToken colonToken equalToken semicolonToken : Token)
      (nameText : String)
      (afterColon afterEqual remaining : List Token)
      (type : TypeSyntax)
      (value : Expr)
      (letKind : letToken.kind = .keywordLet)
      (nameKind : nameToken.kind = .identifier nameText)
      (colonKind : colonToken.kind = .colon)
      (typeParse :
        TypeParses afterColon type (equalToken :: afterEqual))
      (equalKind : equalToken.kind = .equal)
      (valueParse :
        ExprParses 0 afterEqual value (semicolonToken :: remaining))
      (semicolonKind : semicolonToken.kind = .semicolon) :
      LetParses
        (letToken :: nameToken :: colonToken :: afterColon)
        {
          span := SourceSpan.cover letToken.span semicolonToken.span
          name := { value := nameText, span := nameToken.span }
          type
          value
        }
        remaining

inductive BindingsParse :
    List Token → List LetStatement → List Token → Prop where
  | done
      (returnToken : Token)
      (remaining : List Token)
      (returnKind : returnToken.kind = .keywordReturn) :
      BindingsParse (returnToken :: remaining) [] (returnToken :: remaining)
  | more
      (input afterBinding remaining : List Token)
      (binding : LetStatement)
      (bindings : List LetStatement)
      (bindingParse : LetParses input binding afterBinding)
      (tailParse :
        BindingsParse afterBinding bindings remaining) :
      BindingsParse input (binding :: bindings) remaining

inductive ReturnParses :
    List Token → ReturnStatement → List Token → Prop where
  | intro
      (returnToken semicolonToken : Token)
      (afterReturn remaining : List Token)
      (value : Expr)
      (returnKind : returnToken.kind = .keywordReturn)
      (valueParse :
        ExprParses 0 afterReturn value (semicolonToken :: remaining))
      (semicolonKind : semicolonToken.kind = .semicolon) :
      ReturnParses
        (returnToken :: afterReturn)
        {
          span := SourceSpan.cover returnToken.span semicolonToken.span
          value
        }
        remaining

inductive FunctionParses :
    List Token → FunctionDecl → List Token → Prop where
  | intro
      (functionToken nameToken leftParen rightParen arrow
        leftBrace rightBrace : Token)
      (nameText : String)
      (afterArrow afterLeftBrace afterBindings afterResult remaining : List Token)
      (returnType : TypeSyntax)
      (bindings : List LetStatement)
      (result : ReturnStatement)
      (functionKind : functionToken.kind = .keywordFunction)
      (nameKind : nameToken.kind = .identifier nameText)
      (leftParenKind : leftParen.kind = .leftParen)
      (rightParenKind : rightParen.kind = .rightParen)
      (arrowKind : arrow.kind = .arrow)
      (typeParse :
        TypeParses afterArrow returnType (leftBrace :: afterLeftBrace))
      (leftBraceKind : leftBrace.kind = .leftBrace)
      (bindingsParse :
        BindingsParse afterLeftBrace bindings afterBindings)
      (resultParse :
        ReturnParses afterBindings result (rightBrace :: afterResult))
      (rightBraceKind : rightBrace.kind = .rightBrace) :
      FunctionParses
        (functionToken :: nameToken :: leftParen :: rightParen ::
          arrow :: afterArrow)
        {
          span := SourceSpan.cover functionToken.span rightBrace.span
          name := { value := nameText, span := nameToken.span }
          returnType
          bindings
          result
        }
        afterResult

/--
The complete-file grammar relation. The empty remainder in `functionParse`
makes full non-trivia token consumption part of the judgment.
-/
inductive FileParses : Lexed → ParsedFile → Prop where
  | intro
      (tokens : List Token)
      (comments : List Comment)
      (declaration : FunctionDecl)
      (functionParse : FunctionParses tokens declaration []) :
      FileParses
        { tokens, comments }
        {
          span := declaration.span
          function := declaration
          comments
        }

namespace FileParses

theorem function_consumes_all
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed) :
    FunctionParses lexed.tokens parsed.function [] := by
  cases derivation
  assumption

theorem comments_preserved
    {lexed : Lexed}
    {parsed : ParsedFile}
    (derivation : FileParses lexed parsed) :
    parsed.comments = lexed.comments := by
  cases derivation
  rfl

end FileParses

inductive SpanConstraint where
  | exact (span : SourceSpan)
  | starts (span : SourceSpan)
  | ends (span : SourceSpan)
  deriving Repr, BEq, DecidableEq

namespace SpanConstraint

def Holds (constraint : SpanConstraint) (token : Token) : Prop :=
  match constraint with
  | .exact span => token.span = span
  | .starts span =>
      token.span.source = span.source ∧
        token.span.startByte = span.startByte
  | .ends span =>
      token.span.source = span.source ∧
        token.span.endByte = span.endByte

def holds (constraint : SpanConstraint) (token : Token) : Bool :=
  match constraint with
  | .exact span => decide (token.span = span)
  | .starts span =>
      decide (token.span.source = span.source) &&
        decide (token.span.startByte = span.startByte)
  | .ends span =>
      decide (token.span.source = span.source) &&
        decide (token.span.endByte = span.endByte)

theorem holds_eq_true_iff
    (constraint : SpanConstraint)
    (token : Token) :
    constraint.holds token = true ↔ constraint.Holds token := by
  cases constraint <;> simp [holds, Holds]

end SpanConstraint

structure ExpectedToken where
  kind : TokenKind
  constraints : List SpanConstraint := []
  deriving Repr, BEq, DecidableEq

namespace ExpectedToken

def plain (kind : TokenKind) : ExpectedToken :=
  { kind }

def exact (kind : TokenKind) (span : SourceSpan) : ExpectedToken :=
  { kind, constraints := [.exact span] }

def Matches (expected : ExpectedToken) (actual : Token) : Prop :=
  expected.kind = actual.kind ∧
    ∀ constraint ∈ expected.constraints, constraint.Holds actual

def isMatch (expected : ExpectedToken) (actual : Token) : Bool :=
  decide (expected.kind = actual.kind) &&
    expected.constraints.all (·.holds actual)

theorem isMatch_eq_true_iff
    (expected : ExpectedToken)
    (actual : Token) :
    expected.isMatch actual = true ↔ expected.Matches actual := by
  simp [isMatch, Matches, SpanConstraint.holds_eq_true_iff]

private def addFirst
    (constraint : SpanConstraint) :
    List ExpectedToken → List ExpectedToken
  | [] => []
  | first :: rest =>
      { first with constraints := constraint :: first.constraints } :: rest

private def addLast
    (constraint : SpanConstraint) :
    List ExpectedToken → List ExpectedToken
  | [] => []
  | [last] =>
      [{ last with constraints := constraint :: last.constraints }]
  | first :: second :: rest =>
      first :: addLast constraint (second :: rest)

def enclose
    (span : SourceSpan)
    (tokens : List ExpectedToken) : List ExpectedToken :=
  addLast (.ends span) (addFirst (.starts span) tokens)

/-- Pointwise matching between an expected-token sequence and actual tokens. -/
inductive ListMatches : List ExpectedToken → List Token → Prop where
  | nil : ListMatches [] []
  | cons
      {expected : ExpectedToken}
      {actual : Token}
      {expectedTail : List ExpectedToken}
      {actualTail : List Token}
      (head : expected.Matches actual)
      (tail : ListMatches expectedTail actualTail) :
      ListMatches (expected :: expectedTail) (actual :: actualTail)

/-- The first actual token, if present, satisfies `constraint`. -/
def FirstSatisfies
    (constraint : SpanConstraint) : List Token → Prop
  | [] => False
  | first :: _ => constraint.Holds first

/-- The last actual token, if present, satisfies `constraint`. -/
def LastSatisfies
    (constraint : SpanConstraint) : List Token → Prop
  | [] => False
  | [last] => constraint.Holds last
  | _ :: second :: rest => LastSatisfies constraint (second :: rest)

namespace ListMatches

theorem append
    {firstExpected secondExpected : List ExpectedToken}
    {firstActual secondActual : List Token}
    (first : ListMatches firstExpected firstActual)
    (second : ListMatches secondExpected secondActual) :
    ListMatches
      (firstExpected ++ secondExpected) (firstActual ++ secondActual) := by
  induction first with
  | nil => exact second
  | cons head _ inductionHypothesis =>
      exact .cons head inductionHypothesis

theorem length_eq
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches expected actual) :
    expected.length = actual.length := by
  induction relation <;> simp_all

theorem zipped_matches
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches expected actual) :
    ∀ pair ∈ expected.zip actual, pair.1.Matches pair.2 := by
  induction relation with
  | nil => simp
  | cons head _ inductionHypothesis =>
      intro pair member
      simp only [List.zip_cons_cons, List.mem_cons] at member
      rcases member with rfl | member
      · exact head
      · exact inductionHypothesis pair member

theorem split_append
    {firstExpected secondExpected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches (firstExpected ++ secondExpected) actual) :
    ∃ firstActual secondActual,
      actual = firstActual ++ secondActual ∧
      ListMatches firstExpected firstActual ∧
      ListMatches secondExpected secondActual := by
  induction firstExpected generalizing actual with
  | nil =>
      exact ⟨[], actual, rfl, .nil, relation⟩
  | cons expected rest inductionHypothesis =>
      cases relation with
      | cons head tail =>
          rcases inductionHypothesis tail with
            ⟨firstActual, secondActual, actualEq,
              firstRelation, secondRelation⟩
          exact ⟨_ :: firstActual, secondActual, by simp [actualEq],
            .cons head firstRelation, secondRelation⟩

private theorem addConstraint
    (constraint : SpanConstraint)
    (expected : ExpectedToken)
    (actual : Token)
    (holds : constraint.Holds actual)
    (relation : expected.Matches actual) :
    ({ expected with
      constraints := constraint :: expected.constraints } :
      ExpectedToken).Matches actual := by
  refine ⟨relation.1, ?_⟩
  intro candidate member
  simp only [List.mem_cons] at member
  rcases member with rfl | member
  · exact holds
  · exact relation.2 candidate member

private theorem addFirst
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches expected actual)
    (holds : FirstSatisfies constraint actual) :
    ListMatches (ExpectedToken.addFirst constraint expected) actual := by
  cases relation with
  | nil => contradiction
  | cons head tail =>
      exact .cons (addConstraint _ _ _ holds head) tail

private theorem addLast
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches expected actual)
    (holds : LastSatisfies constraint actual) :
    ListMatches (ExpectedToken.addLast constraint expected) actual := by
  induction relation with
  | nil => contradiction
  | @cons expected actual expectedTail actualTail head tail
      inductionHypothesis =>
      cases tail with
      | nil =>
          exact .cons (addConstraint _ _ _ holds head) .nil
      | cons nextHead nextTail =>
          exact .cons head (inductionHypothesis holds)

private theorem ofAddConstraint
    (constraint : SpanConstraint)
    (expected : ExpectedToken)
    (actual : Token)
    (relation :
      ({ expected with
        constraints := constraint :: expected.constraints } :
        ExpectedToken).Matches actual) :
    expected.Matches actual := by
  exact ⟨relation.1, fun candidate member =>
    relation.2 candidate (by simp [member])⟩

private theorem ofAddFirst
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation :
      ListMatches (ExpectedToken.addFirst constraint expected) actual) :
    ListMatches expected actual := by
  cases expected with
  | nil => exact relation
  | cons first rest =>
      cases relation with
      | cons head tail =>
          exact .cons (ofAddConstraint _ _ _ head) tail

private theorem ofAddLast
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation :
      ListMatches (ExpectedToken.addLast constraint expected) actual) :
    ListMatches expected actual := by
  induction expected generalizing actual with
  | nil => exact relation
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          cases relation with
          | cons head tail =>
              exact .cons (ofAddConstraint _ _ _ head) tail
      | cons second tail =>
          cases relation with
          | cons head restRelation =>
              exact .cons head (inductionHypothesis restRelation)

private theorem firstSatisfiesOfAddFirst
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    {actual : List Token}
    (expectedNonempty : expected ≠ [])
    (relation :
      ListMatches (ExpectedToken.addFirst constraint expected) actual) :
    FirstSatisfies constraint actual := by
  cases expected with
  | nil => contradiction
  | cons first rest =>
      cases relation with
      | cons head _ =>
          exact head.2 constraint (by simp)

private theorem addLast_ne_nil
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    (expectedNonempty : expected ≠ []) :
    ExpectedToken.addLast constraint expected ≠ [] := by
  cases expected with
  | nil => contradiction
  | cons head tail =>
      cases tail <;> simp [ExpectedToken.addLast]

private theorem lastSatisfiesOfAddLast
    (constraint : SpanConstraint) :
    ∀ (expected : List ExpectedToken) (actual : List Token),
      expected ≠ [] →
      ListMatches (ExpectedToken.addLast constraint expected) actual →
      LastSatisfies constraint actual
  | [], _, expectedNonempty, _ => (expectedNonempty rfl).elim
  | [_], [], _, relation => by cases relation
  | [_], [_], _, relation => by
      cases relation with
      | cons head tail =>
          exact head.2 constraint (by simp)
  | [_], _ :: _ :: _, _, relation => by
      cases relation with
      | cons _ tail => cases tail
  | _ :: _ :: _, [], _, relation => by cases relation
  | first :: second :: rest, [_], _, relation => by
      cases relation with
      | cons _ tail =>
          have lengthEq := tail.length_eq
          have lengthPositive :
              0 < (ExpectedToken.addLast constraint
                (second :: rest)).length :=
            List.length_pos_iff.mpr (addLast_ne_nil (by simp))
          simp only [List.length_nil] at lengthEq
          omega
  | first :: second :: rest, actual :: next :: tail, _, relation => by
      cases relation with
      | cons _ restRelation =>
          exact lastSatisfiesOfAddLast constraint (second :: rest)
            (next :: tail) (by simp) restRelation

private theorem addFirst_ne_nil
    {constraint : SpanConstraint}
    {expected : List ExpectedToken}
    (expectedNonempty : expected ≠ []) :
    ExpectedToken.addFirst constraint expected ≠ [] := by
  cases expected <;> simp_all [ExpectedToken.addFirst]

/--
Enclosure adds only the asserted first- and last-token span constraints.
This theorem is the public proof boundary for the private list transforms used
by `enclose`.
-/
theorem enclose
    {span : SourceSpan}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation : ListMatches expected actual)
    (starts : FirstSatisfies (.starts span) actual)
    (ends : LastSatisfies (.ends span) actual) :
    ListMatches (ExpectedToken.enclose span expected) actual := by
  exact addLast (addFirst relation starts) ends

/-- Remove the enclosure constraints while retaining pointwise matching. -/
theorem of_enclose
    {span : SourceSpan}
    {expected : List ExpectedToken}
    {actual : List Token}
    (relation :
      ListMatches (ExpectedToken.enclose span expected) actual) :
    ListMatches expected actual := by
  exact ofAddFirst (ofAddLast relation)

/-- A nonempty enclosed match satisfies its opening span constraint. -/
theorem starts_of_enclose
    {span : SourceSpan}
    {expected : List ExpectedToken}
    {actual : List Token}
    (expectedNonempty : expected ≠ [])
    (relation :
      ListMatches (ExpectedToken.enclose span expected) actual) :
    FirstSatisfies (.starts span) actual := by
  exact firstSatisfiesOfAddFirst expectedNonempty (ofAddLast relation)

/-- A nonempty enclosed match satisfies its closing span constraint. -/
theorem ends_of_enclose
    {span : SourceSpan}
    {expected : List ExpectedToken}
    {actual : List Token}
    (expectedNonempty : expected ≠ [])
    (relation :
      ListMatches (ExpectedToken.enclose span expected) actual) :
    LastSatisfies (.ends span) actual := by
  apply lastSatisfiesOfAddLast
  · exact addFirst_ne_nil (constraint := .starts span) expectedNonempty
  · exact relation

end ListMatches

end ExpectedToken

namespace TypeSyntax

def expectedTokens : TypeSyntax → List ExpectedToken
  | .unit span =>
      ExpectedToken.enclose span [
        .plain .leftParen,
        .plain .rightParen
      ]
  | .named name =>
      [.exact (.identifier name.value) name.span]

def GrammarValid : TypeSyntax → Prop
  | .unit _ => True
  | .named name => name.value = "bool" ∨ name.value = "word"

def grammarValid : TypeSyntax → Bool
  | .unit _ => true
  | .named name => name.value == "bool" || name.value == "word"

theorem grammarValid_eq_true_iff (type : TypeSyntax) :
    type.grammarValid = true ↔ type.GrammarValid := by
  cases type <;> simp [grammarValid, GrammarValid]

end TypeSyntax

namespace UnaryOp

def tokenKind : UnaryOp → TokenKind
  | .not => .bang

end UnaryOp

namespace BinaryOp

def tokenKind : BinaryOp → TokenKind
  | .mul => .star
  | .div => .slash
  | .mod => .percent
  | .add => .plus
  | .sub => .minus
  | .bitAnd => .ampersand
  | .bitXor => .caret
  | .bitOr => .pipe
  | .lt => .less
  | .gt => .greater
  | .le => .lessEqual
  | .ge => .greaterEqual
  | .eq => .equalEqual
  | .ne => .bangEqual

def precedence : BinaryOp → Nat
  | .eq | .ne => 1
  | .lt | .gt | .le | .ge => 2
  | .bitOr => 3
  | .bitXor => 4
  | .bitAnd => 5
  | .add | .sub => 6
  | .mul | .div | .mod => 7

def associativity : BinaryOp → Associativity
  | .eq | .ne | .lt | .gt | .le | .ge => .nonAssociative
  | _ => .left

end BinaryOp

namespace Expr

private def commaJoin
    (arguments : List (List ExpectedToken)) : List ExpectedToken :=
  match arguments with
  | [] => []
  | first :: rest =>
      first ++ rest.flatMap fun argument =>
        .plain .comma :: argument

def expectedTokens : Expr → List ExpectedToken
  | .unit span =>
      ExpectedToken.enclose span [
        .plain .leftParen,
        .plain .rightParen
      ]
  | .integer literal =>
      let kind :=
        match literal.base with
        | .decimal => TokenKind.decimal literal.digits
        | .hexadecimal => TokenKind.hexadecimal literal.digits
      [.exact kind literal.span]
  | .name identifier =>
      [.exact (.identifier identifier.value) identifier.span]
  | .group span inner =>
      ExpectedToken.enclose span
        (.plain .leftParen :: inner.expectedTokens ++
          [.plain .rightParen])
  | .call span callee arguments =>
      ExpectedToken.enclose span
        (.exact (.identifier callee.value) callee.span ::
          .plain .leftParen ::
          commaJoin (arguments.map expectedTokens) ++
          [.plain .rightParen])
  | .unary span operator operand =>
      ExpectedToken.enclose span
        (.exact operator.value.tokenKind operator.span ::
          operand.expectedTokens)
  | .binary span operator left right =>
      ExpectedToken.enclose span
        (left.expectedTokens ++
          .exact operator.value.tokenKind operator.span ::
          right.expectedTokens)
  | .ifThenElse span condition thenBranch elseBranch =>
      ExpectedToken.enclose span
        (.plain .keywordIf ::
          condition.expectedTokens ++
          .plain (.identifier "then") ::
          thenBranch.expectedTokens ++
          .plain .keywordElse ::
          elseBranch.expectedTokens)
termination_by expression => sizeOf expression

/-- Public empty-call equation hiding the private comma-joining helper. -/
theorem expectedTokens_call_nil
    (span : SourceSpan)
    (callee : Name) :
    expectedTokens (.call span callee []) =
      ExpectedToken.enclose span
        [
          .exact (.identifier callee.value) callee.span,
          .plain .leftParen,
          .plain .rightParen
        ] := by
  simp [expectedTokens, commaJoin]

/-- Public nonempty-call equation hiding the private comma-joining helper. -/
theorem expectedTokens_call_cons
    (span : SourceSpan)
    (callee : Name)
    (first : Expr)
    (rest : List Expr) :
    expectedTokens (.call span callee (first :: rest)) =
      ExpectedToken.enclose span
        (.exact (.identifier callee.value) callee.span ::
          .plain .leftParen ::
          first.expectedTokens ++
          rest.flatMap (fun argument =>
            .plain .comma :: argument.expectedTokens) ++
          [.plain .rightParen]) := by
  simp [expectedTokens, commaJoin, List.flatMap_map]

def outerPrecedence : Expr → Nat
  | .ifThenElse .. => 0
  | .binary _ operator _ _ => operator.value.precedence
  | .unary .. => 8
  | _ => 9

def allExpressions : Expr → List Expr
  | expression@(.unit _)
  | expression@(.integer _)
  | expression@(.name _) =>
      [expression]
  | expression@(.group _ inner) =>
      expression :: inner.allExpressions
  | expression@(.call _ _ arguments) =>
      expression :: arguments.flatMap allExpressions
  | expression@(.unary _ _ operand) =>
      expression :: operand.allExpressions
  | expression@(.binary _ _ left right) =>
      expression :: left.allExpressions ++ right.allExpressions
  | expression@(.ifThenElse _ condition thenBranch elseBranch) =>
      expression ::
        condition.allExpressions ++
        thenBranch.allExpressions ++
        elseBranch.allExpressions
termination_by expression => sizeOf expression

def LocallyGrammarValid : Expr → Prop
  | .unary _ _ operand =>
      8 ≤ operand.outerPrecedence
  | .binary _ operator left right =>
      match operator.value.associativity with
      | .left =>
          operator.value.precedence ≤ left.outerPrecedence ∧
            operator.value.precedence < right.outerPrecedence
      | .nonAssociative =>
          operator.value.precedence < left.outerPrecedence ∧
            operator.value.precedence < right.outerPrecedence
  | _ =>
      True

def locallyGrammarValid : Expr → Bool
  | .unary _ _ operand =>
      8 ≤ operand.outerPrecedence
  | .binary _ operator left right =>
      match operator.value.associativity with
      | .left =>
          operator.value.precedence ≤ left.outerPrecedence &&
            operator.value.precedence < right.outerPrecedence
      | .nonAssociative =>
          operator.value.precedence < left.outerPrecedence &&
            operator.value.precedence < right.outerPrecedence
  | _ =>
      true

theorem locallyGrammarValid_eq_true_iff (expression : Expr) :
    expression.locallyGrammarValid = true ↔
      expression.LocallyGrammarValid := by
  cases expression with
  | unit span => simp [locallyGrammarValid, LocallyGrammarValid]
  | integer literal => simp [locallyGrammarValid, LocallyGrammarValid]
  | name identifier => simp [locallyGrammarValid, LocallyGrammarValid]
  | group span inner => simp [locallyGrammarValid, LocallyGrammarValid]
  | call span callee arguments =>
      simp [locallyGrammarValid, LocallyGrammarValid]
  | unary span operator operand =>
      simp [locallyGrammarValid, LocallyGrammarValid]
  | binary span operator left right =>
      cases associativity : operator.value.associativity <;>
        simp [locallyGrammarValid, LocallyGrammarValid, associativity]
  | ifThenElse span condition thenBranch elseBranch =>
      simp [locallyGrammarValid, LocallyGrammarValid]

def GrammarValid (expression : Expr) : Prop :=
  ∀ subexpression ∈ expression.allExpressions,
    subexpression.LocallyGrammarValid

def grammarValid (expression : Expr) : Bool :=
  expression.allExpressions.all locallyGrammarValid

theorem grammarValid_eq_true_iff (expression : Expr) :
    expression.grammarValid = true ↔ expression.GrammarValid := by
  simp [grammarValid, GrammarValid, locallyGrammarValid_eq_true_iff]

end Expr

namespace LetStatement

def expectedTokens (statement : LetStatement) : List ExpectedToken :=
  ExpectedToken.enclose statement.span
    (.plain .keywordLet ::
      .exact (.identifier statement.name.value) statement.name.span ::
      .plain .colon ::
      statement.type.expectedTokens ++
      .plain .equal ::
      statement.value.expectedTokens ++
      [.plain .semicolon])

def GrammarValid (statement : LetStatement) : Prop :=
  statement.type.GrammarValid ∧ statement.value.GrammarValid

def grammarValid (statement : LetStatement) : Bool :=
  statement.type.grammarValid && statement.value.grammarValid

theorem grammarValid_eq_true_iff (statement : LetStatement) :
    statement.grammarValid = true ↔ statement.GrammarValid := by
  simp [grammarValid, GrammarValid, TypeSyntax.grammarValid_eq_true_iff,
    Expr.grammarValid_eq_true_iff]

end LetStatement

namespace ReturnStatement

def expectedTokens (statement : ReturnStatement) : List ExpectedToken :=
  ExpectedToken.enclose statement.span
    (.plain .keywordReturn ::
      statement.value.expectedTokens ++
      [.plain .semicolon])

def GrammarValid (statement : ReturnStatement) : Prop :=
  statement.value.GrammarValid

def grammarValid (statement : ReturnStatement) : Bool :=
  statement.value.grammarValid

theorem grammarValid_eq_true_iff (statement : ReturnStatement) :
    statement.grammarValid = true ↔ statement.GrammarValid :=
  Expr.grammarValid_eq_true_iff statement.value

end ReturnStatement

namespace FunctionDecl

def expectedTokens (declaration : FunctionDecl) : List ExpectedToken :=
  ExpectedToken.enclose declaration.span
    (.plain .keywordFunction ::
      .exact (.identifier declaration.name.value) declaration.name.span ::
      .plain .leftParen ::
      .plain .rightParen ::
      .plain .arrow ::
      declaration.returnType.expectedTokens ++
      .plain .leftBrace ::
      declaration.bindings.flatMap LetStatement.expectedTokens ++
      declaration.result.expectedTokens ++
      [.plain .rightBrace])

def GrammarValid (declaration : FunctionDecl) : Prop :=
  declaration.returnType.GrammarValid ∧
    (∀ binding ∈ declaration.bindings, binding.GrammarValid) ∧
    declaration.result.GrammarValid

def grammarValid (declaration : FunctionDecl) : Bool :=
  declaration.returnType.grammarValid &&
    declaration.bindings.all LetStatement.grammarValid &&
    declaration.result.grammarValid

theorem grammarValid_eq_true_iff (declaration : FunctionDecl) :
    declaration.grammarValid = true ↔ declaration.GrammarValid := by
  simp [grammarValid, GrammarValid, TypeSyntax.grammarValid_eq_true_iff,
    LetStatement.grammarValid_eq_true_iff,
    ReturnStatement.grammarValid_eq_true_iff, and_assoc]

end FunctionDecl

namespace ParsedFile

def expectedTokens (parsed : ParsedFile) : List ExpectedToken :=
  ExpectedToken.enclose parsed.span parsed.function.expectedTokens

def CorrespondsTo (parsed : ParsedFile) (lexed : Lexed) : Prop :=
  parsed.expectedTokens.length = lexed.tokens.length ∧
    (∀ pair ∈ parsed.expectedTokens.zip lexed.tokens,
      pair.1.Matches pair.2) ∧
    parsed.comments = lexed.comments

def correspondsTo (parsed : ParsedFile) (lexed : Lexed) : Bool :=
  decide (parsed.expectedTokens.length = lexed.tokens.length) &&
    ((parsed.expectedTokens.zip lexed.tokens).all fun pair =>
      pair.1.isMatch pair.2) &&
    decide (parsed.comments = lexed.comments)

theorem correspondsTo_eq_true_iff
    (parsed : ParsedFile)
    (lexed : Lexed) :
    parsed.correspondsTo lexed = true ↔ parsed.CorrespondsTo lexed := by
  simp [correspondsTo, CorrespondsTo, ExpectedToken.isMatch_eq_true_iff,
    and_assoc]

def GrammarValid (parsed : ParsedFile) : Prop :=
  parsed.function.GrammarValid

def grammarValid (parsed : ParsedFile) : Bool :=
  parsed.function.grammarValid

theorem grammarValid_eq_true_iff (parsed : ParsedFile) :
    parsed.grammarValid = true ↔ parsed.GrammarValid :=
  FunctionDecl.grammarValid_eq_true_iff parsed.function

def ConformsTo
    (parsed : ParsedFile)
    (file : SourceFile)
    (lexed : Lexed) : Prop :=
  parsed.ValidFor file ∧
    parsed.CorrespondsTo lexed ∧
    parsed.GrammarValid

def conformsTo
    (parsed : ParsedFile)
    (file : SourceFile)
    (lexed : Lexed) : Bool :=
  parsed.spansValidFor file &&
    parsed.correspondsTo lexed &&
    parsed.grammarValid

theorem conformsTo_eq_true_iff
    (parsed : ParsedFile)
    (file : SourceFile)
    (lexed : Lexed) :
    parsed.conformsTo file lexed = true ↔
      parsed.ConformsTo file lexed := by
  simp [conformsTo, ConformsTo, ParsedFile.spansValidFor_eq_true_iff,
    correspondsTo_eq_true_iff, grammarValid_eq_true_iff, and_assoc]

end ParsedFile

end Solcore.Surface
