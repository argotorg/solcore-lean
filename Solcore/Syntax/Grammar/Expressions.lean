import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Grammar.Signatures
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties

/-!
Declarative grammar of expressions.

These are stated over abstract child relations, and `Grammar/TermLevels` ties the
recursion.
Main declarations: `ExpressionAtomOrdinaryParses`, `ExpressionAtomRejects`,
`ExpressionPostfixParses`, `ParenthesizedExpressionOrdinaryParses`,
`ArrayLiteralExpressionOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomRecoveryGrammar
/-!
Parser-independent ordinary outcomes of Core expression-atom recovery.

The outer recovery parser always consumes one token before this scan begins.
The scan then gives boundary detection priority over token consumption and
also records a missing carrier slot inside the active token window.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stop conditions of the boundary-prioritized atom recovery scan. -/
inductive ExpressionAtomRecoveryStops : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomRecoveryStops input input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      ExpressionAtomRecoveryStops input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      ExpressionAtomRecoveryStops input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      ExpressionAtomRecoveryStops input input
  | rightBracket {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBracket }) :
      ExpressionAtomRecoveryStops input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      ExpressionAtomRecoveryStops input input
  | question {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .question }) :
      ExpressionAtomRecoveryStops input input
  | colon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .colon }) :
      ExpressionAtomRecoveryStops input input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      ExpressionAtomRecoveryStops input input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      ExpressionAtomRecoveryStops input input
  | elseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .keyword .elseKw }) :
      ExpressionAtomRecoveryStops input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ExpressionAtomRecoveryStops input input

/-- Exact scan after recovery has consumed its mandatory first token. -/
inductive ExpressionAtomRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.Expr → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : ExpressionAtomRecoveryStops input input) :
      ExpressionAtomRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {expression : Syntax.Expr}
      (continues : ¬ ExpressionAtomRecoveryStops input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : ExpressionAtomRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } expression output) :
      ExpressionAtomRecoveryScanParses first last input expression output

/-- Ordinary success of `recoverAtom`, including its mandatory first token. -/
inductive ExpressionAtomRecoveryParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {expression : Syntax.Expr}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : ExpressionAtomRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } expression output) :
      ExpressionAtomRecoveryParses input expression output

/-- Exact non-consuming rejection when `recoverAtom` cannot consume first. -/
inductive ExpressionAtomRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      ExpressionAtomRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomPublicOutcomeGrammar
/-!
Parser-independent ordinary outcomes at the public Core atom rewind and
recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before public atom recovery. -/
inductive ExpressionAtomBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      ExpressionAtomBoundaryStops input
  | semicolon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .semicolon }) :
      ExpressionAtomBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      ExpressionAtomBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      ExpressionAtomBoundaryStops input
  | rightBracket {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBracket }) :
      ExpressionAtomBoundaryStops input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      ExpressionAtomBoundaryStops input
  | question {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .question }) :
      ExpressionAtomBoundaryStops input
  | colon {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .colon }) :
      ExpressionAtomBoundaryStops input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      ExpressionAtomBoundaryStops input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      ExpressionAtomBoundaryStops input
  | elseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .keyword .elseKw }) :
      ExpressionAtomBoundaryStops input

/-- A Core rejection retains its failed cursor while preserving the token
carrier and active window needed for the public cursor rewind. -/
def CoreAtomRejectsWithPreservedWindow
    (coreRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, coreRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Ordinary public atom success is a direct Core success or a recovery that
starts at the original cursor after a window-preserving Core rejection. -/
inductive ExpressionAtomOrdinaryParses
    (coreOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | core {input output : Remainder} {expression : Syntax.Expr}
      (parsed : coreOrdinary input expression output) :
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output
  | recovered {input output : Remainder} {expression : Syntax.Expr}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ ExpressionAtomBoundaryStops input)
      (recovered : ExpressionAtomRecoveryParses input expression output) :
      ExpressionAtomOrdinaryParses coreOrdinary coreRejects input expression
        output

/-- Exact public atom rejection after the Core failure is rewound. -/
inductive ExpressionAtomRejects
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (stops : ExpressionAtomBoundaryStops input) :
      ExpressionAtomRejects coreRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : CoreAtomRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ ExpressionAtomBoundaryStops input)
      (recoveryRejected : ExpressionAtomRecoveryRejects input rejected) :
      ExpressionAtomRejects coreRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreCollectionAtomGrammar
/-!
Parser-independent grammar for parenthesized and array Core expression atoms.

The parenthesized grammar records the parser's delimiter priorities and keeps
tuple elements in source order.  In particular, it mirrors `closeTuple`:
exactly one accumulated element is a group, even when followed by a comma.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Pure forward-order counterpart of the parser's `closeTuple` result. -/
def closeParenthesizedExpression (openingSpan closingSpan : SourceSpan)
    (elements : List Syntax.Expr) : Syntax.Expr :=
  let span := SourceSpan.cover openingSpan closingSpan
  match elements with
  | [only] => { span, value := .group only }
  | _ => { span, value := .tuple { span, elements } }

/--
Exact continuation after the first comma of a parenthesized expression.
The returned elements are in source order and exclude those parsed earlier.
-/
inductive ParenthesizedTupleTailParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → List Syntax.Expr → SourceSpan → Remainder → Prop where
  | trailing {input afterComma output : Remainder}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input [] closingSpan output
  | final {input afterComma afterElement output : Remainder}
      {element : Syntax.Expr} (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input [element] closingSpan
        output
  | next {input afterComma afterElement output : Remainder}
      {element : Syntax.Expr} {elements : List Syntax.Expr}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedTupleTailParses nestedParses afterElement elements
        closingSpan output) :
      ParenthesizedTupleTailParses nestedParses input (element :: elements)
        closingSpan output

/-- Exact prioritized grammar of a grouped or tuple expression atom. -/
inductive ParenthesizedExpressionParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | empty {input afterOpening output : Remainder}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan []) output
  | group {input afterOpening afterElement output : Remainder}
      {element : Syntax.Expr} (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterOpening element afterElement)
      (progress : afterOpening.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterElement
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan [element])
        output
  | tuple {input afterOpening afterFirst output : Remainder}
      {first : Syntax.Expr} {rest : List Syntax.Expr}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedParses afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedTupleTailParses nestedParses afterFirst rest
        closingSpan output) :
      ParenthesizedExpressionParses nestedParses input
        (closeParenthesizedExpression openingSpan closingSpan (first :: rest))
        output

/-- Exact no-trailing-comma grammar of an array expression atom. -/
inductive ArrayLiteralExpressionParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder}
      {values : DelimitedList Syntax.Expr}
      (valuesParsed : NoTrailingDelimitedListParses .leftBracket .rightBracket
        nestedParses input values output) :
      ArrayLiteralExpressionParses nestedParses input {
        span := values.span
        value := .array values
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreParenthesizedOutcomeGrammar
/-!
Parser-independent ordinary outcomes for the guarded Core parenthesized atom.

The rejection relations follow the bespoke `tupleTail` loop rather than a
generic list abstraction, so the single-element group/tuple distinction and
the parser's comma/closing priorities remain explicit.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing exact parenthesized grammar admits arbitrary ordinary nested
expression outcomes as-is. -/
abbrev ParenthesizedExpressionOrdinaryParses :=
  ParenthesizedExpressionParses

/-- Exact ordinary rejection after a comma selected the tuple-tail loop. -/
inductive ParenthesizedTupleTailRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | elementRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementRejected : nestedRejects afterComma rejected) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterComma afterElement : Remainder}
      {element : Syntax.Expr} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsentAfterComma : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (commaAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt afterElement.tokens
        afterElement.endIndex afterElement.cursor (.symbol .rightParen)) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        afterElement
  | laterRejected {input afterComma afterElement rejected : Remainder}
      {element : Syntax.Expr} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects afterElement rejected) :
      ParenthesizedTupleTailRejects nestedOrdinary nestedRejects input
        rejected

/-- Exact rejection after the atom dispatcher selected a present `(`. -/
inductive ParenthesizedExpressionRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | firstRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstRejected : nestedRejects afterOpening rejected) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterOpening afterFirst : Remainder}
      {first : Syntax.Expr} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsentAfterOpening : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (commaAbsent : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
        afterFirst.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt afterFirst.tokens afterFirst.endIndex
        afterFirst.cursor (.symbol .rightParen)) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        afterFirst
  | tailRejected {input afterOpening afterFirst rejected : Remainder}
      {first : Syntax.Expr} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : ParenthesizedTupleTailRejects nestedOrdinary
        nestedRejects afterFirst rejected) :
      ParenthesizedExpressionRejects nestedOrdinary nestedRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreArrayLiteralOutcomeGrammar
/-!
Parser-independent ordinary outcomes for the guarded Core array-literal
branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The exact array grammar already admits arbitrary ordinary nested element
outcomes. -/
abbrev ArrayLiteralExpressionOrdinaryParses :=
  ArrayLiteralExpressionParses

/-- Exact rejection after the atom dispatcher has selected a present `[`.
The opening evidence excludes the generic delimiter-missing branch while the
delimited trace retains first-element and later-tail priority exactly. -/
inductive ArrayLiteralExpressionRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftBracket
      })
      (valuesRejected : DelimitedListRejects .leftBracket .rightBracket true
        false nestedOrdinary nestedRejects input rejected) :
      ArrayLiteralExpressionRejects nestedOrdinary nestedRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLayerGrammar
/-!
Parser-independent grammar combinators for canonical Core expression layers.

The judgments in this module are parameterized by their recursive operand
grammar.  They expose maximal unary and binary consumption, exact precedence
and associativity, and right-associated conditional construction without
mentioning parser fuel.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token spelling of one prefix unary operator. -/
def UnaryOperatorParses (input : Remainder)
    (operator : Located UnaryOp) (output : Remainder) : Prop :=
  ExactTokenParses (.symbol operator.value.symbol) input operator.span output

/-- Neither canonical prefix unary operator occurs at this cursor. -/
def UnaryOperatorAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .bang) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .tilde)

/-- Maximal source-order sequence of prefix unary operators. -/
inductive UnaryOperatorsParses :
    Remainder → List (Located UnaryOp) → Remainder → Prop where
  | done {input : Remainder} (absent : UnaryOperatorAbsentAt input) :
      UnaryOperatorsParses input [] input
  | next {input afterOperator output : Remainder}
      {operator : Located UnaryOp} {operators : List (Located UnaryOp)}
      (operatorParsed : UnaryOperatorParses input operator afterOperator)
      (tail : UnaryOperatorsParses afterOperator operators output) :
      UnaryOperatorsParses input (operator :: operators) output

/-- Pure source-preserving construction used by the unary layer. -/
def applyUnaryOperators
    (operators : List (Located UnaryOp)) (base : Expr) : Expr :=
  operators.foldr (fun operator operand => {
    span := SourceSpan.cover operator.span operand.span
    value := .unary operator operand
  }) base

/-- Prefix-unary grammar over an already complete postfix grammar. -/
def ExpressionUnaryParses
    (postfixParses : Remainder → Expr → Remainder → Prop)
    (input : Remainder) (expression : Expr) (output : Remainder) : Prop :=
  ∃ operators afterOperators base,
    UnaryOperatorsParses input operators afterOperators ∧
    postfixParses afterOperators base output ∧
    expression = applyUnaryOperators operators base

/-- Exact binary-operator tokens at one precedence: one token, or the two
adjacent tokens of `<<` and `>>`, as `BinaryOp.at?` decodes them. -/
def BinaryOperatorAtPrecedenceParses (precedence : Nat)
    (input : Remainder) (operator : Located BinaryOp)
    (output : Remainder) : Prop :=
  operator.value.precedence = precedence ∧
    BinaryOp.at? input.tokens input.endIndex input.cursor = some operator ∧
    output = { input with cursor := input.cursor + operator.value.tokenCount }

/-- No binary operator of one precedence occurs at the current cursor. -/
def BinaryOperatorAtPrecedenceAbsentAt
    (precedence : Nat) (input : Remainder) : Prop :=
  ¬ ∃ operator : Located BinaryOp, operator.value.precedence = precedence ∧
    BinaryOp.at? input.tokens input.endIndex input.cursor = some operator

namespace BinaryOperatorAtPrecedenceParses

/-- The decoded operator fixes its span, its value and the remainder. -/
theorem unique {precedence : Nat} {input leftOutput rightOutput : Remainder}
    {left right : Located BinaryOp}
    (leftParsed : BinaryOperatorAtPrecedenceParses precedence input left leftOutput)
    (rightParsed : BinaryOperatorAtPrecedenceParses precedence input right rightOutput) :
    left = right ∧ leftOutput = rightOutput := by
  have same : left = right := Option.some.inj (leftParsed.2.1.symm.trans rightParsed.2.1)
  subst same
  exact ⟨rfl, leftParsed.2.2.trans rightParsed.2.2.symm⟩

/-- A decoded operator excludes absence at its precedence. -/
theorem not_absent {precedence : Nat} {input output : Remainder}
    {operator : Located BinaryOp}
    (parsed : BinaryOperatorAtPrecedenceParses precedence input operator output)
    (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input) : False :=
  absent ⟨operator, parsed.1, parsed.2.1⟩

end BinaryOperatorAtPrecedenceParses

/-- Pure source-preserving construction used by every binary layer. -/
def binaryNode (left : Expr) (operator : Located BinaryOp)
    (right : Expr) : Expr := {
  span := SourceSpan.cover left.span right.span
  value := .binary left operator right
}

/-- Maximal left-associated tail at one binary precedence. -/
inductive LeftAssociativeTailParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) :
    Remainder → Expr → Expr → Remainder → Prop where
  | done {input : Remainder} {left : Expr}
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence input) :
      LeftAssociativeTailParses operandParses precedence input left left input
  | next {input afterOperator afterRight output : Remainder}
      {left right expression : Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightParsed : operandParses afterOperator right afterRight)
      (tail : LeftAssociativeTailParses operandParses precedence afterRight
        (binaryNode left operator right) expression output) :
      LeftAssociativeTailParses operandParses precedence input left expression
        output

/-- One complete maximal left-associated precedence layer. -/
def LeftAssociativeParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) (input : Remainder)
    (expression : Expr) (output : Remainder) : Prop :=
  ∃ left afterLeft,
    operandParses input left afterLeft ∧
    LeftAssociativeTailParses operandParses precedence afterLeft left
      expression output

/-- One complete non-associative binary precedence layer. -/
inductive NonAssociativeParses
    (operandParses : Remainder → Expr → Remainder → Prop)
    (precedence : Nat) : Remainder → Expr → Remainder → Prop where
  | plain {input output : Remainder} {left : Expr}
      (leftParsed : operandParses input left output)
      (absent : BinaryOperatorAtPrecedenceAbsentAt precedence output) :
      NonAssociativeParses operandParses precedence input left output
  | binary {input afterLeft afterOperator output : Remainder}
      {left right : Expr} {operator : Located BinaryOp}
      (leftParsed : operandParses input left afterLeft)
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence afterLeft
        operator afterOperator)
      (rightParsed : operandParses afterOperator right output) :
      NonAssociativeParses operandParses precedence input
        (binaryNode left operator right) output

/-- Maximal conditional suffix, constructed with right associativity. -/
inductive ConditionalTailParses
    (nestedParses alternativeParses :
      Remainder → Expr → Remainder → Prop) :
    Remainder → Expr → Expr → Remainder → Prop where
  | done {input : Remainder} {condition : Expr}
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .question)) :
      ConditionalTailParses nestedParses alternativeParses input condition
        condition input
  | next {input afterQuestion afterThen afterColon afterAlternative output :
        Remainder}
      {condition thenBranch nextCondition elseBranch : Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionToken : ExactTokenParses (.symbol .question) input questionSpan
        afterQuestion)
      (thenParsed : nestedParses afterQuestion thenBranch afterThen)
      (colonToken : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeParsed : alternativeParses afterColon nextCondition
        afterAlternative)
      (tail : ConditionalTailParses nestedParses alternativeParses
        afterAlternative nextCondition elseBranch output) :
      ConditionalTailParses nestedParses alternativeParses input condition {
        span := SourceSpan.cover condition.span elseBranch.span
        value := .conditional condition questionSpan thenBranch colonSpan
          elseBranch
      } output

/-- One complete maximal right-associated conditional layer. -/
def ConditionalParses
    (nestedParses alternativeParses :
      Remainder → Expr → Remainder → Prop)
    (input : Remainder) (expression : Expr) (output : Remainder) : Prop :=
  ∃ condition afterCondition,
    alternativeParses input condition afterCondition ∧
    ConditionalTailParses nestedParses alternativeParses afterCondition
      condition expression output

/--
Exact composition of every Core expression precedence layer over a supplied
postfix grammar.  Recursive conditional branches use `nestedParses`.
-/
def ExpressionLayerParses
    (nestedParses postfixParses : Remainder → Expr → Remainder → Prop) :
    Remainder → Expr → Remainder → Prop :=
  let unary := ExpressionUnaryParses postfixParses
  let multiply := LeftAssociativeParses unary 9
  let add := LeftAssociativeParses multiply 8
  let shift := LeftAssociativeParses add 7
  let bitAnd := LeftAssociativeParses shift 6
  let bitXor := LeftAssociativeParses bitAnd 5
  let bitOr := LeftAssociativeParses bitXor 4
  let relational := NonAssociativeParses bitOr 3
  let equality := NonAssociativeParses relational 2
  let logicalAnd := LeftAssociativeParses equality 1
  let logicalOr := LeftAssociativeParses logicalAnd 0
  ConditionalParses nestedParses logicalOr

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLayerOutcomeGrammar
/-!
Parser-independent ordinary successes and exact rejection traces for the
generic Core expression operator layers above a supplied postfix outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary unary-layer success is the existing maximal unary grammar. -/
abbrev ExpressionUnaryOrdinaryParses := ExpressionUnaryParses

/-- A unary layer rejects exactly when its postfix operand rejects after the
maximal prefix sequence. -/
inductive ExpressionUnaryRejects
    (postfixRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | postfixRejected {input afterOperators rejected : Remainder}
      {operators : List (Located UnaryOp)}
      (operatorsParsed : UnaryOperatorsParses input operators afterOperators)
      (postfixRejected : postfixRejects afterOperators rejected) :
      ExpressionUnaryRejects postfixRejects input rejected

/-- Ordinary left-associative success is the existing maximal grammar. -/
abbrev LeftAssociativeOrdinaryParses := LeftAssociativeParses

/-- Exact rejection while extending one left-associated precedence tail. -/
inductive LeftAssociativeTailRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | rightRejected {input afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightRejected : operandRejects afterOperator rejected) :
      LeftAssociativeTailRejects operandOrdinary operandRejects precedence
        input left rejected
  | laterRejected
      {input afterOperator afterRight rejected : Remainder}
      {left right : Syntax.Expr} {operator : Located BinaryOp}
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence input
        operator afterOperator)
      (rightParsed : operandOrdinary afterOperator right afterRight)
      (tailRejected : LeftAssociativeTailRejects operandOrdinary
        operandRejects precedence afterRight (binaryNode left operator right)
          rejected) :
      LeftAssociativeTailRejects operandOrdinary operandRejects precedence
        input left rejected

/-- Exact rejection of one complete left-associative precedence layer. -/
inductive LeftAssociativeRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : operandRejects input rejected) :
      LeftAssociativeRejects operandOrdinary operandRejects precedence input
        rejected
  | tailRejected {input afterLeft rejected : Remainder}
      {left : Syntax.Expr}
      (leftParsed : operandOrdinary input left afterLeft)
      (tailRejected : LeftAssociativeTailRejects operandOrdinary
        operandRejects precedence afterLeft left rejected) :
      LeftAssociativeRejects operandOrdinary operandRejects precedence input
        rejected

/-- Ordinary non-associative success is the existing maximal grammar. -/
abbrev NonAssociativeOrdinaryParses := NonAssociativeParses

/-- Exact rejection of one non-associative precedence layer. -/
inductive NonAssociativeRejects
    (operandOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (operandRejects : Remainder → Remainder → Prop)
    (precedence : Nat) : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : operandRejects input rejected) :
      NonAssociativeRejects operandOrdinary operandRejects precedence input
        rejected
  | rightRejected
      {input afterLeft afterOperator rejected : Remainder}
      {left : Syntax.Expr} {operator : Located BinaryOp}
      (leftParsed : operandOrdinary input left afterLeft)
      (operatorParsed : BinaryOperatorAtPrecedenceParses precedence afterLeft
        operator afterOperator)
      (rightRejected : operandRejects afterOperator rejected) :
      NonAssociativeRejects operandOrdinary operandRejects precedence input
        rejected

/-- Ordinary conditional success is the existing right-associated grammar. -/
abbrev ConditionalOrdinaryParses := ConditionalParses

/-- Exact rejection while consuming a conditional suffix. -/
inductive ConditionalTailRejects
    (nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects alternativeRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | thenRejected {input afterQuestion rejected : Remainder}
      {condition : Syntax.Expr} (questionSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenRejected : nestedRejects afterQuestion rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected
  | colonMissing {input afterQuestion afterThen : Remainder}
      {condition thenBranch : Syntax.Expr} (questionSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonAbsent : TokenKindAbsentAt afterThen.tokens afterThen.endIndex
        afterThen.cursor (.symbol .colon)) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition afterThen
  | alternativeRejected
      {input afterQuestion afterThen afterColon rejected : Remainder}
      {condition thenBranch : Syntax.Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonParsed : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeRejected : alternativeRejects afterColon rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected
  | laterRejected
      {input afterQuestion afterThen afterColon afterAlternative rejected :
        Remainder}
      {condition thenBranch nextCondition : Syntax.Expr}
      (questionSpan colonSpan : SourceSpan)
      (questionParsed : ExactTokenParses (.symbol .question) input
        questionSpan afterQuestion)
      (thenParsed : nestedOrdinary afterQuestion thenBranch afterThen)
      (colonParsed : ExactTokenParses (.symbol .colon) afterThen colonSpan
        afterColon)
      (alternativeParsed : alternativeOrdinary afterColon nextCondition
        afterAlternative)
      (tailRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects afterAlternative nextCondition
          rejected) :
      ConditionalTailRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input condition rejected

/-- Exact rejection of one complete conditional layer. -/
inductive ConditionalRejects
    (nestedOrdinary alternativeOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects alternativeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | conditionRejected {input rejected : Remainder}
      (conditionRejected : alternativeRejects input rejected) :
      ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input rejected
  | tailRejected {input afterCondition rejected : Remainder}
      {condition : Syntax.Expr}
      (conditionParsed : alternativeOrdinary input condition afterCondition)
      (tailRejected : ConditionalTailRejects nestedOrdinary alternativeOrdinary
        nestedRejects alternativeRejects afterCondition condition rejected) :
      ConditionalRejects nestedOrdinary alternativeOrdinary nestedRejects
        alternativeRejects input rejected

/-- Ordinary success of the complete operator stack. -/
abbrev ExpressionLayerOrdinaryParses := ExpressionLayerParses

/-- Exact rejection of the complete unary, binary, and conditional stack. -/
def ExpressionLayerRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (postfixOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (postfixRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop :=
  let unary := ExpressionUnaryOrdinaryParses postfixOrdinary
  let unaryRejects := ExpressionUnaryRejects postfixRejects
  let multiply := LeftAssociativeOrdinaryParses unary 9
  let multiplyRejects := LeftAssociativeRejects unary unaryRejects 9
  let add := LeftAssociativeOrdinaryParses multiply 8
  let addRejects := LeftAssociativeRejects multiply multiplyRejects 8
  let shift := LeftAssociativeOrdinaryParses add 7
  let bitAnd := LeftAssociativeOrdinaryParses shift 6
  let shiftRejects := LeftAssociativeRejects add addRejects 7
  let bitAndRejects := LeftAssociativeRejects shift shiftRejects 6
  let bitXor := LeftAssociativeOrdinaryParses bitAnd 5
  let bitXorRejects := LeftAssociativeRejects bitAnd bitAndRejects 5
  let bitOr := LeftAssociativeOrdinaryParses bitXor 4
  let bitOrRejects := LeftAssociativeRejects bitXor bitXorRejects 4
  let relational := NonAssociativeOrdinaryParses bitOr 3
  let relationalRejects := NonAssociativeRejects bitOr bitOrRejects 3
  let equality := NonAssociativeOrdinaryParses relational 2
  let equalityRejects := NonAssociativeRejects relational relationalRejects 2
  let logicalAnd := LeftAssociativeOrdinaryParses equality 1
  let logicalAndRejects := LeftAssociativeRejects equality equalityRejects 1
  let logicalOr := LeftAssociativeOrdinaryParses logicalAnd 0
  let logicalOrRejects := LeftAssociativeRejects logicalAnd logicalAndRejects 0
  ConditionalRejects nestedOrdinary logicalOr nestedRejects logicalOrRejects

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaGrammar
/-!
Parser-independent diagnostic-free grammar for Core lambda parameters and
lambda-expression type suffixes.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Type shapes that do not trigger the parameter-specific comptime warning. -/
def ParameterTypeAllowed (type : Syntax.TypeExpr) : Prop :=
  match type.value with
  | .comptime .. => False
  | _ => True

/-- The contextual `comptime` marker followed by an identifier starts here. -/
def ComptimeLambdaParameterStartsAt (input : Remainder) : Prop :=
  ∃ markerSpan nameSpan spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.comptime.spelling
    } ∧
    TokenAt input.tokens input.endIndex (input.cursor + 1) {
      span := nameSpan
      value := .identifier spelling
    }

/-- Exact inferred-or-typed suffix of an ordinary lambda parameter. -/
inductive OrdinaryLambdaParameterTailParses (name : Syntax.Identifier) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | inferred {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OrdinaryLambdaParameterTailParses name input {
        span := name.span
        value := .inferred name
      } input
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonToken : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output)
      (typeAllowed : ParameterTypeAllowed type) :
      OrdinaryLambdaParameterTailParses name input {
        span := SourceSpan.cover name.span type.span
        value := .typed none name type
      } output

/-- Exact diagnostic-free ordinary lambda parameter grammar. -/
inductive OrdinaryLambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.LambdaParameter}
      (nameParsed : IdentifierParses input name afterName)
      (notComptimeName :
        name.value ≠ ContextualKeyword.comptime.spelling)
      (tail : OrdinaryLambdaParameterTailParses name afterName parameter
        output) :
      OrdinaryLambdaParameterParses input parameter output

/-- Exact diagnostic-free contextual-comptime lambda parameter grammar. -/
inductive ComptimeLambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterMarker afterName afterColon output : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (markerSpan colonSpan : SourceSpan)
      (markerToken : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonToken : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : TypeExprParses afterColon type output)
      (typeAllowed : ParameterTypeAllowed type) :
      ComptimeLambdaParameterParses input {
        span := SourceSpan.cover markerSpan type.span
        value := .typed (some markerSpan) name type
      } output

/-- Exact ordered diagnostic-free grammar of one lambda parameter. -/
inductive LambdaParameterParses :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | comptime {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (parsed : ComptimeLambdaParameterParses input parameter output) :
      LambdaParameterParses input parameter output
  | ordinary {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (parsed : OrdinaryLambdaParameterParses input parameter output) :
      LambdaParameterParses input parameter output

/-- Exact optional `-> Type` suffix of a lambda expression. -/
inductive OptionalLambdaReturnTypeParses :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      OptionalLambdaReturnTypeParses input none input
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      (arrowSpan : SourceSpan)
      (arrowToken : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeParsed : TypeExprParses afterArrow type output) :
      OptionalLambdaReturnTypeParses input (some type) output

/-- Exact lambda expression grammar over a supplied Core block judgment. -/
inductive LambdaExpressionParses
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker afterParameters afterReturn output : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerToken : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses
        .leftParen .rightParen LambdaParameterParses afterMarker parameters
          afterParameters)
      (returnTypeParsed : OptionalLambdaReturnTypeParses afterParameters
        returnType afterReturn)
      (bodyParsed : blockParses afterReturn body output) :
      LambdaExpressionParses blockParses input {
        span := SourceSpan.cover markerSpan body.span
        value := .lambda markerSpan parameters returnType body
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionLambdaOutcomeGrammar
/-!
Parser-independent ordinary outcomes for the guarded Core lambda-expression
branch.  Subordinate parameter, type, and block outcomes are supplied by the
surrounding recursive layer, so diagnosed successes remain explicit there.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary optional `-> Type` success over a supplied type relation. -/
inductive OptionalLambdaReturnTypeOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Option Syntax.TypeExpr → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input none input
  | present {input afterArrow output : Remainder} {type : Syntax.TypeExpr}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeParsed : typeOrdinary afterArrow type output) :
      OptionalLambdaReturnTypeOrdinaryParses typeOrdinary input (some type)
        output

/-- Exact rejection after the optional-return parser commits to a present
arrow. -/
inductive OptionalLambdaReturnTypeRejects
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (typeRejected : typeRejects afterArrow rejected) :
      OptionalLambdaReturnTypeRejects typeOrdinary typeRejects input rejected

/-- Ordinary guarded lambda success over supplied parameter, return-type,
and body relations. -/
inductive LambdaExpressionOrdinaryParses
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker afterParameters afterReturn output : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} {body : Syntax.Block}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
        afterParameters returnType afterReturn)
      (bodyParsed : blockOrdinary afterReturn body output) :
      LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary input {
          span := SourceSpan.cover markerSpan body.span
          value := .lambda markerSpan parameters returnType body
        } output

/-- Exact rejection within the guarded lambda branch, ordered by parameters,
optional return type, then body.  Marker absence belongs to the enclosing
atom dispatcher's failed lambda guard. -/
inductive LambdaExpressionRejects
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (parameterRejects : Remainder → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | parametersRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersRejected : DelimitedListRejects .leftParen .rightParen true
        true parameterOrdinary parameterRejects afterMarker rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected
  | returnTypeRejected
      {input afterMarker afterParameters rejected : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeRejected : OptionalLambdaReturnTypeRejects typeOrdinary
        typeRejects afterParameters rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected
  | bodyRejected
      {input afterMarker afterParameters afterReturn rejected : Remainder}
      {parameters : DelimitedList Syntax.LambdaParameter}
      {returnType : Option Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .lamKw) input markerSpan
        afterMarker)
      (parametersParsed : TrailingDelimitedListParses .leftParen .rightParen
        parameterOrdinary afterMarker parameters afterParameters)
      (returnTypeParsed : OptionalLambdaReturnTypeOrdinaryParses typeOrdinary
        afterParameters returnType afterReturn)
      (bodyRejected : blockRejects afterReturn rejected) :
      LambdaExpressionRejects parameterOrdinary parameterRejects typeOrdinary
        typeRejects blockRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixGrammar
/-!
Parser-independent maximal postfix grammar for Core expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- None of the three canonical postfix suffixes begins at this cursor. -/
def PostfixSuffixAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftBracket) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.symbol .leftParen) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot)

/-- Maximal sequence of index, call, and field suffixes. -/
inductive PostfixTailParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Syntax.Expr → Remainder → Prop where
  | done {input : Remainder} {base : Syntax.Expr}
      (absent : PostfixSuffixAbsentAt input) :
      PostfixTailParses nestedParses input base base input
  | index {input afterOpening afterIndex afterClosing output : Remainder}
      {base index expression : Syntax.Expr}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedParses afterOpening index afterIndex)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex
        closingSpan afterClosing)
      (tail : PostfixTailParses nestedParses afterClosing {
        span := SourceSpan.cover base.span closingSpan
        value := .index base (SourceSpan.cover openingSpan closingSpan) index
      } expression output) :
      PostfixTailParses nestedParses input base expression output
  | call {input afterArguments output : Remainder}
      {base expression : Syntax.Expr}
      {arguments : DelimitedList Syntax.Expr}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListParses
        .leftParen .rightParen nestedParses input arguments afterArguments)
      (tail : PostfixTailParses nestedParses afterArguments {
        span := SourceSpan.cover base.span arguments.span
        value := .call base arguments
      } expression output) :
      PostfixTailParses nestedParses input base expression output
  | field {input afterDot afterName output : Remainder}
      {base expression : Syntax.Expr} {name : Syntax.Identifier}
      (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierParses afterDot name afterName)
      (tail : PostfixTailParses nestedParses afterName {
        span := SourceSpan.cover base.span name.span
        value := .field base dotSpan name
      } expression output) :
      PostfixTailParses nestedParses input base expression output

/-- One atom followed by its complete maximal postfix suffix sequence. -/
def ExpressionPostfixParses
    (atomParses nestedParses :
      Remainder → Syntax.Expr → Remainder → Prop)
    (input : Remainder) (expression : Syntax.Expr)
    (output : Remainder) : Prop :=
  ∃ base afterAtom,
    atomParses input base afterAtom ∧
    PostfixTailParses nestedParses afterAtom base expression output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionStepGrammar
/-!
Parser-independent composition of one complete Core expression recursion
step: atom, maximal postfixes, unary operators, binary precedence, and the
right-associative conditional suffix.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One complete Core expression layer over supplied atom and recursive
expression judgments. -/
def CoreExpressionStepParses
    (atomParses nestedParses :
      Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop :=
  ExpressionLayerParses nestedParses
    (ExpressionPostfixParses atomParses nestedParses)

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLiteralGrammar
/-!
Parser-independent leaf grammar for Core literals and expression names.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of one literal admitted by Core expressions and patterns. -/
inductive CoreLiteralParses :
    Remainder → Syntax.CoreLiteral → Remainder → Prop where
  | decimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .decimalLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .decimal spelling
      } { input with cursor := input.cursor + 1 }
  | hexadecimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .hexadecimalLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .hexadecimal spelling
      } { input with cursor := input.cursor + 1 }
  | string {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .stringLiteral spelling
      }) :
      CoreLiteralParses input {
        span
        value := .string spelling
      } { input with cursor := input.cursor + 1 }

/-- Exact grammar of the identifier-shaped Boolean builtin values. -/
inductive BooleanIdentifierParses :
    Remainder → Syntax.Identifier → Remainder → Prop where
  | trueKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .trueKw
      }) :
      BooleanIdentifierParses input {
        span
        value := "true"
      } { input with cursor := input.cursor + 1 }
  | falseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .falseKw
      }) :
      BooleanIdentifierParses input {
        span
        value := "false"
      } { input with cursor := input.cursor + 1 }

/--
Exact ordered grammar of an expression name.

Boolean keywords have priority.  The ordinary-identifier branch therefore
records that neither Boolean keyword occurs at the input cursor.
-/
inductive ExpressionNameParses :
    Remainder → Syntax.Identifier → Remainder → Prop where
  | boolean {input output : Remainder} {name : Syntax.Identifier}
      (parsed : BooleanIdentifierParses input name output) :
      ExpressionNameParses input name output
  | identifier {input output : Remainder} {name : Syntax.Identifier}
      (trueAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .trueKw))
      (falseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .falseKw))
      (parsed : IdentifierParses input name output) :
      ExpressionNameParses input name output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
/-!
Parser-independent grammar for the literal, identifier, and proxy Core
expression leaves.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of a literal expression leaf. -/
inductive LiteralExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder} {literal : Syntax.CoreLiteral}
      (literalParsed : CoreLiteralParses input literal output) :
      LiteralExpressionParses input {
        span := literal.span
        value := .literal literal
      } output

/-- Exact grammar of an identifier expression leaf, including Boolean names. -/
inductive IdentifierExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (nameParsed : ExpressionNameParses input name output) :
      IdentifierExpressionParses input {
        span := name.span
        value := .identifier name
      } output

/-- Exact grammar of an `@`-prefixed proxy expression leaf. -/
inductive ProxyExpressionParses :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {type : Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at)
        input markerSpan afterMarker)
      (typeParsed : TypeExprParses afterMarker type output) :
      ProxyExpressionParses input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output

/--
Prioritized optional argument list of a leading-dot constructor.  A present
opening parenthesis commits to the no-trailing delimited branch; absence is
recorded only when that opening token is not current.
-/
inductive OptionalDotConstructorArgumentsParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Option (DelimitedList Syntax.Expr) → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalDotConstructorArgumentsParses nestedParses input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.Expr}
      (parsed : NoTrailingDelimitedListParses .leftParen .rightParen
        nestedParses input arguments output) :
      OptionalDotConstructorArgumentsParses nestedParses input
        (some arguments) output

/--
Exact leading-dot constructor grammar, including Boolean-first name parsing,
optional-argument priority, retained marker, and outer range.
-/
inductive DotConstructorParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterDot afterName output : Remainder}
      {name : Syntax.Identifier}
      {arguments : Option (DelimitedList Syntax.Expr)}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameParses afterDot name afterName)
      (argumentsParsed : OptionalDotConstructorArgumentsParses nestedParses
        afterName arguments output) :
      DotConstructorParses nestedParses input {
        span := SourceSpan.cover dotSpan
          (arguments.map (fun values => values.span) |>.getD name.span)
        value := .dotConstructor dotSpan name arguments
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomDispatcherGrammar
/-!
Parser-independent ordered grammar for the seven Core expression-atom
branches.  Starter predicates depend only on the declarative token remainder;
the later constructors retain every earlier failed lookahead.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- A Core literal token starts at the current declarative cursor. -/
def CoreLiteralStartsAt (input : Remainder) : Prop :=
  (∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .decimalLiteral spelling
    }) ∨
  (∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .hexadecimalLiteral spelling
    }) ∨
  ∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .stringLiteral spelling
    }

/-- A Boolean builtin or ordinary identifier starts at the current cursor. -/
def ExpressionNameStartsAt (input : Remainder) : Prop :=
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }) ∨
  ∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier spelling
  }

/--
Exact priority grammar of `expressionAtomCore` over supplied recursive
expression and block judgments.
-/
inductive ExpressionAtomCoreParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | literal {input output : Remainder} {value : Syntax.Expr}
      (parsed : LiteralExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | identifier {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : IdentifierExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | dotConstructor {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (parsed : DotConstructorParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | proxy {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ProxyExpressionParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | parenthesized {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (parsed : ParenthesizedExpressionParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | array {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : ArrayLiteralExpressionParses nestedParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output
  | lambda {input output : Remainder} {value : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (parsed : LambdaExpressionParses blockParses input value output) :
      ExpressionAtomCoreParses nestedParses blockParses input value output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeExpressionAtomDispatchSelectionGrammar
/-! One ordered expression-atom selection, including the final fallback.
Every later branch retains all earlier failed lookaheads. Selection depends
only on the visible token remainder, not on any recursive parsing outcome. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

inductive ExpressionAtomDispatchBranch where
  | literal | name | dotConstructor | proxy | parenthesized | array | lambda | final
  deriving DecidableEq

inductive ExpressionAtomDispatchSelects (input : Remainder) : ExpressionAtomDispatchBranch → Prop where
  | literal (present : CoreLiteralStartsAt input) :
      ExpressionAtomDispatchSelects input .literal
  | name (literalAbsent : ¬ CoreLiteralStartsAt input)
      (present : ExpressionNameStartsAt input) :
      ExpressionAtomDispatchSelects input .name
  | dotConstructor (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .dot }) :
      ExpressionAtomDispatchSelects input .dotConstructor
  | proxy (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .at }) :
      ExpressionAtomDispatchSelects input .proxy
  | parenthesized (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftParen }) :
      ExpressionAtomDispatchSelects input .parenthesized
  | array (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .symbol .leftBracket }) :
      ExpressionAtomDispatchSelects input .array
  | lambda (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (present : ∃ span, TokenAt input.tokens input.endIndex input.cursor { span, value := .keyword .lamKw }) :
      ExpressionAtomDispatchSelects input .lambda
  | final (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.symbol .leftBracket))
      (lambdaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor (.keyword .lamKw)) :
      ExpressionAtomDispatchSelects input .final

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionGrammar
/-!
Parser-independent composition of one concrete Core expression layer over
supplied recursive expression and block judgments.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One concrete Core expression recursion step, from its ordered atom
dispatcher through maximal postfixes and every operator layer. -/
def CoreExpressionStepWithBlockParses
    (nestedParses : Remainder → Syntax.Expr → Remainder → Prop)
    (blockParses : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop :=
  CoreExpressionStepParses
    (ExpressionAtomCoreParses nestedParses blockParses) nestedParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomFinalRejectionGrammar
/-! Exact selection evidence for the final Core atom rejection branch. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Every earlier Core atom starter is absent, so the ordered dispatcher
selects its final non-consuming rejection. -/
inductive ExpressionAtomCoreFinalRejects : Remainder → Prop where
  | final {input : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (lambdaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .lamKw)) :
      ExpressionAtomCoreFinalRejects input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreProxyExpressionOutcomeGrammar
/-!
Parser-independent ordinary success and exact guarded rejection for a Core
proxy-expression leaf.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success of the guarded `@` branch over a supplied type
relation. -/
inductive ProxyExpressionOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {type : Syntax.TypeExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (typeParsed : typeOrdinary afterMarker type output) :
      ProxyExpressionOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan type.span
        value := .proxy markerSpan type
      } output

/-- Exact rejection inside the guarded proxy branch.  Marker absence belongs
to the enclosing atom dispatcher's failed `@` guard; once selected, only the
nested type parser can reject. -/
inductive ProxyExpressionRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | typeRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .at) input markerSpan
        afterMarker)
      (typeRejected : typeRejects afterMarker rejected) :
      ProxyExpressionRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLiteralOutcomeGrammar
/-!
Parser-independent ordinary outcomes for Core literal primitives and their
expression-leaf wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing exact literal grammar is also its ordinary-success grammar. -/
abbrev CoreLiteralOrdinaryParses := CoreLiteralParses

/-- None of the three Core literal token classes starts at this remainder. -/
def CoreLiteralAbsentAt (input : Remainder) : Prop :=
  (¬ ∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .decimalLiteral spelling
    }) ∧
  (¬ ∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .hexadecimalLiteral spelling
    }) ∧
  ¬ ∃ span spelling,
    TokenAt input.tokens input.endIndex input.cursor {
      span
      value := .stringLiteral spelling
    }

/-- Exact non-consuming rejection of the Core literal primitive. -/
inductive CoreLiteralRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (absent : CoreLiteralAbsentAt input) :
      CoreLiteralRejects input input

/-- The exact literal-expression grammar includes every ordinary success. -/
abbrev LiteralExpressionOrdinaryParses := LiteralExpressionParses

/-- Exact non-consuming rejection inherited by the literal-expression leaf. -/
inductive LiteralExpressionRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (absent : CoreLiteralAbsentAt input) :
      LiteralExpressionRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionNameOutcomeGrammar
/-! Ordinary success and exact rejection for a Boolean-first Core name. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing Boolean-first name grammar includes diagnosed identifiers. -/
abbrev ExpressionNameOrdinaryParses := ExpressionNameParses

/-- Neither Boolean keyword nor an ordinary identifier token starts here. -/
def ExpressionNameAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .trueKw) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .falseKw) ∧
    IdentifierAbsentAt input

/-- Exact non-consuming rejection of the Boolean-first expression-name
parser. -/
inductive ExpressionNameRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (absent : ExpressionNameAbsentAt input) :
      ExpressionNameRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionDotConstructorOutcomeGrammar
/-!
Parser-independent ordinary outcomes for the guarded leading-dot Core
constructor branch.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing optional-arguments grammar admits ordinary nested outcomes
as-is. -/
abbrev OptionalDotConstructorArgumentsOrdinaryParses :=
  OptionalDotConstructorArgumentsParses

/-- Exact rejection of a present leading-dot argument list.  Opening-token
evidence records that the optional parser selected, and committed to, its
parenthesized branch. -/
inductive OptionalDotConstructorArgumentsRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | present {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true
        false nestedOrdinary nestedRejects input rejected) :
      OptionalDotConstructorArgumentsRejects nestedOrdinary nestedRejects
        input rejected

/-- The existing exact leading-dot grammar admits ordinary nested outcomes
as-is. -/
abbrev DotConstructorOrdinaryParses := DotConstructorParses

/-- Exact rejection inside the guarded leading-dot constructor branch.  Dot
absence belongs to the enclosing atom dispatcher's failed guard. -/
inductive DotConstructorRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | nameRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : ExpressionNameRejects afterDot rejected) :
      DotConstructorRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected {input afterDot afterName rejected : Remainder}
      {name : Syntax.Identifier} (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : ExpressionNameOrdinaryParses afterDot name afterName)
      (argumentsRejected : OptionalDotConstructorArgumentsRejects
        nestedOrdinary nestedRejects afterName rejected) :
      DotConstructorRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreIdentifierExpressionOutcomeGrammar
/-! Ordinary success and exact rejection for a Core identifier expression. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing identifier-expression grammar already uses ordinary
Boolean-first expression names. -/
abbrev IdentifierExpressionOrdinaryParses := IdentifierExpressionParses

/-- Exact rejection inherited from the wrapped expression-name parser. -/
inductive IdentifierExpressionRejects : Remainder → Remainder → Prop where
  | nameRejected {input rejected : Remainder}
      (nameRejected : ExpressionNameRejects input rejected) :
      IdentifierExpressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionAtomCoreOutcomeGrammar
/-!
Parser-independent ordinary outcomes for the ordered `expressionAtomCore`
dispatcher.

Literal and name branches cannot reject under their positive executable
guards.  The remaining five selected branches retain the exact earlier guard
failures, and the final branch is the established non-consuming rejection.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success of the seven ordered Core atom branches. -/
inductive ExpressionAtomCoreOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (blockOrdinary : Remainder → Syntax.Block → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | literal {input output : Remainder} {expression : Syntax.Expr}
      (parsed : LiteralExpressionOrdinaryParses input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | identifier {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : IdentifierExpressionOrdinaryParses input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | dotConstructor {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (parsed : DotConstructorOrdinaryParses nestedOrdinary input expression
        output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | proxy {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ProxyExpressionOrdinaryParses typeOrdinary input expression
        output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | parenthesized {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (parsed : ParenthesizedExpressionOrdinaryParses nestedOrdinary input
        expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | array {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : ArrayLiteralExpressionOrdinaryParses nestedOrdinary input
        expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output
  | lambda {input output : Remainder} {expression : Syntax.Expr}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (parsed : LambdaExpressionOrdinaryParses parameterOrdinary typeOrdinary
        blockOrdinary input expression output) :
      ExpressionAtomCoreOrdinaryParses nestedOrdinary parameterOrdinary
        typeOrdinary blockOrdinary input expression output

/-- Exact ordinary rejection of the five fallible selected branches or the
final non-consuming branch. -/
inductive ExpressionAtomCoreRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop)
    (parameterOrdinary :
      Remainder → Syntax.LambdaParameter → Remainder → Prop)
    (parameterRejects : Remainder → Remainder → Prop)
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop)
    (blockRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | dotConstructor {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (branchRejected : DotConstructorRejects nestedOrdinary nestedRejects
        input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | proxy {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (branchRejected : ProxyExpressionRejects typeRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | parenthesized {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (branchRejected : ParenthesizedExpressionRejects nestedOrdinary
        nestedRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | array {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (branchRejected : ArrayLiteralExpressionRejects nestedOrdinary
        nestedRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | lambda {input rejected : Remainder}
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (nameAbsent : ¬ ExpressionNameStartsAt input)
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (atAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .at))
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (leftBracketAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBracket))
      (branchRejected : LambdaExpressionRejects parameterOrdinary
        parameterRejects typeOrdinary typeRejects blockRejects input rejected) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input rejected
  | final {input : Remainder}
      (branchRejected : ExpressionAtomCoreFinalRejects input) :
      ExpressionAtomCoreRejects nestedOrdinary nestedRejects
        parameterOrdinary parameterRejects typeOrdinary typeRejects
          blockRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterOutcomeGrammar
/-!
Parser-independent ordinary outcomes of the non-recovering lambda-parameter
core.  Unlike the older clean grammar, these relations retain successful
constraint diagnostics in the ordinary outcome.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Inferred or typed ordinary suffix, including a diagnosed comptime type. -/
inductive OrdinaryLambdaParameterTailOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (name : Syntax.Identifier) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | inferred {input : Remainder}
      (colonAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .colon)) :
      OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name input {
        span := name.span
        value := .inferred name
      } input
  | typed {input afterColon output : Remainder} {type : Syntax.TypeExpr}
      (colonSpan : SourceSpan)
      (colonParsed : ExactTokenParses (.symbol .colon) input colonSpan
        afterColon)
      (typeParsed : typeOrdinary afterColon type output) :
      OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name input {
        span := SourceSpan.cover name.span type.span
        value := .typed none name type
      } output

/-- Ordinary-name branch, including the diagnosed spelling `comptime`. -/
inductive OrdinaryLambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | parsed {input afterName output : Remainder}
      {name : Syntax.Identifier} {parameter : Syntax.LambdaParameter}
      (nameParsed : IdentifierParses input name afterName)
      (tail : OrdinaryLambdaParameterTailOrdinaryParses typeOrdinary name
        afterName parameter output) :
      OrdinaryLambdaParameterOrdinaryParses typeOrdinary input parameter output

/-- Contextual-comptime branch, including its diagnosed successful forms. -/
inductive ComptimeLambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | typed {input afterMarker afterName afterColon output : Remainder}
      {name : Syntax.Identifier} {type : Syntax.TypeExpr}
      (markerSpan colonSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeParsed : typeOrdinary afterColon type output) :
      ComptimeLambdaParameterOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan type.span
        value := .typed (some markerSpan) name type
      } output
  | typeMissing {input afterMarker afterName : Remainder}
      {name : Syntax.Identifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonAbsent : TokenKindAbsentAt afterName.tokens afterName.endIndex
        afterName.cursor (.symbol .colon)) :
      ComptimeLambdaParameterOrdinaryParses typeOrdinary input {
        span := SourceSpan.cover markerSpan name.span
        value := .error
      } afterName

/-- Exact ordered ordinary success of `lambdaParameterCore`. -/
inductive LambdaParameterCoreOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | comptime {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (parsed : ComptimeLambdaParameterOrdinaryParses typeOrdinary input
        parameter output) :
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output
  | ordinary {input output : Remainder}
      {parameter : Syntax.LambdaParameter}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (parsed : OrdinaryLambdaParameterOrdinaryParses typeOrdinary input
        parameter output) :
      LambdaParameterCoreOrdinaryParses typeOrdinary input parameter output

/-- Exact ordered ordinary rejection of `lambdaParameterCore`. -/
inductive LambdaParameterCoreRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | comptimeType {input afterMarker afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (markerSpan colonSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (nameParsed : IdentifierParses afterMarker name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      LambdaParameterCoreRejects typeRejects input rejected
  | ordinaryName {input rejected : Remainder}
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (nameRejected : IdentifierRejects input rejected) :
      LambdaParameterCoreRejects typeRejects input rejected
  | ordinaryType {input afterName afterColon rejected : Remainder}
      {name : Syntax.Identifier} (colonSpan : SourceSpan)
      (comptimeAbsent : ¬ ComptimeLambdaParameterStartsAt input)
      (nameParsed : IdentifierParses input name afterName)
      (colonParsed : ExactTokenParses (.symbol .colon) afterName colonSpan
        afterColon)
      (typeRejected : typeRejects afterColon rejected) :
      LambdaParameterCoreRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreLambdaParameterPublicOutcomeGrammar
/-!
Parser-independent ordinary outcomes at the public lambda-parameter rewind,
boundary, diagnostic-emission, and recovery layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before parameter recovery. -/
inductive LambdaParameterBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      LambdaParameterBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      LambdaParameterBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      LambdaParameterBoundaryStops input

/-- A Core rejection preserves the immutable token carrier and active window. -/
def LambdaParameterCoreRejectsWithPreservedWindow
    (typeRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, LambdaParameterCoreRejects typeRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Direct Core success or exact post-rewind recovery success. -/
inductive LambdaParameterOrdinaryParses
    (typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop)
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.LambdaParameter → Remainder → Prop where
  | core {input output : Remainder} {parameter : Syntax.LambdaParameter}
      (parsed : LambdaParameterCoreOrdinaryParses typeOrdinary input parameter
        output) :
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output
  | recovered {input output : Remainder} {parameter : Syntax.LambdaParameter}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ LambdaParameterBoundaryStops input)
      (recovered : LambdaParameterRecoveryParses input parameter output) :
      LambdaParameterOrdinaryParses typeOrdinary typeRejects input parameter
        output

/-- Exact public rejection at the rewound boundary or in recovery itself. -/
inductive LambdaParameterRejects
    (typeRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (stops : LambdaParameterBoundaryStops input) :
      LambdaParameterRejects typeRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : LambdaParameterCoreRejectsWithPreservedWindow
        typeRejects input)
      (continues : ¬ LambdaParameterBoundaryStops input)
      (recoveryRejected : LambdaParameterRecoveryRejects input rejected) :
      LambdaParameterRejects typeRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionPostfixOutcomeGrammar
/-!
Parser-independent ordinary success and exact rejection for maximal Core
postfix expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The existing postfix grammar admits ordinary nested outcomes as-is. -/
abbrev PostfixTailOrdinaryParses := PostfixTailParses

/-- Exact rejection while extending an already parsed Core atom. -/
inductive PostfixTailRejects
    (nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Expr → Remainder → Prop where
  | indexNestedRejected {input afterOpening rejected : Remainder}
      {base : Syntax.Expr} (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (nestedRejected : nestedRejects afterOpening rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | indexClosingMissing {input afterOpening afterIndex : Remainder}
      {base index : Syntax.Expr} (openingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedOrdinary afterOpening index afterIndex)
      (closingAbsent : TokenKindAbsentAt afterIndex.tokens afterIndex.endIndex
        afterIndex.cursor (.symbol .rightBracket)) :
      PostfixTailRejects nestedOrdinary nestedRejects input base afterIndex
  | indexLaterRejected
      {input afterOpening afterIndex afterClosing rejected : Remainder}
      {base index : Syntax.Expr} (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBracket) input
        openingSpan afterOpening)
      (indexParsed : nestedOrdinary afterOpening index afterIndex)
      (closingToken : ExactTokenParses (.symbol .rightBracket) afterIndex
        closingSpan afterClosing)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects
        afterClosing {
          span := SourceSpan.cover base.span closingSpan
          value := .index base (SourceSpan.cover openingSpan closingSpan) index
        } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | callArgumentsRejected {input rejected : Remainder}
      {base : Syntax.Expr} (openingSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : DelimitedListRejects .leftParen .rightParen true
        false nestedOrdinary nestedRejects input rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | callLaterRejected {input afterArguments rejected : Remainder}
      {base : Syntax.Expr} {arguments : DelimitedList Syntax.Expr}
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (argumentsParsed : NoTrailingDelimitedListParses .leftParen .rightParen
        nestedOrdinary input arguments afterArguments)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects
        afterArguments {
          span := SourceSpan.cover base.span arguments.span
          value := .call base arguments
        } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | fieldNameRejected {input afterDot rejected : Remainder}
      {base : Syntax.Expr} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameRejected : IdentifierRejects afterDot rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected
  | fieldLaterRejected {input afterDot afterName rejected : Remainder}
      {base : Syntax.Expr} {name : Syntax.Identifier} (dotSpan : SourceSpan)
      (indexAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBracket))
      (callAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftParen))
      (dotToken : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : IdentifierParses afterDot name afterName)
      (tailRejected : PostfixTailRejects nestedOrdinary nestedRejects afterName {
        span := SourceSpan.cover base.span name.span
        value := .field base dotSpan name
      } rejected) :
      PostfixTailRejects nestedOrdinary nestedRejects input base rejected

/-- The existing complete postfix grammar admits ordinary outcomes as-is. -/
abbrev ExpressionPostfixOrdinaryParses := ExpressionPostfixParses

/-- Exact rejection of a complete atom-plus-postfix attempt. -/
inductive ExpressionPostfixRejects
    (atomOrdinary nestedOrdinary :
      Remainder → Syntax.Expr → Remainder → Prop)
    (atomRejects nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | atomRejected {input rejected : Remainder}
      (rejectedAtom : atomRejects input rejected) :
      ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects input rejected
  | tailRejected {input afterAtom rejected : Remainder} {base : Syntax.Expr}
      (atomParsed : atomOrdinary input base afterAtom)
      (rejectedTail : PostfixTailRejects nestedOrdinary nestedRejects
        afterAtom base rejected) :
      ExpressionPostfixRejects atomOrdinary nestedOrdinary atomRejects
        nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreExpressionStepOutcomeGrammar
/-!
Named parser-independent ordinary outcomes for one complete Core expression
recursion step.

The bundle hides the atom-core, public recovery, postfix, and operator-stack
composition while leaving each recursive subordinate relation explicit.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Declarative subordinate relations used by one Core expression step. -/
structure CoreExpressionStepRelations where
  nestedOrdinary : Remainder → Syntax.Expr → Remainder → Prop
  nestedRejects : Remainder → Remainder → Prop
  parameterOrdinary : Remainder → Syntax.LambdaParameter → Remainder → Prop
  parameterRejects : Remainder → Remainder → Prop
  typeOrdinary : Remainder → Syntax.TypeExpr → Remainder → Prop
  typeRejects : Remainder → Remainder → Prop
  blockOrdinary : Remainder → Syntax.Block → Remainder → Prop
  blockRejects : Remainder → Remainder → Prop

namespace CoreExpressionStepRelations

/-- Ordered non-recovering atom success for this relation bundle. -/
abbrev atomCoreOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionAtomCoreOrdinaryParses relations.nestedOrdinary
    relations.parameterOrdinary relations.typeOrdinary relations.blockOrdinary

/-- Ordered non-recovering atom rejection for this relation bundle. -/
abbrev atomCoreRejects (relations : CoreExpressionStepRelations) :=
  ExpressionAtomCoreRejects relations.nestedOrdinary relations.nestedRejects
    relations.parameterOrdinary relations.parameterRejects
      relations.typeOrdinary relations.typeRejects relations.blockRejects

/-- Public recovering atom success for this relation bundle. -/
abbrev atomOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionAtomOrdinaryParses relations.atomCoreOrdinary
    relations.atomCoreRejects

/-- Public recovering atom rejection for this relation bundle. -/
abbrev atomRejects (relations : CoreExpressionStepRelations) :=
  ExpressionAtomRejects relations.atomCoreRejects

/-- Complete maximal postfix success for this relation bundle. -/
abbrev postfixOrdinary (relations : CoreExpressionStepRelations) :=
  ExpressionPostfixOrdinaryParses relations.atomOrdinary
    relations.nestedOrdinary

/-- Complete maximal postfix rejection for this relation bundle. -/
abbrev postfixRejects (relations : CoreExpressionStepRelations) :=
  ExpressionPostfixRejects relations.atomOrdinary relations.nestedOrdinary
    relations.atomRejects relations.nestedRejects

/-- One complete operator-stack success for this relation bundle. -/
abbrev ordinaryParses (relations : CoreExpressionStepRelations) :=
  ExpressionLayerOrdinaryParses relations.nestedOrdinary
    relations.postfixOrdinary

/-- One complete operator-stack rejection for this relation bundle. -/
abbrev rejects (relations : CoreExpressionStepRelations) :=
  ExpressionLayerRejects relations.nestedOrdinary relations.nestedRejects
    relations.postfixOrdinary relations.postfixRejects

end CoreExpressionStepRelations

/-- Ordinary success of one complete Core expression recursion step. -/
abbrev CoreExpressionStepOrdinaryParses
    (relations : CoreExpressionStepRelations) := relations.ordinaryParses

/-- Exact rejection of one complete Core expression recursion step. -/
abbrev CoreExpressionStepRejects
    (relations : CoreExpressionStepRelations) := relations.rejects

end Solcore.Syntax.DeclarativeGrammar
end
