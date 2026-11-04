import Solcore.Syntax.Grammar.Expressions
import Solcore.Syntax.Grammar.Basics
import Solcore.Syntax.Unicode.Lowercase
import Solcore.Syntax.Internal.DelimitedOutcomes
import Solcore.Syntax.Internal.TypeOutcomes
import Solcore.Syntax.Internal.ExpressionOutcomes

/-!
Declarative grammar of patterns.

Main declarations: `QualifiedPatternParses`, `DotConstructorPatternParses`,
`ParenthesizedPatternOrdinaryParses`, `PatternRecoveryParses`,
`PatternLayerOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternBasicGrammar
/-!
Parser-independent grammar for the basic Core pattern leaves and
parenthesized patterns.

The parenthesized grammar records the executable parser's delimiter
priorities and keeps tuple elements in source order.  Exactly one accumulated
element closes as a group, including the source form `(pattern,)`.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of the canonical wildcard pattern. -/
inductive WildcardPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.symbol .underscore) input
        markerSpan output) :
      WildcardPatternParses input {
        span := markerSpan
        value := .wildcard markerSpan
      } output

/-- Exact grammar of a literal pattern leaf. -/
inductive LiteralPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} {literal : Syntax.CoreLiteral}
      (literalParsed : CoreLiteralParses input literal output) :
      LiteralPatternParses input {
        span := literal.span
        value := .literal literal
      } output

/-- Exact grammar of a Boolean builtin used as a binder-shaped pattern. -/
inductive BooleanBinderPatternParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input output : Remainder} {name : Syntax.Identifier}
      (nameParsed : BooleanIdentifierParses input name output) :
      BooleanBinderPatternParses input {
        span := name.span
        value := .binder name
      } output

/-- Pure forward-order counterpart of `closePatternTuple`. -/
def closeParenthesizedPattern (openingSpan closingSpan : SourceSpan)
    (elements : List Syntax.Pattern) : Syntax.Pattern :=
  let span := SourceSpan.cover openingSpan closingSpan
  match elements with
  | [only] => { span, value := .group only }
  | _ => { span, value := .tuple { span, elements } }

/--
Exact continuation after the first comma of a parenthesized pattern.
Returned elements are in source order and exclude those parsed earlier.
-/
inductive ParenthesizedPatternTupleTailParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → List Syntax.Pattern → SourceSpan → Remainder → Prop where
  | trailing {input afterComma output : Remainder}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterComma
        closingSpan output) :
      ParenthesizedPatternTupleTailParses nestedParses input [] closingSpan
        output
  | final {input afterComma afterElement output : Remainder}
      {element : Syntax.Pattern} (commaSpan closingSpan : SourceSpan)
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
      ParenthesizedPatternTupleTailParses nestedParses input [element]
        closingSpan output
  | next {input afterComma afterElement output : Remainder}
      {element : Syntax.Pattern} {elements : List Syntax.Pattern}
      (commaSpan closingSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedParses afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tail : ParenthesizedPatternTupleTailParses nestedParses afterElement
        elements closingSpan output) :
      ParenthesizedPatternTupleTailParses nestedParses input
        (element :: elements) closingSpan output

/-- Exact prioritized grammar of an empty tuple, group, or tuple pattern. -/
inductive ParenthesizedPatternParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | empty {input afterOpening output : Remainder}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingParsed : ExactTokenParses (.symbol .rightParen) afterOpening
        closingSpan output) :
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan []) output
  | group {input afterOpening afterElement output : Remainder}
      {element : Syntax.Pattern} (openingSpan closingSpan : SourceSpan)
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
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan [element]) output
  | tuple {input afterOpening afterFirst output : Remainder}
      {first : Syntax.Pattern} {rest : List Syntax.Pattern}
      (openingSpan closingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedParses afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tail : ParenthesizedPatternTupleTailParses nestedParses afterFirst rest
        closingSpan output) :
      ParenthesizedPatternParses nestedParses input
        (closeParenthesizedPattern openingSpan closingSpan (first :: rest))
        output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternParenthesizedOutcomeGrammar
/-!
Parser-independent ordinary outcomes for Core parenthesized patterns.

The tuple-tail rejection relation starts after the executable comma guard has
selected the tail.  Fuel exhaustion and non-progress are invariant failures,
so neither is represented by an ordinary relation.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary parenthesized-pattern success is the existing exact grammar. -/
abbrev ParenthesizedPatternOrdinaryParses := ParenthesizedPatternParses

/-- Exact ordinary rejection after a comma selected the tuple-tail loop. -/
inductive ParenthesizedPatternTupleTailRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | elementRejected {input afterComma rejected : Remainder}
      (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementRejected : nestedRejects afterComma rejected) :
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        rejected
  | closingMissing {input afterComma afterElement : Remainder}
      {element : Syntax.Pattern} (commaSpan : SourceSpan)
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
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        afterElement
  | laterRejected {input afterComma afterElement rejected : Remainder}
      {element : Syntax.Pattern} (commaSpan : SourceSpan)
      (commaParsed : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (closingAbsent : TokenKindAbsentAt afterComma.tokens
        afterComma.endIndex afterComma.cursor (.symbol .rightParen))
      (elementParsed : nestedOrdinary afterComma element afterElement)
      (progress : afterComma.cursor < afterElement.cursor)
      (tailRejected : ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects afterElement rejected) :
      ParenthesizedPatternTupleTailRejects nestedOrdinary nestedRejects input
        rejected

/-- Exact ordinary rejection of the public parenthesized-pattern parser. -/
inductive ParenthesizedPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input input
  | firstRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstRejected : nestedRejects afterOpening rejected) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input rejected
  | closingMissing {input afterOpening afterFirst : Remainder}
      {first : Syntax.Pattern} (openingSpan : SourceSpan)
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
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input afterFirst
  | tailRejected {input afterOpening afterFirst rejected : Remainder}
      {first : Syntax.Pattern} (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftParen) input
        openingSpan afterOpening)
      (closingAbsent : TokenKindAbsentAt afterOpening.tokens
        afterOpening.endIndex afterOpening.cursor (.symbol .rightParen))
      (firstParsed : nestedOrdinary afterOpening first afterFirst)
      (progress : afterOpening.cursor < afterFirst.cursor)
      (tailRejected : ParenthesizedPatternTupleTailRejects nestedOrdinary
        nestedRejects afterFirst rejected) :
      ParenthesizedPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternConstructorGrammar
/-!
Parser-independent grammar for constructor-shaped Core patterns.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Boolean-first pattern names, with exact ordered-choice evidence. -/
inductive PatternNameParses :
    Remainder → Syntax.Identifier → Remainder → Prop where
  | boolean {input output : Remainder} {name : Syntax.Identifier}
      (parsed : BooleanIdentifierParses input name output) :
      PatternNameParses input name output
  | identifier {input output : Remainder} {name : Syntax.Identifier}
      (trueAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .trueKw))
      (falseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .falseKw))
      (hyphenAbsent : name.value.toList.contains '-' = false)
      (parsed : IdentifierParses input name output) :
      PatternNameParses input name output

/-- Exact, non-consuming refinement from a list to its nonempty carrier. -/
inductive RequirePatternArgumentsParses :
    DelimitedList Syntax.Pattern → Remainder →
      NonemptyDelimitedList Syntax.Pattern → Remainder → Prop where
  | parsed {input : Remainder} {span : SourceSpan}
      {head : Syntax.Pattern} {tail : List Syntax.Pattern} :
      RequirePatternArgumentsParses {
        span
        elements := head :: tail
      } input {
        span
        elements := { head, tail }
      } input

/-- Required nonempty, comma-separated constructor arguments. -/
def ConstructorArgumentsParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (input : Remainder) (arguments : NonemptyDelimitedList Syntax.Pattern)
    (output : Remainder) : Prop :=
  NonemptyNoTrailingDelimitedListParses .leftParen .rightParen nestedParses
    input {
      span := arguments.span
      elements := arguments.elements.toList
    } output

/--
An exact parser-independent fallback specification for required arguments.
Disjointness prevents a permissive predicate such as `True` from making the
transactional rewind overlap a successful argument parse.
-/
structure ConstructorArgumentsFallbackSpec
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop) where
  rejects : Remainder → Prop
  disjoint : ∀ input, rejects input →
    ¬ ∃ arguments output,
      ConstructorArgumentsParses nestedParses input arguments output

/-- Exact successful outcomes of transactional optional constructor arguments. -/
inductive OptionalConstructorArgumentsParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (fallback : ConstructorArgumentsFallbackSpec nestedParses) :
    Remainder → Option (NonemptyDelimitedList Syntax.Pattern) →
      Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalConstructorArgumentsParses nestedParses fallback input
        none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : fallback.rejects input) :
      OptionalConstructorArgumentsParses nestedParses fallback input
        none input
  | present {input output : Remainder}
      {arguments : NonemptyDelimitedList Syntax.Pattern}
      (parsed : ConstructorArgumentsParses nestedParses input arguments
        output) :
      OptionalConstructorArgumentsParses nestedParses fallback input
        (some arguments) output

/-- Exact leading-dot constructor-pattern grammar. -/
inductive DotConstructorPatternParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (fallback : ConstructorArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input afterDot afterName output : Remainder}
      {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : PatternNameParses afterDot name afterName)
      (argumentsParsed : OptionalConstructorArgumentsParses nestedParses
        fallback afterName arguments output) :
      DotConstructorPatternParses nestedParses fallback input {
        span := SourceSpan.cover dotSpan
          (arguments.map (fun values => values.span) |>.getD name.span)
        value := .constructor (some dotSpan) [] name arguments
      } output

/-- The parser's Unicode-aware lowercase decision, expressed without parsers. -/
def patternIdentifierStartsWithLowercase (name : Syntax.Identifier) : Bool :=
  match name.value.toList with
  | first :: _ => Unicode.isLowercase first
  | [] => true

/-- Exact Boolean decision separating binders from qualified constructors. -/
def qualifiedPatternIsBinder (qualifiersRev : List Syntax.Identifier)
    (arguments : Option (NonemptyDelimitedList Syntax.Pattern))
    (name : Syntax.Identifier) : Bool :=
  qualifiersRev.isEmpty && arguments.isNone &&
    patternIdentifierStartsWithLowercase name

/-- A qualified pattern path with every checked-identifier diagnostic excluded. -/
def PatternQualifiedNameParses (input : Remainder)
    (path : Syntax.QualifiedName) (output : Remainder) : Prop :=
  QualifiedNameParses input path output ∧
    ∀ component ∈ path.value.components.toList,
      component.value.toList.contains '-' = false

/-!
`componentsReversed` fixes both the final constructor name and the written
qualifier order: the AST stores `qualifiersRev.reverse`.
-/
/-- Exact binder-or-constructor grammar following one maximal qualified name. -/
inductive QualifiedPatternParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (fallback : ConstructorArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | binder {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsParses nestedParses
        fallback afterPath arguments output)
      (componentsReversed : path.value.components.toList.reverse = [name])
      (choice : qualifiedPatternIsBinder [] arguments name = true) :
      QualifiedPatternParses nestedParses fallback input {
        span := path.span
        value := .binder name
      } output
  | constructor {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {qualifiersRev : List Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsParses nestedParses
        fallback afterPath arguments output)
      (componentsReversed :
        path.value.components.toList.reverse = name :: qualifiersRev)
      (choice : qualifiedPatternIsBinder qualifiersRev arguments name = false) :
      QualifiedPatternParses nestedParses fallback input {
        span := SourceSpan.cover path.span
          (arguments.map (fun values => values.span) |>.getD path.span)
        value := .constructor none qualifiersRev.reverse name arguments
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternRecoveryOutcomeGrammar
/-!
Parser-independent ordinary outcomes of Core pattern recovery.

The public pattern layer consumes one token before this scan begins.  The
scan gives pattern boundaries priority over token consumption and records a
missing carrier slot inside the active token window.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact stop conditions of the boundary-prioritized pattern recovery scan. -/
inductive PatternRecoveryStops : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex <= input.cursor) :
      PatternRecoveryStops input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      PatternRecoveryStops input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      PatternRecoveryStops input input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      PatternRecoveryStops input input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      PatternRecoveryStops input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      PatternRecoveryStops input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      PatternRecoveryStops input input

/-- Exact scan after pattern recovery has consumed its mandatory first token. -/
inductive PatternRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.Pattern → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : PatternRecoveryStops input input) :
      PatternRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {pattern : Syntax.Pattern}
      (continues : ¬ PatternRecoveryStops input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : PatternRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } pattern output) :
      PatternRecoveryScanParses first last input pattern output

/-- Ordinary pattern recovery, including its mandatory first token. -/
inductive PatternRecoveryParses :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | recovered {input output : Remainder} {token : Token}
      {pattern : Syntax.Pattern}
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : PatternRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } pattern output) :
      PatternRecoveryParses input pattern output

/-- Exact non-consuming rejection when recovery cannot consume first. -/
inductive PatternRecoveryRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex <= input.cursor) :
      PatternRecoveryRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      PatternRecoveryRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternPublicOutcomeGrammar
/-!
Parser-independent ordinary outcomes at the public Core pattern rewind and
recovery boundary.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming boundaries checked before public pattern recovery. -/
inductive PatternBoundaryStops : Remainder → Prop where
  | windowEnd {input : Remainder} (atEnd : input.endIndex ≤ input.cursor) :
      PatternBoundaryStops input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .comma }) :
      PatternBoundaryStops input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightParen }) :
      PatternBoundaryStops input
  | fatArrow {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .fatArrow }) :
      PatternBoundaryStops input
  | pipe {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .pipe }) :
      PatternBoundaryStops input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .rightBrace }) :
      PatternBoundaryStops input

/-- A Core-pattern rejection retains its failed cursor while preserving the
token carrier and active window needed for the public cursor rewind. -/
def PatternCoreRejectsWithPreservedWindow
    (coreRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ failed, coreRejects input failed ∧
    failed.tokens = input.tokens ∧ failed.endIndex = input.endIndex

/-- Ordinary public pattern success is a direct Core success or recovery from
the original cursor after a window-preserving Core rejection. -/
inductive PatternLayerOrdinaryParses
    (coreOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | core {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : coreOrdinary input pattern output) :
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern output
  | recovered {input output : Remainder} {pattern : Syntax.Pattern}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ PatternBoundaryStops input)
      (recovered : PatternRecoveryParses input pattern output) :
      PatternLayerOrdinaryParses coreOrdinary coreRejects input pattern output

/-- Exact public pattern rejection after the Core failure is rewound. -/
inductive PatternLayerRejects
    (coreRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | boundary {input : Remainder}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (stops : PatternBoundaryStops input) :
      PatternLayerRejects coreRejects input input
  | recovery {input rejected : Remainder}
      (coreRejected : PatternCoreRejectsWithPreservedWindow coreRejects input)
      (continues : ¬ PatternBoundaryStops input)
      (recoveryRejected : PatternRecoveryRejects input rejected) :
      PatternLayerRejects coreRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternComptimeGrammar
/-!
Parser-independent grammar for the Core compile-time pattern.

The marker remains an identifier token in the lexer.  Its contextual role is
recorded here by requiring the exact `comptime` spelling before the supplied
expression grammar.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of `comptime expression` in pattern position. -/
inductive ComptimePatternParses
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {expression : Syntax.Expr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (expressionParsed : expressionParses afterMarker expression output) :
      ComptimePatternParses expressionParses input {
        span := SourceSpan.cover markerSpan expression.span
        value := .comptime markerSpan expression
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternGrammar
/-!
Parser-independent ordered grammar for the non-recovering Core pattern
dispatcher and its diagnostic-free public layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Either Boolean hard keyword starts at the current pattern cursor. -/
def BooleanPatternStartsAt (input : Remainder) : Prop :=
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }

/--
Exact priority grammar of `patternCore`.  Every branch after the wildcard
retains all failed executable guards that precede it.
-/
inductive PatternCoreParses
    (nestedParses : Remainder → Syntax.Pattern → Remainder → Prop)
    (expressionParses : Remainder → Syntax.Expr → Remainder → Prop)
    (fallback : ConstructorArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | wildcard {input output : Remainder} {value : Syntax.Pattern}
      (parsed : WildcardPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | literal {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (parsed : LiteralPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | boolean {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (parsed : BooleanBinderPatternParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | parenthesized {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (parsed : ParenthesizedPatternParses nestedParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | dotConstructor {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (parsed : DotConstructorPatternParses nestedParses fallback input value
        output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | comptime {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (parsed : ComptimePatternParses expressionParses input value output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output
  | qualified {input output : Remainder} {value : Syntax.Pattern}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (parsed : QualifiedPatternParses nestedParses fallback input value
        output) :
      PatternCoreParses nestedParses expressionParses fallback input value
        output

/-- Diagnostic-free public pattern parsing has the same independent grammar. -/
abbrev PatternLayerParses := PatternCoreParses

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternCoreOutcomeGrammar
/-!
Generic parser-independent ordinary outcomes for the ordered `patternCore`
dispatcher.  The four recursive branches are parameters so their concrete
nested pattern and expression outcomes can be connected independently.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev WildcardPatternOrdinaryParses := WildcardPatternParses
abbrev LiteralPatternOrdinaryParses := LiteralPatternParses
abbrev BooleanBinderPatternOrdinaryParses := BooleanBinderPatternParses

/-- Exact non-consuming wildcard-leaf rejection. -/
inductive WildcardPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore)) :
      WildcardPatternRejects input input

/-- Exact non-consuming literal-pattern rejection. -/
inductive LiteralPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (literalAbsent : CoreLiteralAbsentAt input) :
      LiteralPatternRejects input input

/-- Neither Boolean hard keyword starts at this cursor. -/
def BooleanPatternAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .trueKw) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .falseKw)

/-- Exact non-consuming Boolean-binder rejection. -/
inductive BooleanBinderPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (booleanAbsent : BooleanPatternAbsentAt input) :
      BooleanBinderPatternRejects input input

/-- The seven successful branches in executable priority order. -/
inductive PatternCoreBranch where
  | wildcard
  | literal
  | boolean
  | parenthesized
  | dotConstructor
  | comptime
  | qualified
  deriving DecidableEq

/-- Exact guard evidence selecting one ordered Core-pattern branch. -/
inductive PatternCoreBranchSelected : PatternCoreBranch → Remainder → Prop where
  | wildcard {input : Remainder} {span : SourceSpan}
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .underscore }) :
      PatternCoreBranchSelected .wildcard input
  | literal {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (starts : CoreLiteralStartsAt input) :
      PatternCoreBranchSelected .literal input
  | boolean {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (starts : BooleanPatternStartsAt input) :
      PatternCoreBranchSelected .boolean input
  | parenthesized {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .leftParen }) :
      PatternCoreBranchSelected .parenthesized input
  | dotConstructor {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .dot }) :
      PatternCoreBranchSelected .dotConstructor input
  | comptime {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .identifier ContextualKeyword.comptime.spelling
      }) : PatternCoreBranchSelected .comptime input
  | qualified {input : Remainder} {span : SourceSpan} {text : String}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor
          (.identifier ContextualKeyword.comptime.spelling))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .identifier text }) :
      PatternCoreBranchSelected .qualified input

/-- Successful payload of the selected branch. -/
inductive PatternCoreBranchOrdinaryParses
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    PatternCoreBranch → Remainder → Syntax.Pattern → Remainder → Prop where
  | wildcard {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : WildcardPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .wildcard
          input pattern output
  | literal {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : LiteralPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .literal
          input pattern output
  | boolean {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : BooleanBinderPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .boolean
          input pattern output
  | parenthesized {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : parenthesizedOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
          .parenthesized input pattern output
  | dotConstructor {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : dotConstructorOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
          .dotConstructor input pattern output
  | comptime {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : comptimeOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .comptime
          input pattern output
  | qualified {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : qualifiedOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .qualified
          input pattern output

/-- Exact selected ordinary success of the ordered dispatcher. -/
inductive PatternCoreOrdinaryParses
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | selected {branch : PatternCoreBranch} {input output : Remainder}
      {pattern : Syntax.Pattern}
      (selection : PatternCoreBranchSelected branch input)
      (parsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
          pattern output) :
      PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary input pattern output

/-- Rejection payload of one of the four fallible selected branches. -/
inductive PatternCoreBranchRejects
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop) :
    PatternCoreBranch → Remainder → Remainder → Prop where
  | parenthesized {input rejected : Remainder}
      (branchRejected : parenthesizedRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .parenthesized input rejected
  | dotConstructor {input rejected : Remainder}
      (branchRejected : dotConstructorRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .dotConstructor input rejected
  | comptime {input rejected : Remainder}
      (branchRejected : comptimeRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .comptime input rejected
  | qualified {input rejected : Remainder}
      (branchRejected : qualifiedRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .qualified input rejected

/-- Exact final non-consuming dispatcher rejection. -/
inductive PatternCoreFinalRejects : Remainder → Remainder → Prop where
  | final {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (identifierAbsent : IdentifierAbsentAt input) :
      PatternCoreFinalRejects input input

/-- Exact selected or final rejection of the ordered dispatcher. -/
inductive PatternCoreRejects
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | selected {branch : PatternCoreBranch} {input rejected : Remainder}
      (selection : PatternCoreBranchSelected branch input)
      (branchRejected : PatternCoreBranchRejects parenthesizedRejects
        dotConstructorRejects comptimeRejects qualifiedRejects branch input
          rejected) :
      PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects input rejected
  | final {input : Remainder}
      (rejected : PatternCoreFinalRejects input input) :
      PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternComptimeOutcomeGrammar
/-! Parser-independent ordinary outcomes for Core compile-time patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary compile-time-pattern success has the same exact token shape as
the clean grammar while permitting an ordinary supplied expression. -/
abbrev ComptimePatternOrdinaryParses := ComptimePatternParses

/-- Exact rejection is either the non-consuming missing marker or rejection
of the supplied expression after the exact contextual marker. -/
inductive ComptimePatternRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling)) :
      ComptimePatternRejects expressionRejects input input
  | expressionRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.comptime.spelling) input markerSpan
          afterMarker)
      (rejectedExpression : expressionRejects afterMarker rejected) :
      ComptimePatternRejects expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternArgumentsOutcomeGrammar
/-! Ordinary outcomes for Core constructor-pattern argument parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Required constructor arguments support arbitrary ordinary nested patterns. -/
abbrev ConstructorArgumentsOrdinaryParses := ConstructorArgumentsParses

/-- Exact rejection of the required nonempty, no-trailing argument list. -/
abbrev ConstructorArgumentsOrdinaryRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :=
  DelimitedListRejects .leftParen .rightParen false false nestedOrdinary
    nestedRejects

/-- Exact successful outcomes of transactional optional arguments. -/
inductive OptionalConstructorArgumentsOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Option (NonemptyDelimitedList Syntax.Pattern) →
      Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalConstructorArgumentsOrdinaryParses nestedOrdinary nestedRejects
        input none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (argumentsRejected : ∃ rejected,
        ConstructorArgumentsOrdinaryRejects nestedOrdinary nestedRejects input
          rejected) :
      OptionalConstructorArgumentsOrdinaryParses nestedOrdinary nestedRejects
        input none input
  | present {input output : Remainder}
      {arguments : NonemptyDelimitedList Syntax.Pattern}
      (parsed : ConstructorArgumentsOrdinaryParses nestedOrdinary input
        arguments output) :
      OptionalConstructorArgumentsOrdinaryParses nestedOrdinary nestedRejects
        input (some arguments) output

/-- Transactional optional arguments never return an ordinary rejection. -/
def OptionalConstructorArgumentsRejects (_input _rejected : Remainder) : Prop :=
  False

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternQualifiedNameOutcomeGrammar
/-! Ordinary outcomes for qualified names used by Core patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnostic-inclusive pattern paths use the exact maximal qualified-name
grammar without the clean checked-identifier side condition. -/
abbrev PatternQualifiedNameOrdinaryParses := QualifiedNameParses

/-- Qualified pattern paths reuse the context-independent exact dotted-name
rejection trace. -/
abbrev PatternQualifiedNameRejects := TypeQualifiedNameRejects

/-- Qualified pattern paths have deterministic ordinary outcomes. -/
theorem patternQualifiedNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternQualifiedNameOrdinaryParses
      PatternQualifiedNameRejects where
  successOutputUnique := QualifiedNameParses.output_unique
  successRejectDisjoint := TypeQualifiedNameRejects.disjointQualified

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternQualifiedOutcomeGrammar
/-! Ordinary outcomes for qualified Core binder and constructor patterns. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact diagnostic-inclusive qualified-pattern success.  Optional arguments
retain absence, transactional rewind, and committed-present outcomes. -/
inductive QualifiedPatternOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | binder {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterPath arguments output)
      (componentsReversed : path.value.components.toList.reverse = [name])
      (choice : qualifiedPatternIsBinder [] arguments name = true) :
      QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := path.span
        value := .binder name
      } output
  | constructor {input afterPath output : Remainder}
      {path : Syntax.QualifiedName} {name : Syntax.Identifier}
      {qualifiersRev : List Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterPath arguments output)
      (componentsReversed :
        path.value.components.toList.reverse = name :: qualifiersRev)
      (choice : qualifiedPatternIsBinder qualifiersRev arguments name =
        false) :
      QualifiedPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := SourceSpan.cover path.span
          (arguments.map (fun values => values.span) |>.getD path.span)
        value := .constructor none qualifiersRev.reverse name arguments
      } output

/-- Exact sequential rejection.  The second constructor records the
formally complete optional-arguments stage, whose concrete rejection relation
is empty because that parser transactionally rewinds. -/
inductive QualifiedPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | pathRejected {input rejected : Remainder}
      (rejectedPath : PatternQualifiedNameRejects input rejected) :
      QualifiedPatternRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected {input afterPath rejected : Remainder}
      {path : Syntax.QualifiedName}
      (pathParsed : PatternQualifiedNameOrdinaryParses input path afterPath)
      (rejectedArguments : OptionalConstructorArgumentsRejects afterPath
        rejected) :
      QualifiedPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternNameOutcomeGrammar
/-! Ordinary outcomes for the Boolean-first Core pattern name parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Pattern names share the exact Boolean-first ordinary grammar used by
expression names; checked-identifier diagnostics do not alter this shape. -/
abbrev PatternNameOrdinaryParses := ExpressionNameOrdinaryParses

/-- Pattern-name rejection is the same exact three-way token absence. -/
abbrev PatternNameRejects := ExpressionNameRejects

/-- Boolean-first pattern names form a deterministic ordinary outcome. -/
theorem patternNameDeterministicOutcomeSpec :
    DeterministicOutcomeSpec PatternNameOrdinaryParses PatternNameRejects :=
  expressionNameDeterministicOutcomeSpec

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternDotConstructorOutcomeGrammar
/-!
Parser-independent ordinary outcomes for a leading-dot Core constructor
pattern.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary success through the dot, Boolean-first name, and
transactional optional-argument stages. -/
inductive DotConstructorPatternOrdinaryParses
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | parsed {input afterDot afterName output : Remainder}
      {name : Syntax.Identifier}
      {arguments : Option (NonemptyDelimitedList Syntax.Pattern)}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : PatternNameOrdinaryParses afterDot name afterName)
      (argumentsParsed : OptionalConstructorArgumentsOrdinaryParses
        nestedOrdinary nestedRejects afterName arguments output) :
      DotConstructorPatternOrdinaryParses nestedOrdinary nestedRejects input {
        span := SourceSpan.cover dotSpan
          (arguments.map (fun values => values.span) |>.getD name.span)
        value := .constructor (some dotSpan) [] name arguments
      } output

/-- Exact rejection follows parser order: the leading dot is absent, the
committed name rejects after that dot, or the optional-argument stage rejects
after both earlier stages.  The final relation is empty for the concrete
transactional optional parser, but recording it keeps the sequential outcome
shape exact. -/
inductive DotConstructorPatternRejects
    (nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | dotMissing {input : Remainder}
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot)) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input input
  | nameRejected {input afterDot rejected : Remainder}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (rejectedName : PatternNameRejects afterDot rejected) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input rejected
  | argumentsRejected
      {input afterDot afterName rejected : Remainder}
      {name : Syntax.Identifier}
      (dotSpan : SourceSpan)
      (dotParsed : ExactTokenParses (.symbol .dot) input dotSpan afterDot)
      (nameParsed : PatternNameOrdinaryParses afterDot name afterName)
      (rejectedArguments : OptionalConstructorArgumentsRejects afterName
        rejected) :
      DotConstructorPatternRejects nestedOrdinary nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCorePatternStepOutcomeGrammar
/-! Named relations for one complete recursive Core pattern step. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Recursive subordinate outcomes consumed by one Core pattern layer. -/
structure CorePatternStepRelations where
  nestedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop
  nestedRejects : Remainder → Remainder → Prop
  expressionOrdinary : Remainder → Syntax.Expr → Remainder → Prop
  expressionRejects : Remainder → Remainder → Prop

namespace CorePatternStepRelations

abbrev parenthesizedOrdinary (relations : CorePatternStepRelations) :=
  ParenthesizedPatternOrdinaryParses relations.nestedOrdinary

abbrev parenthesizedRejects (relations : CorePatternStepRelations) :=
  ParenthesizedPatternRejects relations.nestedOrdinary
    relations.nestedRejects

abbrev dotConstructorOrdinary (relations : CorePatternStepRelations) :=
  DotConstructorPatternOrdinaryParses relations.nestedOrdinary
    relations.nestedRejects

abbrev dotConstructorRejects (relations : CorePatternStepRelations) :=
  DotConstructorPatternRejects relations.nestedOrdinary
    relations.nestedRejects

abbrev comptimeOrdinary (relations : CorePatternStepRelations) :=
  ComptimePatternOrdinaryParses relations.expressionOrdinary

abbrev comptimeRejects (relations : CorePatternStepRelations) :=
  ComptimePatternRejects relations.expressionRejects

abbrev qualifiedOrdinary (relations : CorePatternStepRelations) :=
  QualifiedPatternOrdinaryParses relations.nestedOrdinary
    relations.nestedRejects

abbrev qualifiedRejects (relations : CorePatternStepRelations) :=
  QualifiedPatternRejects relations.nestedOrdinary relations.nestedRejects

abbrev coreOrdinary (relations : CorePatternStepRelations) :=
  PatternCoreOrdinaryParses relations.parenthesizedOrdinary
    relations.dotConstructorOrdinary relations.comptimeOrdinary
      relations.qualifiedOrdinary

abbrev coreRejects (relations : CorePatternStepRelations) :=
  PatternCoreRejects relations.parenthesizedRejects
    relations.dotConstructorRejects relations.comptimeRejects
      relations.qualifiedRejects

abbrev ordinaryParses (relations : CorePatternStepRelations) :=
  PatternLayerOrdinaryParses relations.coreOrdinary relations.coreRejects

abbrev rejects (relations : CorePatternStepRelations) :=
  PatternLayerRejects relations.coreRejects

end CorePatternStepRelations

/-- Ordinary success of one complete public Core pattern recursion step. -/
abbrev CorePatternStepOrdinaryParses (relations : CorePatternStepRelations) :=
  relations.ordinaryParses

/-- Exact rejection of one complete public Core pattern recursion step. -/
abbrev CorePatternStepRejects (relations : CorePatternStepRelations) :=
  relations.rejects

end Solcore.Syntax.DeclarativeGrammar
end
