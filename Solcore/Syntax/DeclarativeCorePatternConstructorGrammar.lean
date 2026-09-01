import Solcore.Syntax.DeclarativeCoreLiteralGrammar
import Solcore.Syntax.Unicode.Lowercase

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
