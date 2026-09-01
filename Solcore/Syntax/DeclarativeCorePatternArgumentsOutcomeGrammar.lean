import Solcore.Syntax.DeclarativeCorePatternConstructorGrammar
import Solcore.Syntax.DeclarativeDelimitedNoTrailingOutcomeProperties

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
