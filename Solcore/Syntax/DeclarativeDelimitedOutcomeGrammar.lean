import Solcore.Syntax.DeclarativeGrammar

/-!
Parser-independent ordinary outcomes and exact rejection traces for generic
delimited lists.

The successful relation is intentionally allowed to be broader than a clean
grammar: transactional parsing can consume diagnosed elements before a later
ordinary rejection rewinds the whole attempt.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Deterministic, exclusive ordinary outcomes of one nested production. -/
structure DeterministicOutcomeSpec {α : Type}
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (rejects : Remainder → Remainder → Prop) where
  successOutputUnique : ∀ {input : Remainder} {left right : α}
    {afterLeft afterRight : Remainder},
    ordinaryParses input left afterLeft →
    ordinaryParses input right afterRight →
    afterLeft = afterRight
  successRejectDisjoint : ∀ {input rejected : Remainder},
    rejects input rejected →
    ¬ ∃ value output, ordinaryParses input value output

/-- Evidence that a preferred immediate-close branch did not run. -/
inductive PreferredCloseNotTaken (closing : Symbol) :
    Bool → Remainder → Prop where
  | disabled {input : Remainder} :
      PreferredCloseNotTaken closing false input
  | absent {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol closing)) :
      PreferredCloseNotTaken closing true input

/-- Exact ordinary-rejection trace after at least one delimited element. -/
inductive DelimitedTailRejects {α : Type} (closing : Symbol)
    (allowTrailing : Bool)
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | delimiterMissing {input : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .comma))
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol closing)) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input input
  | elementRejected {input rejected : Remainder} (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (continues : PreferredCloseNotTaken closing allowTrailing
        { input with cursor := input.cursor + 1 })
      (nestedRejected : nestedRejects
        { input with cursor := input.cursor + 1 } rejected) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input rejected
  | laterRejected {input afterElement rejected : Remainder}
      {element : α} (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (continues : PreferredCloseNotTaken closing allowTrailing
        { input with cursor := input.cursor + 1 })
      (elementParsed : ordinaryParses
        { input with cursor := input.cursor + 1 } element afterElement)
      (progress : input.cursor + 1 < afterElement.cursor)
      (tailRejected : DelimitedTailRejects closing allowTrailing
        ordinaryParses nestedRejects afterElement rejected) :
      DelimitedTailRejects closing allowTrailing ordinaryParses nestedRejects
        input rejected

/-- Exact ordinary-rejection trace for a complete delimited-list attempt. -/
inductive DelimitedListRejects {α : Type} (opening closing : Symbol)
    (allowEmpty allowTrailing : Bool)
    (ordinaryParses : Remainder → α → Remainder → Prop)
    (nestedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol opening)) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input input
  | firstRejected {input rejected : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (continues : PreferredCloseNotTaken closing allowEmpty
        { input with cursor := input.cursor + 1 })
      (nestedRejected : nestedRejects
        { input with cursor := input.cursor + 1 } rejected) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder} {first : α}
      (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol opening
      })
      (continues : PreferredCloseNotTaken closing allowEmpty
        { input with cursor := input.cursor + 1 })
      (firstParsed : ordinaryParses
        { input with cursor := input.cursor + 1 } first afterFirst)
      (progress : input.cursor + 1 < afterFirst.cursor)
      (tailRejected : DelimitedTailRejects closing allowTrailing
        ordinaryParses nestedRejects afterFirst rejected) :
      DelimitedListRejects opening closing allowEmpty allowTrailing
        ordinaryParses nestedRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
