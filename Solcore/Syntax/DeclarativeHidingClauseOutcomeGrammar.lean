import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar
import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar

/-!
Parser-independent broad ordinary outcomes for import hiding clauses and their
optional guarded wrapper.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary hiding-clause success is the existing exact marker and nonempty
allow-trailing selector-list grammar. -/
abbrev HidingClauseOrdinaryParses := HidingClauseParses

/-- Exact rejection of the required nonempty, allow-trailing selector list
after a consumed `hiding` marker. -/
abbrev HidingSelectorListRejects :=
  DelimitedListRejects .leftBrace .rightBrace false true
    SelectorNameOrdinaryParses SelectorNameRejects

/-- Exact first rejecting stage of one required hiding clause. -/
inductive HidingClauseRejects : Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.hiding.spelling)) :
      HidingClauseRejects input input
  | namesRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses
        (.identifier ContextualKeyword.hiding.spelling) input markerSpan
          afterMarker)
      (namesRejected : HidingSelectorListRejects afterMarker rejected) :
      HidingClauseRejects input rejected

/-- Ordinary optional hiding success is the existing prioritized grammar:
absence is nonconsuming and a present marker commits to the clause. -/
abbrev OptionalHidingOrdinaryParses := OptionalHidingParses

/-- A positive `hiding` lookahead commits the optional wrapper to the required
clause.  The positive witness makes its nested `markerMissing` branch
uninhabitable and keeps absent success exclusive. -/
inductive OptionalHidingRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (markerPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span
          value := .identifier ContextualKeyword.hiding.spelling
        })
      (clauseRejected : HidingClauseRejects input rejected) :
      OptionalHidingRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
