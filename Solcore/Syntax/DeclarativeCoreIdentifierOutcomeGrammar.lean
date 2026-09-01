import Solcore.Syntax.DeclarativeGrammar

/-! Parser-independent exact rejection for one checked Core identifier. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- No ordinary identifier token occurs at the current grammar cursor. -/
def IdentifierAbsentAt (input : Remainder) : Prop :=
  ¬ ∃ span text, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier text
  }

/-- Exact non-consuming rejection of the checked Core identifier primitive. -/
inductive IdentifierRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (identifierAbsent : IdentifierAbsentAt input) :
      IdentifierRejects input input

end Solcore.Syntax.DeclarativeGrammar
