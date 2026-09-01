import Solcore.Syntax.DeclarativeCoreExpressionAtomGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

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
