import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-! Parser-independent exact rejection for canonical generic parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact ordinary rejection of a required nonempty, allow-trailing generic
parameter list. -/
abbrev GenericParametersRejects :=
  DelimitedListRejects .less .greater false true IdentifierParses
    IdentifierRejects

/-- Exact rejection of optional generic parameters after their positive `<`
lookahead commits to the required generic-parameter parser.

The lookahead does not consume the opening token, so the nested rejection also
starts at the original remainder. -/
inductive OptionalGenericParametersRejects : Remainder → Remainder → Prop where
  | present {input rejected : Remainder}
      (openingPresent : ∃ span,
        TokenAt input.tokens input.endIndex input.cursor {
          span
          value := .symbol .less
        })
      (parametersRejected : GenericParametersRejects input rejected) :
      OptionalGenericParametersRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
