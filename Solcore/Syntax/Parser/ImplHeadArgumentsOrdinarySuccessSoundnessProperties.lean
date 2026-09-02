import Solcore.Syntax.DeclarativeImplHeadArgumentsOutcomeGrammar
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedSoundnessProperties
import Solcore.Syntax.Parser.ImplHeadSoundnessProperties

/-! Broad ordinary-success soundness for implementation head arguments. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

/-- The executable delimited stage followed by its pure nonempty refinement
has the exact broad implementation-head argument grammar. -/
theorem implHeadArguments_success_ordinaryOutcome_sound
    {input afterValues output : State}
    {values : DelimitedList TypeExpr}
    {arguments : NonemptyDelimitedList TypeExpr}
    (valuesResult : delimited .less .greater false typeExpr .typeExpr
      .topLevel input = .ok values afterValues)
    (argumentsResult : requireImplArguments values afterValues =
      .ok arguments output) :
    DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
      input.declarativeRemainder arguments output.declarativeRemainder := by
  have valuesParsed := delimited_nonempty_trailing_success_sound
    .less .greater typeExpr DeclarativeGrammar.TypeExprOrdinaryParses
    .typeExpr .topLevel typeExpr_ordinaryOutcome_sound.1
      typeExpr_preservesTokenWindow valuesResult
  have shape := requireImplArguments_success_shape argumentsResult
  unfold DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
  rw [shape.1]
  simpa only [shape.2.1, shape.2.2] using valuesParsed

end Solcore.Syntax.Parser.ImplInternals
