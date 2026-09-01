import Solcore.Syntax.Parser.TypeExprSoundnessProperties

/-! External consumers for recursive type-expression grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeExprSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @TypeExprParses
example := @TypeExprTrailingDelimitedTailParses
example := @TypeExprTrailingDelimitedListParses
example := @OptionalNamedTypeArgumentsParses
example := @OptionalFunctionTypeReturnsParses
example := @typeExprWithFuel_success_sound
example := @typeExpr_success_sound
example := @typeExpr_success_sound_and_validFor

example {input next : State} {value : TypeExpr}
    (result : typeExpr input = .ok value next) :
    TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder :=
  typeExpr_success_sound result

example {input next : State} {value : TypeExpr}
    (inputValid : input.ValidFor)
    (result : typeExpr input = .ok value next) :
    TypeExprParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file :=
  typeExpr_success_sound_and_validFor inputValid result

end Solcore.Test.SyntaxParserTypeExprSoundnessProperties
