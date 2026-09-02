import Solcore.Syntax.DeclarativeCoreTypeNameExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties

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
example := @DottedIdentifierTailParses.value_unique
example := @QualifiedNameParses.value_unique
example := @QualifiedNameParses.result_unique
example := @TypeQualifiedNameTailRejects.output_unique
example := @TypeQualifiedNameRejects.output_unique
example := @typeQualifiedNameExactOutcomeSpec
example := @FunctionTypeReturnsRejects.output_unique
example := @FunctionTypeRejects.output_unique
example := @ComptimeTypeRejects.output_unique
example := @MappingTypeRejects.output_unique
example := @ProxyTypeRejects.output_unique
example := @TupleTypeRejects.output_unique
example := @NamedTypeArgumentsRejects.output_unique
example := @NamedTypeRejects.output_unique
example := @TypeExprCoreRejects.output_unique
example := @TypeExprParses.value_unique
example := @TypeExprParses.result_unique
example := @TypeExprTrailingDelimitedTailParses.value_unique
example := @TypeExprTrailingDelimitedTailParses.result_unique
example := @TypeExprTrailingDelimitedListParses.value_unique
example := @TypeExprTrailingDelimitedListParses.result_unique
example := @OptionalNamedTypeArgumentsParses.value_unique
example := @OptionalNamedTypeArgumentsParses.result_unique
example := @OptionalFunctionTypeReturnsParses.value_unique
example := @OptionalFunctionTypeReturnsParses.result_unique
example := @typeExprExactOutcomeSpecWithFuel
example := @TypeExprRejects.output_unique
example := @typeExprExactOutcomeSpec
example := @typeExprWithFuel_success_sound
example := @typeExpr_success_sound
example := @typeExpr_success_sound_and_validFor
example := @typeExprWithFuel_exactOutcomeSpec
example := @typeExprWithFuel_success_result_unique
example := @typeExprWithFuel_reject_output_unique
example := @typeExpr_exactOutcomeSpec
example := @typeExpr_success_result_unique
example := @typeExpr_reject_output_unique

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
