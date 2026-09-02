import Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryOutcomeSoundnessProperties
import Solcore.Syntax.Parser.TypeAliasSoundnessProperties

/-! External consumers for transparent type-alias grammar soundness. -/

set_option autoImplicit false

namespace Solcore.Test.SyntaxParserTypeAliasSoundnessProperties

open Solcore.Syntax
open Solcore.Syntax.DeclarativeGrammar
open Solcore.Syntax.Parser

example := @OptionalTypeAliasParametersParses
example := @TypeAliasDeclParses
example := @TypeAliasParametersOrdinaryParses
example := @TypeAliasParametersRejects
example := @typeAliasParametersDeterministicOutcomeSpec
example := @typeAliasParametersExactOutcomeSpec
example := @OptionalTypeAliasParametersOrdinaryParses
example := @OptionalTypeAliasParametersRejects
example := @optionalTypeAliasParametersDeterministicOutcomeSpec
example := @OptionalTypeAliasParametersOrdinaryParses.value_unique
example := @OptionalTypeAliasParametersOrdinaryParses.result_unique
example := @OptionalTypeAliasParametersRejects.output_unique
example := @optionalTypeAliasParametersExactOutcomeSpec
example := @TypeAliasValueBoundaryStops
example := @TypeAliasValueRecoveryStops
example := @TypeAliasValueRecoveryScanParses
example := @TypeAliasValueRecoveryParses
example := @TypeAliasValueRecoveryRejects
example := @typeAliasValueRecoveryDeterministicOutcomeSpec
example := @TypeAliasValueRecoveryScanParses.value_unique
example := @TypeAliasValueRecoveryScanParses.result_unique
example := @TypeAliasValueRecoveryParses.value_unique
example := @TypeAliasValueRecoveryParses.result_unique
example := @TypeAliasValueRecoveryRejects.output_unique
example := @typeAliasValueRecoveryExactOutcomeSpec
example := @TypeAliasValueCoreRejectsWithPreservedWindow
example := @TypeAliasValueOrdinaryParses
example := @TypeAliasValueRejects
example := @typeAliasValueDeterministicOutcomeSpec
example := @TypeAliasValueOrdinaryParses.value_unique_of_typeExpr
example := @TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
example := @TypeAliasValueRejects.output_unique
example := @typeAliasValueExactOutcomeSpecOfTypeExpr
example := @TypeAliasDeclOrdinaryParses
example := @TypeAliasDeclRejects
example := @typeAliasDeclDeterministicOutcomeSpec
example := @parseTypeAliasParameters_success_sound
example := @TypeAliasInternals.parseAliasValue_success_sound_of_diagnosticFree
example := @typeAlias_success_sound
example := @typeAlias_success_sound_and_validFor

example := @TypeAliasInternals.recoverTypeAliasValue_success_ordinary_sound
example := @TypeAliasInternals.recoverTypeAliasValue_reject_ordinary_sound
example := @TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcome_sound
example := @TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcomeSpec
example := @TypeAliasInternals.recoverTypeAliasValue_exactOutcomeSpec
example := @TypeAliasInternals.recoverTypeAliasValue_success_result_unique
example := @TypeAliasInternals.recoverTypeAliasValue_reject_output_unique
example := @parseTypeAliasParameters_success_ordinaryOutcome_sound
example := @parseTypeAliasParameters_reject_ordinaryOutcome_sound
example := @parseTypeAliasParameters_ordinaryOutcome_sound
example := @parseTypeAliasParameters_ordinaryOutcomeSpec
example := @parseTypeAliasParameters_exactOutcomeSpec
example := @parseTypeAliasParameters_success_result_unique
example := @parseTypeAliasParameters_reject_output_unique
example := @TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_ordinaryOutcome_sound
example := @TypeAliasInternals.parseAliasValue_ordinaryOutcomeSpec
example := @TypeAliasInternals.parseAliasValue_exactOutcomeSpec_of_typeExpr
example := @TypeAliasInternals.parseAliasValue_success_result_unique_of_typeExpr
example := @TypeAliasInternals.parseAliasValue_reject_output_unique
example := @typeAlias_success_ordinaryOutcome_sound
example := @typeAlias_reject_ordinaryOutcome_sound
example := @typeAlias_ordinaryOutcome_sound
example := @typeAlias_ordinaryOutcomeSpec

example {input next : State} {declaration : TypeAliasDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  typeAlias_success_sound diagnosticFree result

example {input next : State} {declaration : TypeAliasDecl}
    (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file :=
  typeAlias_success_sound_and_validFor inputValid diagnosticFree result

example {input next : State} {value : TypeExpr}
    (result : TypeAliasInternals.parseAliasValue input = .ok value next) :
    TypeAliasValueOrdinaryParses input.declarativeRemainder value
      next.declarativeRemainder :=
  TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : TypeAliasInternals.parseAliasValue input =
      .reject failure rejected) :
    TypeAliasValueRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound result

example {input next : State} {declaration : TypeAliasDecl}
    (result : typeAlias input = .ok declaration next) :
    TypeAliasDeclOrdinaryParses input.declarativeRemainder declaration
      next.declarativeRemainder :=
  typeAlias_success_ordinaryOutcome_sound result

example {input rejected : State} {failure : Failure}
    (result : typeAlias input = .reject failure rejected) :
    TypeAliasDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  typeAlias_reject_ordinaryOutcome_sound result

end Solcore.Test.SyntaxParserTypeAliasSoundnessProperties
