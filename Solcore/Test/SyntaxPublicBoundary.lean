import Solcore

/-! Smoke test for the canonical syntax API exposed by `import Solcore`. -/

set_option autoImplicit false

namespace Tests

open Solcore
open Solcore.Syntax

private def publicSyntaxSource : SourceFile := {
  id := {
    origin := .main
    path := "public-syntax.sol"
  }
  content := "type PublicWord = word;"
}

private def malformedPublicSyntaxSource : SourceFile := {
  id := {
    origin := .main
    path := "public-syntax-malformed.sol"
  }
  content := "function bad(x: ) {}"
}

private def assertTrue (condition : Bool) (label : String) : IO Unit := do
  unless condition do
    throw (IO.userError s!"{label}: expected true")

/-- Exercise the canonical source-to-AST API through the repository umbrella. -/
def testSyntaxPublicBoundary : IO Unit := do
  assertTrue (Syntax.isValidIdentifier "PublicWord")
    "public identifier validator"
  match Syntax.Parser.parse publicSyntaxSource with
  | .error error => throw (IO.userError
      s!"public parser invariant failed: {reprStr error}")
  | .ok output =>
      assertTrue output.isDiagnosticFree "public diagnostic-free result"
      unless output.lexicalDiagnostics.isEmpty do
        throw (IO.userError
          s!"unexpected lexical diagnostics: {reprStr output.lexicalDiagnostics}")
      unless output.parseDiagnostics.isEmpty do
        throw (IO.userError
          s!"unexpected parse diagnostics: {reprStr output.parseDiagnostics}")
      match output.parsed.items with
      | [{ value := .typeAlias declaration, .. }] =>
          let astWitness : TypeAliasDecl := declaration
          assertTrue (astWitness.value.name.value == "PublicWord")
            "public canonical AST"
      | items => throw (IO.userError
          s!"unexpected public AST: {reprStr items}")
  match Syntax.Parser.parse malformedPublicSyntaxSource with
  | .error error => throw (IO.userError
      s!"malformed public parser invariant failed: {reprStr error}")
  | .ok output =>
      assertTrue (!output.isDiagnosticFree)
        "malformed public diagnostic result"

example (output : ParseOutput) :
    output.isDiagnosticFree = true ↔ output.DiagnosticFree :=
  output.isDiagnosticFree_eq_true_iff

example := @Syntax.DeclarativeGrammar.CoreSourceFileOrdinaryParsesFromStart
example := @Syntax.Parser.parseLexed_ok_coreOrdinary_sound
example := @Syntax.Parser.parseLexed_ok_coreOrdinary_sound_and_validFor
example := @Syntax.Parser.parse_ok_coreOrdinary_sound
example := @Syntax.Parser.parse_ok_coreOrdinary_sound_and_validFor
example := @Syntax.DeclarativeGrammar.PredicateRejects
example := @Syntax.DeclarativeGrammar.predicateDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.GroupedPredicateSequenceRejects
example := @Syntax.DeclarativeGrammar.GroupedPredicateSequenceUnavailable
example := @Syntax.DeclarativeGrammar.GroupedPredicateSequenceRejects.no_parse
example := @Syntax.DeclarativeGrammar.BarePredicateSequenceRejects
example := @Syntax.DeclarativeGrammar.barePredicateSequenceDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PredicateSequenceRejects
example := @Syntax.DeclarativeGrammar.predicateSequenceDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalWhereClauseRejects
example := @Syntax.DeclarativeGrammar.optionalWhereClauseDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalReturnClauseRejects
example := @Syntax.DeclarativeGrammar.optionalReturnClauseDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.GenericParametersRejects
example := @Syntax.DeclarativeGrammar.genericParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalGenericParametersRejects
example := @Syntax.DeclarativeGrammar.optionalGenericParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionParameterCoreOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionParameterCoreRejects
example := @Syntax.DeclarativeGrammar.FunctionParameterOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionParameterRejects
example := @Syntax.DeclarativeGrammar.functionParameterDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionParametersRejects
example := @Syntax.DeclarativeGrammar.functionParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionSignatureOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionSignatureRejects
example := @Syntax.DeclarativeGrammar.functionSignatureDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionDeclRejects
example := @Syntax.DeclarativeGrammar.functionDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplMethodOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImplMethodRejects
example := @Syntax.DeclarativeGrammar.implMethodDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
example := @Syntax.DeclarativeGrammar.ConstructorDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ConstructorDeclRejects
example := @Syntax.DeclarativeGrammar.constructorDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FallbackParameterValidationOrdinaryParses
example := @Syntax.DeclarativeGrammar.FallbackDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.FallbackDeclRejects
example := @Syntax.DeclarativeGrammar.fallbackDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalContractFieldInitializerOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalContractFieldInitializerRejects
example := @Syntax.DeclarativeGrammar.optionalContractFieldInitializerDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractFieldOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractFieldRejects
example := @Syntax.DeclarativeGrammar.contractFieldDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasParametersRejects
example := @Syntax.DeclarativeGrammar.typeAliasParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersRejects
example := @Syntax.DeclarativeGrammar.optionalTypeAliasParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueBoundaryStops
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryStops
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryScanParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryRejects
example := @Syntax.DeclarativeGrammar.typeAliasValueRecoveryDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueCoreRejectsWithPreservedWindow
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRejects
example := @Syntax.DeclarativeGrammar.typeAliasValueDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasDeclRejects
example := @Syntax.DeclarativeGrammar.typeAliasDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalEnumConstructorFieldsOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalEnumConstructorFieldsRejects
example := @Syntax.DeclarativeGrammar.optionalEnumConstructorFieldsDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.EnumConstructorOrdinaryParses
example := @Syntax.DeclarativeGrammar.EnumConstructorRejects
example := @Syntax.DeclarativeGrammar.enumConstructorDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.EnumBodyOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.EnumBodyRejects
example := @Syntax.DeclarativeGrammar.enumBodyDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.EnumDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.EnumDeclRejects
example := @Syntax.DeclarativeGrammar.enumDeclDeterministicOutcomeSpec
example := @Syntax.Parser.predicate_reject_sound
example := @Syntax.Parser.predicate_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.groupedPredicates_reject_sound
example := @Syntax.Parser.PredicateInternals.groupedPredicates_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.barePredicates_reject_sound
example := @Syntax.Parser.PredicateInternals.barePredicates_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.predicateSequence_reject_sound
example := @Syntax.Parser.PredicateInternals.predicateSequence_ordinaryOutcome_sound
example := @Syntax.Parser.whereClause_reject_sound
example := @Syntax.Parser.whereClause_ordinaryOutcome_sound
example := @Syntax.Parser.returnClause_reject_sound
example := @Syntax.Parser.returnClause_ordinaryOutcome_sound
example := @Syntax.Parser.genericParameters_reject_sound
example := @Syntax.Parser.genericParameters_ordinaryOutcome_sound
example := @Syntax.Parser.optionalGenericParameters_reject_sound
example := @Syntax.Parser.optionalGenericParameters_ordinaryOutcome_sound
example := @Syntax.Parser.FunctionParameterInternals.namedParameterCore_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_success_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_reject_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_ordinaryOutcomeSpec
example := @Syntax.Parser.functionParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_ordinaryOutcomeSpec
example := @Syntax.Parser.functionSignature_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_ordinaryOutcomeSpec
example := @Syntax.Parser.functionDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.ImplInternals.implMethod_success_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.entryParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.implicitPublicModifiers_ne_reject
example := @Syntax.Parser.constructorDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.fallbackDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractField_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_ordinaryOutcomeSpec
example := @Syntax.Parser.parseTypeAliasParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_ordinaryOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValueAux_success_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_success_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_reject_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_ordinaryOutcomeSpec
example := @Syntax.Parser.typeAlias_success_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_reject_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructorFields_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumConstructorFields_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructor_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumConstructor_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumBody_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumBody_ordinaryOutcomeSpec
example := @Syntax.Parser.enumDecl_ordinaryOutcome_sound
example := @Syntax.Parser.enumDecl_ordinaryOutcomeSpec

example {input output : Syntax.Parser.State} {field : ContractField}
    (result : Syntax.Parser.ContractInternals.contractField
      Syntax.Parser.expression input = .ok field output) :
    Syntax.DeclarativeGrammar.ContractFieldOrdinaryParses
      Syntax.DeclarativeGrammar.CoreExpressionOrdinaryParses
        input.declarativeRemainder field output.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractField_success_ordinaryOutcome_sound
    Syntax.Parser.expression
    Syntax.DeclarativeGrammar.CoreExpressionOrdinaryParses
    Syntax.Parser.expression_ordinaryOutcome_sound.1 result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.ContractInternals.contractField
      Syntax.Parser.expression input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractFieldRejects
      Syntax.DeclarativeGrammar.CoreExpressionOrdinaryParses
      Syntax.DeclarativeGrammar.CoreExpressionPublicRejects
        input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractField_reject_ordinaryOutcome_sound
    Syntax.Parser.expression
    Syntax.DeclarativeGrammar.CoreExpressionOrdinaryParses
    Syntax.DeclarativeGrammar.CoreExpressionPublicRejects
    Syntax.Parser.expression_ordinaryOutcome_sound.1
    Syntax.Parser.expression_ordinaryOutcome_sound.2 result

example {input output : Syntax.Parser.State} {declaration : TypeAliasDecl}
    (result : Syntax.Parser.typeAlias input = .ok declaration output) :
    Syntax.DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder :=
  Syntax.Parser.typeAlias_success_ordinaryOutcome_sound result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.typeAlias input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.TypeAliasDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.typeAlias_reject_ordinaryOutcome_sound result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.enumDecl none input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.EnumDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.enumDecl_reject_ordinaryOutcome_sound none result

end Tests
