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
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses
example := @Syntax.Parser.parseLexed_ok_publicSourceFileOrdinary_sound
example := @Syntax.Parser.parse_ok_publicSourceFileOrdinary_sound
example := @Syntax.Parser.parseLexed_eq_ok_of_nestingExceeds
example := @Syntax.Parser.parseLexed_ok_parseDiagnostics_eq_of_nestingExceeds
example := @Syntax.Parser.parseLexed_ok_sourceFile_executionWitness_of_nestingClears
example := @Syntax.Parser.parseLexed_ok_parseDiagnostics_executionWitness_of_nestingClears
example := @Syntax.Parser.parse_ok_sourceFile_executionWitness_of_nestingClears
example := @Syntax.Parser.productionParseLexed_exists_ok_publicSourceFileOrdinary
example := @Syntax.Parser.productionParse_exists_ok_publicSourceFileOrdinary
example := @Syntax.DeclarativeGrammar.LexedFileValidationOutcome
example := @Syntax.DeclarativeGrammar.LexedFileValidationRejects
example := @Syntax.DeclarativeGrammar.DelimitedTailRejects.output_unique
example := @Syntax.DeclarativeGrammar.DelimitedListRejects.output_unique
example := @Syntax.DeclarativeGrammar.NoTrailingDelimitedTailParses.result_unique
example := @Syntax.DeclarativeGrammar.NoTrailingDelimitedListParses.value_unique
example := @Syntax.DeclarativeGrammar.nonemptyNoTrailingDelimitedListExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.noTrailingDelimitedListExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TrailingDelimitedTailParses.result_unique
example := @Syntax.DeclarativeGrammar.NonemptyTrailingDelimitedListParses.value_unique
example := @Syntax.DeclarativeGrammar.TrailingDelimitedListParses.value_unique
example := @Syntax.DeclarativeGrammar.nonemptyTrailingDelimitedListExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.trailingDelimitedListExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TransactionalFallbackOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.TransactionalFallbackOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TransactionalFallbackRejects.output_unique
example := @Syntax.DeclarativeGrammar.transactionalFallbackExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TransactionalFallbackOrdinaryParses.value_unique_of_success
example := @Syntax.DeclarativeGrammar.TransactionalFallbackOrdinaryParses.result_unique_of_success
example := @Syntax.DeclarativeGrammar.transactionalFallbackExactOutcomeSpecOfSuccess
example := @Syntax.DeclarativeGrammar.DottedIdentifierTailParses.value_unique
example := @Syntax.DeclarativeGrammar.QualifiedNameParses.value_unique
example := @Syntax.DeclarativeGrammar.QualifiedNameParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeQualifiedNameTailRejects.output_unique
example := @Syntax.DeclarativeGrammar.TypeQualifiedNameRejects.output_unique
example := @Syntax.DeclarativeGrammar.typeQualifiedNameExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionTypeReturnsRejects.output_unique
example := @Syntax.DeclarativeGrammar.FunctionTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.ComptimeTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.MappingTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.ProxyTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.TupleTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.NamedTypeArgumentsRejects.output_unique
example := @Syntax.DeclarativeGrammar.NamedTypeRejects.output_unique
example := @Syntax.DeclarativeGrammar.TypeExprCoreRejects.output_unique
example := @Syntax.DeclarativeGrammar.TypeExprParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeExprParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeExprTrailingDelimitedTailParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeExprTrailingDelimitedTailParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeExprTrailingDelimitedListParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeExprTrailingDelimitedListParses.result_unique
example := @Syntax.DeclarativeGrammar.OptionalNamedTypeArgumentsParses.value_unique
example := @Syntax.DeclarativeGrammar.OptionalNamedTypeArgumentsParses.result_unique
example := @Syntax.DeclarativeGrammar.OptionalFunctionTypeReturnsParses.value_unique
example := @Syntax.DeclarativeGrammar.OptionalFunctionTypeReturnsParses.result_unique
example := @Syntax.DeclarativeGrammar.typeExprExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.TypeExprRejects.output_unique
example := @Syntax.DeclarativeGrammar.typeExprExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.coreBlockExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.coreBlockPublicExactOutcomeSpecOfStatementFuel
example := @Syntax.DeclarativeGrammar.isolatedCoreBlockExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.isolatedCoreBlockPublicExactOutcomeSpecOfStatementFuel
example := @Syntax.Parser.typeExprWithFuel_exactOutcomeSpec
example := @Syntax.Parser.typeExprWithFuel_success_result_unique
example := @Syntax.Parser.typeExprWithFuel_reject_output_unique
example := @Syntax.Parser.typeExpr_exactOutcomeSpec
example := @Syntax.Parser.block_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.block_success_result_unique_of_statementFuel
example := @Syntax.Parser.block_reject_output_unique_of_statementFuel
example := @Syntax.Parser.isolatedCoreBlockPublic_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.isolatedCoreBlockPublic_success_result_unique_of_statementFuel
example := @Syntax.Parser.isolatedCoreBlockPublic_reject_output_unique_of_statementFuel
example := @Syntax.DeclarativeGrammar.coreExpressionExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.coreExpressionPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.CoreExpressionOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.CoreExpressionPublicRejects.output_unique
example := @Syntax.Parser.TermInternals.coreExpressionWithFuel_exactOutcomeSpec
example := @Syntax.Parser.TermInternals.coreExpressionWithFuel_success_result_unique
example := @Syntax.Parser.TermInternals.coreExpressionWithFuel_reject_output_unique
example := @Syntax.DeclarativeGrammar.corePatternExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.corePatternPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.CorePatternOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.CorePatternPublicRejects.output_unique
example := @Syntax.Parser.TermInternals.corePatternWithFuel_exactOutcomeSpec
example := @Syntax.Parser.TermInternals.corePatternWithFuel_success_result_unique
example := @Syntax.Parser.TermInternals.corePatternWithFuel_reject_output_unique
example := @Syntax.DeclarativeGrammar.coreStatementExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.coreStatementPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.CoreStatementOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.CoreStatementPublicRejects.output_unique
example := @Syntax.Parser.TermInternals.coreStatementWithFuel_exactOutcomeSpec
example := @Syntax.Parser.TermInternals.coreStatementWithFuel_success_result_unique
example := @Syntax.Parser.TermInternals.coreStatementWithFuel_reject_output_unique
example := @Syntax.Parser.expression_exactOutcomeSpec
example := @Syntax.Parser.expression_success_result_unique
example := @Syntax.Parser.expression_reject_output_unique
example := @Syntax.Parser.pattern_exactOutcomeSpec
example := @Syntax.Parser.pattern_success_result_unique
example := @Syntax.Parser.pattern_reject_output_unique
example := @Syntax.Parser.statement_exactOutcomeSpec
example := @Syntax.Parser.statement_success_result_unique
example := @Syntax.Parser.statement_reject_output_unique
example := @Syntax.Parser.block_exactOutcomeSpec
example := @Syntax.Parser.block_success_result_unique
example := @Syntax.Parser.block_reject_output_unique
example := @Syntax.Parser.isolatedCoreBlockPublic_exactOutcomeSpec
example := @Syntax.Parser.isolatedCoreBlockPublic_success_result_unique
example := @Syntax.Parser.isolatedCoreBlockPublic_reject_output_unique
example := @Syntax.DeclarativeGrammar.coreBlockPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.isolatedCoreBlockPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.coreTermExactOutcomeSpecsWithFuel
example := @Syntax.DeclarativeGrammar.lambdaParameterPublicExactOutcomeSpec
example := @Syntax.Parser.lambdaParameter_exactOutcomeSpec
example := @Syntax.Parser.lambdaParameter_success_result_unique
example := @Syntax.Parser.lambdaParameter_reject_output_unique
example := @Syntax.DeclarativeGrammar.plainTopItemExactOutcomeSpec
example := @Syntax.Parser.constructorSelection_exactOutcomeSpec
example := @Syntax.Parser.constructorSelection_success_result_unique
example := @Syntax.Parser.constructorSelection_reject_output_unique
example := @Syntax.Parser.exportName_exactOutcomeSpec
example := @Syntax.Parser.exportName_success_result_unique
example := @Syntax.Parser.exportName_reject_output_unique
example := @Syntax.Parser.localExportItem_exactOutcomeSpec
example := @Syntax.Parser.localExportItem_success_result_unique
example := @Syntax.Parser.localExportItem_reject_output_unique
example := @Syntax.Parser.exportSelection_exactOutcomeSpec
example := @Syntax.Parser.exportSelection_success_result_unique
example := @Syntax.Parser.exportSelection_reject_output_unique
example := @Syntax.Parser.localExport_exactOutcomeSpec
example := @Syntax.Parser.localExport_success_result_unique
example := @Syntax.Parser.localExport_reject_output_unique
example := @Syntax.Parser.pathExport_exactOutcomeSpec
example := @Syntax.Parser.pathExport_success_result_unique
example := @Syntax.Parser.pathExport_reject_output_unique
example := @Syntax.Parser.exportDecl_exactOutcomeSpec
example := @Syntax.Parser.exportDecl_success_result_unique
example := @Syntax.Parser.exportDecl_reject_output_unique
example := @Syntax.DeclarativeGrammar.ConstructorNamesParses.result_unique
example := @Syntax.DeclarativeGrammar.OptionalConstructorSelectionParses.result_unique
example := @Syntax.DeclarativeGrammar.topItemExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.fileItemsExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.sourceFileExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.PlainTopItemOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TopItemOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.PlainTopItemRejects.output_unique
example := @Syntax.DeclarativeGrammar.TopItemRejects.output_unique
example := @Syntax.DeclarativeGrammar.FileItemsOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.SourceFileOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses.validFor_of_validation
example := @Syntax.DeclarativeGrammar.publicSourceFileOrdinary_exists_unique_of_validation
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses.validFor_of_lexing
example := @Syntax.Parser.FileInternals.plainTopItem_exactOutcomeSpec
example := @Syntax.Parser.FileInternals.plainTopItem_success_result_unique
example := @Syntax.Parser.FileInternals.plainTopItem_reject_output_unique
example := @Syntax.Parser.FileInternals.topItem_exactOutcomeSpec
example := @Syntax.Parser.FileInternals.topItem_success_result_unique
example := @Syntax.Parser.FileInternals.topItem_reject_output_unique
example := @Syntax.Parser.FileInternals.parseItems_exactOutcomeSpec
example := @Syntax.Parser.FileInternals.parseItems_success_result_unique
example := @Syntax.Parser.FileInternals.sourceFile_exactOutcomeSpec
example := @Syntax.Parser.FileInternals.sourceFile_success_result_unique
example := @Syntax.Parser.parseLexed_ok_parsed_value_unique
example := @Syntax.Parser.parse_ok_parsed_value_unique
example := @Syntax.Parser.ordinary_success_iff_exists_ok
example := @Syntax.Parser.functionDecl_ordinary_success_iff
example := @Syntax.Parser.functionDecl_ordinary_reject_iff
example := @Syntax.Parser.constructorDecl_ordinary_success_iff
example := @Syntax.Parser.constructorDecl_ordinary_reject_iff
example := @Syntax.Parser.fallbackDecl_ordinary_success_iff
example := @Syntax.Parser.fallbackDecl_ordinary_reject_iff
example := @Syntax.Parser.implDecl_ordinary_success_iff
example := @Syntax.Parser.implDecl_ordinary_reject_iff
example := @Syntax.Parser.contractDecl_ordinary_success_iff
example := @Syntax.Parser.contractDecl_ordinary_reject_iff
example := @Syntax.Parser.ContractInternals.contractFieldPublic_ordinary_success_iff
example := @Syntax.Parser.ContractInternals.contractFieldPublic_ordinary_reject_iff
example := @Syntax.Parser.ContractInternals.contractMemberCore_ordinary_success_iff
example := @Syntax.Parser.ContractInternals.contractMemberCore_ordinary_reject_iff
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_ordinary_success_iff
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_ordinary_reject_iff
example := @Syntax.Parser.ContractInternals.contractBody_ordinary_success_iff
example := @Syntax.Parser.ContractInternals.contractBody_ordinary_reject_iff
example := @Syntax.Parser.ContractInternals.recoverContractMember_ordinary_success_iff
example := @Syntax.Parser.ContractInternals.recoverContractMember_ordinary_reject_iff
example := @Syntax.Parser.typeAlias_ordinary_success_iff
example := @Syntax.Parser.typeAlias_ordinary_reject_iff
example := @Syntax.Parser.enumDecl_ordinary_success_iff
example := @Syntax.Parser.enumDecl_ordinary_reject_iff
example := @Syntax.Parser.traitDecl_ordinary_success_iff
example := @Syntax.Parser.traitDecl_ordinary_reject_iff
example := @Syntax.Parser.deriveTarget_ordinary_success_iff
example := @Syntax.Parser.deriveTarget_ordinary_reject_iff
example := @Syntax.Parser.deriveAttributeValid_ordinary_success_iff
example := @Syntax.Parser.deriveAttributeValid_ordinary_reject_iff
example := @Syntax.Parser.deriveAttributeRecovered_ordinary_success_iff
example := @Syntax.Parser.deriveAttributeRecovered_ordinary_reject_iff
example := @Syntax.Parser.deriveAttribute_ordinary_success_iff
example := @Syntax.Parser.deriveAttribute_ordinary_reject_iff
example := @Syntax.Parser.yulExpression_ordinary_success_iff
example := @Syntax.Parser.yulExpression_ordinary_reject_iff
example := @Syntax.Parser.yulStatement_ordinary_success_iff
example := @Syntax.Parser.yulStatement_ordinary_reject_iff
example := @Syntax.Parser.yulBody_ordinary_success_iff
example := @Syntax.Parser.yulBody_ordinary_reject_iff
example := @Syntax.Parser.yulExpression_boundary_reject_iff
example := @Syntax.Parser.yulStatement_boundary_reject_iff
example := @Syntax.Parser.ordinary_reject_iff_exists_reject
example := @Syntax.Parser.expression_ordinary_success_iff
example := @Syntax.Parser.expression_ordinary_reject_iff
example := @Syntax.Parser.pattern_ordinary_success_iff
example := @Syntax.Parser.pattern_ordinary_reject_iff
example := @Syntax.Parser.statement_ordinary_success_iff
example := @Syntax.Parser.statement_ordinary_reject_iff
example := @Syntax.Parser.typeExpr_ordinary_success_iff
example := @Syntax.Parser.typeExpr_ordinary_reject_iff
example := @Syntax.Parser.lambdaParameter_ordinary_success_iff
example := @Syntax.Parser.lambdaParameter_ordinary_reject_iff
example := @Syntax.Parser.block_ordinary_success_iff
example := @Syntax.Parser.block_ordinary_reject_iff
example := @Syntax.Parser.isolatedCoreBlockPublic_ordinary_success_iff
example := @Syntax.Parser.isolatedCoreBlockPublic_ordinary_reject_iff
example := @Syntax.Parser.importDecl_ordinary_success_iff
example := @Syntax.Parser.importDecl_ordinary_reject_iff
example := @Syntax.Parser.exportDecl_ordinary_success_iff
example := @Syntax.Parser.exportDecl_ordinary_reject_iff
example := @Syntax.Parser.pragmaDecl_ordinary_success_iff
example := @Syntax.Parser.pragmaDecl_ordinary_reject_iff
example := @Syntax.Parser.FileInternals.plainTopItem_ordinary_success_iff
example := @Syntax.Parser.FileInternals.plainTopItem_ordinary_reject_iff
example := @Syntax.Parser.FileInternals.topItem_ordinary_success_iff
example := @Syntax.Parser.FileInternals.topItem_ordinary_reject_iff
example := @Syntax.Parser.FileInternals.sourceFile_ordinary_iff_exists_ok
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinary_success_iff
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinary_reject_iff
example := @Syntax.Parser.FileInternals.parseItems_ordinary_success_iff_of_remainingCount_lt
example := @Syntax.Parser.FileInternals.parseItems_production_ordinary_success_iff
example := @Syntax.Parser.FileInternals.sourceFile_ordinary_iff_exists_ok_of_topItem
example := @Syntax.Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary
example := @Syntax.Parser.parseLexed_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @Syntax.Parser.parse_exists_ok_iff_publicSourceFileOrdinary
example := @Syntax.Parser.parse_exists_ok_iff_publicSourceFileOrdinary_of_topItem
example := @Syntax.DeclarativeGrammar.topItemRecoveryExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.topItemRecoveryTraceParses_iff
example := @Syntax.DeclarativeGrammar.topItemRecoveryTraceRejects_iff
example := @Syntax.DeclarativeGrammar.LexicalCascadeFilters.output_unique
example := @Syntax.DeclarativeGrammar.lexicalCascadeFilters_total
example := @Syntax.DeclarativeGrammar.lexicalCascadeFilters_nil_lexical
example := @Syntax.DeclarativeGrammar.lexicalCascadeFilters_singleton_iff
example := @Syntax.Parser.FileInternals.finishRecoveredTopItem_success_diagnosticsRev_eq
example := @Syntax.Parser.FileInternals.recoverTopItemAux_success_diagnosticsRev_eq
example := @Syntax.Parser.FileInternals.recoverTopItem_success_diagnosticsRev_eq
example := @Syntax.Parser.FileInternals.finishRecoveredTopItem_success_diagnostics_eq
example := @Syntax.Parser.FileInternals.recoverTopItemAux_success_diagnostics_eq
example := @Syntax.Parser.FileInternals.recoverTopItem_success_diagnostics_eq
example := @Syntax.Parser.FileInternals.recoverTopItem_reject_diagnosticsRev_eq
example := @Syntax.Parser.FileInternals.recoverTopItem_reject_diagnostics_eq
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinary_success_iff_with_trace
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinary_reject_iff_with_trace
example := @Syntax.Parser.FileInternals.topItemRecoveryDiagnostics_spans
example := @Syntax.Parser.FileInternals.topItemRecoveryDiagnostics_injective
example := @Syntax.Parser.FileInternals.recoverTopItem_trace_success_iff
example := @Syntax.Parser.FileInternals.recoverTopItem_trace_reject_iff
example := @Syntax.Parser.FileInternals.atTopItemStart_eq_false_of_topItemStartAbsent
example := @Syntax.Parser.FileInternals.parseItemsItem_eq_rejectAt_of_topItemStartAbsent
example := @Syntax.Parser.FileInternals.recoveredTopItem_eq_error
example := @Syntax.Parser.FileInternals.parseItems_singleRecoveryToEnd_exact
example := @Syntax.Parser.FileInternals.parseItems_production_singleRecoveryToEnd_exact
example := @Syntax.Parser.FileInternals.sourceFile_singleRecoveryToEnd_exact
example := @Syntax.Parser.filterParseDiagnostics_cons_recovered_of_suppressed
example := @Syntax.Parser.filterParseDiagnostics_cons_recovered_of_retained
example := @Syntax.Parser.filterParseDiagnostics_nil_parsed
example := @Syntax.Parser.filterParseDiagnostics_recoveredTopItems_of_filters
example := @Syntax.Parser.filterParseDiagnostics_recoveredTopItems_iff
example := @Syntax.Parser.filterParseDiagnostics_cons_unexpected_of_suppressed
example := @Syntax.Parser.filterParseDiagnostics_cons_unexpected_of_retained
example := @Syntax.Parser.unexpectedDiagnostics_spans
example := @Syntax.Parser.filterParseDiagnostics_unexpected_of_filters
example := @Syntax.Parser.filterParseDiagnostics_unexpected_iff
example := @Syntax.Parser.FileInternals.parseItems_boundaryStop_trace_exact
example := @Syntax.Parser.FileInternals.sourceFile_boundaryStop_trace_exact
example := @Syntax.Parser.parseLexed_eq_ok_singleRecovery_iff
example := @Syntax.Parser.parseLexed_eq_ok_of_singleRecoveryToEnd
example := @Syntax.Parser.parse_eq_ok_singleRecovery_iff
example := @Syntax.Parser.parse_eq_ok_of_singleRecoveryToEnd
example := @Syntax.DeclarativeGrammar.currentInputAt_total
example := @Syntax.DeclarativeGrammar.CurrentInputAt.result_unique
example := @Syntax.DeclarativeGrammar.rejectAtReports_total
example := @Syntax.DeclarativeGrammar.RejectAtReports.diagnostic_unique
example := @Syntax.Parser.currentInputAt_currentSpan_peekKind
example := @Syntax.Parser.currentInputAt_iff_currentSpan_peekKind
example := @Syntax.Parser.Failure.toDiagnostic_injective
example := @Syntax.Parser.rejectAt_reports_iff
example := @Syntax.Parser.rejectAt_reject_reports
example := @Syntax.Parser.rawIdentifier_eq_rejectAt_of_identifierAbsent
example := @Syntax.Parser.identifier_eq_rejectAt_of_identifierAbsent
example := @Syntax.Parser.rawIdentifier_reject_reports_iff
example := @Syntax.Parser.identifier_reject_reports_iff
example := @Syntax.Parser.rawIdentifier_reject_diagnostics_eq
example := @Syntax.Parser.identifier_reject_diagnostics_eq
example := @Syntax.DeclarativeGrammar.PragmaNameMissingAt.rejects
example := @Syntax.Parser.peekKind_eq_pragma_of_exactTokenParses
example := @Syntax.Parser.pragmaKeyword_eq_ok_of_exactTokenParses
example := @Syntax.Parser.FileInternals.atTopItemStart_eq_true_of_pragmaToken
example := @Syntax.Parser.FileInternals.plainTopItem_eq_pragma_of_exactTokenParses
example := @Syntax.Parser.FileInternals.topItem_eq_pragma_of_exactTokenParses
example := @Syntax.Parser.pragmaDecl_nameMissing_exact
example := @Syntax.Parser.pragmaDecl_nameMissingAt_exact
example := @Syntax.Parser.FileInternals.plainTopItem_pragmaNameMissing_exact
example := @Syntax.Parser.FileInternals.topItem_pragmaNameMissing_exact
example := @Syntax.Parser.FileInternals.parseItemsItem_pragmaNameMissing_exact
example := @Syntax.Parser.FileInternals.parseItemsItem_pragmaNameMissingAt_exact
example := @Syntax.Parser.parseLexed_eq_ok_pragmaNameMissing_iff
example := @Syntax.Parser.parseLexed_eq_ok_of_pragmaNameMissing
example := @Syntax.Parser.parse_eq_ok_pragmaNameMissing_iff
example := @Syntax.Parser.parse_eq_ok_of_pragmaNameMissing
example := @Syntax.DeclarativeGrammar.ParseDiagnosticCascadeFilters.output_unique
example := @Syntax.DeclarativeGrammar.parseDiagnosticCascadeFilters_total
example := @Syntax.DeclarativeGrammar.parseDiagnosticCascadeFilters_protected_cons
example := @Syntax.DeclarativeGrammar.ParseDiagnosticCascadeFilters.sublist
example := @Syntax.DeclarativeGrammar.parseDiagnosticCascadeFilters_nil_lexical
example := @Syntax.Parser.filterParseDiagnostics_cons_of_suppressed
example := @Syntax.Parser.filterParseDiagnostics_cons_of_retained
example := @Syntax.Parser.filterParseDiagnostics_eq_of_cascadeFilters
example := @Syntax.Parser.filterParseDiagnostics_eq_iff_cascadeFilters
example := @Syntax.DeclarativeGrammar.identifierHyphenSpelling_iff_contains
example := @Syntax.DeclarativeGrammar.identifierDiagnosticTrace_total
example := @Syntax.DeclarativeGrammar.IdentifierDiagnosticTrace.trace_unique
example := @Syntax.DeclarativeGrammar.rawIdentifierTraceParses_iff
example := @Syntax.DeclarativeGrammar.identifierTraceParses_iff
example := @Syntax.DeclarativeGrammar.RawIdentifierTraceParses.result_unique
example := @Syntax.DeclarativeGrammar.IdentifierTraceParses.result_unique
example := @Syntax.Parser.rawIdentifier_success_diagnostics_eq
example := @Syntax.Parser.rawIdentifier_success_trace_sound
example := @Syntax.Parser.identifier_success_diagnosticTrace
example := @Syntax.Parser.identifier_success_diagnostics_eq_of_trace
example := @Syntax.Parser.identifier_success_trace_sound
example := @Syntax.Parser.rawIdentifier_trace_success_iff
example := @Syntax.Parser.identifier_trace_success_iff
example := @Syntax.Parser.acceptToken_eq_ok_of_exactTokenParses
example := @Syntax.Parser.acceptToken_success_diagnostics_eq
example := @Syntax.Parser.acceptToken_exactToken_success_iff
example := @Syntax.Parser.keyword_eq_ok_of_exactTokenParses
example := @Syntax.Parser.symbol_eq_ok_of_exactTokenParses
example := @Syntax.Parser.contextual_eq_ok_of_exactTokenParses
example := @Syntax.Parser.keyword_exactToken_success_iff
example := @Syntax.Parser.symbol_exactToken_success_iff
example := @Syntax.Parser.contextual_exactToken_success_iff
example := @Syntax.Parser.keyword_eq_rejectAt_of_tokenKindAbsent
example := @Syntax.Parser.symbol_eq_rejectAt_of_tokenKindAbsent
example := @Syntax.Parser.contextual_eq_rejectAt_of_tokenKindAbsent
example := @Syntax.Parser.keyword_reject_reports_iff
example := @Syntax.Parser.symbol_reject_reports_iff
example := @Syntax.Parser.contextual_reject_reports_iff
example := @Syntax.Parser.acceptToken_reject_reports
example := @Syntax.Parser.keyword_reject_diagnostics_eq
example := @Syntax.Parser.symbol_reject_diagnostics_eq
example := @Syntax.Parser.contextual_reject_diagnostics_eq
example := @Syntax.Parser.FileInternals.parseItems_singleSuccessToEnd_exact
example := @Syntax.Parser.FileInternals.parseItems_production_singleSuccessToEnd_exact
example := @Syntax.Parser.FileInternals.sourceFile_singleSuccessToEnd_exact
example := @Syntax.DeclarativeGrammar.ParseDiagnosticCascadeFilters.append
example := @Syntax.DeclarativeGrammar.parseDiagnosticCascadeFilters_of_protected
example := @Syntax.DeclarativeGrammar.IdentifierDiagnosticTrace.not_candidate
example := @Syntax.DeclarativeGrammar.IdentifierDiagnosticTrace.cascadeFilters
example := @Syntax.DeclarativeGrammar.identifierListDiagnosticTrace_total
example := @Syntax.DeclarativeGrammar.IdentifierListDiagnosticTrace.trace_unique
example := @Syntax.DeclarativeGrammar.IdentifierListDiagnosticTrace.append
example := @Syntax.DeclarativeGrammar.PragmaItemsTailTraceParses.result_unique
example := @Syntax.DeclarativeGrammar.PragmaItemsTraceParses.result_unique
example := @Syntax.DeclarativeGrammar.PragmaDeclTraceParses.result_unique
example := @Syntax.DeclarativeGrammar.IdentifierListDiagnosticTrace.cascadeFilters
example := @Syntax.DeclarativeGrammar.PragmaDeclTraceParses.cascadeFilters
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_success_diagnosticTrace
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_production_success_trace_sound
example := @Syntax.Parser.PragmaInternals.pragmaItems_success_diagnosticTrace
example := @Syntax.Parser.PragmaInternals.pragmaItems_success_diagnostics_eq_of_trace
example := @Syntax.Parser.PragmaInternals.pragmaItems_success_trace_sound
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_production_success_diagnostics_eq_of_trace
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_production_trace_success_iff
example := @Syntax.Parser.PragmaInternals.pragmaItems_trace_success_iff
example := @Syntax.Parser.pragmaDecl_success_diagnosticTrace
example := @Syntax.Parser.pragmaDecl_success_diagnostics_eq_of_trace
example := @Syntax.Parser.pragmaDecl_success_trace_sound
example := @Syntax.Parser.pragmaDecl_trace_success_iff
example := @Syntax.Parser.parseLexed_eq_ok_singlePragma_iff
example := @Syntax.Parser.parseLexed_eq_ok_of_singlePragma
example := @Syntax.Parser.parse_eq_ok_singlePragma_iff
example := @Syntax.Parser.parse_eq_ok_of_singlePragma
example := @Syntax.Parser.parseLexed_eq_ok_of_singlePragmaTrace
example := @Syntax.Parser.parse_eq_ok_of_singlePragmaTrace
example := @Syntax.Parser.emitDiagnostic_success_trace
example := @Syntax.Parser.bind_success_trace
example := @Syntax.Parser.bind_reject_right_trace
example := @Syntax.Parser.bind_reject_left_trace
example := @Syntax.Parser.map_success_trace
example := @Syntax.Parser.map_reject_trace
example := @Syntax.Parser.bind_invariant_left_exact
example := @Syntax.Parser.orElse_eq_right_of_reject
example := @Syntax.Parser.orElse_success_left_trace
example := @Syntax.Parser.orElse_success_right_trace
example := @Syntax.Parser.orElse_reject_right_trace
example := @Syntax.Parser.orElse_invariant_left_exact
example := @Syntax.Parser.orElse_invariant_right_exact
example := @Syntax.Parser.sourceFile_atWindowEnd_exact
example := @Syntax.Parser.parseLexed_eq_ok_emptyTokens_iff
example := @Syntax.Parser.parseLexed_eq_ok_of_emptyTokens
example := @Syntax.Parser.parse_eq_ok_of_emptyTokens
example := @Syntax.DeclarativeGrammar.ParseDiagnosticCascadeFilters.retained_not_suppressed
example := @Syntax.DeclarativeGrammar.parseDiagnosticCascadeFilters_of_retained
example := @Syntax.DeclarativeGrammar.ParseDiagnosticCascadeFilters.stable
example := @Syntax.Parser.filterParseDiagnostics_idempotent
example := @Syntax.Parser.filterParseDiagnostics_append
example := @Syntax.DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItemValues
example := @Syntax.DeclarativeGrammar.fileItemsExactOutcomeSpecOfTopItem
example := @Syntax.DeclarativeGrammar.sourceFileExactOutcomeSpecOfFileItems
example := @Syntax.DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItemValues
example := @Syntax.DeclarativeGrammar.sourceFileExactOutcomeSpecOfTopItem
example := @Syntax.DeclarativeGrammar.FileItemsRejects.output_unique
example := @Syntax.DeclarativeGrammar.SourceFileRejects.output_unique
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_topItem
example := @Syntax.DeclarativeGrammar.PublicSourceFileOrdinaryParses.value_unique_of_exact_topItem
example := @Syntax.Parser.FileInternals.recoverTopItem_exactOutcomeSpec
example := @Syntax.Parser.FileInternals.recoverTopItem_success_result_unique
example := @Syntax.Parser.FileInternals.recoverTopItem_reject_output_unique
example := @Syntax.Parser.FileInternals.parseItems_exactOutcomeSpec_of_topItemValues
example := @Syntax.Parser.FileInternals.parseItems_exactOutcomeSpec_of_topItem
example := @Syntax.Parser.FileInternals.parseItems_success_result_unique_of_topItemValues
example := @Syntax.Parser.FileInternals.parseItems_success_result_unique_of_topItem
example := @Syntax.Parser.FileInternals.parseItems_reject_output_unique
example := @Syntax.Parser.FileInternals.sourceFile_exactOutcomeSpec_of_topItemValues
example := @Syntax.Parser.FileInternals.sourceFile_exactOutcomeSpec_of_topItem
example := @Syntax.Parser.FileInternals.sourceFile_success_result_unique_of_topItemValues
example := @Syntax.Parser.FileInternals.sourceFile_success_result_unique_of_topItem
example := @Syntax.Parser.FileInternals.sourceFile_reject_output_unique
example := @Syntax.Parser.parseLexed_ok_parsed_value_unique_of_topItemValues
example := @Syntax.Parser.parseLexed_ok_parsed_value_unique_of_topItem
example := @Syntax.Parser.parse_ok_parsed_value_unique_of_topItemValues
example := @Syntax.Parser.parse_ok_parsed_value_unique_of_topItem
example := @Syntax.DeclarativeGrammar.selectedAliasExactOutcomeSpec
example := @Syntax.Parser.selectedAlias_exactOutcomeSpec
example := @Syntax.Parser.selectedAlias_success_result_unique
example := @Syntax.Parser.selectedAlias_reject_output_unique
example := @Syntax.DeclarativeGrammar.selectedImportExactOutcomeSpec
example := @Syntax.Parser.selectedImport_exactOutcomeSpec
example := @Syntax.Parser.selectedImport_success_result_unique
example := @Syntax.Parser.selectedImport_reject_output_unique
example := @Syntax.DeclarativeGrammar.selectedImportsExactOutcomeSpec
example := @Syntax.Parser.selectedImports_exactOutcomeSpec
example := @Syntax.Parser.selectedImports_success_result_unique
example := @Syntax.Parser.selectedImports_reject_output_unique
example := @Syntax.DeclarativeGrammar.hidingClauseExactOutcomeSpec
example := @Syntax.Parser.hidingClause_exactOutcomeSpec
example := @Syntax.Parser.hidingClause_success_result_unique
example := @Syntax.Parser.hidingClause_reject_output_unique
example := @Syntax.DeclarativeGrammar.optionalHidingExactOutcomeSpec
example := @Syntax.Parser.optionalHiding_exactOutcomeSpec
example := @Syntax.Parser.optionalHiding_success_result_unique
example := @Syntax.Parser.optionalHiding_reject_output_unique
example := @Syntax.DeclarativeGrammar.plainImportExactOutcomeSpec
example := @Syntax.Parser.plainImport_exactOutcomeSpec
example := @Syntax.Parser.plainImport_success_result_unique
example := @Syntax.Parser.plainImport_reject_output_unique
example := @Syntax.DeclarativeGrammar.namespaceImportExactOutcomeSpec
example := @Syntax.Parser.namespaceImport_exactOutcomeSpec
example := @Syntax.Parser.namespaceImport_success_result_unique
example := @Syntax.Parser.namespaceImport_reject_output_unique
example := @Syntax.DeclarativeGrammar.wildcardImportExactOutcomeSpec
example := @Syntax.Parser.wildcardImport_exactOutcomeSpec
example := @Syntax.Parser.wildcardImport_success_result_unique
example := @Syntax.Parser.wildcardImport_reject_output_unique
example := @Syntax.DeclarativeGrammar.selectiveImportExactOutcomeSpec
example := @Syntax.Parser.selectiveImport_exactOutcomeSpec
example := @Syntax.Parser.selectiveImport_success_result_unique
example := @Syntax.Parser.selectiveImport_reject_output_unique
example := @Syntax.DeclarativeGrammar.importDeclExactOutcomeSpec
example := @Syntax.Parser.importDecl_exactOutcomeSpec
example := @Syntax.Parser.importDecl_success_result_unique
example := @Syntax.Parser.importDecl_reject_output_unique
example := @Syntax.DeclarativeGrammar.pragmaItemsTailExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.pragmaItemsExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.pragmaDeclExactOutcomeSpec
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_exactOutcomeSpec
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_production_success_result_unique
example := @Syntax.Parser.PragmaInternals.pragmaItemsTail_production_reject_output_unique
example := @Syntax.Parser.PragmaInternals.pragmaItems_exactOutcomeSpec
example := @Syntax.Parser.PragmaInternals.pragmaItems_success_result_unique
example := @Syntax.Parser.PragmaInternals.pragmaItems_reject_output_unique
example := @Syntax.Parser.pragmaDecl_exactOutcomeSpec
example := @Syntax.Parser.pragmaDecl_success_result_unique
example := @Syntax.Parser.pragmaDecl_reject_output_unique
example := @Syntax.DeclarativeGrammar.selectorNameExactOutcomeSpec
example := @Syntax.Parser.selectorName_exactOutcomeSpec
example := @Syntax.Parser.selectorName_success_result_unique
example := @Syntax.Parser.selectorName_reject_output_unique
example := @Syntax.DeclarativeGrammar.modulePathExactOutcomeSpec
example := @Syntax.Parser.modulePath_exactOutcomeSpec
example := @Syntax.Parser.modulePath_success_result_unique
example := @Syntax.Parser.modulePath_reject_output_unique
example := @Syntax.DeclarativeGrammar.exportPathExactOutcomeSpec
example := @Syntax.Parser.exportPath_exactOutcomeSpec
example := @Syntax.Parser.exportPath_success_result_unique
example := @Syntax.Parser.exportPath_reject_output_unique
example := @Syntax.DeclarativeGrammar.importTerminatorExactOutcomeSpec
example := @Syntax.Parser.importTerminator_exactOutcomeSpec
example := @Syntax.Parser.importTerminator_success_result_unique
example := @Syntax.Parser.importTerminator_reject_output_unique
example := @Syntax.DeclarativeGrammar.finishExportExactOutcomeSpec
example := @Syntax.Parser.finishExport_exactOutcomeSpec
example := @Syntax.Parser.finishExport_success_result_unique
example := @Syntax.Parser.finishExport_reject_output_unique
example := @Syntax.DeclarativeGrammar.functionDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.constructorDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.fallbackDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.implMethodExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.implBodyExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.implDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractMemberExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractBodyExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractFieldPublicExactOutcomeSpec
example := @Syntax.Parser.functionDecl_exactOutcomeSpec
example := @Syntax.Parser.functionDecl_success_result_unique
example := @Syntax.Parser.functionDecl_reject_output_unique
example := @Syntax.Parser.constructorDecl_exactOutcomeSpec
example := @Syntax.Parser.constructorDecl_success_result_unique
example := @Syntax.Parser.constructorDecl_reject_output_unique
example := @Syntax.Parser.fallbackDecl_exactOutcomeSpec
example := @Syntax.Parser.fallbackDecl_success_result_unique
example := @Syntax.Parser.fallbackDecl_reject_output_unique
example := @Syntax.Parser.implDecl_exactOutcomeSpec
example := @Syntax.Parser.implDecl_success_result_unique
example := @Syntax.Parser.implDecl_reject_output_unique
example := @Syntax.Parser.contractDecl_exactOutcomeSpec
example := @Syntax.Parser.contractDecl_success_result_unique
example := @Syntax.Parser.contractDecl_reject_output_unique
example := @Syntax.Parser.ImplInternals.implMethod_exactOutcomeSpec
example := @Syntax.Parser.ImplInternals.implMethod_success_result_unique
example := @Syntax.Parser.ImplInternals.implMethod_reject_output_unique
example := @Syntax.Parser.ImplInternals.implBody_exactOutcomeSpec
example := @Syntax.Parser.ImplInternals.implBody_success_result_unique
example := @Syntax.Parser.ImplInternals.implBody_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractFieldPublic_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractFieldPublic_success_result_unique
example := @Syntax.Parser.ContractInternals.contractFieldPublic_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractMemberCore_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractMemberCore_success_result_unique_unconditional
example := @Syntax.Parser.ContractInternals.contractMemberCore_reject_output_unique_unconditional
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_success_result_unique
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractBody_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractBody_success_result_unique
example := @Syntax.Parser.ContractInternals.contractBody_reject_output_unique

example := @Syntax.Parser.typeExpr_success_result_unique
example := @Syntax.Parser.typeExpr_reject_output_unique
example := @Syntax.Parser.validateLexed_reflects_outcome
example := @Syntax.Parser.productionParseLexed_error_iff_validationRejects
example := @Syntax.Parser.productionParseLexed_certifiedOutcome
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
example := @Syntax.DeclarativeGrammar.functionParameterRecoveryExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.functionParameterExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionParametersRejects
example := @Syntax.DeclarativeGrammar.functionParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.functionParametersExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionSignatureOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionSignatureRejects
example := @Syntax.DeclarativeGrammar.functionSignatureDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.functionSignatureExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.FunctionDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.FunctionDeclRejects
example := @Syntax.DeclarativeGrammar.functionDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplMethodOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImplMethodRejects
example := @Syntax.DeclarativeGrammar.implMethodDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalImplDefaultMarkerRejects
example := @Syntax.DeclarativeGrammar.optionalImplDefaultMarkerDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.OptionalImplDefaultMarkerOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.OptionalImplDefaultMarkerRejects.output_unique
example := @Syntax.DeclarativeGrammar.optionalImplDefaultMarkerExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImplHeadArgumentsRejects
example := @Syntax.DeclarativeGrammar.implHeadArgumentsDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.ImplHeadArgumentsOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.ImplHeadArgumentsRejects.output_unique
example := @Syntax.DeclarativeGrammar.implHeadArgumentsExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplMethodTailOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.ImplMethodTailRejects
example := @Syntax.DeclarativeGrammar.implMethodTailDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplMethodTailOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.ImplMethodTailOrdinaryOutcomeParses.value_unique
example := @Syntax.DeclarativeGrammar.ImplMethodTailRejects.output_unique
example := @Syntax.DeclarativeGrammar.implMethodTailExactOutcomeSpecOfMethod
example := @Syntax.DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.ImplBodyRejects
example := @Syntax.DeclarativeGrammar.implBodyDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplBodyOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.ImplBodyOrdinaryOutcomeParses.value_unique
example := @Syntax.DeclarativeGrammar.ImplBodyRejects.output_unique
example := @Syntax.DeclarativeGrammar.implBodyExactOutcomeSpecOfMethod
example := @Syntax.DeclarativeGrammar.implBodyExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.implBodyExactOutcomeSpecOfStatementFuel
example := @Syntax.DeclarativeGrammar.ImplDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImplDeclRejects
example := @Syntax.DeclarativeGrammar.implDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImplDeclOrdinaryParses.result_unique_of_impl_body
example := @Syntax.DeclarativeGrammar.ImplDeclRejects.output_unique_of_impl_body
example := @Syntax.DeclarativeGrammar.implDeclExactOutcomeSpecOfImplBody
example := @Syntax.DeclarativeGrammar.implDeclExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.implDeclExactOutcomeSpecOfStatementFuel
example := @Syntax.DeclarativeGrammar.ContractEntryModifiersOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalFunctionModifierParses.value_unique
example := @Syntax.DeclarativeGrammar.OptionalFunctionModifierParses.result_unique
example := @Syntax.DeclarativeGrammar.ContractEntryModifiersOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.ContractEntryModifiersOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.ConstructorDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ConstructorDeclRejects
example := @Syntax.DeclarativeGrammar.constructorDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ConstructorDeclOrdinaryParses.value_unique_of_exact_children
example := @Syntax.DeclarativeGrammar.ConstructorDeclOrdinaryParses.result_unique_of_exact_children
example := @Syntax.DeclarativeGrammar.ConstructorDeclRejects.output_unique_of_exact_children
example := @Syntax.DeclarativeGrammar.constructorDeclExactOutcomeSpecOfChildren
example := @Syntax.DeclarativeGrammar.constructorDeclExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.constructorDeclExactOutcomeSpecOfStatementFuel
example := @Syntax.DeclarativeGrammar.ConstructorDeclOrdinaryParses.result_unique_of_exact_body
example := @Syntax.DeclarativeGrammar.ConstructorDeclRejects.output_unique_of_exact_body
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
example := @Syntax.DeclarativeGrammar.ContractMemberCoreTokenPresentAt
example := @Syntax.DeclarativeGrammar.ContractMemberCoreOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractMemberCoreRejects
example := @Syntax.DeclarativeGrammar.contractMemberCoreDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractDeriveAttaches
example := @Syntax.DeclarativeGrammar.ContractMemberOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractMemberRejects
example := @Syntax.DeclarativeGrammar.contractMemberDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractMemberOrdinaryParses.value_unique_of_core
example := @Syntax.DeclarativeGrammar.ContractMemberOrdinaryParses.result_unique_of_core
example := @Syntax.DeclarativeGrammar.ContractMemberRejects.output_unique_of_core
example := @Syntax.DeclarativeGrammar.contractMemberExactOutcomeSpecOfCore
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryStops
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryScanParses
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryParses
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryRejects
example := @Syntax.DeclarativeGrammar.contractMemberRecoveryDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryScanParses.value_unique
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryScanParses.result_unique
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryParses.value_unique
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryParses.result_unique
example := @Syntax.DeclarativeGrammar.ContractMemberRecoveryRejects.output_unique
example := @Syntax.DeclarativeGrammar.contractMemberRecoveryExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractMemberRejectsWithPreservedWindow
example := @Syntax.DeclarativeGrammar.ContractMemberTailOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractMemberTailOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.ContractMemberTailRejects
example := @Syntax.DeclarativeGrammar.contractMemberTailDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractBodyOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractBodyOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.ContractBodyRejects
example := @Syntax.DeclarativeGrammar.contractBodyDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ContractDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ContractDeclRejects
example := @Syntax.DeclarativeGrammar.contractDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PlainTopItemTokenPresentAt
example := @Syntax.DeclarativeGrammar.PlainTopItemBranch
example := @Syntax.DeclarativeGrammar.PlainTopItemBranchSelected
example := @Syntax.DeclarativeGrammar.PlainTopItemOrdinaryParses
example := @Syntax.DeclarativeGrammar.PlainTopItemRejects
example := @Syntax.DeclarativeGrammar.plainTopItemDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TopItemDeriveAttaches
example := @Syntax.DeclarativeGrammar.TopItemOrdinaryParses
example := @Syntax.DeclarativeGrammar.TopItemRejects
example := @Syntax.DeclarativeGrammar.topItemDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TopItemRecoveryStops
example := @Syntax.DeclarativeGrammar.TopItemRecoveryScanParses
example := @Syntax.DeclarativeGrammar.TopItemRecoveryParses
example := @Syntax.DeclarativeGrammar.TopItemRecoveryRejects
example := @Syntax.DeclarativeGrammar.topItemRecoveryDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TopItemRejectsWithPreservedWindow
example := @Syntax.DeclarativeGrammar.FileItemsOrdinaryParses
example := @Syntax.DeclarativeGrammar.FileItemsRejects
example := @Syntax.DeclarativeGrammar.fileItemsDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SourceFileOrdinaryParses
example := @Syntax.DeclarativeGrammar.SourceFileRejects
example := @Syntax.DeclarativeGrammar.sourceFileDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasParametersRejects
example := @Syntax.DeclarativeGrammar.typeAliasParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.typeAliasParametersExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersRejects
example := @Syntax.DeclarativeGrammar.optionalTypeAliasParametersDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.OptionalTypeAliasParametersRejects.output_unique
example := @Syntax.DeclarativeGrammar.optionalTypeAliasParametersExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueBoundaryStops
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryStops
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryScanParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryRejects
example := @Syntax.DeclarativeGrammar.typeAliasValueRecoveryDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryScanParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryScanParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeAliasValueRecoveryRejects.output_unique
example := @Syntax.DeclarativeGrammar.typeAliasValueRecoveryExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueCoreRejectsWithPreservedWindow
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasValueRejects
example := @Syntax.DeclarativeGrammar.typeAliasValueDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses.value_unique_of_typeExpr
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
example := @Syntax.DeclarativeGrammar.TypeAliasValueRejects.output_unique
example := @Syntax.DeclarativeGrammar.typeAliasValueExactOutcomeSpecOfTypeExpr
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.typeAliasValueExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.TypeAliasDeclRejects
example := @Syntax.DeclarativeGrammar.typeAliasDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TypeAliasDeclOrdinaryParses.value_unique
example := @Syntax.DeclarativeGrammar.TypeAliasDeclOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TypeAliasDeclRejects.output_unique
example := @Syntax.DeclarativeGrammar.typeAliasDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveReservedComponentAbsentAt
example := @Syntax.DeclarativeGrammar.DeriveComponentRejects
example := @Syntax.DeclarativeGrammar.deriveComponentDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ExactDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.identifierExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.deriveComponentExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.deriveTargetTailExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.deriveTargetExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveTargetTailRejects
example := @Syntax.DeclarativeGrammar.deriveTargetTailDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveTargetRejects
example := @Syntax.DeclarativeGrammar.deriveTargetDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveAttributeValidRejects
example := @Syntax.DeclarativeGrammar.deriveAttributeValidDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveAttributeRecoveryDeclarationStartsAt
example := @Syntax.DeclarativeGrammar.DeriveAttributeRecoveryStops
example := @Syntax.DeclarativeGrammar.DeriveAttributeRecoveryTailParses
example := @Syntax.DeclarativeGrammar.DeriveAttributeRecoveredParses
example := @Syntax.DeclarativeGrammar.DeriveAttributeRecoveredRejects
example := @Syntax.DeclarativeGrammar.deriveAttributeRecoveredDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.DeriveAttributeOrdinaryParses
example := @Syntax.DeclarativeGrammar.DeriveAttributeRejects
example := @Syntax.DeclarativeGrammar.deriveAttributeDeterministicOutcomeSpec
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
example := @Syntax.DeclarativeGrammar.enumConstructorFieldListExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.optionalEnumConstructorFieldsExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.enumConstructorExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.enumBodyExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.enumDeclExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitMethodOrdinaryParses
example := @Syntax.DeclarativeGrammar.TraitMethodRejects
example := @Syntax.DeclarativeGrammar.traitMethodDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitMethodTailOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.TraitMethodTailRejects
example := @Syntax.DeclarativeGrammar.traitMethodTailDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitBodyOrdinaryOutcomeParses
example := @Syntax.DeclarativeGrammar.TraitBodyRejects
example := @Syntax.DeclarativeGrammar.traitBodyDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.TraitDeclRejects
example := @Syntax.DeclarativeGrammar.traitDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SelectorNameOrdinaryParses
example := @Syntax.DeclarativeGrammar.SelectorNameRejects
example := @Syntax.DeclarativeGrammar.selectorNameDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ModulePathOrdinaryParses
example := @Syntax.DeclarativeGrammar.ModulePathRejects
example := @Syntax.DeclarativeGrammar.modulePathDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SelectedAliasOrdinaryParses
example := @Syntax.DeclarativeGrammar.SelectedAliasRejects
example := @Syntax.DeclarativeGrammar.selectedAliasDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SelectedImportOrdinaryParses
example := @Syntax.DeclarativeGrammar.SelectedImportRejects
example := @Syntax.DeclarativeGrammar.selectedImportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SelectedImportsOrdinaryParses
example := @Syntax.DeclarativeGrammar.SelectedImportsRejects
example := @Syntax.DeclarativeGrammar.selectedImportsDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.HidingClauseOrdinaryParses
example := @Syntax.DeclarativeGrammar.HidingClauseRejects
example := @Syntax.DeclarativeGrammar.OptionalHidingOrdinaryParses
example := @Syntax.DeclarativeGrammar.OptionalHidingRejects
example := @Syntax.DeclarativeGrammar.hidingClauseDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.optionalHidingDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImportTerminatorOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImportTerminatorRejects
example := @Syntax.DeclarativeGrammar.importTerminatorDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PlainImportOrdinaryParses
example := @Syntax.DeclarativeGrammar.PlainImportRejects
example := @Syntax.DeclarativeGrammar.plainImportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.NamespaceImportOrdinaryParses
example := @Syntax.DeclarativeGrammar.NamespaceImportRejects
example := @Syntax.DeclarativeGrammar.namespaceImportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.WildcardImportOrdinaryParses
example := @Syntax.DeclarativeGrammar.WildcardImportRejects
example := @Syntax.DeclarativeGrammar.wildcardImportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.SelectiveImportOrdinaryParses
example := @Syntax.DeclarativeGrammar.SelectiveImportRejects
example := @Syntax.DeclarativeGrammar.selectiveImportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ImportDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ImportDeclRejects
example := @Syntax.DeclarativeGrammar.importDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ConstructorSelectionOrdinaryParses
example := @Syntax.DeclarativeGrammar.ConstructorSelectionRejects
example := @Syntax.DeclarativeGrammar.constructorSelectionDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ExportNameOrdinaryParses
example := @Syntax.DeclarativeGrammar.ExportNameRejects
example := @Syntax.DeclarativeGrammar.exportNameDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ExportSelectionOrdinaryParses
example := @Syntax.DeclarativeGrammar.ExportSelectionRejects
example := @Syntax.DeclarativeGrammar.exportSelectionDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.LocalExportItemQualifiedStartAt
example := @Syntax.DeclarativeGrammar.LocalExportItemOrdinaryParses
example := @Syntax.DeclarativeGrammar.LocalExportItemRejects
example := @Syntax.DeclarativeGrammar.localExportItemDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.LocalExportOrdinaryParses
example := @Syntax.DeclarativeGrammar.LocalExportRejects
example := @Syntax.DeclarativeGrammar.localExportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PathExportTokenPresentAt
example := @Syntax.DeclarativeGrammar.PathExportOrdinaryParses
example := @Syntax.DeclarativeGrammar.PathExportRejects
example := @Syntax.DeclarativeGrammar.pathExportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ExportDeclLeftBracePresentAt
example := @Syntax.DeclarativeGrammar.ExportDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.ExportDeclRejects
example := @Syntax.DeclarativeGrammar.exportDeclDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.ExportPathOrdinaryParses
example := @Syntax.DeclarativeGrammar.ExportPathRejects
example := @Syntax.DeclarativeGrammar.exportPathDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.FinishExportOrdinaryParses
example := @Syntax.DeclarativeGrammar.FinishExportRejects
example := @Syntax.DeclarativeGrammar.finishExportDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PragmaItemsTokenPresentAt
example := @Syntax.DeclarativeGrammar.PragmaItemsTailOrdinaryParses
example := @Syntax.DeclarativeGrammar.PragmaItemsTailRejects
example := @Syntax.DeclarativeGrammar.pragmaItemsTailDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PragmaItemsOrdinaryParses
example := @Syntax.DeclarativeGrammar.PragmaItemsRejects
example := @Syntax.DeclarativeGrammar.pragmaItemsDeterministicOutcomeSpec
example := @Syntax.DeclarativeGrammar.PragmaDeclOrdinaryParses
example := @Syntax.DeclarativeGrammar.PragmaDeclRejects
example := @Syntax.DeclarativeGrammar.pragmaDeclDeterministicOutcomeSpec
example := @Syntax.Parser.predicate_reject_sound
example := @Syntax.Parser.predicate_ordinaryOutcome_sound
example := @Syntax.Parser.predicate_exactOutcomeSpec
example := @Syntax.Parser.predicate_success_result_unique
example := @Syntax.Parser.predicate_reject_output_unique
example := @Syntax.Parser.PredicateInternals.groupedPredicates_reject_sound
example := @Syntax.Parser.PredicateInternals.groupedPredicates_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.groupedPredicates_exactOutcomeSpec
example := @Syntax.Parser.PredicateInternals.barePredicates_reject_sound
example := @Syntax.Parser.PredicateInternals.barePredicates_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.barePredicates_exactOutcomeSpec
example := @Syntax.Parser.PredicateInternals.predicateSequence_reject_sound
example := @Syntax.Parser.PredicateInternals.predicateSequence_ordinaryOutcome_sound
example := @Syntax.Parser.PredicateInternals.predicateSequence_exactOutcomeSpec
example := @Syntax.Parser.whereClause_reject_sound
example := @Syntax.Parser.whereClause_ordinaryOutcome_sound
example := @Syntax.Parser.whereClause_exactOutcomeSpec
example := @Syntax.Parser.whereClause_success_result_unique
example := @Syntax.Parser.whereClause_reject_output_unique
example := @Syntax.Parser.returnClause_reject_sound
example := @Syntax.Parser.returnClause_ordinaryOutcome_sound
example := @Syntax.Parser.returnClause_exactOutcomeSpec
example := @Syntax.Parser.returnClause_success_result_unique
example := @Syntax.Parser.returnClause_reject_output_unique
example := @Syntax.Parser.genericParameters_reject_sound
example := @Syntax.Parser.genericParameters_ordinaryOutcome_sound
example := @Syntax.Parser.genericParameters_exactOutcomeSpec
example := @Syntax.Parser.optionalGenericParameters_exactOutcomeSpec
example := @Syntax.Parser.optionalGenericParameters_reject_sound
example := @Syntax.Parser.optionalGenericParameters_ordinaryOutcome_sound
example := @Syntax.Parser.FunctionParameterInternals.namedParameterCore_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_success_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_reject_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_ordinaryOutcome_sound
example := @Syntax.Parser.namedParameter_ordinaryOutcomeSpec
example := @Syntax.Parser.namedParameter_exactOutcomeSpec
example := @Syntax.Parser.namedParameter_success_result_unique
example := @Syntax.Parser.namedParameter_reject_output_unique
example := @Syntax.Parser.functionParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_ordinaryOutcome_sound
example := @Syntax.Parser.functionParameters_ordinaryOutcomeSpec
example := @Syntax.Parser.functionParameters_exactOutcomeSpec
example := @Syntax.Parser.functionParameters_success_result_unique
example := @Syntax.Parser.functionParameters_reject_output_unique
example := @Syntax.Parser.functionSignature_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_ordinaryOutcome_sound
example := @Syntax.Parser.functionSignature_ordinaryOutcomeSpec
example := @Syntax.Parser.functionSignature_exactOutcomeSpec
example := @Syntax.Parser.functionSignature_success_result_unique
example := @Syntax.Parser.functionSignature_reject_output_unique
example := @Syntax.Parser.functionDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_ordinaryOutcome_sound
example := @Syntax.Parser.functionDecl_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.functionDeclExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.functionDeclExactOutcomeSpecOfStatementFuel
example := @Syntax.Parser.functionDecl_exactOutcomeSpec_of_body
example := @Syntax.Parser.functionDecl_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.ImplInternals.implMethod_success_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implMethod_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.implMethodExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.implMethodExactOutcomeSpecOfStatementFuel
example := @Syntax.Parser.ImplInternals.implMethod_exactOutcomeSpec_of_body
example := @Syntax.Parser.ImplInternals.implMethod_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.ImplInternals.implDefaultMarker_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implDefaultMarker_ordinaryOutcomeSpec
example := @Syntax.Parser.ImplInternals.implDefaultMarker_exactOutcomeSpec
example := @Syntax.Parser.ImplInternals.implDefaultMarker_success_result_unique
example := @Syntax.Parser.ImplInternals.implDefaultMarker_reject_output_unique
example := @Syntax.Parser.ImplInternals.implHeadArguments_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implHeadArguments_ordinaryOutcomeSpec
example := @Syntax.Parser.ImplInternals.implHeadArguments_exactOutcomeSpec
example := @Syntax.Parser.ImplInternals.implHeadArguments_success_result_unique
example := @Syntax.Parser.ImplInternals.implHeadArguments_reject_output_unique
example := @Syntax.Parser.ImplInternals.implBody_ordinaryOutcome_sound
example := @Syntax.Parser.ImplInternals.implBody_ordinaryOutcomeSpec
example := @Syntax.Parser.ImplInternals.implBody_exactOutcomeSpec_of_method
example := @Syntax.Parser.ImplInternals.implBody_exactOutcomeSpec_of_body
example := @Syntax.Parser.ImplInternals.implBody_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.ImplInternals.implBody_success_result_unique_of_method
example := @Syntax.Parser.ImplInternals.implBody_reject_output_unique_of_method
example := @Syntax.Parser.ImplInternals.implBody_success_result_unique_of_body
example := @Syntax.Parser.ImplInternals.implBody_reject_output_unique_of_body
example := @Syntax.Parser.ImplInternals.implBody_success_result_unique_of_statementFuel
example := @Syntax.Parser.ImplInternals.implBody_reject_output_unique_of_statementFuel
example := @Syntax.Parser.implDecl_ordinaryOutcome_sound
example := @Syntax.Parser.implDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.implDecl_exactOutcomeSpec_of_implBody
example := @Syntax.Parser.implDecl_exactOutcomeSpec_of_body
example := @Syntax.Parser.implDecl_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.implDecl_success_result_unique_of_implBody
example := @Syntax.Parser.implDecl_reject_output_unique_of_implBody
example := @Syntax.Parser.implDecl_success_result_unique_of_body
example := @Syntax.Parser.implDecl_reject_output_unique_of_body
example := @Syntax.Parser.implDecl_success_result_unique_of_statementFuel
example := @Syntax.Parser.implDecl_reject_output_unique_of_statementFuel
example := @Syntax.Parser.ContractEntryInternals.entryParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.entryParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.implicitPublicModifiers_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractEntryInternals.implicitPublicModifiers_ne_reject
example := @Syntax.Parser.constructorDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_ordinaryOutcome_sound
example := @Syntax.Parser.constructorDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.constructorDecl_exactOutcomeSpec_of_children
example := @Syntax.Parser.constructorDecl_exactOutcomeSpec_of_body
example := @Syntax.Parser.constructorDecl_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.constructorDecl_success_result_unique_of_body
example := @Syntax.Parser.constructorDecl_reject_output_unique_of_body
example := @Syntax.Parser.constructorDecl_success_result_unique_of_children
example := @Syntax.Parser.constructorDecl_reject_output_unique_of_children
example := @Syntax.Parser.fallbackDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_ordinaryOutcome_sound
example := @Syntax.Parser.fallbackDecl_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.fallbackDeclExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.fallbackDeclExactOutcomeSpecOfStatementFuel
example := @Syntax.Parser.fallbackDecl_exactOutcomeSpec_of_body
example := @Syntax.Parser.fallbackDecl_exactOutcomeSpec_of_statementFuel
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractField_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractField_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.optionalContractFieldInitializerExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.contractFieldExactOutcomeSpec
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_success_result_unique
example := @Syntax.Parser.ContractInternals.optionalFieldInitializer_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractField_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractField_success_result_unique
example := @Syntax.Parser.ContractInternals.contractField_reject_output_unique
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfChildren
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfLeaves
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfTermFuel
example := @Syntax.DeclarativeGrammar.contractMemberTailExactOutcomeSpecOfMember
example := @Syntax.DeclarativeGrammar.contractBodyExactOutcomeSpecOfMember
example := @Syntax.DeclarativeGrammar.contractBodyExactOutcomeSpecOfCore
example := @Syntax.DeclarativeGrammar.contractDeclExactOutcomeSpecOfBody
example := @Syntax.DeclarativeGrammar.contractDeclExactOutcomeSpecOfCore
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfCoreTerms
example := @Syntax.DeclarativeGrammar.contractMemberCoreExactOutcomeSpecOfCoreTermFuel
example := @Syntax.DeclarativeGrammar.contractMemberExactOutcomeSpecOfCoreTermFuel
example := @Syntax.DeclarativeGrammar.contractBodyExactOutcomeSpecOfCoreTermFuel
example := @Syntax.DeclarativeGrammar.contractDeclExactOutcomeSpecOfCoreTermFuel
example := @Syntax.Parser.ContractInternals.contractMemberCore_exactOutcomeSpec_of_leaves
example := @Syntax.Parser.ContractInternals.contractMemberCore_exactOutcomeSpec_of_termFuel
example := @Syntax.Parser.ContractInternals.contractMemberCore_exactOutcomeSpec_of_coreTermFuel
example := @Syntax.Parser.ContractInternals.contractMemberCore_success_result_unique
example := @Syntax.Parser.ContractInternals.contractMemberCore_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_coreTermFuel
example := @Syntax.Parser.ContractInternals.contractBody_exactOutcomeSpec_of_member
example := @Syntax.Parser.ContractInternals.contractBody_exactOutcomeSpec_of_core
example := @Syntax.Parser.ContractInternals.contractBody_exactOutcomeSpec_of_coreTermFuel
example := @Syntax.Parser.ContractInternals.contractBody_success_result_unique_of_member
example := @Syntax.Parser.ContractInternals.contractBody_reject_output_unique_of_member
example := @Syntax.Parser.contractDecl_exactOutcomeSpec_of_body
example := @Syntax.Parser.contractDecl_exactOutcomeSpec_of_core
example := @Syntax.Parser.contractDecl_exactOutcomeSpec_of_coreTermFuel
example := @Syntax.Parser.contractDecl_success_result_unique_of_body
example := @Syntax.Parser.contractDecl_reject_output_unique_of_body
example := @Syntax.Parser.ContractInternals.contractMemberCore_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberCore_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberCore_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.attachContractDerive_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.attachContractDerive_total_success
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_exactOutcomeSpec_of_core
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_success_result_unique_of_core
example := @Syntax.Parser.ContractInternals.contractMemberWithAttribute_reject_output_unique_of_core
example := @Syntax.Parser.ContractInternals.recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
example := @Syntax.Parser.ContractInternals.atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt
example := @Syntax.Parser.ContractInternals.contractMemberRecoveryStops_of_guard_eq_true
example := @Syntax.Parser.ContractInternals.contractMemberRecoveryStops_of_advance?_eq_none
example := @Syntax.Parser.ContractInternals.no_contractMemberRecoveryStops_of_nonBoundary_token
example := @Syntax.Parser.ContractInternals.recoverContractMemberAux_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.recoverContractMember_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.recoverContractMember_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.recoverContractMember_ordinaryOutcomeSpec
example := @Syntax.Parser.ContractInternals.recoverContractMember_exactOutcomeSpec
example := @Syntax.Parser.ContractInternals.recoverContractMember_success_result_unique
example := @Syntax.Parser.ContractInternals.recoverContractMember_reject_output_unique
example := @Syntax.Parser.ContractInternals.contractMemberRejectsWithPreservedWindow_of_result
example := @Syntax.Parser.ContractInternals.rewoundContractMember_declarativeRemainder_eq
example := @Syntax.Parser.ContractInternals.cursor_lt_endIndex_of_atEnd_eq_false
example := @Syntax.Parser.ContractInternals.contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
example := @Syntax.Parser.ContractInternals.no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
example := @Syntax.Parser.ContractInternals.closeContractBody_success_exact
example := @Syntax.Parser.ContractInternals.closeContractBody_success_of_rightBrace_guard
example := @Syntax.Parser.ContractInternals.contractMembers_success_ordinaryOutcome_sound_strong
example := @Syntax.Parser.ContractInternals.contractMembers_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractBody_success_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractBody_reject_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractBody_ordinaryOutcome_sound
example := @Syntax.Parser.ContractInternals.contractBody_ordinaryOutcomeSpec
example := @Syntax.Parser.contractDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.contractDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.contractDecl_ordinaryOutcome_sound
example := @Syntax.Parser.contractDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.FileInternals.plainTopItem_success_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.plainTopItem_reject_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.plainTopItem_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.plainTopItem_ordinaryOutcomeSpec
example := @Syntax.Parser.FileInternals.attachDeriveAttribute_success_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.attachDeriveAttribute_total_success
example := @Syntax.Parser.FileInternals.topItem_success_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.topItem_reject_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.topItem_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.topItem_ordinaryOutcomeSpec
example := @Syntax.Parser.FileInternals.recoverTopItem_success_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.recoverTopItem_reject_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.recoverTopItem_ordinaryOutcomeSpec
example := @Syntax.Parser.FileInternals.parseItems_success_ordinaryOutcome_sound_strong
example := @Syntax.Parser.FileInternals.parseItems_reject_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.parseItems_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.parseItems_ordinaryOutcomeSpec
example := @Syntax.Parser.FileInternals.sourceFile_success_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.sourceFile_reject_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.sourceFile_ordinaryOutcome_sound
example := @Syntax.Parser.FileInternals.sourceFile_ordinaryOutcomeSpec
example := @Syntax.Parser.parseTypeAliasParameters_success_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_reject_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_ordinaryOutcome_sound
example := @Syntax.Parser.parseTypeAliasParameters_ordinaryOutcomeSpec
example := @Syntax.Parser.parseTypeAliasParameters_exactOutcomeSpec
example := @Syntax.Parser.parseTypeAliasParameters_success_result_unique
example := @Syntax.Parser.parseTypeAliasParameters_reject_output_unique
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValueAux_success_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_success_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_reject_ordinary_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_ordinaryOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_exactOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_success_result_unique
example := @Syntax.Parser.TypeAliasInternals.recoverTypeAliasValue_reject_output_unique
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_ordinaryOutcome_sound
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_ordinaryOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_exactOutcomeSpec_of_typeExpr
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_success_result_unique_of_typeExpr
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_reject_output_unique
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_exactOutcomeSpec
example := @Syntax.Parser.TypeAliasInternals.parseAliasValue_success_result_unique
example := @Syntax.Parser.typeAlias_success_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_reject_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_ordinaryOutcome_sound
example := @Syntax.Parser.typeAlias_ordinaryOutcomeSpec
example := @Syntax.Parser.typeAlias_exactOutcomeSpec
example := @Syntax.Parser.typeAlias_success_result_unique
example := @Syntax.Parser.typeAlias_reject_output_unique
example := @Syntax.Parser.deriveTarget_success_ordinaryOutcome_sound
example := @Syntax.Parser.deriveTarget_reject_ordinaryOutcome_sound
example := @Syntax.Parser.deriveTarget_ordinaryOutcome_sound
example := @Syntax.Parser.deriveTarget_ordinaryOutcomeSpec
example := @Syntax.Parser.deriveTarget_exactOutcomeSpec
example := @Syntax.Parser.deriveTarget_success_result_unique
example := @Syntax.Parser.deriveTarget_reject_output_unique
example := @Syntax.Parser.deriveAttributeValid_success_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeValid_reject_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeValid_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeValid_ordinaryOutcomeSpec
example := @Syntax.Parser.deriveAttributeValid_exactOutcomeSpec
example := @Syntax.Parser.deriveAttributeValid_success_result_unique
example := @Syntax.Parser.deriveAttributeValid_reject_output_unique
example := @Syntax.Parser.deriveAttributeRecovered_success_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeRecovered_reject_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeRecovered_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttributeRecovered_ordinaryOutcomeSpec
example := @Syntax.Parser.deriveAttributeRecovered_exactOutcomeSpec
example := @Syntax.Parser.deriveAttributeRecovered_success_result_unique
example := @Syntax.Parser.deriveAttributeRecovered_reject_output_unique
example := @Syntax.Parser.deriveAttribute_success_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttribute_reject_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttribute_ordinaryOutcome_sound
example := @Syntax.Parser.deriveAttribute_ordinaryOutcomeSpec
example := @Syntax.Parser.deriveAttribute_exactOutcomeSpec
example := @Syntax.Parser.deriveAttribute_success_result_unique
example := @Syntax.Parser.deriveAttribute_reject_output_unique
example := @Syntax.Parser.EnumInternals.enumConstructorFields_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumConstructorFields_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructor_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumConstructor_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumBody_ordinaryOutcome_sound
example := @Syntax.Parser.EnumInternals.enumBody_ordinaryOutcomeSpec
example := @Syntax.Parser.enumDecl_ordinaryOutcome_sound
example := @Syntax.Parser.enumDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructorFields_exactOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructorFields_success_result_unique
example := @Syntax.Parser.EnumInternals.enumConstructorFields_reject_output_unique
example := @Syntax.Parser.EnumInternals.enumConstructor_exactOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumConstructor_success_result_unique
example := @Syntax.Parser.EnumInternals.enumConstructor_reject_output_unique
example := @Syntax.Parser.EnumInternals.enumBody_exactOutcomeSpec
example := @Syntax.Parser.EnumInternals.enumBody_success_result_unique
example := @Syntax.Parser.EnumInternals.enumBody_reject_output_unique
example := @Syntax.Parser.enumDecl_exactOutcomeSpec
example := @Syntax.Parser.enumDecl_success_result_unique
example := @Syntax.Parser.enumDecl_reject_output_unique
example := @Syntax.Parser.TraitInternals.traitMethod_ordinaryOutcome_sound
example := @Syntax.Parser.TraitInternals.traitMethod_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.traitMethodExactOutcomeSpec
example := @Syntax.Parser.TraitInternals.traitMethod_exactOutcomeSpec
example := @Syntax.Parser.TraitInternals.traitMethod_success_result_unique
example := @Syntax.Parser.TraitInternals.traitMethod_reject_output_unique
example := @Syntax.Parser.TraitInternals.traitBody_ordinaryOutcome_sound
example := @Syntax.Parser.TraitInternals.traitBody_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitMethodTailOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TraitMethodTailRejects.output_unique
example := @Syntax.DeclarativeGrammar.traitMethodTailExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitBodyOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TraitBodyRejects.output_unique
example := @Syntax.DeclarativeGrammar.traitBodyExactOutcomeSpec
example := @Syntax.Parser.TraitInternals.traitBody_exactOutcomeSpec
example := @Syntax.Parser.TraitInternals.traitBody_success_result_unique
example := @Syntax.Parser.TraitInternals.traitBody_reject_output_unique
example := @Syntax.Parser.traitDecl_ordinaryOutcome_sound
example := @Syntax.Parser.traitDecl_ordinaryOutcomeSpec
example := @Syntax.DeclarativeGrammar.TraitDeclOrdinaryParses.result_unique
example := @Syntax.DeclarativeGrammar.TraitDeclRejects.output_unique
example := @Syntax.DeclarativeGrammar.traitDeclExactOutcomeSpec
example := @Syntax.Parser.traitDecl_exactOutcomeSpec
example := @Syntax.Parser.traitDecl_success_result_unique
example := @Syntax.Parser.traitDecl_reject_output_unique
example := @Syntax.Parser.selectorName_ordinaryOutcome_sound
example := @Syntax.Parser.selectorName_ordinaryOutcomeSpec
example := @Syntax.Parser.modulePath_ordinaryOutcome_sound
example := @Syntax.Parser.modulePath_ordinaryOutcomeSpec
example := @Syntax.Parser.selectedAlias_success_ordinaryOutcome_sound
example := @Syntax.Parser.selectedAlias_reject_ordinaryOutcome_sound
example := @Syntax.Parser.selectedAlias_ordinaryOutcome_sound
example := @Syntax.Parser.selectedAlias_ordinaryOutcomeSpec
example := @Syntax.Parser.selectedImport_ordinaryOutcome_sound
example := @Syntax.Parser.selectedImport_ordinaryOutcomeSpec
example := @Syntax.Parser.selectedImports_ordinaryOutcome_sound
example := @Syntax.Parser.selectedImports_ordinaryOutcomeSpec
example := @Syntax.Parser.hidingClause_ordinaryOutcome_sound
example := @Syntax.Parser.hidingClause_ordinaryOutcomeSpec
example := @Syntax.Parser.optionalHiding_ordinaryOutcome_sound
example := @Syntax.Parser.optionalHiding_ordinaryOutcomeSpec
example := @Syntax.Parser.importTerminator_success_ordinaryOutcome_sound
example := @Syntax.Parser.importTerminator_reject_ordinaryOutcome_sound
example := @Syntax.Parser.importTerminator_ordinaryOutcome_sound
example := @Syntax.Parser.importTerminator_ordinaryOutcomeSpec
example := @Syntax.Parser.plainImport_success_ordinaryOutcome_sound
example := @Syntax.Parser.plainImport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.plainImport_ordinaryOutcome_sound
example := @Syntax.Parser.plainImport_ordinaryOutcomeSpec
example := @Syntax.Parser.namespaceImport_success_ordinaryOutcome_sound
example := @Syntax.Parser.namespaceImport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.namespaceImport_ordinaryOutcome_sound
example := @Syntax.Parser.namespaceImport_ordinaryOutcomeSpec
example := @Syntax.Parser.wildcardImport_success_ordinaryOutcome_sound
example := @Syntax.Parser.wildcardImport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.wildcardImport_ordinaryOutcome_sound
example := @Syntax.Parser.wildcardImport_ordinaryOutcomeSpec
example := @Syntax.Parser.selectiveImport_success_ordinaryOutcome_sound
example := @Syntax.Parser.selectiveImport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.selectiveImport_ordinaryOutcome_sound
example := @Syntax.Parser.selectiveImport_ordinaryOutcomeSpec
example := @Syntax.Parser.importDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.importDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.importDecl_ordinaryOutcome_sound
example := @Syntax.Parser.importDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.constructorSelection_success_ordinaryOutcome_sound
example := @Syntax.Parser.constructorSelection_reject_ordinaryOutcome_sound
example := @Syntax.Parser.constructorSelection_ordinaryOutcome_sound
example := @Syntax.Parser.constructorSelection_ordinaryOutcomeSpec
example := @Syntax.Parser.exportName_success_ordinaryOutcome_sound
example := @Syntax.Parser.exportName_reject_ordinaryOutcome_sound
example := @Syntax.Parser.exportName_ordinaryOutcome_sound
example := @Syntax.Parser.exportName_ordinaryOutcomeSpec
example := @Syntax.Parser.exportSelection_success_ordinaryOutcome_sound
example := @Syntax.Parser.exportSelection_reject_ordinaryOutcome_sound
example := @Syntax.Parser.exportSelection_ordinaryOutcome_sound
example := @Syntax.Parser.exportSelection_ordinaryOutcomeSpec
example := @Syntax.Parser.localExportItem_success_ordinaryOutcome_sound
example := @Syntax.Parser.localExportItem_reject_ordinaryOutcome_sound
example := @Syntax.Parser.localExportItem_ordinaryOutcome_sound
example := @Syntax.Parser.localExportItem_ordinaryOutcomeSpec
example := @Syntax.Parser.localExport_success_ordinaryOutcome_sound
example := @Syntax.Parser.localExport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.localExport_ordinaryOutcome_sound
example := @Syntax.Parser.localExport_ordinaryOutcomeSpec
example := @Syntax.Parser.pathExport_success_ordinaryOutcome_sound
example := @Syntax.Parser.pathExport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.pathExport_ordinaryOutcome_sound
example := @Syntax.Parser.pathExport_ordinaryOutcomeSpec
example := @Syntax.Parser.exportDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.exportDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.exportDecl_ordinaryOutcome_sound
example := @Syntax.Parser.exportDecl_ordinaryOutcomeSpec
example := @Syntax.Parser.exportPath_success_ordinaryOutcome_sound
example := @Syntax.Parser.exportPath_reject_ordinaryOutcome_sound
example := @Syntax.Parser.exportPath_ordinaryOutcome_sound
example := @Syntax.Parser.exportPath_ordinaryOutcomeSpec
example := @Syntax.Parser.finishExport_success_ordinaryOutcome_sound
example := @Syntax.Parser.finishExport_reject_ordinaryOutcome_sound
example := @Syntax.Parser.finishExport_ordinaryOutcome_sound
example := @Syntax.Parser.finishExport_ordinaryOutcomeSpec
example := @Syntax.Parser.rawIdentifier_ordinaryOutcome_sound
example := @Syntax.Parser.rawIdentifier_ordinaryOutcomeSpec
example := @Syntax.Parser.PragmaInternals.pragmaItems_ordinaryOutcome_sound
example := @Syntax.Parser.PragmaInternals.pragmaItems_ordinaryOutcomeSpec
example := @Syntax.Parser.pragmaDecl_success_ordinaryOutcome_sound
example := @Syntax.Parser.pragmaDecl_reject_ordinaryOutcome_sound
example := @Syntax.Parser.pragmaDecl_ordinaryOutcome_sound
example := @Syntax.Parser.pragmaDecl_ordinaryOutcomeSpec

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

example {input output : Syntax.Parser.State} {member : ContractMember}
    (result : Syntax.Parser.ContractInternals.contractMemberCore input =
      .ok member output) :
    Syntax.DeclarativeGrammar.ContractMemberCoreOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractMemberCore_success_ordinaryOutcome_sound
    result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.ContractInternals.contractMemberCore input =
      .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractMemberCoreRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractMemberCore_reject_ordinaryOutcome_sound
    result

example {derive : DeriveAttribute}
    {coreMember attached : ContractMember}
    {input output : Syntax.Parser.State}
    (result : Syntax.Parser.ContractInternals.attachContractDerive derive
      coreMember input = .ok attached output) :
    Syntax.DeclarativeGrammar.ContractDeriveAttaches derive coreMember
      attached ∧
      output.declarativeRemainder = input.declarativeRemainder :=
  Syntax.Parser.ContractInternals.attachContractDerive_success_ordinaryOutcome_sound
    result

example {input output : Syntax.Parser.State} {member : ContractMember}
    (result : Syntax.Parser.ContractInternals.contractMemberWithAttribute input =
      .ok member output) :
    Syntax.DeclarativeGrammar.ContractMemberOrdinaryParses
      input.declarativeRemainder member output.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractMemberWithAttribute_success_ordinaryOutcome_sound
    result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.ContractInternals.contractMemberWithAttribute input =
      .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractMemberRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractMemberWithAttribute_reject_ordinaryOutcome_sound
    result

example {input output : Syntax.Parser.State} {member : ContractMember}
    (result : Syntax.Parser.ContractInternals.recoverContractMember input =
      .ok member output) :
    Syntax.DeclarativeGrammar.ContractMemberRecoveryParses
      input.declarativeRemainder member output.declarativeRemainder :=
  Syntax.Parser.ContractInternals.recoverContractMember_success_ordinaryOutcome_sound
    result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.ContractInternals.recoverContractMember input =
      .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractMemberRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.ContractInternals.recoverContractMember_reject_ordinaryOutcome_sound
    result

example {input output : Syntax.Parser.State}
    {body : Syntax.Parser.ContractInternals.ContractBody}
    (result : Syntax.Parser.ContractInternals.contractBody input =
      .ok body output) :
    Syntax.DeclarativeGrammar.ContractBodyOrdinaryParses
      input.declarativeRemainder body.span body.members
        output.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractBody_success_ordinaryOutcome_sound
    result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.ContractInternals.contractBody input =
      .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractBodyRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.ContractInternals.contractBody_reject_ordinaryOutcome_sound
    result

example {input output : Syntax.Parser.State} {declaration : ContractDecl}
    (result : Syntax.Parser.contractDecl input = .ok declaration output) :
    Syntax.DeclarativeGrammar.ContractDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder :=
  Syntax.Parser.contractDecl_success_ordinaryOutcome_sound result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.contractDecl input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.ContractDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.contractDecl_reject_ordinaryOutcome_sound result

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

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.traitDecl input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.TraitDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.traitDecl_reject_ordinaryOutcome_sound result

example {input rejected : Syntax.Parser.State}
    {failure : Syntax.Parser.Failure}
    (result : Syntax.Parser.implDecl input = .reject failure rejected) :
    Syntax.DeclarativeGrammar.ImplDeclRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  Syntax.Parser.implDecl_reject_ordinaryOutcome_sound result

example := @Syntax.DeclarativeGrammar.yulExpressionExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.yulExpressionPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.yulExpressionExactOutcomeSpec
example := @Syntax.Parser.YulExpressionInternals.withFuel_exactOutcomeSpec
example := @Syntax.Parser.YulExpressionInternals.withFuel_success_result_unique
example := @Syntax.Parser.YulExpressionInternals.withFuel_reject_output_unique
example := @Syntax.Parser.yulExpression_publicExactOutcomeSpec
example := @Syntax.Parser.yulExpression_exactOutcomeSpec
example := @Syntax.Parser.yulExpression_success_result_unique
example := @Syntax.Parser.yulExpression_reject_output_unique

example := @Syntax.DeclarativeGrammar.yulStatementExactOutcomeSpecWithFuel
example := @Syntax.DeclarativeGrammar.yulStatementPublicExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.yulStatementExactOutcomeSpec
example := @Syntax.DeclarativeGrammar.yulBodyExactOutcomeSpec
example := @Syntax.Parser.yulStatementWithFuel_exactOutcomeSpec
example := @Syntax.Parser.yulStatementWithFuel_success_result_unique
example := @Syntax.Parser.yulStatementWithFuel_reject_output_unique
example := @Syntax.Parser.yulStatement_publicExactOutcomeSpec
example := @Syntax.Parser.yulStatement_exactOutcomeSpec
example := @Syntax.Parser.yulStatement_success_result_unique
example := @Syntax.Parser.yulStatement_reject_output_unique
example := @Syntax.Parser.yulBody_exactOutcomeSpec
example := @Syntax.Parser.yulBody_success_result_unique
example := @Syntax.Parser.yulBody_reject_output_unique

end Tests
