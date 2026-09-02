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

end Tests
