import Solcore.Syntax.Parser.TermRecursiveProperties

/-! External consumers for simultaneous canonical term contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.RecursiveStatementValid
example := @TermInternals.RecursiveStatementClosure
example := @TermInternals.PatternParserContract
example := @TermInternals.PatternParserContract.preservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract
example := @TermInternals.RecursiveFuelContract.expressionPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.expressionCursorMonotoneOnSuccess
example := @TermInternals.RecursiveFuelContract.patternPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.statementPreservesTokensOnSuccess
example := @TermInternals.RecursiveFuelContract.statementValidFor
example := @TermInternals.coreRecursiveWithFuel_contract
example := @TermInternals.corePatternWithFuel_contract_of_recursive

end Tests
