import Solcore.Syntax.Parser.TermStatementProperties

/-! External consumers for the canonical statement recovery boundary. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.recognizedStatementOrFallback
example := @TermInternals.recognizedStatementOrFallback_validFor
example := @TermInternals.recognizedStatementOrFallback_preservesTokenWindow
example := @TermInternals.recognizedStatementOrFallback_preservesTokensOnSuccess
example :=
  @TermInternals.recognizedStatementOrFallback_preservesTokensOnSuccess_of_success
example := @TermInternals.recognizedStatementOrFallback_cursorMonotoneOnSuccess
example :=
  @TermInternals.recognizedStatementOrFallback_startsAtCurrentTokenOnSuccess
example := @TermInternals.StatementParserContract
example := @TermInternals.StatementParserContract.preservesTokensOnSuccess
example := @TermInternals.recognizedStatementOrFallback_contract
example := @TermInternals.statementLayer
example := @TermInternals.StatementLayerInputs
example := @TermInternals.statementLayer_contract

end Tests
