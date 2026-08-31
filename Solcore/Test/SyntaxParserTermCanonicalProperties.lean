import Solcore.Syntax.Parser.TermCanonicalProperties

/-! External consumers for unconditional canonical Core parser contracts. -/

namespace Tests

open Solcore.Syntax.Parser

example := @TermInternals.canonicalStatementClosure
example := @TermInternals.coreRecursiveWithFuel_canonical_contract
example := @TermInternals.canonicalStatementFuelContract
example := @TermInternals.coreExpressionWithFuel_canonical_contract
example := @TermInternals.corePatternWithFuel_canonical_contract
example := @TermInternals.coreStatementWithFuel_canonical_contract
example := @expression_canonical_contract
example := @pattern_canonical_contract
example := @statement_canonical_contract
example := @block_canonical_validFor
example := @block_canonical_preservesTokenWindow
example := @block_canonical_cursorMonotoneOnSuccess
example := @block_canonical_startsAtCurrentTokenOnSuccess

end Tests
