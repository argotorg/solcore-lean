import Solcore.Syntax.CoreTermValidity
import Solcore.Syntax.Parser.TermRecursiveProperties

/-! Unconditional canonical contracts for the public Core term parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- Canonical recursive statement validity closes one constructed layer. -/
theorem canonicalStatementClosure :
    RecursiveStatementClosure CoreStatement.ValidFor := {
  close := fun _ _ valid => CoreStatement.ValidFor.ofStatement valid
}

/-- The simultaneous fuel theorem instantiated with canonical validity. -/
theorem coreRecursiveWithFuel_canonical_contract (fuel : Nat) :
    RecursiveFuelContract CoreStatement.ValidFor fuel :=
  coreRecursiveWithFuel_contract CoreStatement.ValidFor
    canonicalStatementClosure fuel

/-- The statement family required by the earlier expression-only lift. -/
theorem canonicalStatementFuelContract :
    CoreStatementFuelContract CoreStatement.ValidFor := {
  validFor := fun fuel =>
    (coreRecursiveWithFuel_canonical_contract fuel).statementValidFor
      canonicalStatementClosure
  preservesTokenWindow := fun fuel =>
    (coreRecursiveWithFuel_canonical_contract fuel).statement.preservesTokenWindow
  spanValid := fun _ _ valid => valid.span_valid
}

/-- Canonical fuel-bounded expression parsing has its complete contract. -/
theorem coreExpressionWithFuel_canonical_contract (fuel : Nat) :
    ExpressionInternals.ExpressionContract CoreStatement.ValidFor
      (coreExpressionWithFuel fuel) :=
  (coreRecursiveWithFuel_canonical_contract fuel).expression

/-- Canonical fuel-bounded pattern parsing has its complete contract. -/
theorem corePatternWithFuel_canonical_contract (fuel : Nat) :
    PatternParserContract CoreStatement.ValidFor (corePatternWithFuel fuel) :=
  (coreRecursiveWithFuel_canonical_contract fuel).pattern

/-- Canonical fuel-bounded statement parsing has its complete contract. -/
theorem coreStatementWithFuel_canonical_contract (fuel : Nat) :
    StatementParserContract CoreStatement.ValidFor
      (coreStatementWithFuel fuel) := by
  let syntaxContract :=
    (coreRecursiveWithFuel_canonical_contract fuel).statement
  exact {
    validFor := syntaxContract.validFor.mono canonicalStatementClosure.close
    preservesTokenWindow := syntaxContract.preservesTokenWindow
    cursorMonotoneOnSuccess := syntaxContract.cursorMonotoneOnSuccess
    startsAtCurrentTokenOnSuccess :=
      syntaxContract.startsAtCurrentTokenOnSuccess
  }

end TermInternals

/-- The public expression parser preserves canonical recursive validity. -/
theorem expression_canonical_contract :
    ExpressionInternals.ExpressionContract CoreStatement.ValidFor expression :=
  expression_contract_of_coreStatement CoreStatement.ValidFor
    TermInternals.canonicalStatementFuelContract

/-- The public pattern parser preserves canonical recursive validity. -/
theorem pattern_canonical_contract :
    TermInternals.PatternParserContract CoreStatement.ValidFor pattern := {
  validFor := by
    intro input inputValid
    unfold pattern
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold pattern
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold pattern at parsed
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).cursorMonotoneOnSuccess
        input value next parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold pattern at parsed
    exact (TermInternals.corePatternWithFuel_canonical_contract
      (input.remainingCount + 1)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

/-- The public statement parser preserves canonical recursive validity. -/
theorem statement_canonical_contract :
    TermInternals.StatementParserContract CoreStatement.ValidFor statement := {
  validFor := by
    intro input inputValid
    unfold statement
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold statement
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).preservesTokenWindow input
  cursorMonotoneOnSuccess := by
    intro input value next parsed
    unfold statement at parsed
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).cursorMonotoneOnSuccess
        input value next parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold statement at parsed
    exact (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

/-- Public Core blocks retain canonical statement provenance. -/
theorem block_canonical_validFor (policy : TailExpressionPolicy) :
    (block policy).ValidFor (Block.ValidFor CoreStatement.ValidFor) := by
  intro input inputValid
  unfold block
  let statementContract :=
    TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)
  exact coreBlock_validFor CoreStatement.ValidFor
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    statementContract.validFor statementContract.preservesTokensOnSuccess
    (fun _ _ valid => valid.span_valid) input inputValid

/-- Public Core blocks preserve their complete token window. -/
theorem block_canonical_preservesTokenWindow (policy : TailExpressionPolicy) :
    Parser.PreservesTokenWindow (block policy) := by
  intro input
  unfold block
  exact coreBlock_preservesTokenWindow
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    (TermInternals.coreStatementWithFuel_canonical_contract
      (input.remainingCount + 1)).preservesTokenWindow input

/-- Public Core-block success never rewinds its caller. -/
theorem block_canonical_cursorMonotoneOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.CursorMonotoneOnSuccess (block policy) := by
  intro input value next parsed
  unfold block at parsed
  exact coreBlock_cursorMonotoneOnSuccess
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    input value next parsed

/-- Public Core-block success starts at its opening brace. -/
theorem block_canonical_startsAtCurrentTokenOnSuccess
    (policy : TailExpressionPolicy) :
    Parser.StartsAtCurrentTokenOnSuccess (block policy) (·.span) := by
  intro input value next parsed
  unfold block at parsed
  exact coreBlock_startsAtCurrentTokenOnSuccess
    (TermInternals.coreStatementWithFuel (input.remainingCount + 1)) policy
    input value next parsed

end Solcore.Syntax.Parser
