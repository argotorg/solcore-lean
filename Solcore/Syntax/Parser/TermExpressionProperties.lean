import Solcore.Syntax.Parser.Term
import Solcore.Syntax.Parser.ExpressionProperties

/-! Fuel-inductive contracts for the public canonical Core expression parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- The statement-side assumptions needed by recursive expression blocks. -/
structure CoreStatementFuelContract
    (statementValid : SourceFile → Statement → Prop) : Prop where
  validFor : ∀ fuel,
    (coreStatementWithFuel fuel).ValidFor statementValid
  preservesTokenWindow : ∀ fuel,
    Parser.PreservesTokenWindow (coreStatementWithFuel fuel)
  spanValid : ∀ (file : SourceFile) (statement : Statement),
    statementValid file statement → statement.span.ValidFor file

/-- Every fuel-bounded Core expression parser satisfies the complete
expression contract when its same-fuel statement parser satisfies the block
boundary. -/
theorem coreExpressionWithFuel_contract
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid) :
    ∀ fuel, ExpressionInternals.ExpressionContract statementValid
      (coreExpressionWithFuel fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      refine {
        validFor := ?_
        preservesTokenWindow := ?_
        cursorLtOnSuccess := ?_
        startsAtCurrentTokenOnSuccess := ?_
      }
      · intro input inputValid
        trivial
      · intro input
        trivial
      · intro input next value parsed
        simp [coreExpressionWithFuel] at parsed
      · intro input value next parsed
        simp [coreExpressionWithFuel] at parsed
  | succ fuel inductionHypothesis =>
      let statement := coreStatementWithFuel fuel
      let rawBlock := coreBlock statement .require
      let block := isolateBlock rawBlock
      have rawBlockValid : rawBlock.ValidFor
          (Block.ValidFor statementValid) :=
        coreBlock_validFor statementValid statement .require
          (statementContract.validFor fuel)
          (statementContract.preservesTokenWindow fuel).preservesTokensOnSuccess
          statementContract.spanValid
      have blockValid : block.ValidFor (Block.ValidFor statementValid) :=
        isolateBlock_validFor statementValid rawBlock rawBlockValid
      have rawBlockWindow : Parser.PreservesTokenWindow rawBlock :=
        coreBlock_preservesTokenWindow statement .require
          (statementContract.preservesTokenWindow fuel)
      have blockWindow : Parser.PreservesTokenWindow block :=
        isolateBlock_preservesTokenWindow rawBlock rawBlockWindow
      have blockCursor : Parser.CursorMonotoneOnSuccess block :=
        isolateBlock_cursorMonotoneOnSuccess rawBlock
          (coreBlock_cursorMonotoneOnSuccess statement .require)
      have blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span) :=
        isolateBlock_startsAtCurrentTokenOnSuccess rawBlock
          (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
      simpa only [coreExpressionWithFuel, statement, rawBlock, block] using
        ExpressionInternals.expressionLayer_concrete_contract
          (coreExpressionWithFuel fuel) block statementValid
          inductionHypothesis blockValid blockWindow blockCursor blockStarts

/-- Fuel-bounded Core expression parsing preserves source provenance. -/
theorem coreExpressionWithFuel_validFor
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    (coreExpressionWithFuel fuel).ValidFor
      (Expr.ValidFor statementValid) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).validFor

/-- Fuel-bounded Core expression parsing preserves ordinary token windows. -/
theorem coreExpressionWithFuel_preservesTokenWindow
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.PreservesTokenWindow (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).preservesTokenWindow

/-- Fuel-bounded Core expression success retains its token carrier. -/
theorem coreExpressionWithFuel_preservesTokensOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.PreservesTokensOnSuccess (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).preservesTokensOnSuccess

/-- Fuel-bounded Core expression success strictly advances. -/
theorem coreExpressionWithFuel_cursor_lt_onSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) {input next : State} {value : Expr}
    (parsed : coreExpressionWithFuel fuel input = .ok value next) :
    input.cursor < next.cursor :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).cursorLtOnSuccess parsed

/-- Fuel-bounded Core expression success is cursor-monotone. -/
theorem coreExpressionWithFuel_cursorMonotoneOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).cursorMonotoneOnSuccess

/-- Fuel-bounded Core expression success begins at its current token. -/
theorem coreExpressionWithFuel_startsAtCurrentTokenOnSuccess
    (statementValid : SourceFile → Statement → Prop)
    (statementContract : CoreStatementFuelContract statementValid)
    (fuel : Nat) :
    Parser.StartsAtCurrentTokenOnSuccess
      (coreExpressionWithFuel fuel) (·.span) :=
  (coreExpressionWithFuel_contract statementValid statementContract fuel).startsAtCurrentTokenOnSuccess

end TermInternals

/-- Lift the fuel-indexed proof to the public state-sized expression parser. -/
theorem expression_contract_of_coreStatement
    (statementValid : SourceFile → Statement → Prop)
    (statementContract :
      TermInternals.CoreStatementFuelContract statementValid) :
    ExpressionInternals.ExpressionContract statementValid expression := {
  validFor := by
    intro input inputValid
    unfold expression
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).validFor input inputValid
  preservesTokenWindow := by
    intro input
    unfold expression
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).preservesTokenWindow input
  cursorLtOnSuccess := by
    intro input next value parsed
    unfold expression at parsed
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).cursorLtOnSuccess parsed
  startsAtCurrentTokenOnSuccess := by
    intro input value next parsed
    unfold expression at parsed
    exact (TermInternals.coreExpressionWithFuel_contract statementValid
      statementContract (input.remainingCount + 1)).startsAtCurrentTokenOnSuccess
        input value next parsed
}

end Solcore.Syntax.Parser
