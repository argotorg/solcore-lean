import Solcore.Syntax.Parser.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionLayerBlockFuelTotalityProperties
import Solcore.Syntax.Parser.PatternLayerFuelTotalityProperties
import Solcore.Syntax.Parser.Statement.StatementLayerStrictProperties
import Solcore.Syntax.Parser.TermRecursiveProperties

/-! Simultaneous fuel totality for the three recursive Core term families. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

mutual

/-- Ordinary-input budget for the expression parser at one recursion depth. -/
def coreExpressionTotalityFuel : Nat → Nat
  | 0 => 0
  | fuel + 1 => Nat.min (coreExpressionTotalityFuel fuel)
      (coreStatementTotalityFuel fuel + 1) + 1

/-- Ordinary-input budget for the pattern parser at one recursion depth. -/
def corePatternTotalityFuel : Nat → Nat
  | 0 => 0
  | fuel + 1 => Nat.min (corePatternTotalityFuel fuel + 1)
      (coreExpressionTotalityFuel fuel + 1)

/-- Ordinary-input budget for the statement parser at one recursion depth. -/
def coreStatementTotalityFuel : Nat → Nat
  | 0 => 0
  | fuel + 1 => statementLayerFuel (coreStatementTotalityFuel fuel)
      (coreExpressionTotalityFuel fuel) (corePatternTotalityFuel fuel)

end

/-- The three totality contracts at one shared parser recursion depth. -/
structure RecursiveFuelTotalityContract
    (statementValid : SourceFile → Statement → Prop)
    (fuel : Nat) : Prop where
  expression : FuelElementTotalityContract (coreExpressionWithFuel fuel)
    (coreExpressionTotalityFuel fuel)
  pattern : FuelElementTotalityContract (corePatternWithFuel fuel)
    (corePatternTotalityFuel fuel)
  statement : FuelStatementTotalityContract
    (RecursiveStatementValid statementValid) (coreStatementWithFuel fuel)
    (coreStatementTotalityFuel fuel)

/-- Every successful positive-fuel Core statement strictly advances. -/
theorem coreStatementWithFuel_cursor_lt_onSuccess
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) (fuel : Nat)
    {input next : State} {value : Statement}
    (parsed : coreStatementWithFuel fuel input = .ok value next) :
    input.cursor < next.cursor := by
  cases fuel with
  | zero => simp [coreStatementWithFuel] at parsed
  | succ fuel =>
      have syntaxContract :=
        coreRecursiveWithFuel_contract statementValid closure fuel
      exact statementLayer_cursor_lt_onSuccess (coreStatementWithFuel fuel)
        (coreExpressionWithFuel fuel) (corePatternWithFuel fuel)
        syntaxContract.expression.cursorLtOnSuccess (by
          simpa only [coreStatementWithFuel] using parsed)

/-- All three canonical recursive parsers are fuel-total at every depth. -/
theorem coreRecursiveWithFuel_fuelTotalityContract
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) :
    ∀ fuel, RecursiveFuelTotalityContract statementValid fuel := by
  intro fuel
  induction fuel with
  | zero =>
      let syntaxContract :=
        coreRecursiveWithFuel_contract statementValid closure 0
      exact {
        expression := {
          validFor := syntaxContract.expression.validFor.mono
            (fun _ _ _ => trivial)
          preservesTokenWindow :=
            syntaxContract.expression.preservesTokenWindow
          cursorLtOnSuccess := syntaxContract.expression.cursorLtOnSuccess
          ordinary := by
            intro input inputValid adequate
            simp only [coreExpressionTotalityFuel] at adequate
            omega
        }
        pattern := {
          validFor := syntaxContract.pattern.validFor.mono
            (fun _ _ _ => trivial)
          preservesTokenWindow := syntaxContract.pattern.preservesTokenWindow
          cursorLtOnSuccess := by
            intro input next value result
            simp [corePatternWithFuel] at result
          ordinary := by
            intro input inputValid adequate
            simp only [corePatternTotalityFuel] at adequate
            omega
        }
        statement := {
          toStatementParserContract := syntaxContract.statement
          ordinary := by
            intro input inputValid adequate
            simp only [coreStatementTotalityFuel] at adequate
            omega
        }
      }
  | succ fuel inductionHypothesis =>
      let syntaxContract :=
        coreRecursiveWithFuel_contract statementValid closure fuel
      let statement := coreStatementWithFuel fuel
      let rawBlock := coreBlock statement .require
      let block := isolateBlock rawBlock
      have statementStrict : ∀ {input next : State} {value : Statement},
          statement input = .ok value next → input.cursor < next.cursor :=
        coreStatementWithFuel_cursor_lt_onSuccess statementValid closure fuel
      have rawBlockCanonical : rawBlock.ValidFor
          (Block.ValidFor (RecursiveStatementValid statementValid)) :=
        coreBlock_validFor (RecursiveStatementValid statementValid) statement
          .require syntaxContract.statement.validFor
          syntaxContract.statement.preservesTokensOnSuccess
          (fun _ _ valid => valid.span_valid)
      have rawBlockValid : rawBlock.ValidFor (Block.ValidFor statementValid) :=
        rawBlockCanonical.mono (fun file body valid =>
          ⟨valid.1, fun retained member =>
            closure.close file retained (valid.2 retained member)⟩)
      have blockValid : block.ValidFor (Block.ValidFor statementValid) :=
        isolateBlock_validFor statementValid rawBlock rawBlockValid
      have blockWindow : Parser.PreservesTokenWindow block :=
        isolateBlock_preservesTokenWindow rawBlock
          (coreBlock_preservesTokenWindow statement .require
            syntaxContract.statement.preservesTokenWindow)
      have blockCursor : Parser.CursorMonotoneOnSuccess block :=
        isolateBlock_cursorMonotoneOnSuccess rawBlock
          (coreBlock_cursorMonotoneOnSuccess statement .require)
      have blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span) :=
        isolateBlock_startsAtCurrentTokenOnSuccess rawBlock
          (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
      let blockTotality := isolatedCoreBlock_fuelTotalityContract statement
        .require (coreStatementTotalityFuel fuel)
        inductionHypothesis.statement statementStrict
        (fun _ _ valid => valid.span_valid)
      have expressionLayer :=
        ExpressionInternals.expressionLayer_blockFuelTotalityContract
          (coreExpressionWithFuel fuel) block
          (coreExpressionTotalityFuel fuel)
          (coreStatementTotalityFuel fuel + 1) syntaxContract.expression
          inductionHypothesis.expression blockValid blockWindow blockCursor
          blockStarts blockTotality
      have expression : FuelElementTotalityContract
          (coreExpressionWithFuel (fuel + 1))
          (coreExpressionTotalityFuel (fuel + 1)) := by
        simpa only [coreExpressionWithFuel, coreExpressionTotalityFuel,
          statement, rawBlock, block] using expressionLayer
      have patternLayer := PatternInternals.patternLayer_fuelElementTotalityContract
        (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
        (corePatternTotalityFuel fuel) (coreExpressionTotalityFuel fuel)
        inductionHypothesis.pattern inductionHypothesis.expression
        (Expr.ValidFor statementValid) syntaxContract.pattern.validFor
        syntaxContract.expression.validFor (fun valid => valid.span_valid)
        syntaxContract.expression.startsAtCurrentTokenOnSuccess
      have pattern : FuelElementTotalityContract
          (corePatternWithFuel (fuel + 1))
          (corePatternTotalityFuel (fuel + 1)) := by
        simpa only [corePatternWithFuel, corePatternTotalityFuel] using
          patternLayer
      have statementLayer := statementLayer_fuelTotalityContract statement
        (coreExpressionWithFuel fuel) (corePatternWithFuel fuel)
        (coreStatementTotalityFuel fuel) (coreExpressionTotalityFuel fuel)
        (corePatternTotalityFuel fuel) inductionHypothesis.statement
        statementStrict syntaxContract.expression inductionHypothesis.expression
        syntaxContract.pattern inductionHypothesis.pattern
      have statementResult : FuelStatementTotalityContract
          (RecursiveStatementValid statementValid)
          (coreStatementWithFuel (fuel + 1))
          (coreStatementTotalityFuel (fuel + 1)) := by
        simpa only [coreStatementWithFuel, coreStatementTotalityFuel,
          statement] using statementLayer
      exact { expression, pattern, statement := statementResult }

end Solcore.Syntax.Parser.TermInternals
