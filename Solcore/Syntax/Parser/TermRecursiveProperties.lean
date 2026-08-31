import Solcore.Syntax.Parser.TermExpressionProperties
import Solcore.Syntax.Parser.TermPatternProperties
import Solcore.Syntax.Parser.TermStatementProperties

/-! Simultaneous fuel contracts for canonical Core terms. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace TermInternals

/-- The syntax validity produced by one canonical statement layer. -/
abbrev RecursiveStatementValid
    (statementValid : SourceFile → Statement → Prop) :
    SourceFile → Statement → Prop :=
  Statement.ValidFor (Expr.ValidFor statementValid)
    (Pattern.ValidFor (Expr.ValidFor statementValid)) YulStmt.ValidFor

/-- Explicitly close canonical syntax validity into a client statement
predicate.  This post-fixed-point assumption is intentionally not implicit. -/
structure RecursiveStatementClosure
    (statementValid : SourceFile → Statement → Prop) : Prop where
  close : ∀ file statement,
    RecursiveStatementValid statementValid file statement →
      statementValid file statement

/-- Complete contracts for one fuel-bounded recursive pattern parser. -/
structure PatternParserContract
    (statementValid : SourceFile → Statement → Prop)
    (parser : Parser Pattern) : Prop where
  validFor : parser.ValidFor
    (Pattern.ValidFor (Expr.ValidFor statementValid))
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess parser (·.span)

namespace PatternParserContract

theorem preservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop}
    {parser : Parser Pattern}
    (contract : PatternParserContract statementValid parser) :
    Parser.PreservesTokensOnSuccess parser :=
  contract.preservesTokenWindow.preservesTokensOnSuccess

end PatternParserContract

/-- Expression, pattern, and statement contracts at one identical fuel. -/
structure RecursiveFuelContract
    (statementValid : SourceFile → Statement → Prop)
    (fuel : Nat) : Prop where
  expression : ExpressionInternals.ExpressionContract statementValid
    (coreExpressionWithFuel fuel)
  pattern : PatternParserContract statementValid (corePatternWithFuel fuel)
  statement : StatementParserContract
    (RecursiveStatementValid statementValid) (coreStatementWithFuel fuel)

namespace RecursiveFuelContract

theorem expressionPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (coreExpressionWithFuel fuel) :=
  contract.expression.preservesTokensOnSuccess

theorem expressionCursorMonotoneOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.CursorMonotoneOnSuccess (coreExpressionWithFuel fuel) :=
  contract.expression.cursorMonotoneOnSuccess

theorem patternPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (corePatternWithFuel fuel) :=
  contract.pattern.preservesTokensOnSuccess

theorem statementPreservesTokensOnSuccess
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel) :
    Parser.PreservesTokensOnSuccess (coreStatementWithFuel fuel) :=
  contract.statement.preservesTokensOnSuccess

theorem statementValidFor
    {statementValid : SourceFile → Statement → Prop} {fuel : Nat}
    (contract : RecursiveFuelContract statementValid fuel)
    (closure : RecursiveStatementClosure statementValid) :
    (coreStatementWithFuel fuel).ValidFor statementValid :=
  contract.statement.validFor.mono closure.close

end RecursiveFuelContract

/-- The three mutually recursive Core parsers satisfy their complete contracts
at every common fuel, conditional on the explicit statement-validity closure. -/
theorem coreRecursiveWithFuel_contract
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) :
    ∀ fuel, RecursiveFuelContract statementValid fuel := by
  intro fuel
  induction fuel with
  | zero =>
      have expressionZero : ExpressionInternals.ExpressionContract
          statementValid (coreExpressionWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorLtOnSuccess := by
          intro input next value parsed
          simp [coreExpressionWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [coreExpressionWithFuel] at parsed
      }
      have patternZero : PatternParserContract statementValid
          (corePatternWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorMonotoneOnSuccess := by
          intro input value next parsed
          simp [corePatternWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [corePatternWithFuel] at parsed
      }
      have statementZero : StatementParserContract
          (RecursiveStatementValid statementValid)
          (coreStatementWithFuel 0) := {
        validFor := by intro input inputValid; trivial
        preservesTokenWindow := by intro input; trivial
        cursorMonotoneOnSuccess := by
          intro input value next parsed
          simp [coreStatementWithFuel] at parsed
        startsAtCurrentTokenOnSuccess := by
          intro input value next parsed
          simp [coreStatementWithFuel] at parsed
      }
      exact {
        expression := expressionZero
        pattern := patternZero
        statement := statementZero
      }
  | succ fuel inductionHypothesis =>
      let statement := coreStatementWithFuel fuel
      let rawBlock := coreBlock statement .require
      let block := isolateBlock rawBlock
      have rawBlockCanonical : rawBlock.ValidFor
          (Block.ValidFor (RecursiveStatementValid statementValid)) :=
        coreBlock_validFor (RecursiveStatementValid statementValid)
          statement .require
          inductionHypothesis.statement.validFor
          inductionHypothesis.statement.preservesTokensOnSuccess
          (fun _ _ valid => valid.span_valid)
      have rawBlockValid : rawBlock.ValidFor (Block.ValidFor statementValid) :=
        rawBlockCanonical.mono (fun file body valid =>
          ⟨valid.1, fun retained member =>
            closure.close file retained (valid.2 retained member)⟩)
      have blockValid : block.ValidFor (Block.ValidFor statementValid) :=
        isolateBlock_validFor statementValid rawBlock rawBlockValid
      have rawBlockWindow : Parser.PreservesTokenWindow rawBlock :=
        coreBlock_preservesTokenWindow statement .require
          inductionHypothesis.statement.preservesTokenWindow
      have blockWindow : Parser.PreservesTokenWindow block :=
        isolateBlock_preservesTokenWindow rawBlock rawBlockWindow
      have blockCursor : Parser.CursorMonotoneOnSuccess block :=
        isolateBlock_cursorMonotoneOnSuccess rawBlock
          (coreBlock_cursorMonotoneOnSuccess statement .require)
      have blockStarts : Parser.StartsAtCurrentTokenOnSuccess block (·.span) :=
        isolateBlock_startsAtCurrentTokenOnSuccess rawBlock
          (coreBlock_startsAtCurrentTokenOnSuccess statement .require)
      have expressionLayerContract :=
        ExpressionInternals.expressionLayer_concrete_contract
          (coreExpressionWithFuel fuel) block statementValid
          inductionHypothesis.expression blockValid blockWindow blockCursor
          blockStarts
      have expressionContract : ExpressionInternals.ExpressionContract
          statementValid (coreExpressionWithFuel (fuel + 1)) := by
        simpa only [coreExpressionWithFuel, statement, rawBlock, block] using
          expressionLayerContract
      have patternLayerContract : PatternParserContract statementValid
          (patternLayer (corePatternWithFuel fuel)
            (coreExpressionWithFuel fuel)) := {
        validFor := PatternInternals.patternLayer_validFor
          (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
          (Expr.ValidFor statementValid) inductionHypothesis.pattern.validFor
          inductionHypothesis.pattern.preservesTokenWindow
          inductionHypothesis.expression.validFor
          (fun valid => valid.span_valid)
          inductionHypothesis.expression.startsAtCurrentTokenOnSuccess
          inductionHypothesis.expression.preservesTokenWindow
        preservesTokenWindow := PatternInternals.patternLayer_preservesTokenWindow
          (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
          inductionHypothesis.pattern.preservesTokenWindow
          inductionHypothesis.expression.preservesTokenWindow
        cursorMonotoneOnSuccess :=
          PatternInternals.patternLayer_cursorMonotoneOnSuccess
            (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
            inductionHypothesis.pattern.cursorMonotoneOnSuccess
            inductionHypothesis.expression.cursorMonotoneOnSuccess
        startsAtCurrentTokenOnSuccess :=
          PatternInternals.patternLayer_startsAtCurrentTokenOnSuccess
            (corePatternWithFuel fuel) (coreExpressionWithFuel fuel)
            inductionHypothesis.pattern.preservesTokenWindow
            inductionHypothesis.expression.preservesTokenWindow
      }
      have patternContract : PatternParserContract statementValid
          (corePatternWithFuel (fuel + 1)) := by
        simpa only [corePatternWithFuel] using patternLayerContract
      have layerInputs : StatementLayerInputs
          (Expr.ValidFor statementValid)
          (Pattern.ValidFor (Expr.ValidFor statementValid))
          (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
          (corePatternWithFuel fuel) := {
        nestedContract := inductionHypothesis.statement
        expressionValid := inductionHypothesis.expression.validFor
        expressionSpanValid := fun _ _ valid => valid.span_valid
        expressionWindow := inductionHypothesis.expression.preservesTokenWindow
        expressionCursorLt := inductionHypothesis.expression.cursorLtOnSuccess
        expressionStarts :=
          inductionHypothesis.expression.startsAtCurrentTokenOnSuccess
        patternValid := inductionHypothesis.pattern.validFor
        patternWindow := inductionHypothesis.pattern.preservesTokenWindow
        patternCursor := inductionHypothesis.pattern.cursorMonotoneOnSuccess
      }
      have statementLayerContract := statementLayer_contract
        (Expr.ValidFor statementValid)
        (Pattern.ValidFor (Expr.ValidFor statementValid))
        (coreStatementWithFuel fuel) (coreExpressionWithFuel fuel)
        (corePatternWithFuel fuel) layerInputs
      have statementSyntax : StatementParserContract
          (RecursiveStatementValid statementValid)
          (coreStatementWithFuel (fuel + 1)) := by
        simpa only [coreStatementWithFuel, RecursiveStatementValid] using
          statementLayerContract
      exact {
        expression := expressionContract
        pattern := patternContract
        statement := statementSyntax
      }

/-- Reassemble the pattern half from the established all-fuel expression
family through the public lifts in `TermPatternProperties`. -/
theorem corePatternWithFuel_contract_of_recursive
    (statementValid : SourceFile → Statement → Prop)
    (closure : RecursiveStatementClosure statementValid) (fuel : Nat) :
    PatternParserContract statementValid (corePatternWithFuel fuel) := {
  validFor := corePatternWithFuel_validFor (Expr.ValidFor statementValid)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.validFor)
    (fun valid => valid.span_valid)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.startsAtCurrentTokenOnSuccess)
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.preservesTokenWindow)
    fuel
  preservesTokenWindow := corePatternWithFuel_preservesTokenWindow
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.preservesTokenWindow)
    fuel
  cursorMonotoneOnSuccess := corePatternWithFuel_cursorMonotoneOnSuccess
    (fun fuel =>
      let contract := coreRecursiveWithFuel_contract statementValid closure fuel
      contract.expression.cursorMonotoneOnSuccess)
    fuel
  startsAtCurrentTokenOnSuccess :=
    corePatternWithFuel_startsAtCurrentTokenOnSuccess
      (fun fuel =>
        let contract := coreRecursiveWithFuel_contract statementValid closure fuel
        contract.expression.preservesTokenWindow)
      fuel
}

end TermInternals
end Solcore.Syntax.Parser
