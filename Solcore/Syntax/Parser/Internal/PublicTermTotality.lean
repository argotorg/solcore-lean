import Solcore.Syntax.Parser.Internal.StatementTotality
import Solcore.Syntax.Parser.Internal.ExpressionTotality
import Solcore.Syntax.Parser.Internal.PatternProofs
import Solcore.Syntax.Parser.Internal.TermBasics

/-!
Totality of the parsers of public terms: on valid input they make progress and end in an
ordinary outcome.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.TermRecursiveFuelTotalityProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicStatementFuelTotalityProperties
/-! Totality of the dynamically fueled public Core statement parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TermInternals

/-- The recursive adequacy budgets have their expected one-step statement lag. -/
theorem coreTotalityFuels_closedForm : ∀ fuel,
    coreExpressionTotalityFuel fuel = fuel ∧
    corePatternTotalityFuel fuel = fuel ∧
    coreStatementTotalityFuel fuel = fuel.pred := by
  intro fuel
  induction fuel with
  | zero =>
      simp [coreExpressionTotalityFuel, corePatternTotalityFuel,
        coreStatementTotalityFuel]
  | succ fuel inductionHypothesis =>
      rcases inductionHypothesis with
        ⟨expressionFuel, patternFuel, statementFuel⟩
      refine ⟨?_, ?_, ?_⟩
      · rw [coreExpressionTotalityFuel, expressionFuel, statementFuel]
        cases fuel <;> simp
      · rw [corePatternTotalityFuel, patternFuel, expressionFuel]
        simp
      · rw [coreStatementTotalityFuel, statementLayerFuel, expressionFuel,
          patternFuel, statementFuel]
        cases fuel <;> simp [MatchInternals.matchStatementFuel]

/-- Two units above the token count leave one unit of statement adequacy. -/
theorem coreStatementTotalityFuel_add_two (remainingCount : Nat) :
    coreStatementTotalityFuel (remainingCount + 2) =
      remainingCount + 1 := by
  rw [(coreTotalityFuels_closedForm (remainingCount + 2)).2.2]
  simp

end Solcore.Syntax.Parser.TermInternals

namespace Solcore.Syntax.Parser

/-- The public statement parser is ordinary on every valid input. -/
theorem statement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid statement := by
  intro input inputValid
  let contract := TermInternals.coreRecursiveWithFuel_fuelTotalityContract
    CoreStatement.ValidFor TermInternals.canonicalStatementClosure
      (input.remainingCount + 2)
  have adequate : input.remainingCount <
      TermInternals.coreStatementTotalityFuel
        (input.remainingCount + 2) := by
    rw [TermInternals.coreStatementTotalityFuel_add_two]
    omega
  simpa only [statement] using
    contract.statement.ordinary input inputValid adequate

/-- Public statement syntax/state laws paired with unconditional totality. -/
theorem statement_totalityContract :
    TermInternals.StatementTotalityContract CoreStatement.ValidFor
      statement := {
  toStatementParserContract := statement_canonical_contract
  invariantFree := statement_invariantFreeOnValid
}

/-- No internal invariant can escape public statement parsing. -/
theorem statement_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    statement input ≠ .invariant error :=
  statement_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PublicCoreTermTotalityProperties
/-! Unconditional totality for public Core expressions, patterns, and blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The dynamically fueled public expression is ordinary on valid input. -/
theorem expression_invariantFreeOnValid :
    Parser.InvariantFreeOnValid expression := by
  intro input inputValid
  let contract := TermInternals.coreRecursiveWithFuel_fuelTotalityContract
    CoreStatement.ValidFor TermInternals.canonicalStatementClosure
      (input.remainingCount + 1)
  have adequate : input.remainingCount <
      TermInternals.coreExpressionTotalityFuel
        (input.remainingCount + 1) := by
    rw [(TermInternals.coreTotalityFuels_closedForm
      (input.remainingCount + 1)).1]
    omega
  simpa only [expression] using
    contract.expression.ordinary input inputValid adequate

/-- No internal invariant can escape public expression parsing. -/
theorem expression_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    expression input ≠ .invariant error :=
  expression_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public expression syntax/state laws paired with unconditional totality. -/
theorem expression_elementTotalityContract :
    ElementTotalityContract expression := {
  validFor := expression_canonical_contract.validFor.mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := expression_canonical_contract.preservesTokenWindow
  cursorLtOnSuccess := expression_canonical_contract.cursorLtOnSuccess
  invariantFree := expression_ne_invariant
}

/-- The dynamically fueled public pattern is ordinary on valid input. -/
theorem pattern_invariantFreeOnValid :
    Parser.InvariantFreeOnValid pattern := by
  intro input inputValid
  let contract := TermInternals.coreRecursiveWithFuel_fuelTotalityContract
    CoreStatement.ValidFor TermInternals.canonicalStatementClosure
      (input.remainingCount + 1)
  have adequate : input.remainingCount <
      TermInternals.corePatternTotalityFuel
        (input.remainingCount + 1) := by
    rw [(TermInternals.coreTotalityFuels_closedForm
      (input.remainingCount + 1)).2.1]
    omega
  simpa only [pattern] using
    contract.pattern.ordinary input inputValid adequate

/-- No internal invariant can escape public pattern parsing. -/
theorem pattern_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    pattern input ≠ .invariant error :=
  pattern_invariantFreeOnValid.ne_invariant input inputValid error

/-- Public pattern syntax/state laws paired with unconditional totality. -/
theorem pattern_elementTotalityContract :
    ElementTotalityContract pattern := {
  validFor := pattern_canonical_contract.validFor.mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := pattern_canonical_contract.preservesTokenWindow
  cursorLtOnSuccess := by
    intro input next value parsed
    unfold pattern at parsed
    exact (TermInternals.coreRecursiveWithFuel_fuelTotalityContract
      CoreStatement.ValidFor TermInternals.canonicalStatementClosure
        (input.remainingCount + 1)).pattern.cursorLtOnSuccess parsed
  invariantFree := pattern_ne_invariant
}

/-- Either public Core-block tail policy is ordinary on valid input. -/
theorem block_invariantFreeOnValid (policy : TailExpressionPolicy) :
    Parser.InvariantFreeOnValid (block policy) := by
  intro input inputValid
  let depth := input.remainingCount + 1
  let contract := TermInternals.coreRecursiveWithFuel_fuelTotalityContract
    CoreStatement.ValidFor TermInternals.canonicalStatementClosure depth
  have adequate : input.remainingCount <
      TermInternals.coreStatementTotalityFuel depth + 1 := by
    rw [(TermInternals.coreTotalityFuels_closedForm depth).2.2]
    simp [depth]
  simpa only [block, depth] using coreBlock_ordinary_of_statementFuel
    (TermInternals.coreStatementWithFuel depth) policy
      (TermInternals.coreStatementTotalityFuel depth) contract.statement
      (TermInternals.coreStatementWithFuel_cursor_lt_onSuccess
        CoreStatement.ValidFor TermInternals.canonicalStatementClosure depth)
      input inputValid adequate

/-- No internal invariant can escape either public Core-block policy. -/
theorem block_ne_invariant (policy : TailExpressionPolicy)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    block policy input ≠ .invariant error :=
  (block_invariantFreeOnValid policy).ne_invariant input inputValid error

/-- Public block syntax/state laws paired with unconditional totality. -/
theorem block_elementTotalityContract (policy : TailExpressionPolicy) :
    ElementTotalityContract (block policy) := {
  validFor := (block_canonical_validFor policy).mono (fun _ _ _ => trivial)
  preservesTokenWindow := block_canonical_preservesTokenWindow policy
  cursorLtOnSuccess := by
    intro input next value parsed
    unfold block at parsed
    exact coreBlock_cursor_lt_onSuccess
      (TermInternals.coreStatementWithFuel (input.remainingCount + 1))
        policy parsed
  invariantFree := block_ne_invariant policy
}

end Solcore.Syntax.Parser
end
