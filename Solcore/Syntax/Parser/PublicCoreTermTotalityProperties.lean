import Solcore.Syntax.Parser.BlockFuelTotalityProperties
import Solcore.Syntax.Parser.PublicStatementFuelTotalityProperties

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
