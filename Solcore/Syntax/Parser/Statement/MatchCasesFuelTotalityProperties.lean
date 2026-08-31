import Solcore.Syntax.Parser.Statement.MatchCaseFuelTotalityProperties

/-! Fuel-aware totality for canonical Core match-case iteration. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.MatchInternals

/--
Fuel-bounded totality for a case-list parser which may succeed without
consuming when no `case` marker is present.
-/
structure FuelCaseListTotalityContract
    (caseValid : SourceFile → MatchCase → Prop)
    (parser : Parser (List MatchCase)) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (List.ValidFor caseValid)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace FuelCaseListTotalityContract

/-- Adequate arm fuel excludes every invariant from a packaged case list. -/
theorem ne_invariant
    {caseValid : SourceFile → MatchCase → Prop}
    {parser : Parser (List MatchCase)} {fuel : Nat}
    (contract : FuelCaseListTotalityContract caseValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end FuelCaseListTotalityContract

/-- Loop fuel and recursive arm fuel remain independent during iteration. -/
theorem matchCases_ordinary_of_fuels
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseFuel : Nat)
    (caseContract : FuelElementTotalityContract
      (matchCase statement patternParser) caseFuel) :
    ∀ loopFuel casesRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < caseFuel →
      (∃ cases next,
        matchCases statement patternParser loopFuel casesRev input =
          .ok cases next) ∨
      (∃ failure next,
        matchCases statement patternParser loopFuel casesRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero => intros; omega
  | succ loopFuel inductionHypothesis =>
      intro casesRev input inputValid loopAdequate caseAdequate
      unfold matchCases
      split
      · cases caseResult : matchCase statement patternParser input with
        | invariant error =>
            exact False.elim (caseContract.ne_invariant input inputValid
              caseAdequate error caseResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok retainedCase next =>
            have caseReply := caseContract.validFor input inputValid
            rw [caseResult] at caseReply
            have caseWindow := caseContract.preservesTokenWindow input
            rw [caseResult] at caseWindow
            have progress := caseContract.cursorLtOnSuccess caseResult
            have nextLoop : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress caseReply.2.1
                caseWindow.2 progress loopAdequate
            have nextCase : next.remainingCount < caseFuel :=
              remainingCount_lt_of_cursor_le caseWindow.2
                (Nat.le_of_lt progress) caseAdequate
            change
              (∃ cases final,
                (if next.cursor > input.cursor then
                  matchCases statement patternParser loopFuel
                    (retainedCase :: casesRev) next
                else
                  .invariant (.noProgress .statement next.currentSpan)) =
                    .ok cases final) ∨
              (∃ failure final,
                (if next.cursor > input.cursor then
                  matchCases statement patternParser loopFuel
                    (retainedCase :: casesRev) next
                else
                  .invariant (.noProgress .statement next.currentSpan)) =
                    .reject failure final)
            rw [if_pos progress]
            exact inductionHypothesis (retainedCase :: casesRev) next
              caseReply.2.1 nextLoop nextCase
      · exact Or.inl ⟨casesRev.reverse, input, rfl⟩

/-- Adequate loop and arm fuels rule out every case-list invariant. -/
theorem matchCases_ne_invariant_of_fuels
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (caseFuel loopFuel : Nat)
    (caseContract : FuelElementTotalityContract
      (matchCase statement patternParser) caseFuel)
    (casesRev : List MatchCase) (input : State)
    (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (caseAdequate : input.remainingCount < caseFuel)
    (error : ParserInvariantError) :
    matchCases statement patternParser loopFuel casesRev input ≠
      .invariant error := by
  intro failed
  rcases matchCases_ordinary_of_fuels statement patternParser caseFuel
      caseContract loopFuel casesRev input inputValid loopAdequate
        caseAdequate with
    ⟨cases, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/--
Package the production wrapper whose loop fuel is chosen dynamically from the
current token window while recursive arm fuel remains an explicit bound.
-/
theorem matchCases_production_fuelTotalityContract
    (expressionValueValid : SourceFile → Expr → Prop)
    (patternValueValid : SourceFile → Pattern → Prop)
    (yulValueValid : SourceFile → YulStmt → Prop)
    (statement : Parser Statement) (patternParser : Parser Pattern)
    (statementFuel patternFuel : Nat)
    (statementContract : TermInternals.FuelStatementTotalityContract
      (Statement.ValidFor expressionValueValid patternValueValid
        yulValueValid) statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (patternValid : patternParser.ValidFor patternValueValid)
    (patternContract : FuelElementTotalityContract
      patternParser patternFuel) :
    FuelCaseListTotalityContract
      (MatchCase.ValidFor expressionValueValid patternValueValid
        yulValueValid)
      (fun input => matchCases statement patternParser
        (input.remainingCount + 1) [] input)
      (Nat.min (patternFuel + 1) (statementFuel + 3)) := by
  let caseContract := matchCase_fuelElementTotalityContract
    expressionValueValid patternValueValid yulValueValid statement
      patternParser statementFuel patternFuel statementContract
      statementStrict patternValid patternContract
  let caseValid := matchCase_validFor expressionValueValid patternValueValid
    yulValueValid statement patternParser statementContract.validFor
      statementContract.preservesTokenWindow.preservesTokensOnSuccess
      patternValid
      patternContract.preservesTokenWindow.preservesTokensOnSuccess
      (fun {_input _value _next} parsed =>
        Nat.le_of_lt (patternContract.cursorLtOnSuccess parsed))
  exact {
    validFor := fun input inputValid =>
      matchCases_validFor expressionValueValid patternValueValid
        yulValueValid statement patternParser caseValid
          (input.remainingCount + 1) [] input inputValid (by
            intro item member
            simp at member)
    preservesTokenWindow := fun input =>
      matchCases_preservesTokenWindow statement patternParser
        caseContract.preservesTokenWindow (input.remainingCount + 1) [] input
    cursorMonotoneOnSuccess := fun input value next result =>
      matchCases_cursorMonotoneOnSuccess statement patternParser
        (input.remainingCount + 1) [] input value next result
    ordinary := fun input inputValid adequate =>
      matchCases_ordinary_of_fuels statement patternParser
        (Nat.min (patternFuel + 1) (statementFuel + 3)) caseContract
        (input.remainingCount + 1) [] input inputValid (by omega) adequate
  }

end Solcore.Syntax.Parser.MatchInternals
