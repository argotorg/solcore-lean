import Solcore.Syntax.Parser.BlockTotalityProperties
import Solcore.Syntax.Parser.TermStatementFallbackFuelTotalityProperties

/-! Recursive-fuel totality for Core blocks and isolated Core blocks. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem closeCoreBlock_ordinary (opening : Token)
    (policy : TailExpressionPolicy) (bodyRev : List Statement) :
    Parser.Ordinary (closeCoreBlock opening policy bodyRev) := by
  intro input
  cases result : closeCoreBlock opening policy bodyRev input with
  | ok body next => exact Or.inl ⟨body, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      exact False.elim
        (closeCoreBlock_ne_invariant opening policy bodyRev input error result)

/--
The block-item loop stays ordinary while both its decreasing loop fuel and
the fixed recursive statement fuel are adequate.
-/
theorem coreBlockItems_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (opening : Token) (policy : TailExpressionPolicy) :
    ∀ loopFuel bodyRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < statementFuel →
      (∃ body final,
        coreBlockItems statement opening policy loopFuel bodyRev input =
          .ok body final) ∨
      (∃ failure final,
        coreBlockItems statement opening policy loopFuel bodyRev input =
          .reject failure final) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro bodyRev input inputValid loopAdequate statementAdequate
      unfold coreBlockItems
      split
      · exact closeCoreBlock_ordinary opening policy bodyRev input
      · split
        · have atEnd : input.atEnd = true := by assumption
          have cursorAtEnd : input.window.endIndex ≤ input.cursor := by
            simpa [State.atEnd] using atEnd
          have peekNone : input.peek? = none := by
            unfold State.peek?
            simp [Nat.not_lt_of_ge cursorAtEnd]
          cases closingResult : symbol .rightBrace .statement input with
          | ok closing next =>
              simp [symbol, acceptToken, peekNone, rejectAt] at closingResult
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | invariant error =>
              exact False.elim
                ((symbol_ordinary .rightBrace .statement).ne_invariant
                  input error closingResult)
        · cases statementResult : statement input with
          | invariant error =>
              exact False.elim
                (contract.ne_invariant input inputValid statementAdequate
                  error statementResult)
          | reject failure rejected =>
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok value next =>
            have replyValid := contract.validFor input inputValid
            rw [statementResult] at replyValid
            have replyWindow := contract.preservesTokenWindow input
            rw [statementResult] at replyWindow
            have progress := statementStrict statementResult
            have nextLoopAdequate : next.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress replyValid.2.1
                replyWindow.2 progress loopAdequate
            have nextStatementAdequate :
                next.remainingCount < statementFuel :=
              remainingCount_lt_of_cursor_le replyWindow.2
                (Nat.le_of_lt progress) statementAdequate
            dsimp only
            split
            · exact inductionHypothesis (value :: bodyRev) next
                replyValid.2.1 nextLoopAdequate nextStatementAdequate
            · omega

/-- One opening-brace token supplies the extra unit needed by statement fuel. -/
theorem coreBlock_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final, coreBlock statement policy input = .ok body final) ∨
      (∃ failure final,
        coreBlock statement policy input = .reject failure final) := by
  rcases (symbol_ordinary .leftBrace .statement) input with
    ⟨opening, afterOpening, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .statement input
      inputValid
    rw [openingResult] at openingReply
    have openingWindow :=
      symbol_preservesTokenWindow .leftBrace .statement input
    rw [openingResult] at openingWindow
    have openingProgress : input.cursor < afterOpening.cursor :=
      acceptToken_cursor_lt_onSuccess (.symbol .leftBrace) .statement
        (· == .symbol .leftBrace) openingResult
    have statementAdequate :
        afterOpening.remainingCount < statementFuel :=
      remainingCount_lt_after_strict_progress openingReply.2.1
        openingWindow.2 openingProgress adequate
    simpa only [coreBlock, openingResult] using
      coreBlockItems_ordinary_of_statementFuel statement statementFuel
        contract statementStrict opening policy
          (afterOpening.remainingCount + 1) [] afterOpening openingReply.2.1
          (by omega) statementAdequate
  · exact Or.inr ⟨failure, rejected, by
      simp only [coreBlock, openingResult]⟩

/-- Adequate statement fuel excludes every Core-block invariant. -/
theorem coreBlock_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    coreBlock statement policy input ≠ .invariant error := by
  intro failed
  rcases coreBlock_ordinary_of_statementFuel statement policy statementFuel
      contract statementStrict input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Isolation preserves fuel adequacy because its child window only shrinks. -/
theorem isolatedCoreBlock_ordinary_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1) :
    (∃ body final,
      isolateBlock (coreBlock statement policy) input = .ok body final) ∨
    (∃ failure final,
      isolateBlock (coreBlock statement policy) input =
        .reject failure final) := by
  cases captureResult : BlockInternals.captureBlock? input with
  | none =>
      simpa only [isolateBlock, captureResult] using
        coreBlock_ordinary_of_statementFuel statement policy statementFuel
          contract statementStrict input inputValid adequate
  | some captured =>
      have capturedValid :=
        BlockInternals.captureBlock?_validFor inputValid captureResult
      let child := input.enterWindow input.cursor captured.window
      have childAdequate : child.remainingCount < statementFuel + 1 := by
        simp only [child, State.remainingCount, State.enterWindow]
        have endLe := capturedValid.endIndex_le_window
        simp only [State.remainingCount] at adequate
        omega
      rcases coreBlock_ordinary_of_statementFuel statement policy
          statementFuel contract statementStrict child capturedValid.entered
            childAdequate with
        ⟨body, childAfter, childResult⟩ |
        ⟨failure, childAfter, childResult⟩
      · exact Or.inl ⟨body,
          State.mergeDiagnostics
            ({ input with cursor := captured.window.endIndex }) childAfter, by
          simp only [isolateBlock, captureResult, childResult, child]⟩
      · exact Or.inl ⟨{ span := captured.span, value := [] },
          State.emit (State.mergeDiagnostics
            ({ input with cursor := captured.window.endIndex }) childAfter)
              failure.toDiagnostic, by
          simp only [isolateBlock, captureResult, childResult, child]⟩

/-- Adequate statement fuel also excludes isolated-block invariants. -/
theorem isolatedCoreBlock_ne_invariant_of_statementFuel
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < statementFuel + 1)
    (error : ParserInvariantError) :
    isolateBlock (coreBlock statement policy) input ≠ .invariant error := by
  intro failed
  rcases isolatedCoreBlock_ordinary_of_statementFuel statement policy
      statementFuel contract statementStrict input inputValid adequate with
    ⟨body, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Package a recursive-fuel Core block for expression-layer recursion. -/
theorem coreBlock_fuelTotalityContract
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (statementSpan : ∀ file value,
      statementValueValid file value → value.span.ValidFor file) :
    FuelElementTotalityContract
      (coreBlock statement policy) (statementFuel + 1) := {
  validFor := (coreBlock_validFor statementValueValid statement policy
    contract.validFor contract.preservesTokenWindow.preservesTokensOnSuccess
      statementSpan).mono (fun _ _ _ => trivial)
  preservesTokenWindow := coreBlock_preservesTokenWindow statement policy
    contract.preservesTokenWindow
  cursorLtOnSuccess := coreBlock_cursor_lt_onSuccess statement policy
  ordinary := coreBlock_ordinary_of_statementFuel statement policy
    statementFuel contract statementStrict
}

/-- Package the derive-safe captured Core block at the same recursive fuel. -/
theorem isolatedCoreBlock_fuelTotalityContract
    {statementValueValid : SourceFile → Statement → Prop}
    (statement : Parser Statement) (policy : TailExpressionPolicy)
    (statementFuel : Nat)
    (contract : TermInternals.FuelStatementTotalityContract
      statementValueValid statement statementFuel)
    (statementStrict : ∀ {input next : State} {value : Statement},
      statement input = .ok value next → input.cursor < next.cursor)
    (statementSpan : ∀ file value,
      statementValueValid file value → value.span.ValidFor file) :
    FuelElementTotalityContract
      (isolateBlock (coreBlock statement policy)) (statementFuel + 1) := {
  validFor := (isolatedCoreBlock_validFor statementValueValid statement policy
    contract.validFor contract.preservesTokenWindow.preservesTokensOnSuccess
      statementSpan).mono (fun _ _ _ => trivial)
  preservesTokenWindow := isolatedCoreBlock_preservesTokenWindow statement
    policy contract.preservesTokenWindow
  cursorLtOnSuccess := BlockInternals.isolateBlock_cursor_lt_onSuccess _
    (coreBlock_cursor_lt_onSuccess statement policy)
  ordinary := isolatedCoreBlock_ordinary_of_statementFuel statement policy
    statementFuel contract statementStrict
}

end Solcore.Syntax.Parser
