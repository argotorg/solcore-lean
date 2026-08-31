import Solcore.Syntax.Parser.Statement.ForItemFuelTotalityProperties

/-! Fuel-aware totality for comma-separated Core `for` header items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

/--
Validity, window, monotonicity, and fuel-bounded ordinary control for a
possibly empty `for` item list. No strict field is required for empty lists.
-/
structure ForItemsFuelTotalityContract
    (itemValid : SourceFile → ForItem → Prop)
    (parser : Parser (List ForItem)) (fuel : Nat) : Prop where
  validFor : parser.ValidFor (List.ValidFor itemValid)
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  cursorMonotoneOnSuccess : Parser.CursorMonotoneOnSuccess parser
  ordinary : ∀ input, input.ValidFor → input.remainingCount < fuel →
    (∃ items next, parser input = .ok items next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace ForItemsFuelTotalityContract

theorem ne_invariant
    {itemValid : SourceFile → ForItem → Prop}
    {parser : Parser (List ForItem)} {fuel : Nat}
    (contract : ForItemsFuelTotalityContract itemValid parser fuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases contract.ordinary input inputValid adequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end ForItemsFuelTotalityContract

/--
The loop fuel decreases independently of the fixed fuel required by every
`forItem` invocation.
-/
theorem forItemsTail_ordinary_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel) :
    ∀ loopFuel itemsRev input,
      input.ValidFor → input.remainingCount < loopFuel →
      input.remainingCount < itemFuel →
      (∃ items next,
        forItemsTail expression stop loopFuel itemsRev input =
          .ok items next) ∨
      (∃ failure next,
        forItemsTail expression stop loopFuel itemsRev input =
          .reject failure next) := by
  intro loopFuel
  induction loopFuel with
  | zero =>
      intro itemsRev input inputValid loopAdequate itemAdequate
      omega
  | succ loopFuel inductionHypothesis =>
      intro itemsRev input inputValid loopAdequate itemAdequate
      unfold forItemsTail
      split
      · cases commaResult : symbol .comma .statement input with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .comma .statement input error commaResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok comma afterComma =>
            have commaReply := symbol_validFor .comma .statement input
              inputValid
            rw [commaResult] at commaReply
            have commaWindow :=
              symbol_preservesTokenWindow .comma .statement input
            rw [commaResult] at commaWindow
            have commaProgress : input.cursor < afterComma.cursor :=
              acceptToken_cursor_lt_onSuccess (.symbol .comma) .statement
                (· == .symbol .comma) commaResult
            have commaLoopAdequate :
                afterComma.remainingCount < loopFuel :=
              remainingCount_lt_after_strict_progress commaReply.2.1
                commaWindow.2 commaProgress loopAdequate
            have commaItemAdequate :
                afterComma.remainingCount < itemFuel :=
              remainingCount_lt_of_cursor_le commaWindow.2
                (Nat.le_of_lt commaProgress) itemAdequate
            dsimp only
            split
            · exact Or.inr ⟨{
                  span := afterComma.currentSpan
                  found := afterComma.peekKind?
                  expected := { head := .expression, tail := [] }
                  context := .statement
                }, afterComma, rfl⟩
            · cases itemResult : forItem expression afterComma with
              | invariant error =>
                  exact False.elim (itemContract.ne_invariant afterComma
                    commaReply.2.1 commaItemAdequate error itemResult)
              | reject failure rejected =>
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok item next =>
                  have itemReply := itemContract.validFor afterComma
                    commaReply.2.1
                  rw [itemResult] at itemReply
                  have itemWindow := itemContract.preservesTokenWindow
                    afterComma
                  rw [itemResult] at itemWindow
                  have itemProgress :=
                    itemContract.cursorLtOnSuccess itemResult
                  have nextLoopAdequate :
                      next.remainingCount < loopFuel :=
                    remainingCount_lt_of_cursor_le itemWindow.2
                      (Nat.le_of_lt itemProgress) commaLoopAdequate
                  have nextItemAdequate :
                      next.remainingCount < itemFuel :=
                    remainingCount_lt_of_cursor_le itemWindow.2
                      (Nat.le_of_lt itemProgress) commaItemAdequate
                  dsimp only
                  split
                  · exact inductionHypothesis (item :: itemsRev) next
                      itemReply.2.1 nextLoopAdequate nextItemAdequate
                  · omega
      · exact Or.inl ⟨itemsRev.reverse, input, rfl⟩

theorem forItemsTail_ne_invariant_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (loopFuel : Nat) (itemsRev : List ForItem)
    (input : State) (inputValid : input.ValidFor)
    (loopAdequate : input.remainingCount < loopFuel)
    (itemAdequate : input.remainingCount < itemFuel)
    (error : ParserInvariantError) :
    forItemsTail expression stop loopFuel itemsRev input ≠
      .invariant error := by
  intro failed
  rcases forItemsTail_ordinary_of_itemFuel expression stop itemFuel
      itemContract loopFuel itemsRev input inputValid loopAdequate
        itemAdequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- A complete list is ordinary below the fixed item-parser fuel bound. -/
theorem forItems_ordinary_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < itemFuel) :
    (∃ items next, forItems expression stop input = .ok items next) ∨
      (∃ failure next,
        forItems expression stop input = .reject failure next) := by
  unfold forItems
  split
  · exact Or.inl ⟨[], input, rfl⟩
  · cases itemResult : forItem expression input with
    | invariant error =>
        exact False.elim
          (itemContract.ne_invariant input inputValid adequate error itemResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok item next =>
        have itemReply := itemContract.validFor input inputValid
        rw [itemResult] at itemReply
        have itemWindow := itemContract.preservesTokenWindow input
        rw [itemResult] at itemWindow
        have progress := itemContract.cursorLtOnSuccess itemResult
        have nextItemAdequate : next.remainingCount < itemFuel :=
          remainingCount_lt_of_cursor_le itemWindow.2
            (Nat.le_of_lt progress) adequate
        exact forItemsTail_ordinary_of_itemFuel expression stop itemFuel
          itemContract (next.remainingCount + 1) [item] next itemReply.2.1
            (by omega) nextItemAdequate

theorem forItems_ne_invariant_of_itemFuel
    (expression : Parser Expr) (stop : Symbol) (itemFuel : Nat)
    (itemContract : FuelElementTotalityContract
      (forItem expression) itemFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < itemFuel)
    (error : ParserInvariantError) :
    forItems expression stop input ≠ .invariant error := by
  intro failed
  rcases forItems_ordinary_of_itemFuel expression stop itemFuel itemContract
      input inputValid adequate with
    ⟨items, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

/-- Build the non-strict list contract from the strict canonical item parser. -/
theorem forItems_fuelTotalityContract
    {statementValid : SourceFile → Statement → Prop}
    (expression : Parser Expr) (stop : Symbol) (expressionFuel : Nat)
    (expressionSyntax :
      ExpressionInternals.ExpressionContract statementValid expression)
    (expressionTotality :
      FuelElementTotalityContract expression expressionFuel) :
    ForItemsFuelTotalityContract
      (ForItem.ValidFor (Expr.ValidFor statementValid))
      (forItems expression stop) expressionFuel := by
  let itemContract := forItem_fuelElementTotalityContract expression
    expressionFuel expressionSyntax expressionTotality
  exact {
    validFor := forItems_validFor expression stop
      (Expr.ValidFor statementValid)
      (forItem_validFor expression (Expr.ValidFor statementValid)
        expressionSyntax.validFor (fun _ _ valid => valid.span_valid)
          expressionSyntax.preservesTokenWindow
            expressionSyntax.cursorLtOnSuccess
              expressionSyntax.startsAtCurrentTokenOnSuccess)
    preservesTokenWindow := forItems_preservesTokenWindow expression stop
      itemContract.preservesTokenWindow
    cursorMonotoneOnSuccess := forItems_cursorMonotoneOnSuccess expression stop
      expressionSyntax.cursorMonotoneOnSuccess
    ordinary := forItems_ordinary_of_itemFuel expression stop expressionFuel
      itemContract
  }

end Solcore.Syntax.Parser.ControlInternals
