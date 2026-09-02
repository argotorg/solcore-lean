import Solcore.Syntax.DeclarativePragmaItemsOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.PragmaTotalityProperties

/-! Exact executable ordinary success for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTokenPresentAt_of_isSymbol_eq_true
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.PragmaItemsTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pragmaDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .pragmaDecl parsed).1⟩

private theorem remainingCount_lt_after_pragma_item
    {fuel : Nat} {input afterComma afterItem : State}
    {comma : Token} {item : Identifier}
    (commaResult : symbol .comma .pragmaDecl input = .ok comma afterComma)
    (itemResult : identifier .pragmaDecl afterComma = .ok item afterItem)
    (adequate : input.remainingCount < fuel + 1) :
    afterItem.remainingCount < fuel := by
  rcases symbol_ok_state_shape .comma .pragmaDecl commaResult with
    ⟨commaFound, rfl⟩
  rcases identifier_ok_state_shape .pragmaDecl itemResult with
    ⟨_token, _found, _span, _tokens, itemCursor⟩
  have itemWindow := identifier_preservesTokenWindow .pragmaDecl
    { input with cursor := input.cursor + 1 }
  rw [itemResult] at itemWindow
  have cursorBeforeEnd :=
    State.cursor_lt_endIndex_of_peek?_eq_some commaFound
  have endIndexEq : afterItem.window.endIndex = input.window.endIndex := by
    simpa using congrArg TokenWindow.endIndex itemWindow.2
  have cursorEq : afterItem.cursor = input.cursor + 2 := by
    simpa only [State.cursor] using itemCursor
  simp only [State.remainingCount] at adequate ⊢
  rw [endIndexEq, cursorEq]
  omega

/-- With adequate fuel, a successful executable tail returns the reverse
accumulator followed by the exact forward suffix parsed from the input. -/
theorem pragmaItemsTail_success_ordinaryOutcome_sound_of_remainingCount_lt :
    ∀ fuel itemsRev input items output,
      input.remainingCount < fuel →
      pragmaItemsTail fuel itemsRev input = .ok items output →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.PragmaItemsTailOrdinaryParses
          input.declarativeRemainder suffix output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items output adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input items output adequate result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent)⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .pragmaDecl input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl
                  commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases semicolonPresent : isSymbol afterComma .semicolon with
              | true =>
                  simp only [semicolonPresent, if_true] at result
                  cases result
                  exact ⟨[], by simp,
                    .trailing comma.span
                      (pragmaItemsTokenPresentAt_of_isSymbol_eq_true .comma
                        commaPresent)
                      (symbol_success_exactTokenParses .comma .pragmaDecl
                        commaResult)
                      (pragmaItemsTokenPresentAt_of_isSymbol_eq_true
                        .semicolon semicolonPresent)⟩
              | false =>
                  simp only [semicolonPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : identifier .pragmaDecl afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      rcases inductionHypothesis (item :: itemsRev) afterItem
                          items output
                          (remainingCount_lt_after_pragma_item commaResult
                            itemResult adequate)
                          result with ⟨suffix, itemsEq, tailParsed⟩
                      refine ⟨item :: suffix, ?_,
                        .next comma.span
                          (pragmaItemsTokenPresentAt_of_isSymbol_eq_true
                            .comma commaPresent)
                          (symbol_success_exactTokenParses .comma .pragmaDecl
                            commaResult)
                          (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                            semicolonPresent)
                          (identifier_success_sound .pragmaDecl itemResult)
                          tailParsed⟩
                      simpa [List.reverse_cons, List.append_assoc] using
                        itemsEq

/-- Production fuel specializes successful tail reflection without exposing
the fuel arithmetic to callers. -/
theorem pragmaItemsTail_production_success_ordinaryOutcome_sound
    (itemsRev : List Identifier) {input output : State}
    {items : List Identifier}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .ok items output) :
    ∃ suffix,
      items = itemsRev.reverse ++ suffix ∧
      DeclarativeGrammar.PragmaItemsTailOrdinaryParses
        input.declarativeRemainder suffix output.declarativeRemainder :=
  pragmaItemsTail_success_ordinaryOutcome_sound_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev input items output (by omega) result

/-- Every successful public pragma-item scan records exact priority guards,
forward item order, and its final remainder. -/
theorem pragmaItems_success_ordinaryOutcome_sound
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    DeclarativeGrammar.PragmaItemsOrdinaryParses
      input.declarativeRemainder items output.declarativeRemainder := by
  unfold pragmaItems at result
  cases semicolonPresent : isSymbol input .semicolon with
  | true =>
      simp only [semicolonPresent, if_true] at result
      cases result
      exact .empty
        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true .semicolon
          semicolonPresent)
  | false =>
      simp only [semicolonPresent, Bool.false_eq_true, if_false] at result
      cases firstResult : identifier .pragmaDecl input with
      | invariant error => simp [firstResult] at result
      | reject failure rejected => simp [firstResult] at result
      | ok first afterFirst =>
          simp only [firstResult] at result
          rcases pragmaItemsTail_production_success_ordinaryOutcome_sound
              [first] result with ⟨suffix, itemsEq, tailParsed⟩
          have itemsForm : items = first :: suffix := by simpa using itemsEq
          rw [itemsForm]
          exact .nonempty
            (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonPresent)
            (identifier_success_sound .pragmaDecl firstResult) tailParsed

end Solcore.Syntax.Parser.PragmaInternals
