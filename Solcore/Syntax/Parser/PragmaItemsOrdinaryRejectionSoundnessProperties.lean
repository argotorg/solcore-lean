import Solcore.Syntax.Parser.PragmaItemsOrdinarySuccessSoundnessProperties

/-! Exact executable ordinary rejection for pragma item scanning. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
    (value : Symbol) {input : State}
    (present : isSymbol input value = true) :
    DeclarativeGrammar.PragmaItemsTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .pragmaDecl present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .pragmaDecl parsed).1⟩

private theorem remainingCount_lt_after_rejected_pragma_item_step
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

/-- With adequate fuel, every executable tail rejection records the first
checked identifier rejection reached after exact comma/semicolon priority. -/
theorem pragmaItemsTail_reject_ordinaryOutcome_sound_of_remainingCount_lt :
    ∀ fuel itemsRev input failure rejected,
      input.remainingCount < fuel →
      pragmaItemsTail fuel itemsRev input = .reject failure rejected →
      DeclarativeGrammar.PragmaItemsTailRejects
        input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input failure rejected adequate
      omega
  | succ fuel inductionHypothesis =>
      intro itemsRev input failure rejected adequate result
      unfold pragmaItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false => simp [commaPresent] at result
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .pragmaDecl input with
          | invariant error => simp [commaResult] at result
          | reject commaFailure commaRejected =>
              rcases symbol_eq_ok_of_isSymbol_eq_true .comma .pragmaDecl
                  commaPresent with ⟨comma, parsed⟩
              rw [parsed] at commaResult
              contradiction
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases semicolonPresent : isSymbol afterComma .semicolon with
              | true => simp [semicolonPresent] at result
              | false =>
                  simp only [semicolonPresent, Bool.false_eq_true, if_false]
                    at result
                  cases itemResult : identifier .pragmaDecl afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject itemFailure itemRejected =>
                      simp only [itemResult] at result
                      cases result
                      exact .identifierRejected comma.span
                        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
                          .comma commaPresent)
                        (symbol_success_exactTokenParses .comma .pragmaDecl
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                          semicolonPresent)
                        (identifier_reject_sound .pragmaDecl itemResult)
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      exact .laterRejected comma.span
                        (pragmaItemsTokenPresentAt_of_isSymbol_eq_true_reject
                          .comma commaPresent)
                        (symbol_success_exactTokenParses .comma .pragmaDecl
                          commaResult)
                        (symbolAbsentAt_of_isSymbol_eq_false .semicolon
                          semicolonPresent)
                        (identifier_success_sound .pragmaDecl itemResult)
                        (inductionHypothesis (item :: itemsRev) afterItem
                          failure rejected
                          (remainingCount_lt_after_rejected_pragma_item_step
                            commaResult itemResult adequate)
                          result)

/-- Production fuel specializes rejected tail reflection without exposing
the fuel arithmetic to callers. -/
theorem pragmaItemsTail_production_reject_ordinaryOutcome_sound
    (itemsRev : List Identifier) {input rejected : State}
    {failure : Failure}
    (result : pragmaItemsTail (input.remainingCount + 1) itemsRev input =
      .reject failure rejected) :
    DeclarativeGrammar.PragmaItemsTailRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  pragmaItemsTail_reject_ordinaryOutcome_sound_of_remainingCount_lt
    (input.remainingCount + 1) itemsRev input failure rejected (by omega)
      result

/-- Every rejected public pragma-item scan records whether the first checked
identifier or a committed suffix rejected. -/
theorem pragmaItems_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    DeclarativeGrammar.PragmaItemsRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold pragmaItems at result
  cases semicolonPresent : isSymbol input .semicolon with
  | true => simp [semicolonPresent] at result
  | false =>
      simp only [semicolonPresent, Bool.false_eq_true, if_false] at result
      have semicolonAbsent :=
        symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonPresent
      cases firstResult : identifier .pragmaDecl input with
      | invariant error => simp [firstResult] at result
      | reject firstFailure firstRejected =>
          simp only [firstResult] at result
          cases result
          exact .firstIdentifierRejected semicolonAbsent
            (identifier_reject_sound .pragmaDecl firstResult)
      | ok first afterFirst =>
          simp only [firstResult] at result
          exact .tailRejected semicolonAbsent
            (identifier_success_sound .pragmaDecl firstResult)
            (pragmaItemsTail_production_reject_ordinaryOutcome_sound [first]
              result)

end Solcore.Syntax.Parser.PragmaInternals
