import Solcore.Syntax.Parser.CoreForItemSoundnessProperties
import Solcore.Syntax.Parser.CoreForItemsDiagnosticReflectionProperties

/-!
Exact diagnostic-free soundness for the reverse-accumulating Core `for` item
loop and its public forward-order list parser.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ControlInternals

private theorem symbolTokenAt_of_isSymbol_eq_true (symbolValue : Symbol)
    {input : State} (present : isSymbol input symbolValue = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol symbolValue } := by
  unfold isSymbol State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      change (token.value == .symbol symbolValue) = true at present
      have parsed : symbol symbolValue .statement input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold symbol acceptToken
        simp only [found, present, ↓reduceIte]
      exact ⟨token.span, (symbol_ok_tokenAt symbolValue .statement parsed).1⟩

/--
The executable reverse accumulator is the prefix of the returned list; the
declarative tail is the remaining forward suffix.
-/
theorem forItemsTail_success_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder) :
    ∀ fuel itemsRev input items next,
      next.diagnosticsRev = [] →
      forItemsTail expression stop fuel itemsRev input = .ok items next →
      ∃ suffix,
        items = itemsRev.reverse ++ suffix ∧
        DeclarativeGrammar.ForItemsTailParses expressionParses stop
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        input.diagnosticsRev = [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next diagnosticFree result
      simp [forItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next diagnosticFree result
      unfold forItemsTail at result
      cases commaPresent : isSymbol input .comma with
      | false =>
          simp only [commaPresent, Bool.false_eq_true, if_false] at result
          cases result
          exact ⟨[], by simp,
            .done (symbolAbsentAt_of_isSymbol_eq_false .comma commaPresent),
            diagnosticFree⟩
      | true =>
          simp only [commaPresent, if_true] at result
          cases commaResult : symbol .comma .statement input with
          | invariant error => simp [commaResult] at result
          | reject failure rejected => simp [commaResult] at result
          | ok comma afterComma =>
              simp only [commaResult] at result
              cases stopPresent : isSymbol afterComma stop with
              | true =>
                  simp only [stopPresent, if_true] at result
                  unfold rejectAt at result
                  contradiction
              | false =>
                  simp only [stopPresent, Bool.false_eq_true, if_false] at result
                  cases itemResult : forItem expression afterComma with
                  | invariant error => simp [itemResult] at result
                  | reject failure rejected => simp [itemResult] at result
                  | ok item afterItem =>
                      simp only [itemResult] at result
                      by_cases progress : afterItem.cursor > afterComma.cursor
                      · simp only [progress, if_true] at result
                        rcases inductionHypothesis (item :: itemsRev)
                            afterItem items next diagnosticFree result with
                          ⟨suffix, itemsEq, tailGrammar, afterItemFree⟩
                        have itemGrammar := forItem_success_sound expression
                          expressionParses expressionReflects expressionSound
                            afterItemFree itemResult
                        have afterCommaFree :=
                          forItem_reflectsDiagnosticFreeOnSuccess expression
                            expressionReflects afterComma item afterItem
                              itemResult afterItemFree
                        have inputFree :=
                          symbol_reflectsDiagnosticFreeOnSuccess .comma
                            .statement input comma afterComma commaResult
                              afterCommaFree
                        refine ⟨item :: suffix, ?_,
                          .next comma.span
                            (symbol_success_exactTokenParses .comma .statement
                              commaResult)
                            (symbolAbsentAt_of_isSymbol_eq_false stop
                              stopPresent)
                            itemGrammar (by
                              simpa [State.declarativeRemainder] using
                                progress) tailGrammar,
                          inputFree⟩
                        simpa [List.reverse_cons, List.append_assoc] using
                          itemsEq
                      · simp only [progress, if_false] at result
                        contradiction

/-- Every public success is a forward list with the exact prioritized stop. -/
theorem forItems_success_sound
    (expression : Parser Expr) (stop : Symbol)
    (expressionParses : DeclarativeGrammar.Remainder → Expr →
      DeclarativeGrammar.Remainder → Prop)
    (expressionReflects : Parser.ReflectsDiagnosticFreeOnSuccess expression)
    (expressionSound : ∀ {input next : State} {value : Expr},
      next.diagnosticsRev = [] → expression input = .ok value next →
      expressionParses input.declarativeRemainder value
        next.declarativeRemainder)
    (expressionStrict : ∀ {input next : State} {value : Expr},
      expression input = .ok value next → input.cursor < next.cursor)
    {input next : State} {items : List ForItem}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : forItems expression stop input = .ok items next) :
    DeclarativeGrammar.ForItemsParses expressionParses stop
      input.declarativeRemainder items next.declarativeRemainder := by
  unfold forItems at result
  cases stopPresent : isSymbol input stop with
  | true =>
      simp only [stopPresent, if_true] at result
      cases result
      rcases symbolTokenAt_of_isSymbol_eq_true stop stopPresent with
        ⟨span, stopCurrent⟩
      exact .empty span stopCurrent
  | false =>
      simp only [stopPresent, Bool.false_eq_true, if_false] at result
      cases itemResult : forItem expression input with
      | invariant error => simp [itemResult] at result
      | reject failure rejected => simp [itemResult] at result
      | ok first afterFirst =>
          simp only [itemResult] at result
          rcases forItemsTail_success_sound expression stop expressionParses
              expressionReflects expressionSound
              (afterFirst.remainingCount + 1) [first] afterFirst items next
              diagnosticFree result with
            ⟨suffix, itemsEq, tailGrammar, afterFirstFree⟩
          have firstGrammar := forItem_success_sound expression
            expressionParses expressionReflects expressionSound
              afterFirstFree itemResult
          have progress := forItem_cursor_lt_onSuccess_of_expressionStrict
            expression expressionStrict itemResult
          rw [itemsEq]
          simpa using DeclarativeGrammar.ForItemsParses.nonempty
            (symbolAbsentAt_of_isSymbol_eq_false stop stopPresent)
            firstGrammar (by
              simpa [State.declarativeRemainder] using progress) tailGrammar

end Solcore.Syntax.Parser.ControlInternals
