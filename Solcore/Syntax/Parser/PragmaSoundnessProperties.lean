import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Pragma

/-! Success soundness of the canonical pragma parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem pragmaItemsTail_success_sound :
    ∀ fuel itemsRev input items next,
      PragmaInternals.pragmaItemsTail fuel itemsRev input = .ok items next →
      ∃ restItems,
        items = itemsRev.reverse ++ restItems ∧
        DeclarativeGrammar.PragmaItemsTailParses input.tokens
          input.window.endIndex input.cursor restItems next.cursor ∧
        next.tokens = input.tokens ∧ next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input items next result
      simp [PragmaInternals.pragmaItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input items next result
      unfold PragmaInternals.pragmaItemsTail at result
      split at result
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            have commaSound := symbol_ok_tokenAt
              .comma .pragmaDecl commaResult
            simp only [commaResult] at result
            split at result
            · have trailing :
                  DeclarativeGrammar.PragmaItemsTailParses input.tokens
                    input.window.endIndex input.cursor []
                    afterComma.cursor := by
                simpa only [commaSound.2, State.cursor] using
                  (DeclarativeGrammar.PragmaItemsTailParses.trailing
                    comma.span commaSound.1)
              have commaTokens : afterComma.tokens = input.tokens := by
                rw [commaSound.2]
              have commaWindow : afterComma.window = input.window := by
                rw [commaSound.2]
              cases result
              exact ⟨[], by simp, trailing, commaTokens, commaWindow⟩
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  have itemSound := identifier_ok_tokenAt
                    .pragmaDecl itemResult
                  simp only [itemResult] at result
                  rcases inductionHypothesis (item :: itemsRev)
                    afterItem items next result
                    with ⟨restItems, itemsEq, tailGrammar,
                      nextTokens, nextWindow⟩
                  have itemToken :
                      DeclarativeGrammar.TokenAt input.tokens
                        input.window.endIndex (input.cursor + 1) {
                          span := item.span
                          value := .identifier item.value
                        } := by
                    simpa only [commaSound.2, State.tokens, State.window,
                      State.cursor] using itemSound.1
                  have recursiveTail :
                      DeclarativeGrammar.PragmaItemsTailParses input.tokens
                        input.window.endIndex (input.cursor + 2) restItems
                        next.cursor := by
                    simpa only [itemSound.2.1, itemSound.2.2.1,
                      itemSound.2.2.2, commaSound.2, State.tokens,
                      State.window, State.cursor, Nat.add_assoc] using
                        tailGrammar
                  refine ⟨item :: restItems, ?_,
                    .next comma.span commaSound.1 itemToken recursiveTail,
                    ?_, ?_⟩
                  · calc
                      items = (item :: itemsRev).reverse ++ restItems :=
                        itemsEq
                      _ = itemsRev.reverse ++ (item :: restItems) := by
                        simp [List.reverse_cons, List.append_assoc]
                  · simpa only [itemSound.2.1, commaSound.2, State.tokens]
                      using nextTokens
                  · simpa only [itemSound.2.2.1, commaSound.2, State.window]
                      using nextWindow
      · cases result
        exact ⟨[], by simp,
          .done input.cursor, rfl, rfl⟩

private theorem pragmaItems_success_sound {input next : State}
    {items : List Identifier}
    (result : PragmaInternals.pragmaItems input = .ok items next) :
    DeclarativeGrammar.PragmaItemsParses input.tokens input.window.endIndex
        input.cursor items next.cursor ∧
      next.tokens = input.tokens ∧ next.window = input.window := by
  unfold PragmaInternals.pragmaItems at result
  split at result
  · cases result
    exact ⟨.empty input.cursor, rfl, rfl⟩
  · cases itemResult : identifier .pragmaDecl input with
    | invariant error => simp [itemResult] at result
    | reject failure rejected => simp [itemResult] at result
    | ok item afterItem =>
        have itemSound := identifier_ok_tokenAt .pragmaDecl itemResult
        simp only [itemResult] at result
        rcases pragmaItemsTail_success_sound
          (afterItem.remainingCount + 1) [item] afterItem items next result
          with ⟨restItems, itemsEq, recursiveGrammar,
            nextTokens, nextWindow⟩
        have liftedTail :
            DeclarativeGrammar.PragmaItemsTailParses input.tokens
              input.window.endIndex (input.cursor + 1) restItems
              next.cursor := by
          simpa only [itemSound.2.1, itemSound.2.2.1,
            itemSound.2.2.2] using recursiveGrammar
        have itemsForm : items = item :: restItems := by
          simpa using itemsEq
        rw [itemsForm]
        exact ⟨.nonempty itemSound.1 liftedTail,
          nextTokens.trans itemSound.2.1,
          nextWindow.trans itemSound.2.2.1⟩

/-- Every successful pragma parse is licensed by the independent token grammar. -/
theorem pragmaDecl_success_sound {input next : State}
    {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    DeclarativeGrammar.PragmaDeclParses input.declarativeRemainder declaration
      next.declarativeRemainder := by
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error =>
      simp only [bind, keywordResult] at result
      contradiction
  | reject failure rejected =>
      simp only [bind, keywordResult] at result
      contradiction
  | ok pragmaKeyword afterKeyword =>
      have keywordSound := keyword_ok_tokenAt
        .pragmaKw .pragmaDecl keywordResult
      simp only [keywordResult, bind] at result
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          have nameSound := rawIdentifier_ok_tokenAt .pragmaDecl nameResult
          simp only [nameResult] at result
          cases itemsResult : PragmaInternals.pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject failure rejected => simp [itemsResult] at result
          | ok items afterItems =>
              have itemsSound := pragmaItems_success_sound itemsResult
              simp only [itemsResult] at result
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon final =>
                  have semicolonSound := symbol_ok_tokenAt
                    .semicolon .pragmaDecl semicolonResult
                  simp only [semicolonResult] at result
                  cases result
                  refine ⟨pragmaKeyword.span, semicolon.span,
                    afterItems.cursor, ?_⟩
                  simp only [State.declarativeRemainder]
                  refine ⟨?_, ?_, keywordSound.1, ?_, ?_, ?_, ?_, trivial⟩
                  · calc
                      next.tokens = afterItems.tokens := by
                        rw [semicolonSound.2]
                      _ = afterName.tokens := itemsSound.2.1
                      _ = afterKeyword.tokens := by rw [nameSound.2]
                      _ = input.tokens := by rw [keywordSound.2]
                  · apply congrArg TokenWindow.endIndex
                    calc
                      next.window = afterItems.window := by
                        rw [semicolonSound.2]
                      _ = afterName.window := itemsSound.2.2
                      _ = afterKeyword.window := by rw [nameSound.2]
                      _ = input.window := by rw [keywordSound.2]
                  · simpa only [keywordSound.2, State.tokens,
                      State.window, State.cursor] using nameSound.1
                  · simpa only [nameSound.2, keywordSound.2, State.tokens,
                      State.window, State.cursor, Nat.add_assoc] using
                        itemsSound.1
                  · simpa only [itemsSound.2.1, itemsSound.2.2,
                      nameSound.2, keywordSound.2, State.tokens,
                      State.window] using semicolonSound.1
                  · rw [semicolonSound.2]

/-- Successful parsing also carries the existing source-provenance contract. -/
theorem pragmaDecl_success_sound_and_validFor {input next : State}
    {declaration : PragmaDecl} (inputValid : input.ValidFor)
    (result : pragmaDecl input = .ok declaration next) :
    DeclarativeGrammar.PragmaDeclParses input.declarativeRemainder declaration
        next.declarativeRemainder ∧
      declaration.ValidFor input.file := by
  refine ⟨pragmaDecl_success_sound result, ?_⟩
  have valid := pragmaDecl_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
