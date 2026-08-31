import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.StateCursorProperties

set_option autoImplicit false

namespace Solcore.Syntax

namespace PragmaDecl

/-- Every source range retained by a provisional pragma belongs to one file. -/
def ValidFor (file : SourceFile) (declaration : PragmaDecl) : Prop :=
  declaration.span.ValidFor file ∧
    declaration.value.name.span.ValidFor file ∧
    ∀ item ∈ declaration.value.items, item.span.ValidFor file

end PragmaDecl

end Solcore.Syntax

namespace Solcore.Syntax.Parser

private def pragmaItemsTail :
    Nat → List Identifier → State → Reply (List Identifier)
  | 0, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, itemsRev, state =>
      if isSymbol state .comma then
        match symbol .comma .pragmaDecl state with
        | .ok _ afterComma =>
            if isSymbol afterComma .semicolon then
              .ok itemsRev.reverse afterComma
            else
              match identifier .pragmaDecl afterComma with
              | .ok item next =>
                  pragmaItemsTail fuel (item :: itemsRev) next
              | .reject failure next => .reject failure next
              | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        .ok itemsRev.reverse state

private def pragmaItems : Parser (List Identifier) := fun state =>
  if isSymbol state .semicolon then
    .ok [] state
  else
    match identifier .pragmaDecl state with
    | .ok item next =>
        pragmaItemsTail (next.remainingCount + 1) [item] next
    | .reject failure next => .reject failure next
    | .invariant error => .invariant error

private def pragmaItemsValidFor (file : SourceFile)
    (items : List Identifier) : Prop :=
  ∀ item ∈ items, item.span.ValidFor file

private theorem pragmaItemsTail_properties :
    ∀ fuel itemsRev input,
      (input.ValidFor → pragmaItemsValidFor input.file itemsRev →
        (pragmaItemsTail fuel itemsRev input).ValidFor input
          pragmaItemsValidFor) ∧
      ∀ items next, pragmaItemsTail fuel itemsRev input = .ok items next →
        next.tokens = input.tokens ∧ input.cursor ≤ next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input
      exact ⟨fun _ _ => trivial, fun _ _ result => by contradiction⟩
  | succ fuel inductionHypothesis =>
      intro itemsRev input
      unfold pragmaItemsTail
      split
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error =>
            exact ⟨fun _ _ => trivial, fun _ _ result => by
              contradiction⟩
        | reject failure rejected =>
            refine ⟨?_, fun _ _ result => by contradiction⟩
            intro inputValid _itemsValid
            have commaValid := symbol_validFor .comma .pragmaDecl
              input inputValid
            rw [commaResult] at commaValid
            simpa only [Reply.ValidFor] using commaValid
        | ok comma afterComma =>
            have commaShape :=
              symbol_ok_state_shape .comma .pragmaDecl commaResult
            simp only
            split
            · refine ⟨?_, ?_⟩
              · intro inputValid itemsValid
                have commaValid := symbol_validFor .comma .pragmaDecl
                  input inputValid
                rw [commaResult] at commaValid
                exact ⟨by simpa [pragmaItemsValidFor] using itemsValid,
                  commaValid.2.1, commaValid.2.2⟩
              intro items next result
              cases result
              rw [commaShape.2]
              exact ⟨rfl, Nat.le_add_right _ 1⟩
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error =>
                  exact ⟨fun _ _ => trivial, fun _ _ result => by
                    contradiction⟩
              | reject failure rejected =>
                  refine ⟨?_, fun _ _ result => by
                    contradiction⟩
                  intro inputValid _itemsValid
                  have commaValid := symbol_validFor .comma .pragmaDecl
                    input inputValid
                  rw [commaResult] at commaValid
                  have itemValid := identifier_validFor .pragmaDecl
                    afterComma commaValid.2.1
                  rw [itemResult] at itemValid
                  exact itemValid.of_file_eq commaValid.2.2
              | ok item afterItem =>
                  simp only
                  refine ⟨?_, ?_⟩
                  · intro inputValid itemsValid
                    have commaValid := symbol_validFor .comma .pragmaDecl
                      input inputValid
                    rw [commaResult] at commaValid
                    have itemValid := identifier_validFor .pragmaDecl
                      afterComma commaValid.2.1
                    rw [itemResult] at itemValid
                    have accumulatedValid :
                        pragmaItemsValidFor afterItem.file
                          (item :: itemsRev) := by
                      intro retained member
                      rcases List.mem_cons.mp member with rfl | member
                      · simpa only [Located.ValidFor, itemValid.2.2] using
                          itemValid.1
                      · simpa [itemValid.2.2, commaValid.2.2] using
                          itemsValid retained member
                    exact (inductionHypothesis (item :: itemsRev)
                      afterItem).1 itemValid.2.1 accumulatedValid |>.of_file_eq
                        (itemValid.2.2.trans commaValid.2.2)
                  intro items next result
                  have recursiveShape :=
                    (inductionHypothesis (item :: itemsRev) afterItem).2
                      items next result
                  rcases identifier_ok_state_shape .pragmaDecl itemResult with
                    ⟨_token, _found, _span, itemTokens, itemCursor⟩
                  have commaCursor :
                      afterComma.cursor = input.cursor + 1 := by
                    rw [commaShape.2]
                  exact ⟨recursiveShape.1.trans
                      (itemTokens.trans (by rw [commaShape.2])), by omega⟩
      · refine ⟨?_, ?_⟩
        · intro inputValid itemsValid
          exact ⟨by simpa [pragmaItemsValidFor] using itemsValid,
            inputValid, rfl⟩
        intro items next result
        cases result
        exact ⟨rfl, Nat.le_refl _⟩

private theorem pragmaItems_validFor :
    pragmaItems.ValidFor pragmaItemsValidFor := by
  intro input inputValid
  unfold pragmaItems
  split
  · exact ⟨by simp [pragmaItemsValidFor], inputValid, rfl⟩
  · cases itemResult : identifier .pragmaDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        have itemValid := identifier_validFor .pragmaDecl input inputValid
        rw [itemResult] at itemValid
        exact itemValid
    | ok item afterItem =>
        have itemValid := identifier_validFor .pragmaDecl input inputValid
        rw [itemResult] at itemValid
        simp only
        exact ((pragmaItemsTail_properties
          (afterItem.remainingCount + 1) [item] afterItem).1
          itemValid.2.1 (by
            intro retained member
            simp only [List.mem_singleton] at member
            subst item
            simpa only [Located.ValidFor, itemValid.2.2] using
              itemValid.1)).of_file_eq
              itemValid.2.2

private theorem pragmaItems_ok_state_shape {input next : State}
    {items : List Identifier} (result : pragmaItems input = .ok items next) :
    next.tokens = input.tokens ∧ input.cursor ≤ next.cursor := by
  unfold pragmaItems at result
  split at result
  · cases result
    exact ⟨rfl, Nat.le_refl _⟩
  · cases itemResult : identifier .pragmaDecl input with
    | invariant error => simp [itemResult] at result
    | reject failure rejected => simp [itemResult] at result
    | ok item afterItem =>
        simp only [itemResult] at result
        have tailShape := (pragmaItemsTail_properties
          (afterItem.remainingCount + 1) [item] afterItem).2
            items next result
        rcases identifier_ok_state_shape .pragmaDecl itemResult with
          ⟨_token, _found, _span, itemTokens, itemCursor⟩
        exact ⟨tailShape.1.trans itemTokens,
          Nat.le_trans (by omega) tailShape.2⟩

/-- Parse one canonical provisional pragma declaration. -/
def pragmaDecl : Parser PragmaDecl := do
  let pragmaKeyword ← keyword .pragmaKw .pragmaDecl
  -- The pragma name deliberately omits the ordinary hyphen diagnostic.
  let name ← rawIdentifier .pragmaDecl
  let items ← pragmaItems
  let semicolon ← symbol .semicolon .pragmaDecl
  pure {
    span := SourceSpan.cover pragmaKeyword.span semicolon.span
    value := { name, items }
  }

/-- Pragma parsing preserves its cover, raw name, and every item range. -/
theorem pragmaDecl_validFor :
    pragmaDecl.ValidFor PragmaDecl.ValidFor := by
  intro input inputValid
  unfold pragmaDecl
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp only [keywordResult, bind,
      Reply.ValidFor]
  | reject failure rejected =>
      have keywordValid := keyword_validFor .pragmaKw .pragmaDecl
        input inputValid
      rw [keywordResult] at keywordValid
      simpa only [keywordResult, bind, Reply.ValidFor] using
        keywordValid
  | ok pragmaKeyword afterKeyword =>
      have keywordValid := keyword_validFor .pragmaKw .pragmaDecl
        input inputValid
      rw [keywordResult] at keywordValid
      have keywordShape :=
        acceptToken_ok_state_shape (.keyword .pragmaKw) .pragmaDecl
          (· == .keyword .pragmaKw) keywordResult
      simp only [keywordResult, bind]
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have nameValid := rawIdentifier_validFor .pragmaDecl
            afterKeyword keywordValid.2.1
          rw [nameResult] at nameValid
          exact nameValid.of_file_eq keywordValid.2.2
      | ok name afterName =>
          have nameValid := rawIdentifier_validFor .pragmaDecl
            afterKeyword keywordValid.2.1
          rw [nameResult] at nameValid
          have nameShape := rawIdentifier_ok_state_shape .pragmaDecl nameResult
          simp only
          cases itemsResult : pragmaItems afterName with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              have itemsValid := pragmaItems_validFor afterName nameValid.2.1
              rw [itemsResult] at itemsValid
              exact itemsValid.of_file_eq
                (nameValid.2.2.trans keywordValid.2.2)
          | ok items afterItems =>
              have itemsValid := pragmaItems_validFor afterName nameValid.2.1
              rw [itemsResult] at itemsValid
              have itemsShape := pragmaItems_ok_state_shape itemsResult
              simp only
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  have semicolonValid := symbol_validFor .semicolon .pragmaDecl
                    afterItems itemsValid.2.1
                  rw [semicolonResult] at semicolonValid
                  exact semicolonValid.of_file_eq
                    (itemsValid.2.2.trans
                      (nameValid.2.2.trans keywordValid.2.2))
              | ok semicolon next =>
                  simp only
                  have semicolonValid := symbol_validFor .semicolon .pragmaDecl
                    afterItems itemsValid.2.1
                  rw [semicolonResult] at semicolonValid
                  have semicolonShape := symbol_ok_state_shape
                    .semicolon .pragmaDecl semicolonResult
                  have keywordFound :=
                    State.getElem?_eq_some_of_peek?_eq_some keywordShape.1
                  have semicolonFoundAfterItems :=
                    State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
                  have semicolonFoundInput :
                      input.tokens[afterItems.cursor]? = some semicolon := by
                    rw [itemsShape.1, nameShape, keywordShape.2] at semicolonFoundAfterItems
                    exact semicolonFoundAfterItems
                  have keywordBeforeSemicolon :
                      pragmaKeyword.span.endByte ≤ semicolon.span.startByte := by
                    apply inputValid.token_end_le_token_start_of_getElem?_lt
                      keywordFound semicolonFoundInput
                    have keywordAdvanced :
                        input.cursor < afterKeyword.cursor := by
                      rw [keywordShape.2]
                      simp
                    have nameAdvanced :
                        afterKeyword.cursor < afterName.cursor := by
                      rw [nameShape]
                      simp
                    exact Nat.lt_of_lt_of_le
                      (Nat.lt_trans keywordAdvanced nameAdvanced) itemsShape.2
                  have keywordSpanValid :
                      pragmaKeyword.span.ValidFor input.file := by
                    simpa only [Located.ValidFor] using keywordValid.1
                  have semicolonSpanValid :
                      semicolon.span.ValidFor input.file := by
                    simpa only [Located.ValidFor, semicolonValid.2.2,
                      itemsValid.2.2, nameValid.2.2,
                      keywordValid.2.2] using semicolonValid.1
                  have coverValid := SourceSpan.cover_validFor
                    keywordSpanValid semicolonSpanValid
                    (Nat.le_trans keywordSpanValid.2.1
                      (Nat.le_trans keywordBeforeSemicolon
                        semicolonSpanValid.2.1))
                  simp only [Reply.ValidFor,
                    PragmaDecl.ValidFor]
                  exact ⟨⟨coverValid,
                      by simpa only [Located.ValidFor, nameValid.2.2,
                        keywordValid.2.2] using nameValid.1,
                      by simpa only [pragmaItemsValidFor, itemsValid.2.2,
                        nameValid.2.2, keywordValid.2.2] using itemsValid.1⟩,
                    semicolonValid.2.1,
                    semicolonValid.2.2.trans (itemsValid.2.2.trans
                      (nameValid.2.2.trans keywordValid.2.2))⟩

/-- Successful pragma parsing preserves the immutable token carrier. -/
theorem pragmaDecl_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess pragmaDecl := by
  intro input declaration next result
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error =>
      simp only [bind, keywordResult] at result
      contradiction
  | reject failure rejected =>
      simp only [bind, keywordResult] at result
      contradiction
  | ok pragmaKeyword afterKeyword =>
      simp only [keywordResult, bind] at result
      cases nameResult : rawIdentifier .pragmaDecl afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok name afterName =>
          simp only [nameResult] at result
          cases itemsResult : pragmaItems afterName with
          | invariant error => simp [itemsResult] at result
          | reject failure rejected => simp [itemsResult] at result
          | ok items afterItems =>
              simp only [itemsResult] at result
              cases semicolonResult : symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon final =>
                  simp only [semicolonResult] at result
                  cases result
                  have keywordTokens := keyword_preservesTokensOnSuccess
                    .pragmaKw .pragmaDecl input pragmaKeyword afterKeyword
                      keywordResult
                  have nameTokens := rawIdentifier_preservesTokensOnSuccess
                    .pragmaDecl afterKeyword name afterName nameResult
                  have itemsTokens :=
                    (pragmaItems_ok_state_shape itemsResult).1
                  have semicolonTokens := symbol_preservesTokensOnSuccess
                    .semicolon .pragmaDecl afterItems semicolon next
                      semicolonResult
                  exact semicolonTokens.trans
                    (itemsTokens.trans (nameTokens.trans keywordTokens))

end Solcore.Syntax.Parser
