import Solcore.Syntax.Parser.Modules
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.State
import Solcore.Syntax.Module
import Solcore.Syntax.Grammar.Modules
import Solcore.Syntax.Parser.Internal.TypeSoundness
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Internal.ImportOutcomes
import Solcore.Syntax.Parser.Internal.TypeFormTotality
import Solcore.Syntax.Internal.ExportOutcomes

/-!
Proofs about the parsers of exports, module paths and pragmas: token-window and cursor
laws, source validity, soundness against the declarative grammar, and exact outcomes.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Pragma
set_option autoImplicit false

namespace Solcore.Syntax.Parser

open PragmaInternals

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

private theorem pragmaItemsTail_preservesTokenWindow :
    ∀ fuel itemsRev,
      Parser.PreservesTokenWindow (pragmaItemsTail fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro itemsRev input
      unfold pragmaItemsTail
      split
      · have commaShape :=
          symbol_preservesTokenWindow .comma .pragmaDecl input
        cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error =>
            simp only [Reply.PreservesTokenWindow]
        | reject failure rejected =>
            rw [commaResult] at commaShape
            simpa only [Reply.PreservesTokenWindow] using commaShape
        | ok comma afterComma =>
            rw [commaResult] at commaShape
            simp only
            split
            · exact commaShape
            · have itemShape :=
                identifier_preservesTokenWindow .pragmaDecl afterComma
              cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error =>
                  simp only [Reply.PreservesTokenWindow]
              | reject failure rejected =>
                  rw [itemResult] at itemShape
                  simpa only [Reply.PreservesTokenWindow] using
                    itemShape.trans commaShape
              | ok item next =>
                  rw [itemResult] at itemShape
                  simpa only using
                    (inductionHypothesis (item :: itemsRev) next).trans
                      (itemShape.trans commaShape)
      · exact ⟨rfl, rfl⟩

private theorem pragmaItems_preservesTokenWindow :
    Parser.PreservesTokenWindow pragmaItems := by
  intro input
  unfold pragmaItems
  split
  · exact ⟨rfl, rfl⟩
  · have itemShape := identifier_preservesTokenWindow .pragmaDecl input
    cases itemResult : identifier .pragmaDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [itemResult] at itemShape
        exact itemShape
    | ok item next =>
        rw [itemResult] at itemShape
        exact (pragmaItemsTail_preservesTokenWindow
          (next.remainingCount + 1) [item] next).trans itemShape

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

/-- Pragma parsing preserves every ordinary token window. -/
theorem pragmaDecl_preservesTokenWindow :
    Parser.PreservesTokenWindow pragmaDecl := by
  unfold pragmaDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .pragmaKw .pragmaDecl)
  intro pragmaKeyword
  apply Parser.bind_preservesTokenWindow
    (rawIdentifier_preservesTokenWindow .pragmaDecl)
  intro name
  apply Parser.bind_preservesTokenWindow pragmaItems_preservesTokenWindow
  intro items
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .pragmaDecl)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

/-- A pragma declaration starts at its retained `pragma` keyword token. -/
theorem pragmaDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess pragmaDecl (·.span) := by
  intro input declaration next result
  unfold pragmaDecl at result
  cases keywordResult : keyword .pragmaKw .pragmaDecl input with
  | invariant error => simp [bind, keywordResult] at result
  | reject failure rejected => simp [bind, keywordResult] at result
  | ok pragmaKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
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
              cases semicolonResult :
                  symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon final =>
                  simp only [semicolonResult] at result
                  cases result
                  exact ⟨pragmaKeyword,
                    (acceptToken_ok_state_shape (.keyword .pragmaKw)
                      .pragmaDecl (· == .keyword .pragmaKw)
                      keywordResult).1, rfl⟩

/-- Every successful pragma consumes its keyword, name, and terminator. -/
theorem pragmaDecl_cursor_lt_onSuccess {input next : State}
    {declaration : PragmaDecl}
    (result : pragmaDecl input = .ok declaration next) :
    input.cursor < next.cursor := by
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
              cases semicolonResult :
                  symbol .semicolon .pragmaDecl afterItems with
              | invariant error => simp [semicolonResult] at result
              | reject failure rejected => simp [semicolonResult] at result
              | ok semicolon final =>
                  simp only [semicolonResult] at result
                  cases result
                  have keywordCursor :=
                    (acceptToken_ok_state_shape (.keyword .pragmaKw)
                      .pragmaDecl (· == .keyword .pragmaKw)
                      keywordResult).2
                  have nameCursor :=
                    rawIdentifier_ok_state_shape .pragmaDecl nameResult
                  have itemsCursor :=
                    (pragmaItems_ok_state_shape itemsResult).2
                  have semicolonCursor :=
                    (symbol_ok_state_shape .semicolon .pragmaDecl
                      semicolonResult).2
                  have keywordProgress :
                      input.cursor < afterKeyword.cursor := by
                    rw [keywordCursor]
                    simp
                  have nameProgress :
                      afterKeyword.cursor < afterName.cursor := by
                    rw [nameCursor]
                    simp
                  have semicolonProgress :
                      afterItems.cursor < next.cursor := by
                    rw [semicolonCursor]
                    simp
                  exact Nat.lt_trans keywordProgress
                    (Nat.lt_trans nameProgress
                      (Nat.lt_of_le_of_lt itemsCursor semicolonProgress))

/-- Successful pragma parsing never moves the parser cursor backwards. -/
theorem pragmaDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess pragmaDecl := by
  intro input declaration next result
  exact Nat.le_of_lt (pragmaDecl_cursor_lt_onSuccess result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaDiagnosticReflectionProperties
/-! Diagnostic-freedom reflection for provisional pragma declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.PragmaInternals

private theorem pragmaItemsTail_reflectsDiagnosticFreeOnSuccess :
    ∀ fuel itemsRev,
      Parser.ReflectsDiagnosticFreeOnSuccess (pragmaItemsTail fuel itemsRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro itemsRev input value next result diagnosticFree
      simp [pragmaItemsTail] at result
  | succ fuel inductionHypothesis =>
      intro itemsRev input value next result diagnosticFree
      unfold pragmaItemsTail at result
      split at result
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant error => simp [commaResult] at result
        | reject failure rejected => simp [commaResult] at result
        | ok comma afterComma =>
            simp only [commaResult] at result
            split at result
            · cases result
              exact symbol_reflectsDiagnosticFreeOnSuccess .comma .pragmaDecl
                input comma next commaResult diagnosticFree
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant error => simp [itemResult] at result
              | reject failure rejected => simp [itemResult] at result
              | ok item afterItem =>
                  simp only [itemResult] at result
                  have afterItemFree := inductionHypothesis (item :: itemsRev)
                    afterItem value next result diagnosticFree
                  have afterCommaFree :=
                    identifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl
                      afterComma item afterItem itemResult afterItemFree
                  exact symbol_reflectsDiagnosticFreeOnSuccess .comma
                    .pragmaDecl input comma afterComma commaResult
                      afterCommaFree
      · cases result
        exact diagnosticFree

private theorem pragmaItems_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess pragmaItems := by
  intro input value next result diagnosticFree
  unfold pragmaItems at result
  split at result
  · cases result
    exact diagnosticFree
  · cases itemResult : identifier .pragmaDecl input with
    | invariant error => simp [itemResult] at result
    | reject failure rejected => simp [itemResult] at result
    | ok item afterItem =>
        simp only [itemResult] at result
        have afterItemFree := pragmaItemsTail_reflectsDiagnosticFreeOnSuccess
          (afterItem.remainingCount + 1) [item] afterItem value next result
            diagnosticFree
        exact identifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl input
          item afterItem itemResult afterItemFree

end Solcore.Syntax.Parser.PragmaInternals

namespace Solcore.Syntax.Parser

/-- Pragma parsing cannot erase an incoming diagnostic. -/
theorem pragmaDecl_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess pragmaDecl := by
  unfold pragmaDecl
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (keyword_reflectsDiagnosticFreeOnSuccess .pragmaKw .pragmaDecl)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (rawIdentifier_reflectsDiagnosticFreeOnSuccess .pragmaDecl)
  intro name
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    PragmaInternals.pragmaItems_reflectsDiagnosticFreeOnSuccess
  intro items
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .semicolon .pragmaDecl)
  intro semicolon
  exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PragmaSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.ModulePath
set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Module-path parsing preserves its cover, marker, and component ranges. -/
theorem modulePath_validFor (context : ParseContext) :
    (modulePath context).ValidFor ModulePath.ValidFor := by
  intro input inputValid
  unfold modulePath
  split
  · cases markerResult : symbol .at context input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have markerValid := symbol_validFor .at context input inputValid
        rw [markerResult] at markerValid
        simpa only [markerResult, Reply.ValidFor] using markerValid
    | ok marker afterMarker =>
        have markerValid := symbol_validFor .at context input inputValid
        rw [markerResult] at markerValid
        have markerShape := symbol_ok_state_shape .at context markerResult
        simp only
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have nameValid := qualifiedName_validFor context .topLevel
              afterMarker markerValid.2.1
            rw [nameResult] at nameValid
            simpa only [nameResult, Reply.ValidFor] using
              nameValid.of_file_eq markerValid.2.2
        | ok name next =>
            have nameValid := qualifiedName_validFor context .topLevel
              afterMarker markerValid.2.1
            rw [nameResult] at nameValid
            have nameValidInput : QualifiedName.ValidFor input.file name := by
              simpa [markerValid.2.2] using nameValid.1
            have markerSpanValid : marker.span.ValidFor input.file := by
              simpa only [Located.ValidFor] using markerValid.1
            rcases qualifiedName_ok_state_shape context .topLevel nameResult with
              ⟨firstToken, firstFound, firstStart, _nameTokens⟩
            have markerFound :=
              State.getElem?_eq_some_of_peek?_eq_some markerShape.1
            have firstFoundInput :
                input.tokens[input.cursor + 1]? = some firstToken := by
              have foundAfterMarker :=
                State.getElem?_eq_some_of_peek?_eq_some firstFound
              simpa [markerShape.2] using foundAfterMarker
            have markerBeforeFirst :
                marker.span.endByte ≤ firstToken.span.startByte := by
              exact inputValid.token_end_le_token_start_of_getElem?_lt
                markerFound firstFoundInput (by simp)
            have markerBeforeNameEnd :
                marker.span.startByte ≤ name.span.endByte := by
              apply Nat.le_trans markerSpanValid.2.1
              apply Nat.le_trans markerBeforeFirst
              rw [firstStart]
              exact nameValidInput.1.2.1
            have coverValid :
                (SourceSpan.cover marker.span name.span).ValidFor input.file :=
              SourceSpan.cover_validFor markerSpanValid nameValidInput.1
                markerBeforeNameEnd
            simp only [Reply.ValidFor, ModulePath.ValidFor]
            exact ⟨⟨coverValid, markerSpanValid, nameValidInput.2⟩,
              nameValid.2.1, nameValid.2.2.trans markerValid.2.2⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := qualifiedName_validFor context .topLevel
          input inputValid
        rw [nameResult] at nameValid
        simpa only [nameResult, Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := qualifiedName_validFor context .topLevel
          input inputValid
        rw [nameResult] at nameValid
        simp only [Reply.ValidFor, ModulePath.ValidFor]
        exact ⟨⟨nameValid.1.1, trivial, nameValid.1.2⟩,
          nameValid.2.1, nameValid.2.2⟩

/-- Module paths preserve tokens and the active window on every reply. -/
theorem modulePath_preservesTokenWindow (context : ParseContext) :
    Parser.PreservesTokenWindow (modulePath context) := by
  intro input
  unfold modulePath
  split
  · have markerShape := symbol_preservesTokenWindow .at context input
    cases markerResult : symbol .at context input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [markerResult] at markerShape
        exact markerShape
    | ok marker afterMarker =>
        rw [markerResult] at markerShape
        simp only
        have nameShape := qualifiedName_preservesTokenWindow context
          .topLevel afterMarker
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => trivial
        | reject failure rejected =>
            rw [nameResult] at nameShape
            exact nameShape.trans markerShape
        | ok name next =>
            rw [nameResult] at nameShape
            exact nameShape.trans markerShape
  · have nameShape := qualifiedName_preservesTokenWindow context
      .topLevel input
    cases nameResult : qualifiedName context .topLevel input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [nameResult] at nameShape
        exact nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        exact nameShape

/-- Module-path success preserves the immutable token carrier. -/
theorem modulePath_preservesTokensOnSuccess (context : ParseContext) :
    Parser.PreservesTokensOnSuccess (modulePath context) := by
  intro input path next result
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            have nameTokens := qualifiedName_preservesTokensOnSuccess
              context .topLevel afterMarker name next nameResult
            have markerShape := symbol_ok_state_shape .at context markerResult
            calc
              next.tokens = afterMarker.tokens := nameTokens
              _ = input.tokens := by rw [markerShape.2]
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_preservesTokensOnSuccess context .topLevel
          input name next nameResult

/-- A module path starts at its package marker or first name component. -/
theorem modulePath_startsAtCurrentTokenOnSuccess (context : ParseContext) :
    Parser.StartsAtCurrentTokenOnSuccess (modulePath context) (·.span) := by
  intro input path next result
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            exact ⟨marker,
              (symbol_ok_state_shape .at context markerResult).1, rfl⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_startsAtCurrentTokenOnSuccess context .topLevel
          input name next nameResult

/-- Every successful module path consumes at least its first path token. -/
theorem modulePath_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    input.cursor < next.cursor := by
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            simp only [nameResult] at result
            cases result
            have markerProgress : input.cursor < afterMarker.cursor := by
              rw [(symbol_ok_state_shape .at context markerResult).2]
              simp
            exact Nat.lt_trans markerProgress
              (qualifiedName_cursor_lt_onSuccess context .topLevel nameResult)
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        simp only [nameResult] at result
        cases result
        exact qualifiedName_cursor_lt_onSuccess context .topLevel nameResult

/-- Successful module-path parsing never rewinds the cursor. -/
theorem modulePath_cursorMonotoneOnSuccess (context : ParseContext) :
    Parser.CursorMonotoneOnSuccess (modulePath context) := by
  intro input path next result
  exact Nat.le_of_lt (modulePath_cursor_lt_onSuccess context result)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinaryRejectionSoundnessProperties`
-/

/-! Exact executable rejection reflection for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path rejection comes from the qualified name in
the prioritized local or exact-marker external-package branch. -/
theorem modulePath_reject_ordinaryOutcome_sound (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : modulePath context input = .reject failure rejected) :
    DeclarativeGrammar.ModulePathRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold modulePath at result
  by_cases markerPresent : isSymbol input .at = true
  · rcases symbol_eq_ok_of_isSymbol_eq_true .at context markerPresent with
      ⟨marker, markerResult⟩
    simp only [markerPresent, if_true, markerResult] at result
    cases nameResult : qualifiedName context .topLevel
        { input with cursor := input.cursor + 1 } with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .externalRejected marker.span
          (symbol_success_exactTokenParses .at context markerResult)
          (qualifiedName_reject_type_sound context .topLevel nameResult)
  · have markerAbsent : isSymbol input .at = false :=
      Bool.eq_false_iff.mpr markerPresent
    simp only [markerAbsent, Bool.false_eq_true, if_false] at result
    cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .localRejected
          (symbolAbsentAt_of_isSymbol_eq_false .at markerAbsent)
          (qualifiedName_reject_type_sound context .topLevel nameResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathSoundnessProperties`
-/

/-! Success soundness of canonical module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful module-path parse follows the independent token grammar. -/
theorem modulePath_success_sound (context : ParseContext)
    {input next : State} {path : ModulePath}
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
      next.declarativeRemainder := by
  unfold modulePath at result
  split at result
  · cases markerResult : symbol .at context input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .at context markerResult
        simp only [markerResult] at result
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error => simp [nameResult] at result
        | reject failure rejected => simp [nameResult] at result
        | ok name final =>
            have nameSound := qualifiedName_success_sound context .topLevel
              nameResult
            simp only [nameResult] at result
            cases result
            apply DeclarativeGrammar.ModulePathParses.externalPackage
              marker.span markerSound.1
            simpa only [markerSound.2, State.declarativeRemainder,
              State.tokens, State.window, State.cursor] using nameSound
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name final =>
        have nameSound := qualifiedName_success_sound context .topLevel
          nameResult
        simp only [nameResult] at result
        cases result
        exact DeclarativeGrammar.ModulePathParses.local nameSound

/-- Success soundness composes with the established source-provenance contract. -/
theorem modulePath_success_sound_and_validFor (context : ParseContext)
    {input next : State} {path : ModulePath} (inputValid : input.ValidFor)
    (result : modulePath context input = .ok path next) :
    DeclarativeGrammar.ModulePathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file := by
  refine ⟨modulePath_success_sound context result, ?_⟩
  have valid := modulePath_validFor context input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinarySuccessSoundnessProperties`
-/

/-! Broad ordinary-success soundness for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable module-path success follows the existing exact ordinary
grammar without a diagnostic-free premise. -/
theorem modulePath_success_ordinaryOutcome_sound (context : ParseContext)
    {input output : State} {path : ModulePath}
    (result : modulePath context input = .ok path output) :
    DeclarativeGrammar.ModulePathOrdinaryParses input.declarativeRemainder
      path output.declarativeRemainder :=
  modulePath_success_sound context result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable broad ordinary outcomes for module paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package module-path success and exact prioritized rejection. -/
theorem modulePath_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {path : ModulePath},
      modulePath context input = .ok path output →
        DeclarativeGrammar.ModulePathOrdinaryParses
          input.declarativeRemainder path output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      modulePath context input = .reject failure rejected →
        DeclarativeGrammar.ModulePathRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨modulePath_success_ordinaryOutcome_sound context,
    modulePath_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive module-path outcomes. -/
theorem modulePath_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses
      DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathDeterministicOutcomeSpec

/-- Exact values and endpoints for the independent modulePath grammar. -/
theorem modulePath_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.ModulePathOrdinaryParses DeclarativeGrammar.ModulePathRejects :=
  DeclarativeGrammar.modulePathExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem modulePath_success_result_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {left right : ModulePath}
    (leftResult : modulePath context input = .ok left leftOutput)
    (rightResult : modulePath context input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).successResultUnique
    (modulePath_success_ordinaryOutcome_sound context leftResult)
    (modulePath_success_ordinaryOutcome_sound context rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem modulePath_reject_output_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : modulePath context input = .reject leftFailure leftOutput)
    (rightResult : modulePath context input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (modulePath_exactOutcomeSpec ).rejectOutputUnique
    (modulePath_reject_ordinaryOutcome_sound context leftResult)
    (modulePath_reject_ordinaryOutcome_sound context rightResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.ModulePathTotalityProperties`
-/

/-! Totality laws for module-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Module paths always produce an ordinary success or rejection reply. -/
theorem modulePath_ordinary (context : ParseContext) :
    Parser.Ordinary (modulePath context) := by
  intro input
  unfold modulePath
  split
  · cases markerResult : symbol .at context input with
    | invariant error =>
        exact False.elim
          (symbol_ne_invariant .at context input error markerResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok marker afterMarker =>
        dsimp only
        cases nameResult : qualifiedName context .topLevel afterMarker with
        | invariant error =>
            exact False.elim
              (qualifiedName_ne_invariant context .topLevel afterMarker error
                nameResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok name next =>
            exact Or.inl ⟨_, next, rfl⟩
  · cases nameResult : qualifiedName context .topLevel input with
    | invariant error =>
        exact False.elim
          (qualifiedName_ne_invariant context .topLevel input error nameResult)
    | reject failure rejected =>
        exact Or.inr ⟨failure, rejected, rfl⟩
    | ok name next =>
        exact Or.inl ⟨_, next, rfl⟩

/-- Module paths cannot expose an internal parser invariant. -/
theorem modulePath_ne_invariant (context : ParseContext) (input : State)
    (error : ParserInvariantError) :
    modulePath context input ≠ .invariant error :=
  (modulePath_ordinary context).ne_invariant input error

/-- Module paths are invariant-free on the canonical valid-input domain. -/
theorem modulePath_invariantFreeOnValid (context : ParseContext) :
    Parser.InvariantFreeOnValid (modulePath context) :=
  (modulePath_ordinary context).invariantFreeOnValid

/-- Module paths satisfy the generic strict element-parser contract. -/
theorem modulePath_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (modulePath context) := {
  validFor := (modulePath_validFor context).mono (fun _ _ _ => trivial)
  preservesTokenWindow := modulePath_preservesTokenWindow context
  cursorLtOnSuccess := modulePath_cursor_lt_onSuccess context
  invariantFree := fun input _ error =>
    modulePath_ne_invariant context input error
}

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectorNameSoundnessProperties
/-! Success soundness of canonical import/export selector parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Parser recognition and the independent operator catalog agree exactly. -/
theorem operatorPart?_eq_some_iff {kind : TokenKind} {spelling : String} :
    operatorPart? kind = some spelling ↔
      ∃ symbol,
        kind = .symbol symbol ∧
        DeclarativeGrammar.SelectorOperatorSymbol symbol ∧
        spelling = symbol.spelling := by
  cases kind with
  | symbol symbol =>
      cases symbol <;>
        simp [operatorPart?, DeclarativeGrammar.SelectorOperatorSymbol,
          Symbol.spelling, eq_comm]
  | _ => simp [operatorPart?]

/--
Successful collection recovers the unconsumed forward-order suffix of the
parser's reverse accumulator.  An initially empty accumulator necessarily
collects at least one symbol before succeeding.
-/
private theorem operatorParts_success_sound (context : ParseContext) :
    ∀ fuel partsRev input parts next,
      OperatorInternals.operatorParts context fuel partsRev input =
          .ok parts next →
      ∃ suffix,
        parts = partsRev.reverse ++ suffix ∧
        DeclarativeGrammar.SelectorOperatorPartsParses input.tokens
          input.window.endIndex input.cursor suffix next.cursor ∧
        (partsRev = [] → suffix ≠ []) ∧
        next.tokens = input.tokens ∧
        next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input parts next result
      simp [OperatorInternals.operatorParts] at result
  | succ fuel inductionHypothesis =>
      intro partsRev input parts next result
      unfold OperatorInternals.operatorParts at result
      cases found : input.peek? with
      | some token =>
          simp only [found] at result
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only [part] at result
              rcases inductionHypothesis (spelling :: partsRev)
                  { input with cursor := input.cursor + 1 }
                  parts next result with
                ⟨recursiveSuffix, partsEq, tailGrammar, _recursiveNonempty,
                  tokensEq, windowEq⟩
              rcases operatorPart?_eq_some_iff.mp part with
                ⟨symbol, tokenKindEq, allowed, spellingEq⟩
              subst spelling
              have partToken :
                  DeclarativeGrammar.TokenAt input.tokens
                    input.window.endIndex input.cursor {
                      span := token.span
                      value := .symbol symbol
                    } := by
                have tokenEq : token = {
                    span := token.span
                    value := .symbol symbol
                  } := by
                  rcases token with ⟨span, kind⟩
                  simp only at tokenKindEq ⊢
                  subst kind
                  rfl
                rw [← tokenEq]
                exact tokenAt_of_peek?_eq_some found
              refine ⟨symbol.spelling :: recursiveSuffix, ?_, ?_, ?_, ?_, ?_⟩
              · calc
                  parts = (symbol.spelling :: partsRev).reverse ++
                      recursiveSuffix := partsEq
                  _ = partsRev.reverse ++
                      (symbol.spelling :: recursiveSuffix) := by
                    simp [List.reverse_cons, List.append_assoc]
              · apply DeclarativeGrammar.SelectorOperatorPartsParses.next
                  allowed token.span partToken
                simpa only [State.tokens, State.window, State.cursor] using
                  tailGrammar
              · intro _empty
                simp
              · simpa only [State.tokens] using tokensEq
              · simpa only [State.window] using windowEq
          | none =>
              simp only [part] at result
              split at result
              · unfold rejectAt at result
                contradiction
              · cases result
                refine ⟨[], by simp, .done input.cursor, ?_, rfl, rfl⟩
                intro empty
                subst partsRev
                simp_all
      | none =>
          simp only [found] at result
          split at result
          · unfold rejectAt at result
            contradiction
          · cases result
            refine ⟨[], by simp, .done input.cursor, ?_, rfl, rfl⟩
            intro empty
            subst partsRev
            simp_all

/-- Every successful operator selector follows the independent token grammar. -/
theorem operatorSelector_success_sound (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : operatorSelector context input = .ok selector next) :
    DeclarativeGrammar.OperatorSelectorParses input.declarativeRemainder
      selector next.declarativeRemainder := by
  unfold operatorSelector at result
  cases openingResult : symbol .leftParen context input with
  | invariant error => simp [openingResult] at result
  | reject failure rejected => simp [openingResult] at result
  | ok opening afterOpening =>
      have openingSound := symbol_ok_tokenAt .leftParen context openingResult
      simp only [openingResult] at result
      cases partsResult : OperatorInternals.operatorParts context
          (afterOpening.remainingCount + 1) [] afterOpening with
      | invariant error => simp [partsResult] at result
      | reject failure rejected => simp [partsResult] at result
      | ok parts afterParts =>
          simp only [partsResult] at result
          rcases operatorParts_success_sound context
              (afterOpening.remainingCount + 1) [] afterOpening parts
              afterParts partsResult with
            ⟨suffix, partsEq, partsGrammar, suffixNonempty,
              partsTokensEq, partsWindowEq⟩
          have partsEq' : parts = suffix := by simpa using partsEq
          subst parts
          cases closingResult : symbol .rightParen context afterParts with
          | invariant error => simp [closingResult] at result
          | reject failure rejected => simp [closingResult] at result
          | ok closing final =>
              have closingSound := symbol_ok_tokenAt .rightParen context
                closingResult
              simp only [closingResult] at result
              have closingToken := closingSound.1
              have finalEq := closingSound.2
              subst final
              cases result
              unfold DeclarativeGrammar.OperatorSelectorParses
                State.declarativeRemainder
              have openingTokensEq : afterOpening.tokens = input.tokens := by
                rw [openingSound.2]
              have openingWindowEq : afterOpening.window = input.window := by
                rw [openingSound.2]
              refine ⟨opening.span, closing.span, suffix, afterParts.cursor,
                ?_, ?_, openingSound.1, ?_, suffixNonempty rfl, ?_, rfl, rfl⟩
              · exact partsTokensEq.trans openingTokensEq
              · have windowsEq : afterParts.window = input.window :=
                  partsWindowEq.trans openingWindowEq
                exact congrArg TokenWindow.endIndex windowsEq
              · simpa only [openingSound.2, State.tokens, State.window,
                  State.cursor] using partsGrammar
              · simpa only [partsTokensEq, partsWindowEq, openingTokensEq,
                  openingWindowEq, State.tokens, State.window, State.cursor]
                  using closingToken

/-- Every successful selector follows its identifier or operator grammar. -/
theorem selectorName_success_sound (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (result : selectorName context input = .ok selector next) :
    DeclarativeGrammar.SelectorNameParses input.declarativeRemainder selector
      next.declarativeRemainder := by
  unfold selectorName at result
  split at result
  · exact .operator (operatorSelector_success_sound context result)
  · cases identifierResult : identifier context input with
    | invariant error => simp [identifierResult] at result
    | reject failure rejected => simp [identifierResult] at result
    | ok name afterName =>
        have nameSound := identifier_ok_tokenAt context identifierResult
        simp only [identifierResult] at result
        cases result
        apply DeclarativeGrammar.SelectorNameParses.identifier nameSound.1
        · exact nameSound.2.1
        · exact congrArg TokenWindow.endIndex nameSound.2.2.1
        · exact nameSound.2.2.2

/-- Selector grammar soundness composes with source-provenance validity. -/
theorem selectorName_success_sound_and_validFor (context : ParseContext)
    {input next : State} {selector : SelectorName}
    (inputValid : input.ValidFor)
    (result : selectorName context input = .ok selector next) :
    DeclarativeGrammar.SelectorNameParses input.declarativeRemainder selector
        next.declarativeRemainder ∧
      selector.ValidFor input.file := by
  refine ⟨selectorName_success_sound context result, ?_⟩
  have valid := selectorName_validFor context input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectorNameOrdinarySuccessSoundnessProperties
/-! Broad ordinary-success soundness for import and export selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable selector-name success follows the exact identifier or
maximal parenthesized-operator grammar without a diagnostic-free premise. -/
theorem selectorName_success_ordinaryOutcome_sound (context : ParseContext)
    {input output : State} {selector : SelectorName}
    (result : selectorName context input = .ok selector output) :
    DeclarativeGrammar.SelectorNameOrdinaryParses
      input.declarativeRemainder selector output.declarativeRemainder :=
  selectorName_success_sound context result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectorNameOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem selectorOperatorPartAbsentAt_of_peek?_eq_none
    {input : State} (found : input.peek? = none) :
    DeclarativeGrammar.SelectorOperatorPartAbsentAt
      input.declarativeRemainder := by
  rintro ⟨symbol, span, allowed, token⟩
  have inside : input.cursor < input.window.endIndex := by
    simpa [State.declarativeRemainder] using token.1
  have atCursor : input.tokens[input.cursor]? = some {
      span
      value := TokenKind.symbol symbol
    } := by
    simpa [State.declarativeRemainder] using token.2
  unfold State.peek? at found
  simp [inside, atCursor] at found

private theorem selectorOperatorPartAbsentAt_of_part_eq_none
    {input : State} {token : Token}
    (found : input.peek? = some token)
    (stopped : operatorPart? token.value = none) :
    DeclarativeGrammar.SelectorOperatorPartAbsentAt
      input.declarativeRemainder := by
  rintro ⟨symbol, span, allowed, partToken⟩
  have actual := State.getElem?_eq_some_of_peek?_eq_some found
  have tokenEq : token = { span, value := TokenKind.symbol symbol } := by
    exact Option.some.inj (actual.symm.trans partToken.2)
  have accepted : operatorPart? token.value = some symbol.spelling := by
    apply operatorPart?_eq_some_iff.mpr
    exact ⟨symbol, by rw [tokenEq], allowed, rfl⟩
  rw [accepted] at stopped
  contradiction

private theorem operatorParts_success_maximal_sound
    (context : ParseContext) :
    ∀ fuel partsRev input parts next,
      OperatorInternals.operatorParts context fuel partsRev input =
          .ok parts next →
      ∃ suffix,
        parts = partsRev.reverse ++ suffix ∧
        DeclarativeGrammar.MaximalSelectorOperatorPartsParses
          input.declarativeRemainder suffix next.declarativeRemainder ∧
        (partsRev = [] → suffix ≠ []) := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input parts next result
      simp [OperatorInternals.operatorParts] at result
  | succ fuel inductionHypothesis =>
      intro partsRev input parts next result
      unfold OperatorInternals.operatorParts at result
      cases found : input.peek? with
      | some token =>
          simp only [found] at result
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only [part] at result
              rcases inductionHypothesis (spelling :: partsRev)
                  { input with cursor := input.cursor + 1 }
                  parts next result with
                ⟨suffix, partsEq, tail, suffixNonempty⟩
              rcases operatorPart?_eq_some_iff.mp part with
                ⟨symbol, tokenKindEq, allowed, spellingEq⟩
              subst spelling
              have partToken : DeclarativeGrammar.TokenAt input.tokens
                  input.window.endIndex input.cursor {
                    span := token.span
                    value := TokenKind.symbol symbol
                  } := by
                have tokenEq : token = {
                    span := token.span
                    value := TokenKind.symbol symbol
                  } := by
                  rcases token with ⟨span, kind⟩
                  simp only at tokenKindEq ⊢
                  subst kind
                  rfl
                rw [← tokenEq]
                exact tokenAt_of_peek?_eq_some found
              refine ⟨symbol.spelling :: suffix, ?_, ?_, ?_⟩
              · calc
                  parts = (symbol.spelling :: partsRev).reverse ++ suffix :=
                    partsEq
                  _ = partsRev.reverse ++ (symbol.spelling :: suffix) := by
                    simp [List.reverse_cons, List.append_assoc]
              · exact .next allowed token.span partToken (by
                  simpa only [State.declarativeRemainder, State.tokens,
                    State.window, State.cursor] using tail)
              · intro _empty
                simp
          | none =>
              simp only [part] at result
              split at result
              · unfold rejectAt at result
                contradiction
              · cases result
                refine ⟨[], by simp, .done ?_, ?_⟩
                · exact selectorOperatorPartAbsentAt_of_part_eq_none
                    found part
                · intro empty
                  subst partsRev
                  simp_all
      | none =>
          simp only [found] at result
          split at result
          · unfold rejectAt at result
            contradiction
          · cases result
            refine ⟨[], by simp, .done ?_, ?_⟩
            · exact selectorOperatorPartAbsentAt_of_peek?_eq_none found
            · intro empty
              subst partsRev
              simp_all

private theorem operatorParts_reject_implies_empty
    (context : ParseContext) :
    ∀ fuel partsRev input failure rejected,
      OperatorInternals.operatorParts context fuel partsRev input =
          .reject failure rejected →
      partsRev = [] ∧ rejected = input ∧
        DeclarativeGrammar.SelectorOperatorPartAbsentAt
          input.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro partsRev input failure rejected result
      simp [OperatorInternals.operatorParts] at result
  | succ fuel inductionHypothesis =>
      intro partsRev input failure rejected result
      unfold OperatorInternals.operatorParts at result
      cases found : input.peek? with
      | some token =>
          simp only [found] at result
          cases part : operatorPart? token.value with
          | some spelling =>
              simp only [part] at result
              have impossible := inductionHypothesis (spelling :: partsRev)
                { input with cursor := input.cursor + 1 }
                failure rejected result
              simp at impossible
          | none =>
              simp only [part] at result
              split at result
              · unfold rejectAt at result
                cases result
                refine ⟨?_, rfl, ?_⟩
                · simpa using ‹partsRev.isEmpty = true›
                · exact selectorOperatorPartAbsentAt_of_part_eq_none
                    found part
              · contradiction
      | none =>
          simp only [found] at result
          split at result
          · unfold rejectAt at result
            cases result
            refine ⟨?_, rfl, ?_⟩
            · simpa using ‹partsRev.isEmpty = true›
            · exact selectorOperatorPartAbsentAt_of_peek?_eq_none found
          · contradiction

/-- Every selector-name rejection records its exact prioritized identifier or
operator failure and retained remainder. -/
theorem selectorName_reject_ordinaryOutcome_sound
    (context : ParseContext) {input rejected : State} {failure : Failure}
    (result : selectorName context input = .reject failure rejected) :
    DeclarativeGrammar.SelectorNameRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold selectorName at result
  by_cases openingPresent : isSymbol input .leftParen = true
  · simp only [openingPresent, if_true] at result
    rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen context
        openingPresent with
      ⟨opening, openingResult⟩
    unfold operatorSelector at result
    simp only [openingResult] at result
    cases partsResult : OperatorInternals.operatorParts context
        (({ input with cursor := input.cursor + 1 } : State).remainingCount + 1)
        [] { input with cursor := input.cursor + 1 } with
    | invariant error => simp [partsResult] at result
    | reject partsFailure partsRejected =>
        rcases operatorParts_reject_implies_empty context
            (({ input with cursor := input.cursor + 1 } : State).remainingCount +
              1)
            [] { input with cursor := input.cursor + 1 } partsFailure
              partsRejected partsResult with
          ⟨_empty, rejectedEq, partAbsent⟩
        subst partsRejected
        simp only [partsResult] at result
        cases result
        exact .emptyOperator opening.span
          (symbol_success_exactTokenParses .leftParen context openingResult)
          partAbsent
    | ok parts afterParts =>
        simp only [partsResult] at result
        rcases operatorParts_success_maximal_sound context
            (({ input with cursor := input.cursor + 1 } : State).remainingCount +
              1)
            [] { input with cursor := input.cursor + 1 } parts afterParts
              partsResult with
          ⟨suffix, partsEq, partsParsed, partsNonempty⟩
        have partsEq' : parts = suffix := by simpa using partsEq
        subst parts
        cases closingResult : symbol .rightParen context afterParts with
        | invariant error => simp [closingResult] at result
        | ok closing final => simp [closingResult] at result
        | reject closingFailure closingRejected =>
            have rejectedEq := symbol_reject_state_eq .rightParen context
              closingResult
            subst closingRejected
            simp only [closingResult] at result
            cases result
            exact .closingMissing opening.span
              (symbol_success_exactTokenParses .leftParen context
                openingResult)
              partsParsed (partsNonempty rfl)
              (symbol_reject_tokenKindAbsentAt .rightParen context
                closingResult)
  · have openingAbsent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr openingPresent
    simp only [openingAbsent, Bool.false_eq_true, if_false] at result
    cases nameResult : identifier context input with
    | invariant error => simp [nameResult] at result
    | ok name output => simp [nameResult] at result
    | reject nameFailure nameRejected =>
        simp only [nameResult] at result
        cases result
        exact .identifierRejected
          (symbolAbsentAt_of_isSymbol_eq_false .leftParen openingAbsent)
          (identifier_reject_sound context nameResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.SelectorNameOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for selector names. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package selector-name success and exact prioritized rejection. -/
theorem selectorName_ordinaryOutcome_sound (context : ParseContext) :
    (∀ {input output : State} {selector : SelectorName},
      selectorName context input = .ok selector output →
        DeclarativeGrammar.SelectorNameOrdinaryParses
          input.declarativeRemainder selector output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      selectorName context input = .reject failure rejected →
        DeclarativeGrammar.SelectorNameRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨selectorName_success_ordinaryOutcome_sound context,
    selectorName_reject_ordinaryOutcome_sound context⟩

/-- Re-export deterministic and exclusive selector-name outcomes. -/
theorem selectorName_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.SelectorNameOrdinaryParses
      DeclarativeGrammar.SelectorNameRejects :=
  DeclarativeGrammar.selectorNameDeterministicOutcomeSpec


/-- Exact values and endpoints for the independent selectorName grammar. -/
theorem selectorName_exactOutcomeSpec  :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.SelectorNameOrdinaryParses DeclarativeGrammar.SelectorNameRejects :=
  DeclarativeGrammar.selectorNameExactOutcomeSpec

/-- Executable successes agree on their complete value and remainder. -/
theorem selectorName_success_result_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {left right : SelectorName}
    (leftResult : selectorName context input = .ok left leftOutput)
    (rightResult : selectorName context input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectorName_exactOutcomeSpec ).successResultUnique
    (selectorName_success_ordinaryOutcome_sound context leftResult)
    (selectorName_success_ordinaryOutcome_sound context rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem selectorName_reject_output_unique (context : ParseContext)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : selectorName context input = .reject leftFailure leftOutput)
    (rightResult : selectorName context input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (selectorName_exactOutcomeSpec ).rejectOutputUnique
    (selectorName_reject_ordinaryOutcome_sound context leftResult)
    (selectorName_reject_ordinaryOutcome_sound context rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FinishExportOrdinaryRejectionSoundnessProperties
/-! Exact executable rejection reflection for export termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable export-finishing rejection is the exact nonconsuming
absence of its required semicolon. -/
theorem finishExport_reject_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) {input rejected : State} {failure : Failure}
    (result : ExportInternals.finishExport start value input =
      .reject failure rejected) :
    DeclarativeGrammar.FinishExportRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold ExportInternals.finishExport at result
  cases semicolonResult : symbol .semicolon .exportDecl input with
  | invariant error => simp [bind, semicolonResult] at result
  | ok semicolon afterSemicolon =>
      simp [bind, semicolonResult, pure] at result
  | reject semicolonFailure semicolonRejected =>
      have rejectedEq := symbol_reject_state_eq .semicolon .exportDecl
        semicolonResult
      simp only [bind, semicolonResult] at result
      cases result
      rw [rejectedEq]
      exact .semicolonMissing
        (symbol_reject_tokenKindAbsentAt .semicolon .exportDecl
          semicolonResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportProperties
/-! Provenance, token-window, and cursor contracts for export subparsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem exportBind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

private theorem getState_preservesExportTokenWindow :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem exportPathTail_validFor (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (ExportInternals.exportPathTail first fuel last tailRev state).ValidFor
        state QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold ExportInternals.exportPathTail
      split
      · cases dotResult : symbol .dot .exportDecl state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot .exportDecl state stateValid
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using dotValid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .exportDecl state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot .exportDecl dotResult
            simp only
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have componentValid := identifier_validFor .exportDecl
                  afterDot dotValid.2.1
                rw [componentResult] at componentValid
                simpa only [Reply.ValidFor] using
                  componentValid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid := identifier_validFor .exportDecl
                  afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases identifier_ok_state_shape .exportDecl componentResult with
                  ⟨componentToken, componentFound, componentSpan,
                    componentTokens, componentCursor⟩
                have componentFoundInState :
                    state.tokens[state.cursor + 1]? = some componentToken := by
                  have foundAtCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some componentFound
                  simpa [dotShape.2] using foundAtCursor
                have firstBeforeComponentIndex :
                    firstIndex < state.cursor + 1 :=
                  Nat.lt_of_lt_of_le firstBeforeCursor
                    (Nat.le_add_right state.cursor 1)
                have firstEndBeforeComponentStart :
                    first.span.endByte ≤ component.span.startByte := by
                  have ordered :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      firstFound componentFoundInState
                      firstBeforeComponentIndex
                  simpa [firstSpan, componentSpan] using ordered
                have firstBeforeComponent :
                    first.span.startByte ≤ component.span.endByte := by
                  apply Nat.le_trans firstValid.2.1
                  apply Nat.le_trans firstEndBeforeComponentStart
                  have spanValid : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  exact spanValid.2.1
                have firstValidNext : first.span.ValidFor next.file := by
                  simpa [componentValid.2.2, dotValid.2.2] using firstValid
                have componentValidNext :
                    component.span.ValidFor next.file := by
                  have spanValid : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  simpa [componentValid.2.2] using spanValid
                have tailValidNext : ∀ item ∈ component :: tailRev,
                    item.span.ValidFor next.file := by
                  intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact componentValidNext
                  · simpa [componentValid.2.2, dotValid.2.2] using
                      tailValid item member
                have firstFoundNext :
                    next.tokens[firstIndex]? = some firstToken := by
                  simpa [componentTokens, dotShape.2] using firstFound
                have firstBeforeNextCursor : firstIndex < next.cursor := by
                  have firstBeforeAfterDot : firstIndex < afterDot.cursor := by
                    rw [dotShape.2]
                    exact Nat.lt_of_lt_of_le firstBeforeCursor
                      (Nat.le_add_right state.cursor 1)
                  rw [componentCursor]
                  exact Nat.lt_of_lt_of_le firstBeforeAfterDot
                    (Nat.le_add_right afterDot.cursor 1)
                exact (inductionHypothesis component (component :: tailRev)
                  next firstIndex firstToken componentValid.2.1
                  firstValidNext componentValidNext tailValidNext
                  firstBeforeComponent firstFoundNext firstSpan
                  firstBeforeNextCursor).of_file_eq
                    (componentValid.2.2.trans dotValid.2.2)
      · unfold ExportInternals.finishExportPath Reply.ValidFor
          QualifiedName.ValidFor
        refine ⟨⟨?_, ?_⟩, stateValid, rfl⟩
        · exact SourceSpan.cover_validFor firstValid lastValid
            firstBeforeLast
        · intro component member
          simp only [NonemptyList.toList, List.mem_cons,
            List.mem_reverse] at member
          rcases member with rfl | member
          · exact firstValid
          · exact tailValid component member

/-- Export paths preserve every retained component and their covering span. -/
theorem exportPath_validFor :
    ExportInternals.exportPath.ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold ExportInternals.exportPath
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have firstValid := identifier_validFor .exportDecl input inputValid
      rw [firstResult] at firstValid
      simpa only [Reply.ValidFor] using firstValid
  | ok first next =>
      have firstValid := identifier_validFor .exportDecl input inputValid
      rw [firstResult] at firstValid
      rcases identifier_ok_state_shape .exportDecl firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have firstFoundNext :
          next.tokens[input.cursor]? = some firstToken := by
        have foundAtCursor :=
          State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using foundAtCursor
      have firstValidNext : first.span.ValidFor next.file := by
        have spanValid : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using spanValid
      exact (exportPathTail_validFor first (next.remainingCount + 1)
        first [] next input.cursor firstToken firstValid.2.1
        firstValidNext firstValidNext (by simp) firstValidNext.2.1
        firstFoundNext firstSpan (by rw [firstCursor]; simp)).of_file_eq
          firstValid.2.2

private theorem exportPathTail_preservesTokenWindow (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold ExportInternals.exportPathTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot .exportDecl input
        cases dotResult : symbol .dot .exportDecl input with
        | invariant error =>
            simp only [Reply.PreservesTokenWindow]
        | reject failure rejected =>
            rw [dotResult] at dotShape
            simpa only [Reply.PreservesTokenWindow] using dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            simp only
            have componentShape :=
              identifier_preservesTokenWindow .exportDecl afterDot
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error =>
                simp only [Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simpa only [Reply.PreservesTokenWindow] using
                  componentShape.trans dotShape
            | ok component afterComponent =>
                rw [componentResult] at componentShape
                simpa only using (inductionHypothesis component
                    (component :: tailRev) afterComponent).trans
                  (componentShape.trans dotShape)
      · unfold ExportInternals.finishExportPath
        exact ⟨rfl, rfl⟩

/-- Export paths preserve their immutable token carrier and active window. -/
theorem exportPath_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportPath := by
  intro input
  unfold ExportInternals.exportPath
  have firstShape := identifier_preservesTokenWindow .exportDecl input
  cases firstResult : identifier .exportDecl input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first afterFirst =>
      rw [firstResult] at firstShape
      exact (exportPathTail_preservesTokenWindow first
        (afterFirst.remainingCount + 1) first [] afterFirst).trans firstShape

/-- Successful export paths retain the immutable lexer token carrier. -/
theorem exportPath_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportPath :=
  exportPath_preservesTokenWindow.preservesTokensOnSuccess

private theorem exportPathTail_keepsFirstStart (first : Identifier) :
    ∀ fuel last tailRev input path next,
      ExportInternals.exportPathTail first fuel last tailRev input =
          .ok path next →
        path.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact inductionHypothesis component (component :: tailRev)
                  afterComponent path next result
      · unfold ExportInternals.finishExportPath at result
        cases result
        rfl

/-- An export path starts at the first identifier token that it retains. -/
theorem exportPath_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportPath (·.span) := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      rcases identifier_ok_state_shape .exportDecl firstResult with
        ⟨token, found, tokenSpan, _tokens, _cursor⟩
      refine ⟨token, found, ?_⟩
      rw [tokenSpan]
      exact (exportPathTail_keepsFirstStart first
        (afterFirst.remainingCount + 1) first [] afterFirst path next
        result).symm

private theorem exportPathTail_cursorMonotoneOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
      Parser.CursorMonotoneOnSuccess
        (ExportInternals.exportPathTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      · cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact Nat.le_trans
                  (symbol_cursorMonotoneOnSuccess .dot .exportDecl
                    input dot afterDot dotResult)
                  (Nat.le_trans
                    (identifier_cursorMonotoneOnSuccess .exportDecl
                      afterDot component afterComponent componentResult)
                    (inductionHypothesis component (component :: tailRev)
                      afterComponent path next result))
      · unfold ExportInternals.finishExportPath at result
        cases result
        exact Nat.le_refl _

/-- Successful export-path parsing never rewinds the parser cursor. -/
theorem exportPath_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportPath := by
  intro input path next result
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact Nat.le_trans
        (identifier_cursorMonotoneOnSuccess .exportDecl
          input first afterFirst firstResult)
        (exportPathTail_cursorMonotoneOnSuccess first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result)

private theorem starConstructorSelection_validFor :
    (do
      let opening ← symbol .leftParen .exportDecl
      let marker ← symbol .star .exportDecl
      let closing ← symbol .rightParen .exportDecl
      pure ({
        span := SourceSpan.cover opening.span closing.span
        value := ConstructorSelectionValue.all marker.span
      } : ConstructorSelection)).ValidFor ConstructorSelection.ValidFor := by
  let parser : Parser ConstructorSelection := do
    let opening ← symbol .leftParen .exportDecl
    let marker ← symbol .star .exportDecl
    let closing ← symbol .rightParen .exportDecl
    pure {
      span := SourceSpan.cover opening.span closing.span
      value := .all marker.span
    }
  change parser.ValidFor ConstructorSelection.ValidFor
  have weak : parser.ValidFor (fun _ _ => True) := by
    dsimp [parser]
    apply Parser.bind_validFor (symbol_validFor .leftParen .exportDecl)
    intro opening
    apply Parser.bind_validFor (symbol_validFor .star .exportDecl)
    intro marker
    apply Parser.bind_validFor (symbol_validFor .rightParen .exportDecl)
    intro closing
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : parser input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok selection final =>
      rw [parsed] at weakResult
      have stages := parsed
      dsimp [parser] at stages
      rcases exportBind_ok_components stages with
        ⟨opening, afterOpening, openingResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨marker, afterMarker, markerResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨closing, afterClosing, closingResult, finished⟩
      have openingValid := symbol_validFor .leftParen .exportDecl
        input inputValid
      rw [openingResult] at openingValid
      have markerValid := symbol_validFor .star .exportDecl
        afterOpening openingValid.2.1
      rw [markerResult] at markerValid
      have closingValid := symbol_validFor .rightParen .exportDecl
        afterMarker markerValid.2.1
      rw [closingResult] at closingValid
      have openingSpanValid : opening.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using openingValid.1
      have markerSpanValid : marker.span.ValidFor input.file := by
        simpa only [Located.ValidFor, openingValid.2.2] using markerValid.1
      have closingSpanValid : closing.span.ValidFor input.file := by
        simpa only [Located.ValidFor, markerValid.2.2,
          openingValid.2.2] using closingValid.1
      have openingShape := symbol_ok_state_shape .leftParen .exportDecl
        openingResult
      have closingShape := symbol_ok_state_shape .rightParen .exportDecl
        closingResult
      have openingAt :=
        State.getElem?_eq_some_of_peek?_eq_some openingShape.1
      have closingAtAfterMarker :=
        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
      have closingAtInput :
          input.tokens[afterMarker.cursor]? = some closing := by
        have openingTokens := symbol_preservesTokensOnSuccess
          .leftParen .exportDecl input opening afterOpening openingResult
        have markerTokens := symbol_preservesTokensOnSuccess
          .star .exportDecl afterOpening marker afterMarker markerResult
        simpa [markerTokens, openingTokens] using closingAtAfterMarker
      have cursorOrder : input.cursor < afterMarker.cursor :=
        Nat.lt_trans
          (acceptToken_cursor_lt_onSuccess (.symbol .leftParen) .exportDecl
            (· == .symbol .leftParen) openingResult)
          (acceptToken_cursor_lt_onSuccess (.symbol .star) .exportDecl
            (· == .symbol .star) markerResult)
      have openingBeforeClosing :=
        inputValid.token_end_le_token_start_of_getElem?_lt
          openingAt closingAtInput cursorOrder
      have outerValid := SourceSpan.cover_validFor openingSpanValid
        closingSpanValid (Nat.le_trans openingSpanValid.2.1
          (Nat.le_trans openingBeforeClosing closingSpanValid.2.1))
      cases finished
      exact ⟨⟨outerValid, markerSpanValid⟩,
        weakResult.2.1, weakResult.2.2⟩

private theorem namedConstructorSelection_validFor :
    (do
      let values ← delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
      let constructors ← ExportInternals.requireConstructorNames values
      pure ({
        span := values.span
        value := ConstructorSelectionValue.named constructors
      } : ConstructorSelection)).ValidFor ConstructorSelection.ValidFor := by
  apply Parser.bind_validFor_of_value
    (delimitedNoTrailing_validFor Located.ValidFor .leftParen .rightParen
      false (identifier .exportDecl) .exportDecl .topLevel
      (identifier_validFor .exportDecl)
      (identifier_preservesTokensOnSuccess .exportDecl))
  intro values input inputValid valuesValid
  unfold ExportInternals.requireConstructorNames
  cases elements : values.elements with
  | nil => trivial
  | cons head tail =>
      simp only [bind, pure, Reply.ValidFor,
        ConstructorSelection.ValidFor]
      refine ⟨⟨valuesValid.1, ?_⟩, inputValid, trivial⟩
      intro constructor member
      exact valuesValid.2 constructor (by
        simpa [NonemptyList.toList, elements] using member)

/-- Constructor selections retain their delimiter, marker, and name ranges. -/
theorem constructorSelection_validFor :
    ExportInternals.constructorSelection.ValidFor
      ConstructorSelection.ValidFor := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · exact starConstructorSelection_validFor
  · exact namedConstructorSelection_validFor

private theorem requireConstructorNames_preservesTokenWindow
    (values : DelimitedList Identifier) :
    Parser.PreservesTokenWindow
      (ExportInternals.requireConstructorNames values) := by
  intro input
  unfold ExportInternals.requireConstructorNames
  cases values.elements <;> trivial

/-- Constructor selections preserve every ordinary token window. -/
theorem constructorSelection_preservesTokenWindow :
    Parser.PreservesTokenWindow
      ExportInternals.constructorSelection := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_preservesTokenWindow getState_preservesExportTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .leftParen .exportDecl)
    intro opening
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .star .exportDecl)
    intro marker
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .rightParen .exportDecl)
    intro closing
    exact Parser.pure_preservesTokenWindow _
  · apply Parser.bind_preservesTokenWindow
      (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen false
        false (identifier .exportDecl) .exportDecl .topLevel
        (identifier_preservesTokenWindow .exportDecl))
    intro values
    apply Parser.bind_preservesTokenWindow
      (requireConstructorNames_preservesTokenWindow values)
    intro constructors
    exact Parser.pure_preservesTokenWindow _

/-- Successful constructor selections retain the lexer token carrier. -/
theorem constructorSelection_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess
      ExportInternals.constructorSelection :=
  constructorSelection_preservesTokenWindow.preservesTokensOnSuccess

private theorem requireConstructorNames_cursorMonotoneOnSuccess
    (values : DelimitedList Identifier) :
    Parser.CursorMonotoneOnSuccess
      (ExportInternals.requireConstructorNames values) := by
  intro input constructors next parsed
  unfold ExportInternals.requireConstructorNames at parsed
  cases elements : values.elements with
  | nil => simp [elements] at parsed
  | cons head tail =>
      simp only [elements] at parsed
      cases parsed
      exact Nat.le_refl _

/-- Successful constructor selections never rewind the cursor. -/
theorem constructorSelection_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess
      ExportInternals.constructorSelection := by
  unfold ExportInternals.constructorSelection
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .leftParen .exportDecl)
    intro opening
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .star .exportDecl)
    intro marker
    apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .rightParen .exportDecl)
    intro closing
    exact Parser.pure_cursorMonotoneOnSuccess _
  · apply Parser.bind_cursorMonotoneOnSuccess
      (delimitedNoTrailing_cursorMonotoneOnSuccess .leftParen .rightParen
        false (identifier .exportDecl) .exportDecl .topLevel)
    intro values
    apply Parser.bind_cursorMonotoneOnSuccess
      (requireConstructorNames_cursorMonotoneOnSuccess values)
    intro constructors
    exact Parser.pure_cursorMonotoneOnSuccess _

private theorem starConstructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (do
      let opening ← symbol .leftParen .exportDecl
      let marker ← symbol .star .exportDecl
      let closing ← symbol .rightParen .exportDecl
      pure ({
        span := SourceSpan.cover opening.span closing.span
        value := ConstructorSelectionValue.all marker.span
      } : ConstructorSelection)) (·.span) := by
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (symbol_startsAtCurrentTokenOnSuccess .leftParen .exportDecl)
  intro opening input selection final parsed
  rcases exportBind_ok_components parsed with
    ⟨marker, afterMarker, _markerResult, rest⟩
  rcases exportBind_ok_components rest with
    ⟨closing, afterClosing, _closingResult, finished⟩
  cases finished
  rfl

private theorem namedConstructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess (do
      let values ← delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel
      let constructors ← ExportInternals.requireConstructorNames values
      pure ({
        span := values.span
        value := ConstructorSelectionValue.named constructors
      } : ConstructorSelection)) (·.span) := by
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (delimitedNoTrailing_startsAtCurrentTokenOnSuccess .leftParen .rightParen
      false (identifier .exportDecl) .exportDecl .topLevel)
  intro values input selection final parsed
  rcases exportBind_ok_components parsed with
    ⟨constructors, afterConstructors, _constructorsResult, finished⟩
  cases finished
  rfl

/-- A constructor selection starts at its opening parenthesis. -/
theorem constructorSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.constructorSelection (·.span) := by
  intro input selection final parsed
  unfold ExportInternals.constructorSelection at parsed
  simp only [getState, bind] at parsed
  split at parsed
  · exact starConstructorSelection_startsAtCurrentTokenOnSuccess
      input selection final parsed
  · exact namedConstructorSelection_startsAtCurrentTokenOnSuccess
      input selection final parsed

/-- Export names retain every marker, identifier, and constructor range. -/
theorem exportName_validFor :
    ExportInternals.exportName.ValidFor ExportName.ValidFor := by
  intro input inputValid
  unfold ExportInternals.exportName
  split
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        simpa only [Reply.ValidFor] using markerValid
    | ok marker next =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        simp only [Reply.ValidFor, ExportName.ValidFor]
        exact ⟨⟨by simpa only [Located.ValidFor] using markerValid.1,
          by simpa only [Located.ValidFor] using markerValid.1⟩,
          markerValid.2.1, markerValid.2.2⟩
  · split
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have selectedValid := operatorSelector_validFor .exportDecl
            input inputValid
          rw [selectedResult] at selectedValid
          simpa only [Reply.ValidFor] using selectedValid
      | ok selected next =>
          have selectedValid := operatorSelector_validFor .exportDecl
            input inputValid
          rw [selectedResult] at selectedValid
          cases selectedValue : selected.value with
          | identifier name => simp only [selectedValue, Reply.ValidFor]
          | operator spelling =>
              simp only [selectedValue, Reply.ValidFor, ExportName.ValidFor]
              exact ⟨⟨selectedValid.1.1, selectedValid.1.1⟩,
                selectedValid.2.1, selectedValid.2.2⟩
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have nameValid := identifier_validFor .exportDecl input inputValid
          rw [nameResult] at nameValid
          simpa only [Reply.ValidFor] using nameValid
      | ok name afterName =>
          have nameValid := identifier_validFor .exportDecl input inputValid
          rw [nameResult] at nameValid
          have nameSpanValid : name.span.ValidFor input.file := by
            simpa only [Located.ValidFor] using nameValid.1
          simp only
          split
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have constructorsValid := constructorSelection_validFor
                  afterName nameValid.2.1
                rw [constructorsResult] at constructorsValid
                simpa only [Reply.ValidFor] using
                  constructorsValid.of_file_eq nameValid.2.2
            | ok constructors next =>
                have constructorsValid := constructorSelection_validFor
                  afterName nameValid.2.1
                rw [constructorsResult] at constructorsValid
                have constructorsValidInput :
                    ConstructorSelection.ValidFor input.file constructors := by
                  simpa [nameValid.2.2] using constructorsValid.1
                rcases identifier_ok_state_shape .exportDecl nameResult with
                  ⟨nameToken, nameFound, nameTokenSpan, nameTokens,
                    nameCursor⟩
                rcases constructorSelection_startsAtCurrentTokenOnSuccess
                    afterName constructors next constructorsResult with
                  ⟨opening, openingFound, openingStart⟩
                have nameAt :=
                  State.getElem?_eq_some_of_peek?_eq_some nameFound
                have openingAtAfterName :=
                  State.getElem?_eq_some_of_peek?_eq_some openingFound
                have openingAtInput :
                    input.tokens[afterName.cursor]? = some opening := by
                  simpa [nameTokens] using openingAtAfterName
                have nameBeforeOpening :=
                  inputValid.token_end_le_token_start_of_getElem?_lt
                    nameAt openingAtInput (by rw [nameCursor]; simp)
                have ordered : name.span.startByte ≤ constructors.span.endByte :=
                  Nat.le_trans nameSpanValid.2.1 (Nat.le_trans
                    (by simpa [nameTokenSpan] using nameBeforeOpening)
                    (by rw [openingStart]; exact constructorsValidInput.1.2.1))
                have outerValid := SourceSpan.cover_validFor nameSpanValid
                  constructorsValidInput.1 ordered
                simp only [Reply.ValidFor, ExportName.ValidFor]
                refine ⟨⟨outerValid, nameSpanValid, ?_⟩,
                  constructorsValid.2.1,
                  constructorsValid.2.2.trans nameValid.2.2⟩
                intro retained member
                have retainedEq : retained = constructors := by
                  simpa using member.symm
                subst retained
                exact constructorsValidInput
          · simp only [Reply.ValidFor, ExportName.ValidFor]
            exact ⟨⟨nameSpanValid, nameSpanValid, by simp⟩,
              nameValid.2.1, nameValid.2.2⟩

/-- Export-name parsing preserves every ordinary token window. -/
theorem exportName_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportName := by
  intro input
  unfold ExportInternals.exportName
  split
  · have markerShape := symbol_preservesTokenWindow .star .exportDecl input
    cases markerResult : symbol .star .exportDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [markerResult] at markerShape
        exact markerShape
    | ok marker next =>
        rw [markerResult] at markerShape
        exact markerShape
  · split
    · have selectedShape :=
        operatorSelector_preservesTokenWindow .exportDecl input
      cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [selectedResult] at selectedShape
          exact selectedShape
      | ok selected next =>
          rw [selectedResult] at selectedShape
          cases selectedValue : selected.value with
          | identifier name =>
              simp only [selectedValue, Reply.PreservesTokenWindow]
          | operator spelling =>
              simpa only [selectedValue, Reply.PreservesTokenWindow] using
                selectedShape
    · have nameShape := identifier_preservesTokenWindow .exportDecl input
      cases nameResult : identifier .exportDecl input with
      | invariant error => trivial
      | reject failure rejected =>
          rw [nameResult] at nameShape
          exact nameShape
      | ok name afterName =>
          rw [nameResult] at nameShape
          simp only
          split
          · have constructorsShape :=
              constructorSelection_preservesTokenWindow afterName
            cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => trivial
            | reject failure rejected =>
                rw [constructorsResult] at constructorsShape
                exact constructorsShape.trans nameShape
            | ok constructors next =>
                rw [constructorsResult] at constructorsShape
                exact constructorsShape.trans nameShape
          · exact nameShape

/-- Successful export names retain the immutable lexer token carrier. -/
theorem exportName_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportName :=
  exportName_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful export-name parsing never rewinds the cursor. -/
theorem exportName_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportName := by
  intro input exported next parsed
  unfold ExportInternals.exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_cursorMonotoneOnSuccess .star .exportDecl
          input marker next markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
            simp only [selectedValue] at parsed
            cases parsed
            exact operatorSelector_cursorMonotoneOnSuccess .exportDecl
              input selected next selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          split at parsed
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact Nat.le_trans
                  (identifier_cursorMonotoneOnSuccess .exportDecl
                    input name afterName nameResult)
                  (constructorSelection_cursorMonotoneOnSuccess
                    afterName constructors next constructorsResult)
          · cases parsed
            exact identifier_cursorMonotoneOnSuccess .exportDecl
              input name next nameResult

/-- An export name starts at its wildcard, operator, or identifier token. -/
theorem exportName_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportName (·.span) := by
  intro input exported next parsed
  unfold ExportInternals.exportName at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_startsAtCurrentTokenOnSuccess .star .exportDecl
          input marker next markerResult
  · split at parsed
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at parsed
      | reject failure rejected => simp [selectedResult] at parsed
      | ok selected afterSelected =>
          simp only [selectedResult] at parsed
          cases selectedValue : selected.value with
          | identifier name => simp [selectedValue] at parsed
          | operator spelling =>
            simp only [selectedValue] at parsed
            cases parsed
            exact operatorSelector_startsAtCurrentTokenOnSuccess .exportDecl
              input selected next selectedResult
    · cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at parsed
      | reject failure rejected => simp [nameResult] at parsed
      | ok name afterName =>
          simp only [nameResult] at parsed
          rcases identifier_ok_state_shape .exportDecl nameResult with
            ⟨token, found, tokenSpan, _tokens, _cursor⟩
          split at parsed
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at parsed
            | reject failure rejected => simp [constructorsResult] at parsed
            | ok constructors afterConstructors =>
                simp only [constructorsResult] at parsed
                cases parsed
                exact ⟨token, found, by
                  simp [SourceSpan.cover, tokenSpan]⟩
          · cases parsed
            exact ⟨token, found, congrArg SourceSpan.startByte tokenSpan⟩

/-- Local export items retain their name or module-wildcard ranges. -/
theorem localExportItem_validFor :
    ExportInternals.localExportItem.ValidFor LocalExportItem.ValidFor := by
  intro input inputValid
  unfold ExportInternals.localExportItem
  split
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have pathValid := exportPath_validFor input inputValid
        rw [pathResult] at pathValid
        simpa only [Reply.ValidFor] using pathValid
    | ok path afterPath =>
        have pathValid := exportPath_validFor input inputValid
        rw [pathResult] at pathValid
        simp only
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot .exportDecl afterPath
              pathValid.2.1
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using
              dotValid.of_file_eq pathValid.2.2
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .exportDecl afterPath
              pathValid.2.1
            rw [dotResult] at dotValid
            simp only
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have markerValid := symbol_validFor .star .exportDecl
                  afterDot dotValid.2.1
                rw [markerResult] at markerValid
                simpa only [Reply.ValidFor] using markerValid.of_file_eq
                  (dotValid.2.2.trans pathValid.2.2)
            | ok marker next =>
                have markerValid := symbol_validFor .star .exportDecl
                  afterDot dotValid.2.1
                rw [markerResult] at markerValid
                have markerSpanValid : marker.span.ValidFor input.file := by
                  simpa only [Located.ValidFor, dotValid.2.2,
                    pathValid.2.2] using markerValid.1
                rcases exportPath_startsAtCurrentTokenOnSuccess
                    input path afterPath pathResult with
                  ⟨firstToken, firstFound, firstStart⟩
                have firstAt :=
                  State.getElem?_eq_some_of_peek?_eq_some firstFound
                have markerShape := symbol_ok_state_shape .star .exportDecl
                  markerResult
                have markerAtAfterDot :=
                  State.getElem?_eq_some_of_peek?_eq_some markerShape.1
                have pathTokens := exportPath_preservesTokensOnSuccess
                  input path afterPath pathResult
                have dotTokens := symbol_preservesTokensOnSuccess .dot
                  .exportDecl afterPath dot afterDot dotResult
                have markerAtInput :
                    input.tokens[afterDot.cursor]? = some marker := by
                  simpa [dotTokens, pathTokens] using markerAtAfterDot
                have firstBeforeMarker :=
                  inputValid.token_end_le_token_start_of_getElem?_lt
                    firstAt markerAtInput (Nat.lt_of_le_of_lt
                      (exportPath_cursorMonotoneOnSuccess
                        input path afterPath pathResult)
                      (acceptToken_cursor_lt_onSuccess (.symbol .dot)
                        .exportDecl (· == .symbol .dot) dotResult))
                have firstSpanValid :=
                  inputValid.peek?_span_validFor firstFound
                have ordered : path.span.startByte ≤ marker.span.endByte := by
                  calc
                    path.span.startByte = firstToken.span.startByte :=
                      firstStart.symm
                    _ ≤ firstToken.span.endByte := firstSpanValid.2.1
                    _ ≤ marker.span.startByte := firstBeforeMarker
                    _ ≤ marker.span.endByte := markerSpanValid.2.1
                have outerValid := SourceSpan.cover_validFor pathValid.1.1
                  markerSpanValid ordered
                simp only [Reply.ValidFor, LocalExportItem.ValidFor]
                exact ⟨⟨outerValid, pathValid.1, markerSpanValid⟩,
                  markerValid.2.1, markerValid.2.2.trans
                    (dotValid.2.2.trans pathValid.2.2)⟩
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have nameValid := exportName_validFor input inputValid
        rw [nameResult] at nameValid
        simpa only [Reply.ValidFor] using nameValid
    | ok name next =>
        have nameValid := exportName_validFor input inputValid
        rw [nameResult] at nameValid
        simp only [Reply.ValidFor, LocalExportItem.ValidFor]
        exact ⟨⟨nameValid.1.1, nameValid.1⟩,
          nameValid.2.1, nameValid.2.2⟩

/-- Local export items preserve every ordinary token window. -/
theorem localExportItem_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.localExportItem := by
  intro input
  unfold ExportInternals.localExportItem
  split
  · have pathShape := exportPath_preservesTokenWindow input
    cases pathResult : ExportInternals.exportPath input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [pathResult] at pathShape
        exact pathShape
    | ok path afterPath =>
        rw [pathResult] at pathShape
        simp only
        have dotShape := symbol_preservesTokenWindow .dot .exportDecl afterPath
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape.trans pathShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            simp only
            have markerShape :=
              symbol_preservesTokenWindow .star .exportDecl afterDot
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => trivial
            | reject failure rejected =>
                rw [markerResult] at markerShape
                exact markerShape.trans (dotShape.trans pathShape)
            | ok marker next =>
                rw [markerResult] at markerShape
                exact markerShape.trans (dotShape.trans pathShape)
  · have nameShape := exportName_preservesTokenWindow input
    cases nameResult : ExportInternals.exportName input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [nameResult] at nameShape
        exact nameShape
    | ok name next =>
        rw [nameResult] at nameShape
        exact nameShape

/-- Successful local export items retain the lexer token carrier. -/
theorem localExportItem_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.localExportItem :=
  localExportItem_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful local export items never rewind the cursor. -/
theorem localExportItem_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.localExportItem := by
  intro input item next parsed
  unfold ExportInternals.localExportItem at parsed
  split at parsed
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at parsed
    | reject failure rejected => simp [pathResult] at parsed
    | ok path afterPath =>
        simp only [pathResult] at parsed
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at parsed
            | reject failure rejected => simp [markerResult] at parsed
            | ok marker afterMarker =>
                simp only [markerResult] at parsed
                cases parsed
                exact Nat.le_trans
                  (exportPath_cursorMonotoneOnSuccess
                    input path afterPath pathResult)
                  (Nat.le_trans
                    (symbol_cursorMonotoneOnSuccess .dot .exportDecl
                      afterPath dot afterDot dotResult)
                    (symbol_cursorMonotoneOnSuccess .star .exportDecl
                      afterDot marker next markerResult))
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at parsed
    | reject failure rejected => simp [nameResult] at parsed
    | ok name afterName =>
        simp only [nameResult] at parsed
        cases parsed
        exact exportName_cursorMonotoneOnSuccess
          input name next nameResult

/-- A local export item starts at its module path or exported name. -/
theorem localExportItem_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.localExportItem (·.span) := by
  intro input item next parsed
  unfold ExportInternals.localExportItem at parsed
  split at parsed
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at parsed
    | reject failure rejected => simp [pathResult] at parsed
    | ok path afterPath =>
        simp only [pathResult] at parsed
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at parsed
        | reject failure rejected => simp [dotResult] at parsed
        | ok dot afterDot =>
            simp only [dotResult] at parsed
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at parsed
            | reject failure rejected => simp [markerResult] at parsed
            | ok marker afterMarker =>
                simp only [markerResult] at parsed
                cases parsed
                rcases exportPath_startsAtCurrentTokenOnSuccess
                    input path afterPath pathResult with
                  ⟨token, found, start⟩
                exact ⟨token, found, by
                  simpa [SourceSpan.cover] using start⟩
  · cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at parsed
    | reject failure rejected => simp [nameResult] at parsed
    | ok name afterName =>
        simp only [nameResult] at parsed
        cases parsed
        exact exportName_startsAtCurrentTokenOnSuccess
          input name next nameResult

/-- Export selections retain their wildcard or selected-name ranges. -/
theorem exportSelection_validFor :
    ExportInternals.exportSelection.ValidFor ExportSelection.ValidFor := by
  intro input inputValid
  unfold ExportInternals.exportSelection
  split
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        simpa only [Reply.ValidFor] using markerValid
    | ok marker next =>
        have markerValid := symbol_validFor .star .exportDecl input inputValid
        rw [markerResult] at markerValid
        have markerSpanValid : marker.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using markerValid.1
        simp only [Reply.ValidFor, ExportSelection.ValidFor]
        exact ⟨⟨markerSpanValid, markerSpanValid⟩,
          markerValid.2.1, markerValid.2.2⟩
  · cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp only [Reply.ValidFor]
    | reject failure rejected =>
        have itemsValid := delimited_validFor ExportName.ValidFor
          .leftBrace .rightBrace true ExportInternals.exportName
          .exportDecl .topLevel exportName_validFor
          exportName_preservesTokensOnSuccess input inputValid
        rw [itemsResult] at itemsValid
        simpa only [Reply.ValidFor] using itemsValid
    | ok items next =>
        have itemsValid := delimited_validFor ExportName.ValidFor
          .leftBrace .rightBrace true ExportInternals.exportName
          .exportDecl .topLevel exportName_validFor
          exportName_preservesTokensOnSuccess input inputValid
        rw [itemsResult] at itemsValid
        simp only [Reply.ValidFor, ExportSelection.ValidFor]
        exact ⟨⟨itemsValid.1.1, itemsValid.1.1, itemsValid.1.2⟩,
          itemsValid.2.1, itemsValid.2.2⟩

/-- Export selections preserve every ordinary token window. -/
theorem exportSelection_preservesTokenWindow :
    Parser.PreservesTokenWindow ExportInternals.exportSelection := by
  intro input
  unfold ExportInternals.exportSelection
  split
  · have markerShape := symbol_preservesTokenWindow .star .exportDecl input
    cases markerResult : symbol .star .exportDecl input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [markerResult] at markerShape
        exact markerShape
    | ok marker next =>
        rw [markerResult] at markerShape
        exact markerShape
  · have itemsShape := delimited_preservesTokenWindow .leftBrace
      .rightBrace true ExportInternals.exportName .exportDecl .topLevel
      exportName_preservesTokenWindow input
    cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => trivial
    | reject failure rejected =>
        rw [itemsResult] at itemsShape
        exact itemsShape
    | ok items next =>
        rw [itemsResult] at itemsShape
        exact itemsShape

/-- Successful export selections retain the lexer token carrier. -/
theorem exportSelection_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess ExportInternals.exportSelection :=
  exportSelection_preservesTokenWindow.preservesTokensOnSuccess

/-- Successful export selections never rewind the cursor. -/
theorem exportSelection_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess ExportInternals.exportSelection := by
  intro input selection next parsed
  unfold ExportInternals.exportSelection at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_cursorMonotoneOnSuccess .star .exportDecl
          input marker next markerResult
  · cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at parsed
    | reject failure rejected => simp [itemsResult] at parsed
    | ok items afterItems =>
        simp only [itemsResult] at parsed
        cases parsed
        exact delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace true
          ExportInternals.exportName .exportDecl .topLevel
          input items next itemsResult

/-- An export selection starts at its wildcard or opening brace. -/
theorem exportSelection_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess
      ExportInternals.exportSelection (·.span) := by
  intro input selection next parsed
  unfold ExportInternals.exportSelection at parsed
  split at parsed
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at parsed
    | reject failure rejected => simp [markerResult] at parsed
    | ok marker afterMarker =>
        simp only [markerResult] at parsed
        cases parsed
        exact symbol_startsAtCurrentTokenOnSuccess .star .exportDecl
          input marker next markerResult
  · cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at parsed
    | reject failure rejected => simp [itemsResult] at parsed
    | ok items afterItems =>
        simp only [itemsResult] at parsed
        cases parsed
        exact delimited_startsAtCurrentTokenOnSuccess .leftBrace .rightBrace
          true ExportInternals.exportName .exportDecl .topLevel
          input items next itemsResult

/-- Export termination preserves the declaration cover and payload ranges. -/
theorem finishExport_validFor (start : SourceSpan) (value : ExportDeclValue)
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor)
    (valueValid : match value with
      | .local items =>
          items.span.ValidFor input.file ∧
            ∀ item ∈ items.elements,
              LocalExportItem.ValidFor input.file item
      | .module path => QualifiedName.ValidFor input.file path
      | .moduleAs path alias =>
          QualifiedName.ValidFor input.file path ∧
            alias.span.ValidFor input.file
      | .itemsFrom path selection =>
          QualifiedName.ValidFor input.file path ∧
            ExportSelection.ValidFor input.file selection) :
    (ExportInternals.finishExport start value input).ValidFor input
      ExportDecl.ValidFor := by
  have semicolonValid := symbol_validFor .semicolon .exportDecl
    input inputValid
  unfold ExportInternals.finishExport
  cases semicolonResult : symbol .semicolon .exportDecl input with
  | invariant error => simp only [bind, semicolonResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [semicolonResult] at semicolonValid
      simpa only [bind, semicolonResult, Reply.ValidFor] using semicolonValid
  | ok semicolon next =>
      rw [semicolonResult] at semicolonValid
      have semicolonSpanValid : semicolon.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using semicolonValid.1
      have semicolonShape := symbol_ok_state_shape .semicolon .exportDecl
        semicolonResult
      have semicolonAt :=
        State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
      have startBeforeSemicolon :=
        inputValid.token_end_le_token_start_of_getElem?_lt
          startFound semicolonAt startBefore
      have ordered : start.startByte ≤ semicolon.span.endByte :=
        Nat.le_trans startValid.2.1 (Nat.le_trans
          (by simpa [startSpan] using startBeforeSemicolon)
          semicolonSpanValid.2.1)
      simp only [bind, semicolonResult, Reply.ValidFor,
        ExportDecl.ValidFor]
      exact ⟨⟨SourceSpan.cover_validFor startValid semicolonSpanValid
          ordered, valueValid⟩, semicolonValid.2.1, semicolonValid.2.2⟩

/-- Export termination preserves every ordinary token window. -/
theorem finishExport_preservesTokenWindow (start : SourceSpan)
    (value : ExportDeclValue) :
    Parser.PreservesTokenWindow
      (ExportInternals.finishExport start value) := by
  unfold ExportInternals.finishExport
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .exportDecl)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

theorem finishExport_preservesTokensOnSuccess (start : SourceSpan)
    (value : ExportDeclValue) :
    Parser.PreservesTokensOnSuccess
      (ExportInternals.finishExport start value) :=
  (finishExport_preservesTokenWindow start value).preservesTokensOnSuccess

/-- Export termination never rewinds the cursor. -/
theorem finishExport_cursorMonotoneOnSuccess (start : SourceSpan)
    (value : ExportDeclValue) :
    Parser.CursorMonotoneOnSuccess
      (ExportInternals.finishExport start value) := by
  unfold ExportInternals.finishExport
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .exportDecl)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

theorem finishExport_keepsStartByte (start : SourceSpan)
    (value : ExportDeclValue) {input next : State} {result : ExportDecl}
    (parsed : ExportInternals.finishExport start value input =
      .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ExportInternals.finishExport at parsed
  rcases exportBind_ok_components parsed with
    ⟨semicolon, afterSemicolon, _semicolonResult, finished⟩
  cases finished
  rfl

/-- Braced local exports retain every selected item and declaration range. -/
theorem localExport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ExportInternals.localExport start input).ValidFor input
      ExportDecl.ValidFor := by
  unfold ExportInternals.localExport
  have itemsValid := delimited_validFor LocalExportItem.ValidFor
    .leftBrace .rightBrace true ExportInternals.localExportItem
    .exportDecl .topLevel localExportItem_validFor
    localExportItem_preservesTokensOnSuccess input inputValid
  cases itemsResult : delimited .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel input with
  | invariant error => simp only [bind, itemsResult, Reply.ValidFor]
  | reject failure rejected =>
      rw [itemsResult] at itemsValid
      simpa only [bind, itemsResult, Reply.ValidFor] using itemsValid
  | ok items afterItems =>
      rw [itemsResult] at itemsValid
      have itemsValidAfter : DelimitedList.ValidFor
          LocalExportItem.ValidFor afterItems.file items := by
        simpa [itemsValid.2.2] using itemsValid.1
      have startValidAfter : start.ValidFor afterItems.file := by
        simpa [itemsValid.2.2] using startValid
      have startFoundAfter :
          afterItems.tokens[startIndex]? = some startToken := by
        simpa [delimited_preservesTokensOnSuccess .leftBrace .rightBrace true
          ExportInternals.localExportItem .exportDecl .topLevel
          localExportItem_preservesTokensOnSuccess input items afterItems
          itemsResult] using startFound
      have startBeforeAfter : startIndex < afterItems.cursor :=
        Nat.lt_of_lt_of_le startBefore
          (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace true
            ExportInternals.localExportItem .exportDecl .topLevel
            input items afterItems itemsResult)
      have finished := finishExport_validFor start (.local items) afterItems
        itemsValid.2.1 startValidAfter startFoundAfter startSpan
        startBeforeAfter ⟨itemsValidAfter.1, itemsValidAfter.2⟩
      simpa only [bind, itemsResult] using
        finished.of_file_eq itemsValid.2.2

/-- Braced local exports preserve every ordinary token window. -/
theorem localExport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow (ExportInternals.localExport start) := by
  unfold ExportInternals.localExport
  apply Parser.bind_preservesTokenWindow
    (delimited_preservesTokenWindow .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel
      localExportItem_preservesTokenWindow)
  intro items
  exact finishExport_preservesTokenWindow start (.local items)

theorem localExport_preservesTokensOnSuccess (start : SourceSpan) :
    Parser.PreservesTokensOnSuccess (ExportInternals.localExport start) :=
  (localExport_preservesTokenWindow start).preservesTokensOnSuccess

/-- Braced local exports never rewind the cursor. -/
theorem localExport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess (ExportInternals.localExport start) := by
  unfold ExportInternals.localExport
  apply Parser.bind_cursorMonotoneOnSuccess
    (delimited_cursorMonotoneOnSuccess .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel)
  intro items
  exact finishExport_cursorMonotoneOnSuccess start (.local items)

theorem localExport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ExportDecl}
    (parsed : ExportInternals.localExport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ExportInternals.localExport at parsed
  rcases exportBind_ok_components parsed with
    ⟨items, afterItems, _itemsResult, finished⟩
  exact finishExport_keepsStartByte start (.local items) finished

private theorem pathExport_weakValidFor (start : SourceSpan) :
    (ExportInternals.pathExport start).ValidFor (fun _ _ => True) := by
  have pathWeak : ExportInternals.exportPath.ValidFor (fun _ _ => True) :=
    exportPath_validFor.mono (fun _ _ _ => trivial)
  have selectionWeak : ExportInternals.exportSelection.ValidFor
      (fun _ _ => True) :=
    exportSelection_validFor.mono (fun _ _ _ => trivial)
  unfold ExportInternals.pathExport
  apply Parser.bind_validFor pathWeak
  intro path
  apply Parser.bind_validFor getState_validFor
  intro observed
  split
  · apply Parser.bind_validFor (symbol_validFor .dot .exportDecl)
    intro dot
    apply Parser.bind_validFor selectionWeak
    intro selection
    unfold ExportInternals.finishExport
    apply Parser.bind_validFor (symbol_validFor .semicolon .exportDecl)
    intro semicolon
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  · split
    · apply Parser.bind_validFor (keyword_validFor .asKw .exportDecl)
      intro asMarker
      apply Parser.bind_validFor (identifier_validFor .exportDecl)
      intro alias
      unfold ExportInternals.finishExport
      apply Parser.bind_validFor (symbol_validFor .semicolon .exportDecl)
      intro semicolon
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
    · unfold ExportInternals.finishExport
      apply Parser.bind_validFor (symbol_validFor .semicolon .exportDecl)
      intro semicolon
      exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)

/-- Path exports retain their path, suffix payload, and declaration cover. -/
theorem pathExport_validFor (start : SourceSpan) (input : State)
    (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    {startIndex : Nat} {startToken : Token}
    (startFound : input.tokens[startIndex]? = some startToken)
    (startSpan : startToken.span = start)
    (startBefore : startIndex < input.cursor) :
    (ExportInternals.pathExport start input).ValidFor input
      ExportDecl.ValidFor := by
  have weak := pathExport_weakValidFor start input inputValid
  cases parsed : ExportInternals.pathExport start input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weak
      exact weak
  | ok result final =>
      rw [parsed] at weak
      have stages := parsed
      unfold ExportInternals.pathExport at stages
      rcases exportBind_ok_components stages with
        ⟨path, afterPath, pathResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨observed, afterObserved, observedResult, rest⟩
      unfold getState at observedResult
      cases observedResult
      have pathReply := exportPath_validFor input inputValid
      rw [pathResult] at pathReply
      have pathTokens := exportPath_preservesTokensOnSuccess
        input path afterPath pathResult
      have startFoundAfterPath :
          afterPath.tokens[startIndex]? = some startToken := by
        rw [pathTokens]
        exact startFound
      have startBeforeAfterPath : startIndex < afterPath.cursor :=
        Nat.lt_of_lt_of_le startBefore
          (exportPath_cursorMonotoneOnSuccess
            input path afterPath pathResult)
      split at rest
      · rcases exportBind_ok_components rest with
          ⟨dot, afterDot, dotResult, rest⟩
        rcases exportBind_ok_components rest with
          ⟨selection, afterSelection, selectionResult, finished⟩
        have dotReply := symbol_validFor .dot .exportDecl
          afterPath pathReply.2.1
        rw [dotResult] at dotReply
        have selectionReply := exportSelection_validFor
          afterDot dotReply.2.1
        rw [selectionResult] at selectionReply
        have finalFile : afterSelection.file = input.file :=
          selectionReply.2.2.trans (dotReply.2.2.trans pathReply.2.2)
        have startFoundFinal :
            afterSelection.tokens[startIndex]? = some startToken := by
          rw [exportSelection_preservesTokensOnSuccess afterDot selection
            afterSelection selectionResult]
          rw [symbol_preservesTokensOnSuccess .dot .exportDecl
            afterPath dot afterDot dotResult]
          exact startFoundAfterPath
        have startBeforeFinal : startIndex < afterSelection.cursor :=
          Nat.lt_of_lt_of_le startBeforeAfterPath (Nat.le_trans
            (symbol_cursorMonotoneOnSuccess .dot .exportDecl
              afterPath dot afterDot dotResult)
            (exportSelection_cursorMonotoneOnSuccess
              afterDot selection afterSelection selectionResult))
        have strong := finishExport_validFor start
          (.itemsFrom path selection) afterSelection selectionReply.2.1
          (by simpa [finalFile] using startValid) startFoundFinal startSpan
          startBeforeFinal ⟨by simpa [finalFile] using pathReply.1,
            by simpa [selectionReply.2.2] using selectionReply.1⟩
        rw [finished] at strong
        exact strong.of_file_eq finalFile
      · split at rest
        · rcases exportBind_ok_components rest with
            ⟨asMarker, afterAs, asResult, rest⟩
          rcases exportBind_ok_components rest with
            ⟨alias, afterAlias, aliasResult, finished⟩
          have asReply := keyword_validFor .asKw .exportDecl
            afterPath pathReply.2.1
          rw [asResult] at asReply
          have aliasReply := identifier_validFor .exportDecl
            afterAs asReply.2.1
          rw [aliasResult] at aliasReply
          have finalFile : afterAlias.file = input.file :=
            aliasReply.2.2.trans (asReply.2.2.trans pathReply.2.2)
          have startFoundFinal :
              afterAlias.tokens[startIndex]? = some startToken := by
            rw [identifier_preservesTokensOnSuccess .exportDecl
              afterAs alias afterAlias aliasResult]
            rw [keyword_preservesTokensOnSuccess .asKw .exportDecl
              afterPath asMarker afterAs asResult]
            exact startFoundAfterPath
          have startBeforeFinal : startIndex < afterAlias.cursor :=
            Nat.lt_of_lt_of_le startBeforeAfterPath (Nat.le_trans
              (keyword_cursorMonotoneOnSuccess .asKw .exportDecl
                afterPath asMarker afterAs asResult)
              (identifier_cursorMonotoneOnSuccess .exportDecl
                afterAs alias afterAlias aliasResult))
          have strong := finishExport_validFor start (.moduleAs path alias)
            afterAlias aliasReply.2.1 (by simpa [finalFile] using startValid)
            startFoundFinal startSpan startBeforeFinal
            ⟨by simpa [finalFile] using pathReply.1,
              by
                have aliasSpanValid : alias.span.ValidFor afterAs.file := by
                  simpa only [Located.ValidFor] using aliasReply.1
                simpa [aliasReply.2.2] using aliasSpanValid⟩
          rw [finished] at strong
          exact strong.of_file_eq finalFile
        · have strong := finishExport_validFor start (.module path)
            afterPath pathReply.2.1
            (by simpa [pathReply.2.2] using startValid)
            startFoundAfterPath startSpan startBeforeAfterPath
            (by simpa [pathReply.2.2] using pathReply.1)
          rw [rest] at strong
          exact strong.of_file_eq pathReply.2.2

/-- Path exports preserve every ordinary token window. -/
theorem pathExport_preservesTokenWindow (start : SourceSpan) :
    Parser.PreservesTokenWindow (ExportInternals.pathExport start) := by
  unfold ExportInternals.pathExport
  apply Parser.bind_preservesTokenWindow exportPath_preservesTokenWindow
  intro path
  apply Parser.bind_preservesTokenWindow getState_preservesExportTokenWindow
  intro observed
  split
  · apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .dot .exportDecl)
    intro dot
    apply Parser.bind_preservesTokenWindow exportSelection_preservesTokenWindow
    intro selection
    exact finishExport_preservesTokenWindow start (.itemsFrom path selection)
  · split
    · apply Parser.bind_preservesTokenWindow
        (keyword_preservesTokenWindow .asKw .exportDecl)
      intro asMarker
      apply Parser.bind_preservesTokenWindow
        (identifier_preservesTokenWindow .exportDecl)
      intro alias
      exact finishExport_preservesTokenWindow start (.moduleAs path alias)
    · exact finishExport_preservesTokenWindow start (.module path)

theorem pathExport_preservesTokensOnSuccess (start : SourceSpan) :
    Parser.PreservesTokensOnSuccess (ExportInternals.pathExport start) :=
  (pathExport_preservesTokenWindow start).preservesTokensOnSuccess

/-- Successful path exports never rewind the cursor. -/
theorem pathExport_cursorMonotoneOnSuccess (start : SourceSpan) :
    Parser.CursorMonotoneOnSuccess (ExportInternals.pathExport start) := by
  unfold ExportInternals.pathExport
  apply Parser.bind_cursorMonotoneOnSuccess
    exportPath_cursorMonotoneOnSuccess
  intro path
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · apply Parser.bind_cursorMonotoneOnSuccess
      (symbol_cursorMonotoneOnSuccess .dot .exportDecl)
    intro dot
    apply Parser.bind_cursorMonotoneOnSuccess
      exportSelection_cursorMonotoneOnSuccess
    intro selection
    exact finishExport_cursorMonotoneOnSuccess start
      (.itemsFrom path selection)
  · split
    · apply Parser.bind_cursorMonotoneOnSuccess
        (keyword_cursorMonotoneOnSuccess .asKw .exportDecl)
      intro asMarker
      apply Parser.bind_cursorMonotoneOnSuccess
        (identifier_cursorMonotoneOnSuccess .exportDecl)
      intro alias
      exact finishExport_cursorMonotoneOnSuccess start (.moduleAs path alias)
    · exact finishExport_cursorMonotoneOnSuccess start (.module path)

theorem pathExport_keepsStartByte (start : SourceSpan)
    {input next : State} {result : ExportDecl}
    (parsed : ExportInternals.pathExport start input = .ok result next) :
    start.startByte = result.span.startByte := by
  unfold ExportInternals.pathExport at parsed
  rcases exportBind_ok_components parsed with
    ⟨path, afterPath, _pathResult, rest⟩
  rcases exportBind_ok_components rest with
    ⟨observed, afterObserved, observedResult, rest⟩
  unfold getState at observedResult
  cases observedResult
  split at rest
  · rcases exportBind_ok_components rest with
      ⟨dot, afterDot, _dotResult, rest⟩
    rcases exportBind_ok_components rest with
      ⟨selection, afterSelection, _selectionResult, finished⟩
    exact finishExport_keepsStartByte start
      (.itemsFrom path selection) finished
  · split at rest
    · rcases exportBind_ok_components rest with
        ⟨asMarker, afterAs, _asResult, rest⟩
      rcases exportBind_ok_components rest with
        ⟨alias, afterAlias, _aliasResult, finished⟩
      exact finishExport_keepsStartByte start (.moduleAs path alias) finished
    · exact finishExport_keepsStartByte start (.module path) rest

/-- Complete export parsing preserves every retained source range. -/
theorem exportDecl_validFor : exportDecl.ValidFor ExportDecl.ValidFor := by
  intro input inputValid
  unfold exportDecl
  cases keywordResult : keyword .exportKw .exportDecl input with
  | invariant error => simp only [bind, keywordResult, Reply.ValidFor]
  | reject failure rejected =>
      have keywordReply := keyword_validFor .exportKw .exportDecl
        input inputValid
      rw [keywordResult] at keywordReply
      simpa only [bind, keywordResult, Reply.ValidFor] using keywordReply
  | ok exportKeyword afterKeyword =>
      have keywordReply := keyword_validFor .exportKw .exportDecl
        input inputValid
      rw [keywordResult] at keywordReply
      have keywordShape := acceptToken_ok_state_shape
        (.keyword .exportKw) .exportDecl (· == .keyword .exportKw)
        keywordResult
      have startFoundAfter :
          afterKeyword.tokens[input.cursor]? = some exportKeyword := by
        rw [keywordShape.2]
        exact State.getElem?_eq_some_of_peek?_eq_some keywordShape.1
      have startBeforeAfter : input.cursor < afterKeyword.cursor := by
        rw [keywordShape.2]
        simp
      have startValidAfter :
          exportKeyword.span.ValidFor afterKeyword.file := by
        have validAtInput : exportKeyword.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using keywordReply.1
        simpa [keywordReply.2.2] using validAtInput
      simp only [bind, keywordResult, getState]
      split
      · exact (localExport_validFor exportKeyword.span afterKeyword
          keywordReply.2.1 startValidAfter startFoundAfter rfl
          startBeforeAfter).of_file_eq keywordReply.2.2
      · exact (pathExport_validFor exportKeyword.span afterKeyword
          keywordReply.2.1 startValidAfter startFoundAfter rfl
          startBeforeAfter).of_file_eq keywordReply.2.2

/-- Complete export parsing preserves every ordinary token window. -/
theorem exportDecl_preservesTokenWindow :
    Parser.PreservesTokenWindow exportDecl := by
  unfold exportDecl
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .exportKw .exportDecl)
  intro exportKeyword
  apply Parser.bind_preservesTokenWindow getState_preservesExportTokenWindow
  intro observed
  split
  · exact localExport_preservesTokenWindow exportKeyword.span
  · exact pathExport_preservesTokenWindow exportKeyword.span

theorem exportDecl_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess exportDecl :=
  exportDecl_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete export parsing never rewinds the parser cursor. -/
theorem exportDecl_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess exportDecl := by
  unfold exportDecl
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .exportKw .exportDecl)
  intro exportKeyword
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  split
  · exact localExport_cursorMonotoneOnSuccess exportKeyword.span
  · exact pathExport_cursorMonotoneOnSuccess exportKeyword.span

/-- Complete export parsing starts at the leading `export` token. -/
theorem exportDecl_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess exportDecl (·.span) := by
  unfold exportDecl
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .exportKw) .exportDecl (· == .keyword .exportKw))
  intro exportKeyword input result final parsed
  rcases exportBind_ok_components parsed with
    ⟨observed, afterObserved, observedResult, branchResult⟩
  unfold getState at observedResult
  cases observedResult
  split at branchResult
  · exact localExport_keepsStartByte exportKeyword.span branchResult
  · exact pathExport_keepsStartByte exportKeyword.span branchResult

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportFinishSoundnessProperties
/-! Exact semicolon soundness for canonical export finishing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful export finishing consumes one exact semicolon. -/
theorem finishExport_success_sound (start : SourceSpan)
    (value : ExportDeclValue) {input next : State}
    {declaration : ExportDecl}
    (result : ExportInternals.finishExport start value input =
      .ok declaration next) :
    DeclarativeGrammar.FinishExportParses start value
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.finishExport at result
  cases semicolonResult : symbol .semicolon .exportDecl input with
  | invariant error => simp [bind, semicolonResult] at result
  | reject failure rejected => simp [bind, semicolonResult] at result
  | ok semicolon afterSemicolon =>
      have semicolonSound := symbol_ok_tokenAt .semicolon .exportDecl
        semicolonResult
      simp only [bind, semicolonResult, pure] at result
      cases result
      unfold DeclarativeGrammar.FinishExportParses
      refine ⟨semicolon.span, semicolonSound.1, ?_, rfl⟩
      rw [semicolonSound.2]
      rfl

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.FinishExportOrdinaryOutcomeSoundnessProperties
/-! Complete executable broad ordinary outcomes for export termination. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export exact export-finishing success as a broad ordinary outcome. -/
theorem finishExport_success_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) {input output : State}
    {declaration : ExportDecl}
    (result : ExportInternals.finishExport start value input =
      .ok declaration output) :
    DeclarativeGrammar.FinishExportOrdinaryParses start value
      input.declarativeRemainder declaration output.declarativeRemainder :=
  finishExport_success_sound start value result

/-- Package exact export-finishing success and missing-semicolon rejection. -/
theorem finishExport_ordinaryOutcome_sound (start : SourceSpan)
    (value : ExportDeclValue) :
    (∀ {input output : State} {declaration : ExportDecl},
      ExportInternals.finishExport start value input = .ok declaration output →
        DeclarativeGrammar.FinishExportOrdinaryParses start value
          input.declarativeRemainder declaration output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      ExportInternals.finishExport start value input = .reject failure rejected →
        DeclarativeGrammar.FinishExportRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨finishExport_success_ordinaryOutcome_sound start value,
    finishExport_reject_ordinaryOutcome_sound start value⟩

/-- Re-export deterministic and exclusive export-finishing outcomes. -/
theorem finishExport_ordinaryOutcomeSpec (start : SourceSpan)
    (value : ExportDeclValue) :
    DeclarativeGrammar.DeterministicOutcomeSpec
      (DeclarativeGrammar.FinishExportOrdinaryParses start value)
      DeclarativeGrammar.FinishExportRejects :=
  DeclarativeGrammar.finishExportDeterministicOutcomeSpec start value


/-- Exact values and endpoints for the independent finishExport grammar. -/
theorem finishExport_exactOutcomeSpec (start : SourceSpan) (value : ExportDeclValue) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      (DeclarativeGrammar.FinishExportOrdinaryParses start value) DeclarativeGrammar.FinishExportRejects :=
  DeclarativeGrammar.finishExportExactOutcomeSpec start value

/-- Executable successes agree on their complete value and remainder. -/
theorem finishExport_success_result_unique (start : SourceSpan) (value : ExportDeclValue)
    {input leftOutput rightOutput : State} {left right : ExportDecl}
    (leftResult : ExportInternals.finishExport start value input = .ok left leftOutput)
    (rightResult : ExportInternals.finishExport start value input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (finishExport_exactOutcomeSpec start value).successResultUnique
    (finishExport_success_ordinaryOutcome_sound start value leftResult)
    (finishExport_success_ordinaryOutcome_sound start value rightResult)

/-- Executable rejections agree on their complete declarative endpoint. -/
theorem finishExport_reject_output_unique (start : SourceSpan) (value : ExportDeclValue)
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : ExportInternals.finishExport start value input = .reject leftFailure leftOutput)
    (rightResult : ExportInternals.finishExport start value input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  (finishExport_exactOutcomeSpec start value).rejectOutputUnique
    (finishExport_reject_ordinaryOutcome_sound start value leftResult)
    (finishExport_reject_ordinaryOutcome_sound start value rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportPathSoundnessProperties
/-! Success soundness of maximal canonical export paths. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Failed composite lookahead excludes exactly a dot-identifier pair. -/
private theorem dotIdentifierAbsentAt_of_continuesExportPath_eq_false
    {input : State}
    (stopped : ExportInternals.continuesExportPath input = false) :
    DeclarativeGrammar.DotIdentifierAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨dotSpan, componentSpan, text, dotAt, componentAt⟩
  have dotPresent : isSymbol input .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  have componentPresent :
      input.peekOffsetKind? 1 = some (.identifier text) := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [componentAt.1, ↓reduceIte, componentAt.2, Option.map_some]
  unfold ExportInternals.continuesExportPath at stopped
  rw [dotPresent, componentPresent] at stopped
  contradiction

/-- Successful tail execution recovers its forward-order declarative suffix. -/
private theorem exportPathTail_success_sound (first : Identifier) :
    ∀ fuel last tailRev input path next,
      ExportInternals.exportPathTail first fuel last tailRev input =
          .ok path next →
      ∃ components,
        path.value.components.head = first ∧
        path.value.components.tail = tailRev.reverse ++ components ∧
        DeclarativeGrammar.ExportPathTailParses input.tokens
          input.window.endIndex input.cursor components next.cursor ∧
        path.span = SourceSpan.cover first.span
          (DeclarativeGrammar.finalIdentifier last components).span ∧
        next.tokens = input.tokens ∧ next.window = input.window := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input path next result
      simp [ExportInternals.exportPathTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input path next result
      unfold ExportInternals.exportPathTail at result
      split at result
      next continues =>
        cases dotResult : symbol .dot .exportDecl input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                have componentSound := identifier_ok_tokenAt .exportDecl
                  componentResult
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent path next result with
                  ⟨components, headEq, componentsEq, tailGrammar, spanEq,
                    nextTokens, nextWindow⟩
                have componentToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 1) {
                        span := component.span
                        value := .identifier component.value
                      } := by
                  simpa only [dotSound.2, State.tokens, State.window,
                    State.cursor] using componentSound.1
                have recursiveTail :
                    DeclarativeGrammar.ExportPathTailParses input.tokens
                      input.window.endIndex (input.cursor + 2) components
                      next.cursor := by
                  simpa only [componentSound.2.1, componentSound.2.2.1,
                    componentSound.2.2.2, dotSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using tailGrammar
                refine ⟨component :: components, headEq, ?_,
                  .next dot.span dotSound.1 componentToken recursiveTail,
                  ?_, ?_, ?_⟩
                · calc
                    path.value.components.tail =
                        (component :: tailRev).reverse ++ components :=
                      componentsEq
                    _ = tailRev.reverse ++ (component :: components) := by
                      simp [List.reverse_cons, List.append_assoc]
                · simpa only [DeclarativeGrammar.finalIdentifier] using spanEq
                · exact nextTokens.trans
                    (componentSound.2.1.trans (by rw [dotSound.2]))
                · exact nextWindow.trans
                    (componentSound.2.2.1.trans (by rw [dotSound.2]))
      next stopped =>
        have stoppedFalse :
            ExportInternals.continuesExportPath input = false := by
          cases found : ExportInternals.continuesExportPath input <;> simp_all
        have absent :=
          dotIdentifierAbsentAt_of_continuesExportPath_eq_false stoppedFalse
        unfold ExportInternals.finishExportPath at result
        cases result
        exact ⟨[], rfl, by simp, .done input.cursor absent,
          by simp [DeclarativeGrammar.finalIdentifier], rfl, rfl⟩

/-- Every successful export path follows the maximal declarative path grammar. -/
theorem exportPath_success_sound {input next : State}
    {path : QualifiedName}
    (result : ExportInternals.exportPath input = .ok path next) :
    DeclarativeGrammar.ExportPathParses input.declarativeRemainder path
      next.declarativeRemainder := by
  unfold ExportInternals.exportPath at result
  cases firstResult : identifier .exportDecl input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      have firstSound := identifier_ok_tokenAt .exportDecl firstResult
      simp only [firstResult] at result
      rcases exportPathTail_success_sound first
          (afterFirst.remainingCount + 1) first [] afterFirst path next result with
        ⟨components, headEq, componentsEq, tailGrammar, spanEq,
          nextTokens, nextWindow⟩
      have tailEq : path.value.components.tail = components := by
        simpa using componentsEq
      unfold DeclarativeGrammar.ExportPathParses State.declarativeRemainder
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact nextTokens.trans firstSound.2.1
      · exact congrArg TokenWindow.endIndex
          (nextWindow.trans firstSound.2.2.1)
      · simpa only [headEq] using firstSound.1
      · simpa only [firstSound.2.1, firstSound.2.2.1,
          firstSound.2.2.2, tailEq] using tailGrammar
      · simpa only [headEq, tailEq] using spanEq

/-- Export-path grammar soundness composes with source validity. -/
theorem exportPath_success_sound_and_validFor {input next : State}
    {path : QualifiedName} (inputValid : input.ValidFor)
    (result : ExportInternals.exportPath input = .ok path next) :
    DeclarativeGrammar.ExportPathParses input.declarativeRemainder path
        next.declarativeRemainder ∧
      path.ValidFor input.file := by
  refine ⟨exportPath_success_sound result, ?_⟩
  have valid := exportPath_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ConstructorSelectionSoundnessProperties
/-! Success soundness of canonical constructor selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Requiring constructor names preserves state and forward element order. -/
theorem requireConstructorNames_success_shape
    {values : DelimitedList Identifier}
    {input next : State} {constructors : NonemptyList Identifier}
    (result : ExportInternals.requireConstructorNames values input =
      .ok constructors next) :
    next = input ∧ constructors.toList = values.elements := by
  unfold ExportInternals.requireConstructorNames at result
  cases elements : values.elements with
  | nil => simp [elements] at result
  | cons head tail =>
      simp only [elements, pure] at result
      cases result
      exact ⟨rfl, by simp [NonemptyList.toList]⟩

/-- Every successful constructor selection follows the independent grammar. -/
theorem constructorSelection_success_sound {input next : State}
    {selection : ConstructorSelection}
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    DeclarativeGrammar.ConstructorSelectionParses
      input.declarativeRemainder selection next.declarativeRemainder := by
  by_cases all :
      input.peekOffsetKind? 1 == some (.symbol .star)
  · cases openingResult : symbol .leftParen .exportDecl input with
    | invariant error =>
        simp [ExportInternals.constructorSelection, getState, bind, all,
          openingResult] at result
    | reject failure rejected =>
        simp [ExportInternals.constructorSelection, getState, bind, all,
          openingResult] at result
    | ok opening afterOpening =>
        have openingSound := symbol_ok_tokenAt .leftParen .exportDecl
          openingResult
        cases markerResult : symbol .star .exportDecl afterOpening with
        | invariant error =>
            simp [ExportInternals.constructorSelection, getState, bind, all,
              openingResult, markerResult] at result
        | reject failure rejected =>
            simp [ExportInternals.constructorSelection, getState, bind, all,
              openingResult, markerResult] at result
        | ok marker afterMarker =>
            have markerSound := symbol_ok_tokenAt .star .exportDecl
              markerResult
            cases closingResult : symbol .rightParen .exportDecl afterMarker with
            | invariant error =>
                simp [ExportInternals.constructorSelection, getState, bind,
                  all, openingResult, markerResult, closingResult] at result
            | reject failure rejected =>
                simp [ExportInternals.constructorSelection, getState, bind,
                  all, openingResult, markerResult, closingResult] at result
            | ok closing final =>
                have closingSound := symbol_ok_tokenAt .rightParen .exportDecl
                  closingResult
                simp only [ExportInternals.constructorSelection, getState,
                  bind, all, ↓reduceIte, openingResult, markerResult,
                  closingResult, pure] at result
                cases result
                have markerToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 1) {
                        span := marker.span
                        value := .symbol .star
                      } := by
                  simpa only [openingSound.2, State.tokens, State.window,
                    State.cursor] using markerSound.1
                have closingToken :
                    DeclarativeGrammar.TokenAt input.tokens
                      input.window.endIndex (input.cursor + 2) {
                        span := closing.span
                        value := .symbol .rightParen
                      } := by
                  simpa only [markerSound.2, openingSound.2, State.tokens,
                    State.window, State.cursor, Nat.add_assoc] using
                    closingSound.1
                have grammar :=
                  DeclarativeGrammar.ConstructorSelectionParses.all
                    (input := input.declarativeRemainder)
                    opening.span marker.span closing.span openingSound.1
                    markerToken closingToken
                simpa only [closingSound.2, markerSound.2, openingSound.2,
                  State.declarativeRemainder, State.tokens, State.window,
                  State.cursor, Nat.add_assoc] using grammar
  · have named :
        (input.peekOffsetKind? 1 == some (.symbol .star)) = false := by
      cases found : input.peekOffsetKind? 1 == some (.symbol .star) with
      | false => rfl
      | true => exact False.elim (all found)
    cases valuesResult : delimitedNoTrailing .leftParen .rightParen false
        (identifier .exportDecl) .exportDecl .topLevel input with
    | invariant error =>
        simp [ExportInternals.constructorSelection, getState, bind, named,
          valuesResult] at result
    | reject failure rejected =>
        simp [ExportInternals.constructorSelection, getState, bind, named,
          valuesResult] at result
    | ok values afterValues =>
        have valuesGrammar := delimitedNoTrailing_nonempty_success_sound
          .leftParen .rightParen (identifier .exportDecl)
          DeclarativeGrammar.IdentifierParses .exportDecl .topLevel
          (identifier_success_sound .exportDecl)
          (identifier_preservesTokenWindow .exportDecl) valuesResult
        cases constructorsResult :
            ExportInternals.requireConstructorNames values afterValues with
        | invariant error =>
            simp [ExportInternals.constructorSelection, getState, bind, named,
              valuesResult, constructorsResult] at result
        | reject failure rejected =>
            simp [ExportInternals.constructorSelection, getState, bind, named,
              valuesResult, constructorsResult] at result
        | ok constructors afterConstructors =>
            have shape := requireConstructorNames_success_shape
              constructorsResult
            simp only [ExportInternals.constructorSelection, getState, bind,
              named, Bool.false_eq_true, ↓reduceIte, valuesResult,
              constructorsResult, pure] at result
            cases result
            apply DeclarativeGrammar.ConstructorSelectionParses.named
            unfold DeclarativeGrammar.ConstructorNamesParses
            rw [shape.1]
            simpa only [shape.2] using valuesGrammar

/-- Constructor-selection grammar soundness composes with source validity. -/
theorem constructorSelection_success_sound_and_validFor
    {input next : State} {selection : ConstructorSelection}
    (inputValid : input.ValidFor)
    (result : ExportInternals.constructorSelection input =
      .ok selection next) :
    DeclarativeGrammar.ConstructorSelectionParses
        input.declarativeRemainder selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨constructorSelection_success_sound result, ?_⟩
  have valid := constructorSelection_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportNameSoundnessProperties
/-! Success soundness of canonical export-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful export name follows its prioritized independent grammar. -/
theorem exportName_success_sound {input next : State} {name : ExportName}
    (result : ExportInternals.exportName input = .ok name next) :
    DeclarativeGrammar.ExportNameParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold ExportInternals.exportName at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .star .exportDecl markerResult
        simp only [markerResult] at result
        cases result
        have grammar := DeclarativeGrammar.ExportNameParses.wildcard
          (input := input.declarativeRemainder) marker.span markerSound.1
        simpa only [markerSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using grammar
  · have starFalse : isSymbol input .star = false := by
      cases found : isSymbol input .star <;> simp_all
    have starAbsent := symbolAbsentAt_of_isSymbol_eq_false .star starFalse
    split at result
    · cases selectedResult : operatorSelector .exportDecl input with
      | invariant error => simp [selectedResult] at result
      | reject failure rejected => simp [selectedResult] at result
      | ok selected afterSelected =>
          have selectedGrammar := operatorSelector_success_sound .exportDecl
            selectedResult
          rcases selected with ⟨selectedSpan, selectedValue⟩
          cases selectedValue with
          | identifier identifier =>
              simp [selectedResult] at result
          | operator spelling =>
              simp only [selectedResult] at result
              cases result
              exact DeclarativeGrammar.ExportNameParses.operator starAbsent
                selectedGrammar
    · have leftParenFalse : isSymbol input .leftParen = false := by
        cases found : isSymbol input .leftParen <;> simp_all
      have leftParenAbsent := symbolAbsentAt_of_isSymbol_eq_false
        .leftParen leftParenFalse
      cases nameResult : identifier .exportDecl input with
      | invariant error => simp [nameResult] at result
      | reject failure rejected => simp [nameResult] at result
      | ok parsedName afterName =>
          have nameGrammar := identifier_success_sound .exportDecl nameResult
          simp only [nameResult] at result
          split at result
          · cases constructorsResult :
                ExportInternals.constructorSelection afterName with
            | invariant error => simp [constructorsResult] at result
            | reject failure rejected => simp [constructorsResult] at result
            | ok constructors afterConstructors =>
                have constructorsGrammar := constructorSelection_success_sound
                  constructorsResult
                simp only [constructorsResult] at result
                cases result
                exact DeclarativeGrammar.ExportNameParses.identifier
                  starAbsent leftParenAbsent nameGrammar
                  (.present constructorsGrammar)
          · have constructorsAbsentBool :
                isSymbol afterName .leftParen = false := by
              cases found : isSymbol afterName .leftParen <;> simp_all
            have constructorsAbsent := symbolAbsentAt_of_isSymbol_eq_false
              .leftParen constructorsAbsentBool
            cases result
            exact DeclarativeGrammar.ExportNameParses.identifier
              starAbsent leftParenAbsent nameGrammar
              (.absent constructorsAbsent)

/-- Export-name grammar soundness composes with source validity. -/
theorem exportName_success_sound_and_validFor {input next : State}
    {name : ExportName} (inputValid : input.ValidFor)
    (result : ExportInternals.exportName input = .ok name next) :
    DeclarativeGrammar.ExportNameParses input.declarativeRemainder name
        next.declarativeRemainder ∧
      name.ValidFor input.file := by
  refine ⟨exportName_success_sound result, ?_⟩
  have valid := exportName_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportItemSoundnessProperties
/-! Success soundness of canonical local export items. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Failed local-item dispatch excludes exactly an identifier-dot prefix. -/
private theorem identifierDotAbsentAt_of_dispatcher_eq_false {input : State}
    (stopped :
      (isIdentifier input && isSymbol
        { input with cursor := input.cursor + 1 } .dot) = false) :
    DeclarativeGrammar.IdentifierDotAbsentAt input.tokens
      input.window.endIndex input.cursor := by
  rintro ⟨identifierSpan, dotSpan, text, identifierAt, dotAt⟩
  have identifierPresent : isIdentifier input = true := by
    unfold isIdentifier State.peekKind? State.peek?
    simp only [identifierAt.1, ↓reduceIte, identifierAt.2, Option.map_some]
  have dotPresent :
      isSymbol { input with cursor := input.cursor + 1 } .dot = true := by
    unfold isSymbol State.peekKind? State.peek?
    simp only [dotAt.1, ↓reduceIte, dotAt.2, Option.map_some]
    rfl
  rw [identifierPresent, dotPresent] at stopped
  contradiction

/-- Every successful local export item follows its prioritized grammar. -/
theorem localExportItem_success_sound {input next : State}
    {item : LocalExportItem}
    (result : ExportInternals.localExportItem input = .ok item next) :
    DeclarativeGrammar.LocalExportItemParses input.declarativeRemainder item
      next.declarativeRemainder := by
  unfold ExportInternals.localExportItem at result
  split at result
  · cases pathResult : ExportInternals.exportPath input with
    | invariant error => simp [pathResult] at result
    | reject failure rejected => simp [pathResult] at result
    | ok path afterPath =>
        have pathGrammar := exportPath_success_sound pathResult
        simp only [pathResult] at result
        cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases markerResult : symbol .star .exportDecl afterDot with
            | invariant error => simp [markerResult] at result
            | reject failure rejected => simp [markerResult] at result
            | ok marker afterMarker =>
                have markerSound := symbol_ok_tokenAt .star .exportDecl
                  markerResult
                simp only [markerResult] at result
                cases result
                have markerToken :
                    DeclarativeGrammar.TokenAt afterPath.tokens
                      afterPath.window.endIndex (afterPath.cursor + 1) {
                        span := marker.span
                        value := .symbol .star
                      } := by
                  simpa only [dotSound.2, State.tokens, State.window,
                    State.cursor] using markerSound.1
                have grammar :=
                  DeclarativeGrammar.LocalExportItemParses.moduleWildcard
                    dot.span marker.span pathGrammar dotSound.1 markerToken
                simpa only [markerSound.2, dotSound.2,
                  State.declarativeRemainder, State.tokens, State.window,
                  State.cursor, Nat.add_assoc] using grammar
  · have dispatcherFalse :
        (isIdentifier input && isSymbol
          { input with cursor := input.cursor + 1 } .dot) = false := by
      cases found : isIdentifier input && isSymbol
          { input with cursor := input.cursor + 1 } .dot <;> simp_all
    have qualifiedAbsent :=
      identifierDotAbsentAt_of_dispatcher_eq_false dispatcherFalse
    cases nameResult : ExportInternals.exportName input with
    | invariant error => simp [nameResult] at result
    | reject failure rejected => simp [nameResult] at result
    | ok name afterName =>
        have nameGrammar := exportName_success_sound nameResult
        simp only [nameResult] at result
        cases result
        exact DeclarativeGrammar.LocalExportItemParses.name qualifiedAbsent
          nameGrammar

/-- Local-item grammar soundness composes with source validity. -/
theorem localExportItem_success_sound_and_validFor {input next : State}
    {item : LocalExportItem} (inputValid : input.ValidFor)
    (result : ExportInternals.localExportItem input = .ok item next) :
    DeclarativeGrammar.LocalExportItemParses input.declarativeRemainder item
        next.declarativeRemainder ∧
      item.ValidFor input.file := by
  refine ⟨localExportItem_success_sound result, ?_⟩
  have valid := localExportItem_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.LocalExportSoundnessProperties
/-! Success soundness of braced local export declarations. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful local-export helper follows its complete tail grammar. -/
theorem localExport_success_sound (start : SourceSpan)
    {input next : State} {declaration : ExportDecl}
    (result : ExportInternals.localExport start input =
      .ok declaration next) :
    DeclarativeGrammar.LocalExportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.localExport at result
  cases itemsResult : delimited .leftBrace .rightBrace true
      ExportInternals.localExportItem .exportDecl .topLevel input with
  | invariant error => simp [bind, itemsResult] at result
  | reject failure rejected => simp [bind, itemsResult] at result
  | ok items afterItems =>
      have itemsGrammar := delimited_allowEmpty_trailing_success_sound
        .leftBrace .rightBrace ExportInternals.localExportItem
        DeclarativeGrammar.LocalExportItemParses .exportDecl .topLevel
        localExportItem_success_sound localExportItem_preservesTokenWindow
        itemsResult
      simp only [bind, itemsResult] at result
      have finishGrammar := finishExport_success_sound start (.local items)
        result
      unfold DeclarativeGrammar.LocalExportTailParses
      exact ⟨items, afterItems.declarativeRemainder, itemsGrammar,
        finishGrammar⟩

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.ExportSelectionSoundnessProperties
/-! Success soundness of canonical remote export selections. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful remote selection follows its prioritized grammar. -/
theorem exportSelection_success_sound {input next : State}
    {selection : ExportSelection}
    (result : ExportInternals.exportSelection input = .ok selection next) :
    DeclarativeGrammar.ExportSelectionParses input.declarativeRemainder
      selection next.declarativeRemainder := by
  unfold ExportInternals.exportSelection at result
  split at result
  · cases markerResult : symbol .star .exportDecl input with
    | invariant error => simp [markerResult] at result
    | reject failure rejected => simp [markerResult] at result
    | ok marker afterMarker =>
        have markerSound := symbol_ok_tokenAt .star .exportDecl markerResult
        simp only [markerResult] at result
        cases result
        have grammar := DeclarativeGrammar.ExportSelectionParses.wildcard
          (input := input.declarativeRemainder) marker.span markerSound.1
        simpa only [markerSound.2, State.declarativeRemainder,
          State.tokens, State.window, State.cursor] using grammar
  · have starFalse : isSymbol input .star = false := by
      cases found : isSymbol input .star <;> simp_all
    have starAbsent := symbolAbsentAt_of_isSymbol_eq_false .star starFalse
    cases itemsResult : delimited .leftBrace .rightBrace true
        ExportInternals.exportName .exportDecl .topLevel input with
    | invariant error => simp [itemsResult] at result
    | reject failure rejected => simp [itemsResult] at result
    | ok items afterItems =>
        have itemsGrammar := delimited_allowEmpty_trailing_success_sound
          .leftBrace .rightBrace ExportInternals.exportName
          DeclarativeGrammar.ExportNameParses .exportDecl .topLevel
          exportName_success_sound exportName_preservesTokenWindow itemsResult
        simp only [itemsResult] at result
        cases result
        exact DeclarativeGrammar.ExportSelectionParses.selected starAbsent
          itemsGrammar

/-- Remote-selection grammar soundness composes with source validity. -/
theorem exportSelection_success_sound_and_validFor {input next : State}
    {selection : ExportSelection} (inputValid : input.ValidFor)
    (result : ExportInternals.exportSelection input = .ok selection next) :
    DeclarativeGrammar.ExportSelectionParses input.declarativeRemainder
        selection next.declarativeRemainder ∧
      selection.ValidFor input.file := by
  refine ⟨exportSelection_success_sound result, ?_⟩
  have valid := exportSelection_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.PathExportSoundnessProperties
/-! Success soundness of all canonical path-export suffixes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful path-export helper follows one exact prioritized suffix. -/
theorem pathExport_success_sound (start : SourceSpan)
    {input next : State} {declaration : ExportDecl}
    (result : ExportInternals.pathExport start input =
      .ok declaration next) :
    DeclarativeGrammar.PathExportTailParses start
      input.declarativeRemainder declaration next.declarativeRemainder := by
  unfold ExportInternals.pathExport at result
  cases pathResult : ExportInternals.exportPath input with
  | invariant error => simp [bind, pathResult] at result
  | reject failure rejected => simp [bind, pathResult] at result
  | ok path afterPath =>
      have pathGrammar := exportPath_success_sound pathResult
      simp only [bind, pathResult, getState] at result
      split at result
      · cases dotResult : symbol .dot .exportDecl afterPath with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .exportDecl dotResult
            simp only [dotResult] at result
            cases selectionResult : ExportInternals.exportSelection afterDot with
            | invariant error => simp [selectionResult] at result
            | reject failure rejected => simp [selectionResult] at result
            | ok selection afterSelection =>
                have selectionGrammar := exportSelection_success_sound
                  selectionResult
                simp only [selectionResult] at result
                have finishGrammar := finishExport_success_sound start
                  (.itemsFrom path selection) result
                apply DeclarativeGrammar.PathExportTailParses.itemsFrom
                unfold DeclarativeGrammar.ItemsFromExportTailParses
                refine ⟨path, afterPath.declarativeRemainder, dot.span,
                  selection, afterSelection.declarativeRemainder,
                  pathGrammar, dotSound.1, ?_, finishGrammar⟩
                simpa only [dotSound.2, State.declarativeRemainder,
                  State.tokens, State.window, State.cursor] using
                  selectionGrammar
      · have dotFalse : isSymbol afterPath .dot = false := by
          cases found : isSymbol afterPath .dot <;> simp_all
        have dotAbsent := symbolAbsentAt_of_isSymbol_eq_false .dot dotFalse
        split at result
        · cases asResult : keyword .asKw .exportDecl afterPath with
          | invariant error => simp [asResult] at result
          | reject failure rejected => simp [asResult] at result
          | ok asToken afterAs =>
              have asSound := keyword_ok_tokenAt .asKw .exportDecl asResult
              simp only [asResult] at result
              cases aliasResult : identifier .exportDecl afterAs with
              | invariant error => simp [aliasResult] at result
              | reject failure rejected => simp [aliasResult] at result
              | ok alias afterAlias =>
                  have aliasGrammar := identifier_success_sound .exportDecl
                    aliasResult
                  simp only [aliasResult] at result
                  have finishGrammar := finishExport_success_sound start
                    (.moduleAs path alias) result
                  apply DeclarativeGrammar.PathExportTailParses.moduleAs
                  unfold DeclarativeGrammar.ModuleAsExportTailParses
                  refine ⟨path, afterPath.declarativeRemainder,
                    asToken.span, alias, afterAlias.declarativeRemainder,
                    pathGrammar, dotAbsent, asSound.1, ?_, finishGrammar⟩
                  simpa only [asSound.2, State.declarativeRemainder,
                    State.tokens, State.window, State.cursor] using
                    aliasGrammar
        · have asFalse : isKeyword afterPath .asKw = false := by
            cases found : isKeyword afterPath .asKw <;> simp_all
          have asAbsent := keywordAbsentAt_of_isKeyword_eq_false
            .asKw asFalse
          have finishGrammar := finishExport_success_sound start
            (.module path) result
          apply DeclarativeGrammar.PathExportTailParses.module
          unfold DeclarativeGrammar.ModuleExportTailParses
          exact ⟨path, afterPath.declarativeRemainder, pathGrammar,
            dotAbsent, asAbsent, finishGrammar⟩

end Solcore.Syntax.Parser
end
