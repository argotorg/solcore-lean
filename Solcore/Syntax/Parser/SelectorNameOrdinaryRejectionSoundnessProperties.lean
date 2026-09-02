import Solcore.Syntax.DeclarativeSelectorNameOutcomeGrammar
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.SelectorNameSoundnessProperties

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
