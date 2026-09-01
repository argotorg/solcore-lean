import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Operator

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
