import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Derive

/-! Success soundness of canonical derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reservedDeriveKeyword?_shape {kind : TokenKind}
    {keyword : HardKeyword}
    (result : DeriveTargetInternals.reservedDeriveKeyword? kind =
      some keyword) :
    kind = .keyword keyword ∧
      DeclarativeGrammar.ReservedDeriveTargetKeyword keyword := by
  cases kind <;> simp [DeriveTargetInternals.reservedDeriveKeyword?] at result
  case keyword found =>
    cases found <;>
      simp [DeclarativeGrammar.ReservedDeriveTargetKeyword] at result ⊢
    all_goals try { cases result; constructor <;> trivial }

/-- Every successful derive component follows its identifier-or-keyword grammar. -/
theorem deriveComponent_success_sound {input next : State}
    {name : Identifier}
    (result : DeriveTargetInternals.deriveComponent input = .ok name next) :
    DeclarativeGrammar.DeriveComponentParses input.declarativeRemainder name
      next.declarativeRemainder := by
  unfold DeriveTargetInternals.deriveComponent at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      simp only [found] at result
      cases reserved :
          DeriveTargetInternals.reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved] at result
          exact .identifier (identifier_success_sound .topItem result)
      | some keyword =>
          have shape := reservedDeriveKeyword?_shape reserved
          have tokenAt := tokenAt_of_peek?_eq_some found
          simp only [reserved] at result
          cases result
          rcases token with ⟨tokenSpan, tokenKind⟩
          simp only at shape tokenAt ⊢
          rw [shape.1] at tokenAt
          have grammar := DeclarativeGrammar.DeriveComponentParses.reserved
            (input := input.declarativeRemainder) keyword shape.2 tokenSpan
            (by simpa only [State.declarativeRemainder] using tokenAt)
          simpa only [State.emit, State.declarativeRemainder, State.tokens,
            State.window, State.cursor] using grammar

private theorem deriveTargetTail_success_sound (first : Identifier) :
    ∀ fuel last tailRev input target next,
      DeriveTargetInternals.deriveTargetTail first fuel last tailRev input =
          .ok target next →
      ∃ components,
        target.value.components.head = first ∧
        target.value.components.tail = tailRev.reverse ++ components ∧
        DeclarativeGrammar.DeriveTargetTailParses
          input.declarativeRemainder components next.declarativeRemainder ∧
        target.span = SourceSpan.cover first.span
          (DeclarativeGrammar.finalIdentifier last components).span := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input target next result
      simp [DeriveTargetInternals.deriveTargetTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input target next result
      unfold DeriveTargetInternals.deriveTargetTail at result
      split at result
      · cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            have dotSound := symbol_ok_tokenAt .dot .topItem dotResult
            simp only [dotResult] at result
            cases componentResult :
                DeriveTargetInternals.deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                have componentSound :=
                  deriveComponent_success_sound componentResult
                simp only [componentResult] at result
                rcases inductionHypothesis component (component :: tailRev)
                    afterComponent target next result with
                  ⟨components, headEq, componentsEq, tailGrammar, spanEq⟩
                have componentGrammar :
                    DeclarativeGrammar.DeriveComponentParses {
                      input.declarativeRemainder with
                        cursor := input.cursor + 1
                    } component afterComponent.declarativeRemainder := by
                  simpa only [dotSound.2, State.declarativeRemainder,
                    State.tokens, State.window, State.cursor] using
                    componentSound
                have grammar := DeclarativeGrammar.DeriveTargetTailParses.next
                  dot.span dotSound.1 componentGrammar tailGrammar
                refine ⟨component :: components, headEq, ?_, grammar, ?_⟩
                · calc
                    target.value.components.tail =
                        (component :: tailRev).reverse ++ components :=
                      componentsEq
                    _ = tailRev.reverse ++ (component :: components) := by
                      simp [List.reverse_cons, List.append_assoc]
                · simpa only [DeclarativeGrammar.finalIdentifier] using spanEq
      · have absent : isSymbol input .dot = false :=
          Bool.eq_false_iff.mpr (by assumption)
        have stopped := symbolAbsentAt_of_isSymbol_eq_false .dot absent
        unfold DeriveTargetInternals.finishDeriveTarget at result
        cases result
        exact ⟨[], rfl, by simp, .done stopped,
          by simp [DeclarativeGrammar.finalIdentifier]⟩

/-- Every successful derive target follows its dotted-component grammar. -/
theorem deriveTarget_success_sound {input next : State}
    {target : DeriveTarget}
    (result : deriveTarget input = .ok target next) :
    DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder target
      next.declarativeRemainder := by
  unfold deriveTarget at result
  cases firstResult : DeriveTargetInternals.deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      have firstSound := deriveComponent_success_sound firstResult
      simp only [firstResult] at result
      rcases deriveTargetTail_success_sound first
          (afterFirst.remainingCount + 1) first [] afterFirst target next result with
        ⟨components, headEq, componentsEq, tailGrammar, spanEq⟩
      unfold DeclarativeGrammar.DeriveTargetParses
      refine ⟨first, afterFirst.declarativeRemainder, components,
        firstSound, tailGrammar, ?_⟩
      rcases target with ⟨targetSpan, targetValue⟩
      rcases targetValue with ⟨targetComponents⟩
      rcases targetComponents with ⟨targetHead, targetTail⟩
      simp only at headEq componentsEq spanEq ⊢
      subst targetHead
      have tailEq : targetTail = components := by simpa using componentsEq
      subst targetTail
      rw [spanEq]
      simp

/-- Derive-target grammar soundness composes with source validity. -/
theorem deriveTarget_success_sound_and_validFor {input next : State}
    {target : DeriveTarget} (inputValid : input.ValidFor)
    (result : deriveTarget input = .ok target next) :
    DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder target
        next.declarativeRemainder ∧
      target.ValidFor input.file := by
  refine ⟨deriveTarget_success_sound result, ?_⟩
  have valid := deriveTarget_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
