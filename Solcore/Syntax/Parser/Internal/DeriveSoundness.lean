import Solcore.Syntax.Parser.Declarations
import Solcore.Syntax.Parser.Internal.Basics
import Solcore.Syntax.Parser.Internal.DelimitedSoundness
import Solcore.Syntax.Grammar.Declarations
import Solcore.Syntax.Internal.DeriveOutcomes
import Solcore.Syntax.Validity

/-!
Soundness of the parsers of derive attributes: each success and each rejection has its
declarative derivation, and diagnostic-free runs reflect their grammar.
-/

section
-- leanmerge: from Solcore.Syntax.Parser.Derive
set_option autoImplicit false

namespace Solcore.Syntax.Parser

open DeriveTargetInternals

private theorem deriveComponent_validFor :
    deriveComponent.ValidFor Located.ValidFor := by
  intro input inputValid
  unfold deriveComponent
  cases found : input.peek? with
  | none =>
      change (rejectAt input { head := .identifier, tail := [] }
        .topItem).ValidFor input Located.ValidFor
      unfold rejectAt Reply.ValidFor
      exact ⟨inputValid.currentSpan_validFor, inputValid, rfl⟩
  | some token =>
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved]
          exact identifier_validFor .topItem input inputValid
      | some keywordValue =>
          simp only [reserved, Reply.ValidFor, Located.ValidFor]
          have tokenValid := inputValid.peek?_span_validFor found
          refine ⟨tokenValid, ?_, rfl⟩
          have advanced : input.advance? = some
              (token, { input with cursor := input.cursor + 1 }) := by
            simp [State.advance?, found]
          exact (inputValid.advance?_validFor advanced).emit_validFor _
            tokenValid

private theorem deriveComponent_ok_state_shape {input next : State}
    {name : Identifier} (result : deriveComponent input = .ok name next) :
    ∃ token, input.peek? = some token ∧ token.span = name.span ∧
      next.tokens = input.tokens ∧ next.cursor = input.cursor + 1 := by
  unfold deriveComponent at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      change rejectAt input { head := .identifier, tail := [] }
        .topItem = .ok name next at result
      unfold rejectAt at result
      contradiction
  | some token =>
      simp only [found] at result
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved] at result
          rcases identifier_ok_state_shape .topItem result with
            ⟨parsedToken, parsedFound, parsedSpan, tokens, cursor⟩
          exact ⟨parsedToken, by simpa [found] using parsedFound,
            parsedSpan, tokens, cursor⟩
      | some keywordValue =>
          simp only [reserved] at result
          cases result
          exact ⟨token, rfl, rfl, rfl, rfl⟩

private theorem deriveComponent_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveComponent := by
  intro input name next result
  exact (deriveComponent_ok_state_shape result).choose_spec.2.2.1

private theorem deriveComponent_preservesTokenWindow :
    Parser.PreservesTokenWindow deriveComponent := by
  intro input
  unfold deriveComponent
  cases found : input.peek? with
  | none =>
      exact rejectAt_preservesTokenWindow input
        { head := .identifier, tail := [] } .topItem
  | some token =>
      simp only
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only
          exact identifier_preservesTokenWindow .topItem input
      | some keywordValue =>
          simp [Reply.PreservesTokenWindow, State.emit]

private theorem deriveComponent_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveComponent := by
  intro input name next result
  rw [(deriveComponent_ok_state_shape result).choose_spec.2.2.2]
  exact Nat.le_add_right _ _

private theorem deriveTargetTail_validFor (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor → first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span → firstIndex < state.cursor →
      (deriveTargetTail first fuel last tailRev state).ValidFor state
        QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold deriveTargetTail
      split
      · cases dotResult : symbol .dot .topItem state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .dot .topItem state stateValid
            rw [dotResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot .topItem state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot .topItem dotResult
            simp only
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp only [Reply.ValidFor]
            | reject failure rejected =>
                have valid := deriveComponent_validFor afterDot dotValid.2.1
                rw [componentResult] at valid
                exact valid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid :=
                  deriveComponent_validFor afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases deriveComponent_ok_state_shape componentResult with
                  ⟨componentToken, componentFound, componentSpan,
                    componentTokens, componentCursor⟩
                have componentFoundInState :
                    state.tokens[state.cursor + 1]? = some componentToken := by
                  have atCursor :=
                    State.getElem?_eq_some_of_peek?_eq_some componentFound
                  simpa [dotShape.2] using atCursor
                have firstEndBeforeComponentStart :
                    first.span.endByte ≤ component.span.startByte := by
                  have ordered := stateValid.token_end_le_token_start_of_getElem?_lt
                    firstFound componentFoundInState
                    (Nat.lt_of_lt_of_le firstBeforeCursor
                      (Nat.le_add_right state.cursor 1))
                  simpa [firstSpan, componentSpan] using ordered
                have componentSpanValid :
                    component.span.ValidFor next.file := by
                  have : component.span.ValidFor afterDot.file := by
                    simpa only [Located.ValidFor] using componentValid.1
                  simpa [componentValid.2.2] using this
                apply (inductionHypothesis component (component :: tailRev)
                  next firstIndex firstToken componentValid.2.1
                  (by simpa [componentValid.2.2, dotValid.2.2] using firstValid)
                  componentSpanValid _ _ _ firstSpan _).of_file_eq
                  (componentValid.2.2.trans dotValid.2.2)
                · intro item member
                  rcases List.mem_cons.mp member with rfl | member
                  · exact componentSpanValid
                  · simpa [componentValid.2.2, dotValid.2.2] using
                      tailValid item member
                · exact Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeComponentStart
                      componentSpanValid.2.1)
                · simpa [componentTokens, dotShape.2] using firstFound
                · have dotCursor : afterDot.cursor = state.cursor + 1 := by
                    rw [dotShape.2]
                  rw [componentCursor, dotCursor]
                  exact Nat.lt_trans
                    (Nat.lt_trans firstBeforeCursor (Nat.lt_succ_self _))
                    (Nat.lt_succ_self _)
      · unfold finishDeriveTarget Reply.ValidFor QualifiedName.ValidFor
        refine ⟨⟨SourceSpan.cover_validFor firstValid lastValid
          firstBeforeLast, ?_⟩, stateValid, rfl⟩
        intro component member
        simp only [NonemptyList.toList, List.mem_cons,
          List.mem_reverse] at member
        rcases member with rfl | member
        · exact firstValid
        · exact tailValid component member

/-- Derive-target parsing preserves its covering and component provenance. -/
theorem deriveTarget_validFor :
    deriveTarget.ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold deriveTarget
  cases firstResult : deriveComponent input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := deriveComponent_validFor input inputValid
      rw [firstResult] at valid
      exact valid
  | ok first next =>
      have firstValid := deriveComponent_validFor input inputValid
      rw [firstResult] at firstValid
      rcases deriveComponent_ok_state_shape firstResult with
        ⟨firstToken, firstFound, firstSpan, firstTokens, firstCursor⟩
      have foundNext : next.tokens[input.cursor]? = some firstToken := by
        have atCursor := State.getElem?_eq_some_of_peek?_eq_some firstFound
        simpa [firstTokens] using atCursor
      have spanValid : first.span.ValidFor next.file := by
        have : first.span.ValidFor input.file := by
          simpa only [Located.ValidFor] using firstValid.1
        simpa [firstValid.2.2] using this
      exact (deriveTargetTail_validFor first (next.remainingCount + 1)
        first [] next input.cursor firstToken firstValid.2.1 spanValid
        spanValid (by simp) spanValid.2.1 foundNext firstSpan
        (by rw [firstCursor]; simp)).of_file_eq firstValid.2.2

private theorem deriveTargetTail_ok_state_shape (first : Identifier) :
    ∀ fuel last tailRev input name next,
      deriveTargetTail first fuel last tailRev input = .ok name next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        name.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold deriveTargetTail at result
      split at result
      · cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have recursive := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                have dotShape :=
                  symbol_ok_state_shape .dot .topItem dotResult
                rcases deriveComponent_ok_state_shape componentResult with
                  ⟨_token, _found, _span, componentTokens,
                    componentCursor⟩
                refine ⟨recursive.1.trans
                    (componentTokens.trans (by rw [dotShape.2])), ?_,
                  recursive.2.2⟩
                apply Nat.le_trans _ recursive.2.1
                rw [componentCursor, dotShape.2]
                exact Nat.le_trans (Nat.le_add_right input.cursor 1)
                  (Nat.le_add_right (input.cursor + 1) 1)
      · unfold finishDeriveTarget at result
        cases result
        exact ⟨rfl, Nat.le_refl _, rfl⟩

/--
Successful derive-target parsing begins at the first input token, preserves the
token carrier, and consumes at least that token.
-/
theorem deriveTarget_ok_state_shape {input next : State}
    {name : DeriveTarget} (result : deriveTarget input = .ok name next) :
    ∃ firstToken, input.peek? = some firstToken ∧
      firstToken.span.startByte = name.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold deriveTarget at result
  cases firstResult : deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := deriveTargetTail_ok_state_shape first
        (afterFirst.remainingCount + 1) first [] afterFirst name next result
      rcases deriveComponent_ok_state_shape firstResult with
        ⟨firstToken, found, span, tokens, cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens, ?_⟩
      · exact (congrArg (fun sourceSpan : SourceSpan =>
          sourceSpan.startByte) span).trans tailShape.2.2.symm
      · exact Nat.lt_of_lt_of_le (by rw [cursor]; simp) tailShape.2.1

/-- Derive-target success preserves the immutable token carrier. -/
theorem deriveTarget_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveTarget := by
  intro input name next result
  exact (deriveTarget_ok_state_shape result).choose_spec.2.2.1

private theorem deriveTargetTail_preservesTokenWindow
    (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (deriveTargetTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold deriveTargetTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot .topItem input
        cases dotResult : symbol .dot .topItem input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            have componentShape :=
              deriveComponent_preservesTokenWindow afterDot
            cases componentResult : deriveComponent afterDot with
            | invariant error =>
                simp only [componentResult, Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simpa only [componentResult,
                  Reply.PreservesTokenWindow] using
                    componentShape.trans dotShape
            | ok component next =>
                rw [componentResult] at componentShape
                simpa only [componentResult,
                  Reply.PreservesTokenWindow] using
                    (inductionHypothesis component
                      (component :: tailRev) next).trans
                        (componentShape.trans dotShape)
      · unfold finishDeriveTarget
        exact ⟨rfl, rfl⟩

/-- Derive targets preserve every ordinary token window. -/
theorem deriveTarget_preservesTokenWindow :
    Parser.PreservesTokenWindow deriveTarget := by
  intro input
  unfold deriveTarget
  have firstShape := deriveComponent_preservesTokenWindow input
  cases firstResult : deriveComponent input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first next =>
      rw [firstResult] at firstShape
      exact (deriveTargetTail_preservesTokenWindow first
        (next.remainingCount + 1) first [] next).trans firstShape

/-- Derive-target success never moves the cursor backwards. -/
theorem deriveTarget_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveTarget := by
  intro input name next result
  exact Nat.le_of_lt
    (deriveTarget_ok_state_shape result).choose_spec.2.2.2

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveTargetSoundnessProperties
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
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveTargetOrdinaryRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem reservedDeriveKeyword?_eq_some_of_allowed
    (keyword : HardKeyword)
    (allowed : DeclarativeGrammar.ReservedDeriveTargetKeyword keyword) :
    DeriveTargetInternals.reservedDeriveKeyword? (.keyword keyword) =
      some keyword := by
  cases keyword <;>
    simp [DeclarativeGrammar.ReservedDeriveTargetKeyword,
      DeriveTargetInternals.reservedDeriveKeyword?] at allowed ⊢

private theorem tokenKindAbsentAt_of_peek?_eq_none (kind : TokenKind)
    {input : State} (found : input.peek? = none) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor kind := by
  rintro ⟨span, present⟩
  unfold State.peek? at found
  simp only [present.1, ↓reduceIte, present.2] at found
  contradiction

private theorem identifierAbsentAt_of_peek?_eq_none {input : State}
    (found : input.peek? = none) :
    DeclarativeGrammar.IdentifierAbsentAt input.declarativeRemainder := by
  rintro ⟨span, text, present⟩
  exact tokenKindAbsentAt_of_peek?_eq_none (.identifier text) found
    ⟨span, by simpa only [State.declarativeRemainder] using present⟩

private theorem deriveReservedComponentAbsentAt_of_lookup_none
    {input : State} {token : Token}
    (found : input.peek? = some token)
    (reserved : DeriveTargetInternals.reservedDeriveKeyword? token.value =
      none) :
    DeclarativeGrammar.DeriveReservedComponentAbsentAt
      input.declarativeRemainder := by
  intro keyword allowed
  rintro ⟨span, present⟩
  have current := tokenAt_of_peek?_eq_some found
  have tokenEq : token = { span, value := .keyword keyword } := by
    apply Option.some.inj
    exact current.2.symm.trans (by
      simpa only [State.declarativeRemainder] using present.2)
  subst token
  rw [reservedDeriveKeyword?_eq_some_of_allowed keyword allowed] at reserved
  contradiction

/-- Every executable derive-component rejection records that neither its
reserved-keyword branch nor its checked-identifier branch was available. -/
theorem deriveComponent_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveTargetInternals.deriveComponent input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveComponentRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold DeriveTargetInternals.deriveComponent at result
  cases found : input.peek? with
  | none =>
      simp only [found] at result
      change rejectAt input { head := .identifier, tail := [] } .topItem =
        .reject failure rejected at result
      unfold rejectAt at result
      cases result
      exact .unavailable
        (fun keyword _ => tokenKindAbsentAt_of_peek?_eq_none
          (.keyword keyword) found)
        (.absent (identifierAbsentAt_of_peek?_eq_none found))
  | some token =>
      simp only [found] at result
      cases reserved :
          DeriveTargetInternals.reservedDeriveKeyword? token.value with
      | some keyword => simp [reserved] at result
      | none =>
          simp only [reserved] at result
          have rejectedEq := identifier_reject_state_eq .topItem result
          subst rejected
          exact .unavailable
            (deriveReservedComponentAbsentAt_of_lookup_none found reserved)
            (identifier_reject_sound .topItem result)

namespace DeriveTargetInternals

private theorem deriveTargetTail_reject_ordinaryOutcome_sound_recursive
    (first : Identifier) :
    ∀ fuel last tailRev input failure rejected,
      deriveTargetTail first fuel last tailRev input =
          .reject failure rejected →
        DeclarativeGrammar.DeriveTargetTailRejects
          input.declarativeRemainder rejected.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input failure rejected result
      simp [deriveTargetTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input failure rejected result
      unfold deriveTargetTail at result
      split at result
      · have dotPresent : isSymbol input .dot = true := by assumption
        cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject dotFailure afterDot =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .dot .topItem dotPresent
                with ⟨dot, parsed⟩
            rw [parsed] at dotResult
            contradiction
        | ok dot afterDot =>
            simp only [dotResult] at result
            have dotParsed := symbol_success_exactTokenParses .dot .topItem
              dotResult
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject componentFailure afterComponent =>
                simp only [componentResult] at result
                cases result
                exact .componentRejected dot.span dotParsed
                  (deriveComponent_reject_ordinaryOutcome_sound
                    componentResult)
            | ok component afterComponent =>
                simp only [componentResult] at result
                exact .laterRejected dot.span dotParsed
                  (deriveComponent_success_sound componentResult)
                  (inductionHypothesis component (component :: tailRev)
                    afterComponent failure rejected result)
      · simp [finishDeriveTarget] at result

/-- Rejection under the production fuel follows the exact dotted-tail trace. -/
theorem deriveTargetTail_production_reject_ordinaryOutcome_sound
    (first last : Identifier) (tailRev : List Identifier)
    {input rejected : State} {failure : Failure}
    (result : deriveTargetTail first (input.remainingCount + 1) last tailRev
      input = .reject failure rejected) :
    DeclarativeGrammar.DeriveTargetTailRejects input.declarativeRemainder
      rejected.declarativeRemainder :=
  deriveTargetTail_reject_ordinaryOutcome_sound_recursive first
    (input.remainingCount + 1) last tailRev input failure rejected result

end DeriveTargetInternals

/-- Every executable derive-target rejection is its first unavailable
component or an exact rejection in the maximal dotted tail. -/
theorem deriveTarget_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : deriveTarget input = .reject failure rejected) :
    DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold deriveTarget at result
  cases firstResult : DeriveTargetInternals.deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject firstFailure afterFirst =>
      simp only [firstResult] at result
      cases result
      exact .firstRejected
        (deriveComponent_reject_ordinaryOutcome_sound firstResult)
  | ok first afterFirst =>
      simp only [firstResult] at result
      exact .tailRejected (deriveComponent_success_sound firstResult)
        (DeriveTargetInternals.deriveTargetTail_production_reject_ordinaryOutcome_sound
          first first [] result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveTargetOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for dotted derive targets. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export successful derive-target reflection under the ordinary-outcome
naming convention. -/
theorem deriveTarget_success_ordinaryOutcome_sound {input output : State}
    {target : DeriveTarget}
    (result : deriveTarget input = .ok target output) :
    DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder target
      output.declarativeRemainder :=
  deriveTarget_success_sound result

/-- Package unconditional executable success and exact rejection for one
dotted derive target. -/
theorem deriveTarget_ordinaryOutcome_sound :
    (∀ {input output : State} {target : DeriveTarget},
      deriveTarget input = .ok target output →
        DeclarativeGrammar.DeriveTargetParses input.declarativeRemainder
          target output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      deriveTarget input = .reject failure rejected →
        DeclarativeGrammar.DeriveTargetRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨deriveTarget_success_ordinaryOutcome_sound,
    deriveTarget_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive derive-target outcomes. -/
theorem deriveTarget_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveTargetParses
      DeclarativeGrammar.DeriveTargetRejects :=
  DeclarativeGrammar.deriveTargetDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for derive
targets at the executable reflection boundary. -/
theorem deriveTarget_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveTargetParses
      DeclarativeGrammar.DeriveTargetRejects :=
  DeclarativeGrammar.deriveTargetExactOutcomeSpec

/-- Two successful executable reflections have the same declarative target
and final remainder. -/
theorem deriveTarget_success_result_unique
    {input leftOutput rightOutput : State} {left right : DeriveTarget}
    (leftResult : deriveTarget input = .ok left leftOutput)
    (rightResult : deriveTarget input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveTargetParses.result_unique
    (deriveTarget_success_ordinaryOutcome_sound leftResult)
    (deriveTarget_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact declarative
endpoint. -/
theorem deriveTarget_reject_output_unique
    {input leftOutput rightOutput : State} {leftFailure rightFailure : Failure}
    (leftResult : deriveTarget input = .reject leftFailure leftOutput)
    (rightResult : deriveTarget input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveTargetRejects.output_unique
    (deriveTarget_reject_ordinaryOutcome_sound leftResult)
    (deriveTarget_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeValidOrdinaryRejectionSoundnessProperties
/-!
Exact ordinary-rejection reflection for the proof-visible normal
derive-attribute path.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_reject_tokenKindAbsentAt
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    DeclarativeGrammar.TokenKindAbsentAt input.tokens input.window.endIndex
      input.cursor (.identifier value.spelling) := by
  by_cases present : isContextual input value = true
  · unfold isContextual State.peekKind? at present
    cases found : input.peek? with
    | none => simp [found] at present
    | some token =>
      simp only [found, Option.map_some] at present
      have parsed : contextual value context input =
          .ok token { input with cursor := input.cursor + 1 } := by
        unfold contextual acceptToken
        simp only [found, present, ↓reduceIte]
      rw [parsed] at result
      contradiction
  · exact contextualAbsentAt_of_isContextual_eq_false value
      (Bool.eq_false_iff.mpr present)

private theorem contextual_reject_state_eq
    (value : ContextualKeyword) (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : contextual value context input = .reject failure rejected) :
    rejected = input :=
  acceptToken_reject_state_shape (.contextual value) context
    (·.isContextual value) result

namespace DeriveAttributeInternals

/-- Every normal-path derive-attribute rejection records its exact first
failing token or target-list stage and final rejection remainder. -/
theorem valid_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : valid input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold valid at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [bind, hashResult] at result
  | reject hashFailure hashRejected =>
      have rejectedEq := symbol_reject_state_eq .hash .topItem hashResult
      subst hashRejected
      simp only [bind, hashResult] at result
      cases result
      exact .hashMissing
        (symbol_reject_tokenKindAbsentAt .hash .topItem hashResult)
  | ok hash afterHash =>
      simp only [bind, hashResult] at result
      have hashParsed := symbol_success_exactTokenParses .hash .topItem
        hashResult
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftBracket .topItem
            openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing hash.span hashParsed
            (symbol_reject_tokenKindAbsentAt .leftBracket .topItem
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have openingParsed := symbol_success_exactTokenParses .leftBracket
            .topItem openingResult
          cases markerResult : contextual .derive .topItem afterOpening with
          | invariant error => simp [markerResult] at result
          | reject markerFailure markerRejected =>
              have rejectedEq := contextual_reject_state_eq .derive .topItem
                markerResult
              subst markerRejected
              simp only [markerResult] at result
              cases result
              exact .markerMissing hash.span opening.span hashParsed
                openingParsed
                (contextual_reject_tokenKindAbsentAt .derive .topItem
                  markerResult)
          | ok marker afterMarker =>
              simp only [markerResult] at result
              have markerParsed := contextual_success_exactTokenParses
                .derive .topItem markerResult
              cases targetsResult : delimitedNoTrailing .leftParen
                  .rightParen true deriveTarget .topItem .topLevel
                  afterMarker with
              | invariant error => simp [targetsResult] at result
              | reject targetsFailure targetsRejected =>
                  simp only [targetsResult] at result
                  cases result
                  exact .targetsRejected hash.span opening.span marker.span
                    hashParsed openingParsed markerParsed
                    (delimitedNoTrailing_reject_sound .leftParen .rightParen
                      true deriveTarget DeclarativeGrammar.DeriveTargetParses
                      DeclarativeGrammar.DeriveTargetRejects .topItem
                      .topLevel deriveTarget_success_ordinaryOutcome_sound
                      deriveTarget_reject_ordinaryOutcome_sound targetsResult)
              | ok targets afterTargets =>
                  simp only [targetsResult] at result
                  have targetsParsed :=
                    delimitedNoTrailing_allowEmpty_success_sound .leftParen
                      .rightParen deriveTarget
                      DeclarativeGrammar.DeriveTargetParses .topItem .topLevel
                      deriveTarget_success_ordinaryOutcome_sound
                      deriveTarget_preservesTokenWindow targetsResult
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp [closingResult] at result
                  | reject closingFailure closingRejected =>
                      have rejectedEq := symbol_reject_state_eq .rightBracket
                        .topItem closingResult
                      subst closingRejected
                      simp only [closingResult] at result
                      cases result
                      exact .closingMissing hash.span opening.span marker.span
                        hashParsed openingParsed markerParsed targetsParsed
                        (symbol_reject_tokenKindAbsentAt .rightBracket .topItem
                          closingResult)
                  | ok closing afterClosing =>
                      by_cases empty : targets.elements.isEmpty
                      · simp only [closingResult, empty, if_true,
                          emitDiagnostic, modifyState, pure] at result
                        cases result
                      · simp only [closingResult, empty, Bool.false_eq_true,
                          if_false, pure] at result
                        cases result

end DeriveAttributeInternals
end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveRecoveryDiagnosticProperties
/-! Diagnostics produced by canonical derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful recovered derive tail retains a recovery diagnostic. -/
theorem deriveRecoverTail_success_hasDiagnostic (hash : SourceSpan) :
    ∀ fuel last input value next,
      DeriveAttributeInternals.recoverTail hash last fuel input =
          .ok value next →
        next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value next result
      simp [DeriveAttributeInternals.recoverTail] at result
  | succ fuel inductionHypothesis =>
      intro last input value next result
      unfold DeriveAttributeInternals.recoverTail at result
      split at result
      · cases closingResult : symbol .rightBracket .topItem input with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closing afterClosing =>
            simp only [closingResult] at result
            unfold DeriveAttributeInternals.finishRecovered at result
            cases result
            simp [State.emit]
      · split at result
        · unfold DeriveAttributeInternals.finishRecovered at result
          cases result
          simp [State.emit]
        · cases advanced : input.advance? with
          | some pair =>
              rcases pair with ⟨token, afterToken⟩
              simp only [advanced] at result
              exact inductionHypothesis token.span afterToken value next result
          | none =>
              simp only [advanced] at result
              unfold DeriveAttributeInternals.finishRecovered at result
              cases result
              simp [State.emit]

/-- Every success of the recovered derive-attribute path has a diagnostic. -/
theorem deriveRecovered_success_hasDiagnostic {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold DeriveAttributeInternals.recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [hashResult] at result
  | reject failure rejected => simp [hashResult] at result
  | ok hash afterHash =>
      simp only [hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          exact deriveRecoverTail_success_hasDiagnostic hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening value
            next result

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveDiagnosticReflectionProperties
/-! Backward diagnostic reflection for derive targets and attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace DeriveTargetInternals

/-- A derive component either parses an identifier or adds a retained diagnostic. -/
theorem deriveComponent_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveComponent := by
  intro input name next result diagnosticFree
  unfold deriveComponent at result
  cases found : input.peek? with
  | none => simp [found, rejectAt] at result
  | some token =>
      simp only [found] at result
      cases reserved : reservedDeriveKeyword? token.value with
      | none =>
          simp only [reserved] at result
          exact identifier_reflectsDiagnosticFreeOnSuccess .topItem input name
            next result diagnosticFree
      | some keywordValue =>
          simp only [reserved] at result
          cases result
          simp [State.emit] at diagnosticFree

private theorem finishDeriveTarget_reflectsDiagnosticFreeOnSuccess
    (first last : Identifier) (tailRev : List Identifier) :
    Parser.ReflectsDiagnosticFreeOnSuccess
      (finishDeriveTarget first last tailRev) := by
  intro input target next result diagnosticFree
  unfold finishDeriveTarget at result
  cases result
  exact diagnosticFree

private theorem deriveTargetTail_reflectsDiagnosticFreeOnSuccess
    (first : Identifier) : ∀ fuel last tailRev,
    Parser.ReflectsDiagnosticFreeOnSuccess
      (deriveTargetTail first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input target next result diagnosticFree
      simp [deriveTargetTail] at result
  | succ fuel inductionHypothesis =>
      intro last tailRev input target next result diagnosticFree
      unfold deriveTargetTail at result
      split at result
      · cases dotResult : symbol .dot .topItem input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : deriveComponent afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have afterComponentFree := inductionHypothesis component
                  (component :: tailRev) afterComponent target next result
                    diagnosticFree
                have afterDotFree :=
                  deriveComponent_reflectsDiagnosticFreeOnSuccess afterDot
                    component afterComponent componentResult
                      afterComponentFree
                exact symbol_reflectsDiagnosticFreeOnSuccess .dot .topItem
                  input dot afterDot dotResult afterDotFree
      · exact finishDeriveTarget_reflectsDiagnosticFreeOnSuccess first last
          tailRev input target next result diagnosticFree

end DeriveTargetInternals

/-- Complete dotted derive targets cannot erase incoming diagnostics. -/
theorem deriveTarget_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveTarget := by
  intro input target next result diagnosticFree
  unfold deriveTarget at result
  cases firstResult : DeriveTargetInternals.deriveComponent input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have afterFirstFree :=
        DeriveTargetInternals.deriveTargetTail_reflectsDiagnosticFreeOnSuccess
          first (afterFirst.remainingCount + 1) first [] afterFirst target next
            result diagnosticFree
      exact
        DeriveTargetInternals.deriveComponent_reflectsDiagnosticFreeOnSuccess
          input first afterFirst firstResult afterFirstFree

namespace DeriveAttributeInternals

/-- The normal derive-attribute path cannot erase incoming diagnostics. -/
theorem valid_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess valid := by
  unfold valid
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .hash .topItem)
  intro hash
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .leftBracket .topItem)
  intro opening
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (contextual_reflectsDiagnosticFreeOnSuccess .derive .topItem)
  intro marker
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (delimitedNoTrailing_reflectsDiagnosticFreeOnSuccess
      .leftParen .rightParen true deriveTarget .topItem .topLevel
      deriveTarget_reflectsDiagnosticFreeOnSuccess)
  intro targets
  apply Parser.bind_reflectsDiagnosticFreeOnSuccess
    (symbol_reflectsDiagnosticFreeOnSuccess .rightBracket .topItem)
  intro closing
  split
  · apply Parser.bind_reflectsDiagnosticFreeOnSuccess
      (emitDiagnostic_reflectsDiagnosticFreeOnSuccess _)
    intro emitted
    exact Parser.pure_reflectsDiagnosticFreeOnSuccess _
  · exact Parser.pure_reflectsDiagnosticFreeOnSuccess _

/-- Recovery successes are always diagnosed, so reflection holds vacuously. -/
theorem recovered_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess recovered := by
  intro input value next result diagnosticFree
  exact False.elim (deriveRecovered_success_hasDiagnostic result diagnosticFree)

end DeriveAttributeInternals

/-- Public derive-attribute parsing cannot erase incoming diagnostics. -/
theorem deriveAttribute_reflectsDiagnosticFreeOnSuccess :
    Parser.ReflectsDiagnosticFreeOnSuccess deriveAttribute := by
  unfold deriveAttribute
  exact Parser.orElse_reflectsDiagnosticFreeOnSuccess
    DeriveAttributeInternals.valid_reflectsDiagnosticFreeOnSuccess
    DeriveAttributeInternals.recovered_reflectsDiagnosticFreeOnSuccess

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveValidityProperties
/-! Source-provenance laws for canonical derive-attribute parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem validPath_validFor :
    DeriveAttributeInternals.valid.ValidFor DeriveAttribute.ValidFor := by
  intro input inputValid
  unfold DeriveAttributeInternals.valid
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp only [bind, hashResult, Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at valid
      simp only [bind, hashResult, Reply.ValidFor]
      exact valid
  | ok hash afterHash =>
      have hashValid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashValid
      have hashShape := symbol_ok_state_shape .hash .topItem hashResult
      simp only [bind, hashResult]
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          simp only
          have valid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at valid
          exact valid.of_file_eq hashValid.2.2
      | ok opening afterOpening =>
          simp only
          have openingValid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at openingValid
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error => simp only [Reply.ValidFor]
          | reject failure rejected =>
              simp only
              have valid := contextual_validFor .derive .topItem afterOpening
                openingValid.2.1
              rw [deriveResult] at valid
              exact valid.of_file_eq
                (openingValid.2.2.trans hashValid.2.2)
          | ok deriveKeyword afterDerive =>
              simp only
              have deriveValid := contextual_validFor .derive .topItem
                afterOpening openingValid.2.1
              rw [deriveResult] at deriveValid
              have deriveShape := acceptToken_ok_state_shape
                (.contextual .derive) .topItem (·.isContextual .derive)
                deriveResult
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error => simp only [Reply.ValidFor]
              | reject failure rejected =>
                  simp only
                  have valid := delimitedNoTrailing_validFor
                    QualifiedName.ValidFor .leftParen .rightParen true
                    deriveTarget .topItem .topLevel deriveTarget_validFor
                    deriveTarget_preservesTokensOnSuccess afterDerive
                    deriveValid.2.1
                  rw [targetsResult] at valid
                  exact valid.of_file_eq (deriveValid.2.2.trans
                    (openingValid.2.2.trans hashValid.2.2))
              | ok targets afterTargets =>
                  simp only
                  have targetsValid := delimitedNoTrailing_validFor
                    QualifiedName.ValidFor .leftParen .rightParen true
                    deriveTarget .topItem .topLevel deriveTarget_validFor
                    deriveTarget_preservesTokensOnSuccess afterDerive
                    deriveValid.2.1
                  rw [targetsResult] at targetsValid
                  have targetsTokens :=
                    delimitedNoTrailing_preservesTokensOnSuccess
                      .leftParen .rightParen true deriveTarget .topItem
                      .topLevel deriveTarget_preservesTokensOnSuccess
                      afterDerive targets afterTargets targetsResult
                  have targetsCursor :=
                    delimitedNoTrailing_cursorMonotoneOnSuccess
                      .leftParen .rightParen true deriveTarget .topItem
                      .topLevel afterDerive targets afterTargets targetsResult
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp only [Reply.ValidFor]
                  | reject failure rejected =>
                      simp only
                      have valid := symbol_validFor .rightBracket .topItem
                        afterTargets targetsValid.2.1
                      rw [closingResult] at valid
                      exact valid.of_file_eq (targetsValid.2.2.trans
                        (deriveValid.2.2.trans
                          (openingValid.2.2.trans hashValid.2.2)))
                  | ok closing afterClosing =>
                      simp only
                      have closingValid := symbol_validFor .rightBracket
                        .topItem afterTargets targetsValid.2.1
                      rw [closingResult] at closingValid
                      have closingShape := symbol_ok_state_shape .rightBracket
                        .topItem closingResult
                      have hashFound :=
                        State.getElem?_eq_some_of_peek?_eq_some hashShape.1
                      have closingFound :=
                        State.getElem?_eq_some_of_peek?_eq_some closingShape.1
                      have closingFoundInput :
                          input.tokens[afterTargets.cursor]? = some closing := by
                        simpa [targetsTokens, deriveShape.2, openingShape.2,
                          hashShape.2] using closingFound
                      have hashBeforeClosing :
                          hash.span.endByte ≤ closing.span.startByte := by
                        apply inputValid.token_end_le_token_start_of_getElem?_lt
                          hashFound closingFoundInput
                        have hashProgress : input.cursor < afterHash.cursor := by
                          rw [hashShape.2]
                          simp
                        have openingProgress :
                            afterHash.cursor < afterOpening.cursor := by
                          rw [openingShape.2]
                          simp
                        have deriveProgress :
                            afterOpening.cursor < afterDerive.cursor := by
                          rw [deriveShape.2]
                          simp
                        exact Nat.lt_of_lt_of_le
                          (Nat.lt_trans hashProgress
                            (Nat.lt_trans openingProgress deriveProgress))
                          targetsCursor
                      have hashSpanValid : hash.span.ValidFor input.file := by
                        simpa only [Located.ValidFor] using hashValid.1
                      have closingSpanValid :
                          closing.span.ValidFor input.file := by
                        simpa only [Located.ValidFor, closingValid.2.2,
                          targetsValid.2.2, deriveValid.2.2, openingValid.2.2,
                          hashValid.2.2] using closingValid.1
                      have spanValid := SourceSpan.cover_validFor hashSpanValid
                        closingSpanValid (Nat.le_trans hashSpanValid.2.1
                          (Nat.le_trans hashBeforeClosing
                            closingSpanValid.2.1))
                      have valueValid : DeriveAttribute.ValidFor input.file {
                          span := SourceSpan.cover hash.span closing.span
                          value := { targets }
                        } := ⟨spanValid, by
                          simpa [targetsValid.2.2, deriveValid.2.2,
                            openingValid.2.2, hashValid.2.2]
                            using targetsValid.1⟩
                      have spanValidAfter :
                          (SourceSpan.cover hash.span closing.span).ValidFor
                            afterClosing.file := by
                        simpa [closingValid.2.2, targetsValid.2.2,
                          deriveValid.2.2, openingValid.2.2, hashValid.2.2]
                          using spanValid
                      split
                      · exact ⟨valueValid,
                          closingValid.2.1.emit_validFor _ spanValidAfter,
                          closingValid.2.2.trans (targetsValid.2.2.trans
                            (deriveValid.2.2.trans
                              (openingValid.2.2.trans hashValid.2.2)))⟩
                      · exact ⟨valueValid, closingValid.2.1,
                          closingValid.2.2.trans (targetsValid.2.2.trans
                            (deriveValid.2.2.trans
                              (openingValid.2.2.trans hashValid.2.2)))⟩

private theorem finishRecovered_validFor (hash last : SourceSpan)
    (constraint : ParseConstraint) (state : State)
    (stateValid : state.ValidFor) (hashValid : hash.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : hash.startByte ≤ last.endByte) :
    (DeriveAttributeInternals.finishRecovered hash last constraint state).ValidFor
      state DeriveAttribute.ValidFor := by
  have spanValid := SourceSpan.cover_validFor hashValid lastValid ordered
  unfold DeriveAttributeInternals.finishRecovered Reply.ValidFor
    DeriveAttribute.ValidFor
  exact ⟨⟨spanValid, spanValid, by simp⟩,
    stateValid.emit_validFor _ spanValid, rfl⟩

private theorem recoverTail_validFor (hash : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → hash.ValidFor state.file → last.ValidFor state.file →
      hash.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (DeriveAttributeInternals.recoverTail hash last fuel state).ValidFor state
        DeriveAttribute.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid hashValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold DeriveAttributeInternals.recoverTail
      split
      · cases closingResult : symbol .rightBracket .topItem state with
        | invariant error => simp only [Reply.ValidFor]
        | reject failure rejected =>
            have valid := symbol_validFor .rightBracket .topItem state stateValid
            rw [closingResult] at valid
            simpa only [Reply.ValidFor] using valid
        | ok closing next =>
            have closingValid := symbol_validFor .rightBracket .topItem state
              stateValid
            rw [closingResult] at closingValid
            have closingShape := symbol_ok_state_shape .rightBracket .topItem
              closingResult
            have closingFound := State.getElem?_eq_some_of_peek?_eq_some
              closingShape.1
            have lastBeforeClosing :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                closingFound lastBefore
            have closingSpanValid : closing.span.ValidFor state.file := by
              simpa only [Located.ValidFor] using closingValid.1
            have coverOrdered : hash.startByte ≤ closing.span.endByte :=
              Nat.le_trans ordered (Nat.le_trans (by simpa [lastSpan] using
                lastBeforeClosing) closingSpanValid.2.1)
            exact (finishRecovered_validFor hash closing.span
              .malformedDeriveAttribute next closingValid.2.1
              (by simpa [closingValid.2.2] using hashValid)
              (by simpa [closingValid.2.2] using closingSpanValid)
              coverOrdered).of_file_eq closingValid.2.2
      · split
        · exact finishRecovered_validFor hash last .unclosedDeriveAttribute
            state stateValid hashValid lastValid ordered
        · cases advanced : state.advance? with
          | some pair =>
              rcases pair with ⟨token, next⟩
              have nextValid := stateValid.advance?_validFor advanced
              unfold State.advance? at advanced
              cases found : state.peek? with
              | none => simp [found] at advanced
              | some current =>
                  simp only [found, Option.map_some] at advanced
                  cases advanced
                  have tokenValid := stateValid.peek?_span_validFor found
                  have currentFound :=
                    State.getElem?_eq_some_of_peek?_eq_some found
                  have lastBeforeCurrent :=
                    stateValid.token_end_le_token_start_of_getElem?_lt
                      lastFound currentFound lastBefore
                  apply inductionHypothesis token.span
                    { state with cursor := state.cursor + 1 } state.cursor token
                    nextValid (by simpa using hashValid) (by simpa using tokenValid)
                  · exact Nat.le_trans ordered (Nat.le_trans
                      (by simpa [lastSpan] using lastBeforeCurrent)
                      tokenValid.2.1)
                  · exact currentFound
                  · rfl
                  · simp
          | none =>
              exact finishRecovered_validFor hash last .unclosedDeriveAttribute
                state stateValid hashValid lastValid ordered

private theorem recoveredPath_validFor :
    DeriveAttributeInternals.recovered.ValidFor DeriveAttribute.ValidFor := by
  intro input inputValid
  unfold DeriveAttributeInternals.recovered
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp only [Reply.ValidFor]
  | reject failure rejected =>
      have valid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at valid
      simpa only [Reply.ValidFor] using valid
  | ok hash afterHash =>
      have hashValid := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashValid
      have hashShape := symbol_ok_state_shape .hash .topItem hashResult
      simp only
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp only [Reply.ValidFor]
      | reject failure rejected =>
          have valid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at valid
          exact valid.of_file_eq hashValid.2.2
      | ok opening afterOpening =>
          have openingValid := symbol_validFor .leftBracket .topItem afterHash
            hashValid.2.1
          rw [openingResult] at openingValid
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          have hashFound := State.getElem?_eq_some_of_peek?_eq_some hashShape.1
          have openingFound := State.getElem?_eq_some_of_peek?_eq_some
            openingShape.1
          have hashBeforeOpening :=
            inputValid.token_end_le_token_start_of_getElem?_lt hashFound
              (by simpa [hashShape.2] using openingFound) (by simp)
          have hashSpanValid : hash.span.ValidFor afterOpening.file := by
            simpa only [Located.ValidFor, openingValid.2.2, hashValid.2.2]
              using hashValid.1
          have openingSpanValid : opening.span.ValidFor afterOpening.file := by
            simpa only [Located.ValidFor, openingValid.2.2] using openingValid.1
          exact (recoverTail_validFor hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening
            afterHash.cursor opening openingValid.2.1 hashSpanValid
            openingSpanValid (Nat.le_trans hashSpanValid.2.1
              (Nat.le_trans hashBeforeOpening openingSpanValid.2.1))
            (by simpa [openingShape.2] using openingFound) rfl (by
              rw [openingShape.2]
              simp)).of_file_eq (openingValid.2.2.trans hashValid.2.2)

/-- Derive attributes preserve every retained source range. -/
theorem deriveAttribute_validFor :
    deriveAttribute.ValidFor DeriveAttribute.ValidFor :=
  Parser.orElse_validFor validPath_validFor recoveredPath_validFor

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeSoundnessProperties
/-! Success soundness of normal and public derive-attribute parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem deriveBind_success_components {α β : Type}
    {first : Parser α} {nextParser : α → Parser β}
    {input final : State} {value : β}
    (result : (first >>= nextParser) input = .ok value final) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        nextParser firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => nextParser firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every success of the normal derive path follows its exact token grammar. -/
theorem deriveAttributeValid_success_sound {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold DeriveAttributeInternals.valid at result
  rcases deriveBind_success_components result with
    ⟨hash, afterHash, hashResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨opening, afterOpening, openingResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨deriveMarker, afterDerive, deriveResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨targets, afterTargets, targetsResult, rest⟩
  rcases deriveBind_success_components rest with
    ⟨closing, afterClosing, closingResult, rest⟩
  have finalShape :
      next.declarativeRemainder = afterClosing.declarativeRemainder ∧
        value = {
          span := SourceSpan.cover hash.span closing.span
          value := { targets }
        } := by
    by_cases empty : targets.elements.isEmpty
    · simp only [empty, if_true, emitDiagnostic, modifyState, bind, pure] at rest
      cases rest
      exact ⟨rfl, rfl⟩
    · simp only [empty, pure] at rest
      cases rest
      exact ⟨rfl, rfl⟩
  have hashSound := symbol_ok_tokenAt .hash .topItem hashResult
  have openingSound := symbol_ok_tokenAt .leftBracket .topItem openingResult
  have deriveSound := contextual_ok_tokenAt .derive .topItem deriveResult
  have targetsSound := delimitedNoTrailing_allowEmpty_success_sound
    .leftParen .rightParen deriveTarget
    DeclarativeGrammar.DeriveTargetParses .topItem .topLevel
    deriveTarget_success_sound deriveTarget_preservesTokenWindow targetsResult
  have closingSound := symbol_ok_tokenAt .rightBracket .topItem closingResult
  have openingToken :
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        (input.cursor + 1) {
          span := opening.span
          value := .symbol .leftBracket
        } := by
    simpa only [hashSound.2, State.tokens, State.window, State.cursor] using
      openingSound.1
  have deriveToken :
      DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
        (input.cursor + 2) {
          span := deriveMarker.span
          value := .identifier ContextualKeyword.derive.spelling
        } := by
    simpa only [openingSound.2, hashSound.2, State.tokens, State.window,
      State.cursor, Nat.add_assoc] using deriveSound.1
  have targetsGrammar :
      DeclarativeGrammar.NoTrailingDelimitedListParses .leftParen .rightParen
        DeclarativeGrammar.DeriveTargetParses {
          input.declarativeRemainder with cursor := input.cursor + 3
        } targets afterTargets.declarativeRemainder := by
    simpa only [deriveSound.2, openingSound.2, hashSound.2,
      State.declarativeRemainder, State.tokens, State.window, State.cursor,
      Nat.add_assoc] using targetsSound
  have outputEq : next.declarativeRemainder = {
      afterTargets.declarativeRemainder with
        cursor := afterTargets.cursor + 1
    } := by
    rw [finalShape.1, closingSound.2]
    rfl
  unfold DeclarativeGrammar.DeriveAttributeParses
  exact ⟨hash.span, opening.span, deriveMarker.span, targets,
    afterTargets.declarativeRemainder, closing.span, hashSound.1, openingToken,
    deriveToken, targetsGrammar, closingSound.1, outputEq, finalShape.2⟩

/-- Diagnostic-free public derive success cannot come from recovery. -/
theorem deriveAttribute_success_sound {input next : State}
    {value : DeriveAttribute} (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | ok parsed afterValid =>
      simp only [validResult] at result
      cases result
      exact deriveAttributeValid_success_sound validResult
  | reject failure rejected =>
      simp only [validResult] at result
      exact False.elim
        ((deriveRecovered_success_hasDiagnostic result) diagnosticFree)
  | invariant error => simp [validResult] at result

/-- Public derive grammar soundness composes with source validity. -/
theorem deriveAttribute_success_sound_and_validFor {input next : State}
    {value : DeriveAttribute} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : deriveAttribute input = .ok value next) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
        next.declarativeRemainder ∧
      value.ValidFor input.file := by
  refine ⟨deriveAttribute_success_sound diagnosticFree result, ?_⟩
  have valid := deriveAttribute_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeValidOrdinaryOutcomeSoundnessProperties
/-! Complete broad executable outcomes for the normal derive-attribute path. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Re-export normal-path success reflection under the ordinary-outcome naming
convention. -/
theorem deriveAttributeValid_success_ordinaryOutcome_sound
    {input output : State} {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value output) :
    DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder value
      output.declarativeRemainder :=
  deriveAttributeValid_success_sound result

/-- Re-export exact normal-path rejection reflection outside the internal
namespace. -/
theorem deriveAttributeValid_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : DeriveAttributeInternals.valid input =
      .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeValidRejects
      input.declarativeRemainder rejected.declarativeRemainder :=
  DeriveAttributeInternals.valid_reject_ordinaryOutcome_sound result

/-- Package unconditional success and exact rejection reflection for the
normal derive-attribute path. -/
theorem deriveAttributeValid_ordinaryOutcome_sound :
    (∀ {input output : State} {value : DeriveAttribute},
      DeriveAttributeInternals.valid input = .ok value output →
        DeclarativeGrammar.DeriveAttributeParses input.declarativeRemainder
          value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      DeriveAttributeInternals.valid input = .reject failure rejected →
        DeclarativeGrammar.DeriveAttributeValidRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨deriveAttributeValid_success_ordinaryOutcome_sound,
    deriveAttributeValid_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic and exclusive normal derive-attribute outcomes. -/
theorem deriveAttributeValid_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeParses
      DeclarativeGrammar.DeriveAttributeValidRejects :=
  DeclarativeGrammar.deriveAttributeValidDeterministicOutcomeSpec

/-- Re-export exact normal-path value and rejection-endpoint functionality. -/
theorem deriveAttributeValid_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.DeriveAttributeParses
      DeclarativeGrammar.DeriveAttributeValidRejects :=
  DeclarativeGrammar.deriveAttributeValidExactOutcomeSpec

/-- Two successful normal-path reflections have the same derive attribute and
final declarative remainder. -/
theorem deriveAttributeValid_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : DeriveAttribute}
    (leftResult : DeriveAttributeInternals.valid input =
      .ok left leftOutput)
    (rightResult : DeriveAttributeInternals.valid input =
      .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeParses.result_unique
    (deriveAttributeValid_success_ordinaryOutcome_sound leftResult)
    (deriveAttributeValid_success_ordinaryOutcome_sound rightResult)

/-- Two rejected normal-path reflections have the same exact declarative
endpoint. -/
theorem deriveAttributeValid_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : DeriveAttributeInternals.valid input =
      .reject leftFailure leftOutput)
    (rightResult : DeriveAttributeInternals.valid input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.DeriveAttributeValidRejects.output_unique
    (deriveAttributeValid_reject_ordinaryOutcome_sound leftResult)
    (deriveAttributeValid_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveCarrierProperties
/-! Token-carrier and cursor laws for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem emitDiagnostic_preservesTokenWindowForDerive
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

private theorem deriveAdvance_state_shape {input next : State}
    {token : Token} (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

private theorem validPath_preservesTokenWindow :
    Parser.PreservesTokenWindow DeriveAttributeInternals.valid := by
  unfold DeriveAttributeInternals.valid
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .hash .topItem)
  intro hash
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .leftBracket .topItem)
  intro opening
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .derive .topItem)
  intro deriveKeyword
  apply Parser.bind_preservesTokenWindow
    (delimitedWithPolicy_preservesTokenWindow .leftParen .rightParen true
      false deriveTarget .topItem .topLevel deriveTarget_preservesTokenWindow)
  intro targets
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .rightBracket .topItem)
  intro closing
  split
  · apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForDerive _)
    intro emitted
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow _

private theorem finishRecovered_preservesTokenWindow
    (hash last : SourceSpan) (constraint : ParseConstraint) :
    Parser.PreservesTokenWindow
      (DeriveAttributeInternals.finishRecovered hash last constraint) := by
  intro input
  unfold DeriveAttributeInternals.finishRecovered Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

private theorem recoverTail_preservesTokenWindow (hash : SourceSpan) :
    ∀ fuel last,
      Parser.PreservesTokenWindow
        (DeriveAttributeInternals.recoverTail hash last fuel) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input
      trivial
  | succ fuel inductionHypothesis =>
      intro last input
      unfold DeriveAttributeInternals.recoverTail
      split
      · have closingShape :=
          symbol_preservesTokenWindow .rightBracket .topItem input
        cases closingResult : symbol .rightBracket .topItem input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [closingResult] at closingShape
            exact closingShape
        | ok closing afterClosing =>
            rw [closingResult] at closingShape
            exact (finishRecovered_preservesTokenWindow hash closing.span
              .malformedDeriveAttribute afterClosing).trans closingShape
      · split
        · exact finishRecovered_preservesTokenWindow hash last
            .unclosedDeriveAttribute input
        · cases advanced : input.advance? with
          | some pair =>
              rcases pair with ⟨token, next⟩
              exact (inductionHypothesis token.span next).trans (by
                simp [(deriveAdvance_state_shape advanced).2])
          | none =>
              exact finishRecovered_preservesTokenWindow hash last
                .unclosedDeriveAttribute input

private theorem recoveredPath_preservesTokenWindow :
    Parser.PreservesTokenWindow DeriveAttributeInternals.recovered := by
  intro input
  unfold DeriveAttributeInternals.recovered
  have hashShape := symbol_preservesTokenWindow .hash .topItem input
  cases hashResult : symbol .hash .topItem input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [hashResult] at hashShape
      exact hashShape
  | ok hash afterHash =>
      rw [hashResult] at hashShape
      simp only
      have openingShape :=
        symbol_preservesTokenWindow .leftBracket .topItem afterHash
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error =>
          simp only [Reply.PreservesTokenWindow]
      | reject failure rejected =>
          simp only
          rw [openingResult] at openingShape
          exact openingShape.trans hashShape
      | ok opening afterOpening =>
          simp only
          rw [openingResult] at openingShape
          exact (recoverTail_preservesTokenWindow hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening).trans
              (openingShape.trans hashShape)

/-- Derive attributes preserve every ordinary token window. -/
theorem deriveAttribute_preservesTokenWindow :
    Parser.PreservesTokenWindow deriveAttribute :=
  Parser.orElse_preservesTokenWindow validPath_preservesTokenWindow
    recoveredPath_preservesTokenWindow

private theorem validPath_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.valid input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold DeriveAttributeInternals.valid at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      simp only [bind, hashResult] at result
      contradiction
  | reject failure rejected =>
      simp only [bind, hashResult] at result
      contradiction
  | ok hash afterHash =>
      simp only [bind, hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error => simp [deriveResult] at result
          | reject failure rejected => simp [deriveResult] at result
          | ok deriveKeyword afterDerive =>
              simp only [deriveResult] at result
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error => simp [targetsResult] at result
              | reject failure rejected => simp [targetsResult] at result
              | ok targets afterTargets =>
                  simp only [targetsResult] at result
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error => simp [closingResult] at result
                  | reject failure rejected => simp [closingResult] at result
                  | ok closing afterClosing =>
                      simp only [closingResult] at result
                      have hashShape := symbol_ok_state_shape .hash .topItem
                        hashResult
                      have openingShape := symbol_ok_state_shape .leftBracket
                        .topItem openingResult
                      have deriveShape := acceptToken_ok_state_shape
                        (.contextual .derive) .topItem
                        (·.isContextual .derive) deriveResult
                      have targetsTokens :=
                        delimitedNoTrailing_preservesTokensOnSuccess
                          .leftParen .rightParen true deriveTarget .topItem
                          .topLevel deriveTarget_preservesTokensOnSuccess
                          afterDerive targets afterTargets targetsResult
                      have targetsCursor :=
                        delimitedNoTrailing_cursorMonotoneOnSuccess
                          .leftParen .rightParen true deriveTarget .topItem
                          .topLevel afterDerive targets afterTargets
                          targetsResult
                      have closingShape := symbol_ok_state_shape .rightBracket
                        .topItem closingResult
                      split at result
                      · simp only [emitDiagnostic, modifyState] at result
                        cases result
                        refine ⟨hash, hashShape.1, rfl, ?_, ?_⟩
                        · simp [State.emit, closingShape.2, targetsTokens,
                            deriveShape.2, openingShape.2, hashShape.2]
                        · simp [State.emit, closingShape.2, deriveShape.2,
                            openingShape.2, hashShape.2] at targetsCursor ⊢
                          omega
                      · cases result
                        refine ⟨hash, hashShape.1, rfl, ?_, ?_⟩
                        · simpa [closingShape.2, deriveShape.2, openingShape.2,
                            hashShape.2] using targetsTokens
                        · simp [closingShape.2, deriveShape.2, openingShape.2,
                            hashShape.2] at targetsCursor ⊢
                          omega

private theorem recoverTail_ok_state_shape (hash : SourceSpan) :
    ∀ fuel last input value next,
      DeriveAttributeInternals.recoverTail hash last fuel input =
        .ok value next →
      next.tokens = input.tokens ∧ input.cursor ≤ next.cursor ∧
        value.span.startByte = hash.startByte := by
  intro fuel
  induction fuel with
  | zero => intros; contradiction
  | succ fuel inductionHypothesis =>
      intro last input value next result
      unfold DeriveAttributeInternals.recoverTail at result
      split at result
      · cases closingResult : symbol .rightBracket .topItem input with
        | invariant error => simp [closingResult] at result
        | reject failure rejected => simp [closingResult] at result
        | ok closing afterClosing =>
            simp only [closingResult] at result
            unfold DeriveAttributeInternals.finishRecovered at result
            cases result
            rw [(symbol_ok_state_shape .rightBracket .topItem closingResult).2]
            exact ⟨rfl, Nat.le_add_right _ 1, rfl⟩
      · split at result
        · unfold DeriveAttributeInternals.finishRecovered at result
          cases result
          exact ⟨rfl, Nat.le_refl _, rfl⟩
        · cases advanced : input.advance? with
          | some pair =>
              rcases pair with ⟨token, afterToken⟩
              simp only [advanced] at result
              have recursive := inductionHypothesis token.span afterToken
                value next result
              unfold State.advance? at advanced
              cases found : input.peek? with
              | none => simp [found] at advanced
              | some current =>
                  simp only [found, Option.map_some] at advanced
                  cases advanced
                  exact ⟨recursive.1, Nat.le_trans
                    (Nat.le_add_right input.cursor 1) recursive.2.1,
                    recursive.2.2⟩
          | none =>
              simp only [advanced] at result
              unfold DeriveAttributeInternals.finishRecovered at result
              cases result
              exact ⟨rfl, Nat.le_refl _, rfl⟩

private theorem recoveredPath_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : DeriveAttributeInternals.recovered input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold DeriveAttributeInternals.recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error => simp [hashResult] at result
  | reject failure rejected => simp [hashResult] at result
  | ok hash afterHash =>
      simp only [hashResult] at result
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error => simp [openingResult] at result
      | reject failure rejected => simp [openingResult] at result
      | ok opening afterOpening =>
          simp only [openingResult] at result
          have tailShape := recoverTail_ok_state_shape hash.span
            (afterOpening.remainingCount + 1) opening.span afterOpening
            value next result
          have hashShape := symbol_ok_state_shape .hash .topItem hashResult
          have openingShape := symbol_ok_state_shape .leftBracket .topItem
            openingResult
          refine ⟨hash, hashShape.1, tailShape.2.2.symm, ?_, ?_⟩
          · simpa [openingShape.2, hashShape.2] using tailShape.1
          · exact Nat.lt_of_lt_of_le (by
              simp [openingShape.2, hashShape.2]
              omega) tailShape.2.1

private theorem deriveAttribute_ok_state_shape {input next : State}
    {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    ∃ hash, input.peek? = some hash ∧
      hash.span.startByte = value.span.startByte ∧
      next.tokens = input.tokens ∧ input.cursor < next.cursor := by
  unfold deriveAttribute orElse at result
  cases validResult : DeriveAttributeInternals.valid input with
  | ok value afterValid =>
      simp only [validResult] at result
      cases result
      exact validPath_ok_state_shape validResult
  | reject failure rejected =>
      simp only [validResult] at result
      exact recoveredPath_ok_state_shape result
  | invariant error => simp [validResult] at result

/-- Derive-attribute success preserves the immutable token carrier. -/
theorem deriveAttribute_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess deriveAttribute := by
  intro input value next result
  exact (deriveAttribute_ok_state_shape result).choose_spec.2.2.1

/-- A derive attribute starts at its retained hash token. -/
theorem deriveAttribute_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess deriveAttribute (·.span) := by
  intro input value next result
  rcases deriveAttribute_ok_state_shape result with
    ⟨hash, found, start, _tokens, _cursor⟩
  exact ⟨hash, found, start⟩

/-- Every successful derive attribute consumes at least its `#[` prefix. -/
theorem deriveAttribute_cursor_lt_onSuccess {input next : State}
    {value : DeriveAttribute}
    (result : deriveAttribute input = .ok value next) :
    input.cursor < next.cursor :=
  (deriveAttribute_ok_state_shape result).choose_spec.2.2.2

/-- Derive-attribute success never moves the token cursor backwards. -/
theorem deriveAttribute_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveAttribute := by
  intro input value next result
  exact Nat.le_of_lt (deriveAttribute_cursor_lt_onSuccess result)

end Solcore.Syntax.Parser
end

section
-- leanmerge: from Solcore.Syntax.Parser.DeriveAttributeRecoveredOrdinaryRejectionSoundnessProperties
/-! Exact ordinary-rejection reflection for derive-attribute recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- The malformed-tail scan can succeed or expose an invariant, but cannot
return an ordinary rejection at any fuel. -/
private theorem recoverTail_ne_reject_recursive
    (hash : SourceSpan) :
    ∀ fuel last input failure rejected,
      recoverTail hash last fuel input ≠ .reject failure rejected := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input failure rejected
      simp [recoverTail]
  | succ fuel inductionHypothesis =>
      intro last input failure rejected
      unfold recoverTail
      split
      · have closingPresent : isSymbol input .rightBracket = true := by
          assumption
        cases closingResult : symbol .rightBracket .topItem input with
        | ok closing next =>
            simp [finishRecovered]
        | reject closingFailure closingRejected =>
            rcases symbol_eq_ok_of_isSymbol_eq_true .rightBracket .topItem
                closingPresent with ⟨closing, parsed⟩
            rw [parsed] at closingResult
            contradiction
        | invariant error =>
            simp
      · split
        · simp [finishRecovered]
        · cases advanced : input.advance? with
          | none => simp [finishRecovered]
          | some pair =>
              rcases pair with ⟨token, next⟩
              exact inductionHypothesis token.span next failure rejected

/-- Every recovery-path rejection is an exact missing hash or missing opening
bracket; the production malformed-tail scan contributes no rejection. -/
theorem recovered_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : recovered input = .reject failure rejected) :
    DeclarativeGrammar.DeriveAttributeRecoveredRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recovered at result
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      simp [hashResult] at result
  | reject hashFailure hashRejected =>
      have rejectedEq := symbol_reject_state_eq .hash .topItem hashResult
      subst hashRejected
      simp only [hashResult] at result
      cases result
      exact .hashMissing
        (symbol_reject_tokenKindAbsentAt .hash .topItem hashResult)
  | ok hash afterHash =>
      simp only [hashResult] at result
      have hashParsed := symbol_success_exactTokenParses .hash .topItem
        hashResult
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error =>
          simp [openingResult] at result
      | reject openingFailure openingRejected =>
          have rejectedEq := symbol_reject_state_eq .leftBracket .topItem
            openingResult
          subst openingRejected
          simp only [openingResult] at result
          cases result
          exact .openingMissing hash.span hashParsed
            (symbol_reject_tokenKindAbsentAt .leftBracket .topItem
              openingResult)
      | ok opening afterOpening =>
          simp only [openingResult] at result
          exact False.elim
            (recoverTail_ne_reject_recursive hash.span
              (afterOpening.remainingCount + 1) opening.span afterOpening
              failure rejected result)

end Solcore.Syntax.Parser.DeriveAttributeInternals
end
