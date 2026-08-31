import Solcore.Syntax.Parser.Validity
import Solcore.Syntax.Parser.StateCursorProperties

set_option autoImplicit false

namespace Solcore.Syntax

namespace QualifiedName

/-- Every source range stored by a qualified name belongs to one input file. -/
def ValidFor (file : SourceFile) (name : QualifiedName) : Prop :=
  name.span.ValidFor file ∧
    ∀ component ∈ name.value.components.toList,
      component.span.ValidFor file

end QualifiedName

end Solcore.Syntax

namespace Solcore.Syntax.Parser

private def finishQualifiedName (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply QualifiedName :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := {
      components := {
        head := first
        tail := tailRev.reverse
      }
    }
  } state

private def qualifiedNameTail (context : ParseContext)
    (phase : ParserPhase) (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply QualifiedName
  | 0, _, _, state => .invariant (.fuelExhausted phase state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot context state with
        | .ok _ afterDot =>
            match identifier context afterDot with
            | .ok component next =>
                qualifiedNameTail context phase first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishQualifiedName first last tailRev state

/-- Parse one nonempty dotted ordinary-identifier path. -/
def qualifiedName (context : ParseContext)
    (phase : ParserPhase) : Parser QualifiedName := fun state =>
  match identifier context state with
  | .ok first next =>
      qualifiedNameTail context phase first (next.remainingCount + 1)
        first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

private theorem qualifiedNameTail_validFor
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev state firstIndex firstToken,
      state.ValidFor →
      first.span.ValidFor state.file →
      last.span.ValidFor state.file →
      (∀ component ∈ tailRev, component.span.ValidFor state.file) →
      first.span.startByte ≤ last.span.endByte →
      state.tokens[firstIndex]? = some firstToken →
      firstToken.span = first.span →
      firstIndex < state.cursor →
      (qualifiedNameTail context phase first fuel last tailRev state).ValidFor
        state QualifiedName.ValidFor := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev state firstIndex firstToken stateValid firstValid
        lastValid tailValid firstBeforeLast firstFound firstSpan
        firstBeforeCursor
      unfold qualifiedNameTail
      split
      · cases dotResult : symbol .dot context state with
        | invariant error =>
            simp only [Reply.ValidFor]
        | reject failure rejected =>
            have dotValid := symbol_validFor .dot context state stateValid
            rw [dotResult] at dotValid
            simpa only [Reply.ValidFor] using dotValid
        | ok dot afterDot =>
            have dotValid := symbol_validFor .dot context state stateValid
            rw [dotResult] at dotValid
            have dotShape := symbol_ok_state_shape .dot context dotResult
            simp only
            cases componentResult : identifier context afterDot with
            | invariant error =>
                simp only [Reply.ValidFor]
            | reject failure rejected =>
                have componentValid :=
                  identifier_validFor context afterDot dotValid.2.1
                rw [componentResult] at componentValid
                simpa only [Reply.ValidFor] using
                  componentValid.of_file_eq dotValid.2.2
            | ok component next =>
                have componentValid :=
                  identifier_validFor context afterDot dotValid.2.1
                rw [componentResult] at componentValid
                rcases identifier_ok_state_shape context componentResult with
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
                    first.span.startByte ≤ component.span.endByte :=
                  Nat.le_trans firstValid.2.1
                    (Nat.le_trans firstEndBeforeComponentStart
                      (by
                        have spanValid :
                            component.span.ValidFor afterDot.file := by
                          simpa only [Located.ValidFor] using componentValid.1
                        exact spanValid.2.1))
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
                have recursiveValid :=
                  inductionHypothesis component (component :: tailRev) next
                    firstIndex firstToken componentValid.2.1 firstValidNext
                    componentValidNext tailValidNext firstBeforeComponent
                    firstFoundNext firstSpan firstBeforeNextCursor
                simpa only using recursiveValid.of_file_eq
                  (componentValid.2.2.trans dotValid.2.2)
      · unfold finishQualifiedName Reply.ValidFor QualifiedName.ValidFor
        refine ⟨⟨?_, ?_⟩, stateValid, rfl⟩
        · exact SourceSpan.cover_validFor firstValid lastValid firstBeforeLast
        · intro component member
          simp only [NonemptyList.toList, List.mem_cons,
            List.mem_reverse] at member
          rcases member with rfl | member
          · exact firstValid
          · exact tailValid component member

/-- Qualified-name parsing preserves every component and covering source span. -/
theorem qualifiedName_validFor (context : ParseContext) (phase : ParserPhase) :
    (qualifiedName context phase).ValidFor QualifiedName.ValidFor := by
  intro input inputValid
  unfold qualifiedName
  cases firstResult : identifier context input with
  | invariant error =>
      simp only [Reply.ValidFor]
  | reject failure rejected =>
      have firstValid := identifier_validFor context input inputValid
      rw [firstResult] at firstValid
      simpa only [Reply.ValidFor] using firstValid
  | ok first next =>
      have firstValid := identifier_validFor context input inputValid
      rw [firstResult] at firstValid
      rcases identifier_ok_state_shape context firstResult with
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
      have tailValid := qualifiedNameTail_validFor context phase first
        (next.remainingCount + 1) first [] next input.cursor firstToken
        firstValid.2.1 firstValidNext firstValidNext
        (by simp) firstValidNext.2.1 firstFoundNext firstSpan
        (by rw [firstCursor]; simp)
      simpa only using tailValid.of_file_eq firstValid.2.2

end Solcore.Syntax.Parser
