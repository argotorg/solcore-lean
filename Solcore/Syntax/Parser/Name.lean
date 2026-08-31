import Solcore.Syntax.NameValidity
import Solcore.Syntax.Parser.PrimitiveCarrierProperties
import Solcore.Syntax.Parser.StateCursorProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/- Proof-visible qualified-name parser components. -/
namespace QualifiedNameInternals

/-- Finish a qualified name from its first, last, and reversed tail parts. -/
def finishQualifiedName (first last : Identifier)
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

/-- Fuel-bounded dotted tail used by the public qualified-name parser. -/
def qualifiedNameTail (context : ParseContext)
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

end QualifiedNameInternals

open QualifiedNameInternals

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

private theorem qualifiedNameTail_ok_state_shape
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      qualifiedNameTail context phase first fuel last tailRev input =
        .ok name next →
      next.tokens = input.tokens ∧
        name.span.startByte = first.span.startByte := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have recursiveShape := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                have dotShape :=
                  symbol_ok_state_shape .dot context dotResult
                rcases identifier_ok_state_shape context componentResult with
                  ⟨_token, _found, _span, componentTokens, _cursor⟩
                have dotTokens : afterDot.tokens = input.tokens := by
                  rw [dotShape.2]
                exact ⟨recursiveShape.1.trans
                    (componentTokens.trans dotTokens), recursiveShape.2⟩
      · unfold finishQualifiedName at result
        cases result
        exact ⟨rfl, rfl⟩

/--
A successful qualified name starts at its first input token and leaves the
immutable token carrier unchanged.
-/
theorem qualifiedName_ok_state_shape (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    ∃ firstToken,
      input.peek? = some firstToken ∧
        firstToken.span.startByte = name.span.startByte ∧
        next.tokens = input.tokens := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have tailShape := qualifiedNameTail_ok_state_shape context phase first
        (afterFirst.remainingCount + 1) first [] afterFirst name next result
      rcases identifier_ok_state_shape context firstResult with
        ⟨firstToken, found, span, tokens, _cursor⟩
      refine ⟨firstToken, found, ?_, tailShape.1.trans tokens⟩
      rw [span]
      exact tailShape.2.symm

/-- Qualified-name success preserves the immutable token carrier. -/
theorem qualifiedName_preservesTokensOnSuccess (context : ParseContext)
    (phase : ParserPhase) :
    Parser.PreservesTokensOnSuccess (qualifiedName context phase) := by
  intro input name next result
  exact (qualifiedName_ok_state_shape context phase result).choose_spec.2.2

private theorem qualifiedNameTail_preservesTokenWindow
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev,
      Parser.PreservesTokenWindow
        (qualifiedNameTail context phase first fuel last tailRev) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input
      trivial
  | succ fuel inductionHypothesis =>
      intro last tailRev input
      unfold qualifiedNameTail
      split
      · have dotShape := symbol_preservesTokenWindow .dot context input
        cases dotResult : symbol .dot context input with
        | invariant error => trivial
        | reject failure rejected =>
            rw [dotResult] at dotShape
            exact dotShape
        | ok dot afterDot =>
            rw [dotResult] at dotShape
            have componentShape := identifier_preservesTokenWindow context afterDot
            cases componentResult : identifier context afterDot with
            | invariant error =>
                simp only [componentResult, Reply.PreservesTokenWindow]
            | reject failure rejected =>
                rw [componentResult] at componentShape
                simp only [componentResult]
                exact componentShape.trans dotShape
            | ok component afterComponent =>
                rw [componentResult] at componentShape
                simp only [componentResult]
                exact (inductionHypothesis component (component :: tailRev)
                  afterComponent).trans (componentShape.trans dotShape)
      · exact ⟨rfl, rfl⟩

/-- Qualified names preserve tokens and the active window on every reply. -/
theorem qualifiedName_preservesTokenWindow (context : ParseContext)
    (phase : ParserPhase) :
    Parser.PreservesTokenWindow (qualifiedName context phase) := by
  intro input
  unfold qualifiedName
  have firstShape := identifier_preservesTokenWindow context input
  cases firstResult : identifier context input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [firstResult] at firstShape
      exact firstShape
  | ok first afterFirst =>
      rw [firstResult] at firstShape
      exact (qualifiedNameTail_preservesTokenWindow context phase first
        (afterFirst.remainingCount + 1) first [] afterFirst).trans firstShape

/-- A qualified name starts at the first identifier token it retains. -/
theorem qualifiedName_startsAtCurrentTokenOnSuccess
    (context : ParseContext) (phase : ParserPhase) :
    Parser.StartsAtCurrentTokenOnSuccess
      (qualifiedName context phase) (·.span) := by
  intro input name next result
  rcases qualifiedName_ok_state_shape context phase result with
    ⟨firstToken, found, start, _tokens⟩
  exact ⟨firstToken, found, start⟩

private theorem qualifiedNameTail_cursorMonotoneOnSuccess
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev input name next,
      qualifiedNameTail context phase first fuel last tailRev input =
        .ok name next →
      input.cursor ≤ next.cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev input name next result
      contradiction
  | succ fuel inductionHypothesis =>
      intro last tailRev input name next result
      unfold qualifiedNameTail at result
      split at result
      · cases dotResult : symbol .dot context input with
        | invariant error => simp [dotResult] at result
        | reject failure rejected => simp [dotResult] at result
        | ok dot afterDot =>
            simp only [dotResult] at result
            cases componentResult : identifier context afterDot with
            | invariant error => simp [componentResult] at result
            | reject failure rejected => simp [componentResult] at result
            | ok component afterComponent =>
                simp only [componentResult] at result
                have dotMonotone := symbol_cursorMonotoneOnSuccess
                  .dot context input dot afterDot dotResult
                have componentMonotone :=
                  identifier_cursorMonotoneOnSuccess context afterDot
                    component afterComponent componentResult
                have recursiveMonotone := inductionHypothesis component
                  (component :: tailRev) afterComponent name next result
                exact Nat.le_trans dotMonotone
                  (Nat.le_trans componentMonotone recursiveMonotone)
      · unfold finishQualifiedName at result
        cases result
        exact Nat.le_refl _

/-- Every successful qualified name consumes its first identifier. -/
theorem qualifiedName_cursor_lt_onSuccess (context : ParseContext)
    (phase : ParserPhase) {input next : State} {name : QualifiedName}
    (result : qualifiedName context phase input = .ok name next) :
    input.cursor < next.cursor := by
  unfold qualifiedName at result
  cases firstResult : identifier context input with
  | invariant error => simp [firstResult] at result
  | reject failure rejected => simp [firstResult] at result
  | ok first afterFirst =>
      simp only [firstResult] at result
      have firstProgress : input.cursor < afterFirst.cursor := by
        rw [(identifier_ok_state_shape context firstResult).choose_spec.2.2.2]
        simp
      have tailMonotone := qualifiedNameTail_cursorMonotoneOnSuccess
        context phase first (afterFirst.remainingCount + 1) first []
          afterFirst name next result
      exact Nat.lt_of_lt_of_le firstProgress tailMonotone

/-- Successful qualified-name parsing never rewinds the cursor. -/
theorem qualifiedName_cursorMonotoneOnSuccess (context : ParseContext)
    (phase : ParserPhase) :
    Parser.CursorMonotoneOnSuccess (qualifiedName context phase) := by
  intro input name next result
  exact Nat.le_of_lt (qualifiedName_cursor_lt_onSuccess context phase result)

end Solcore.Syntax.Parser
