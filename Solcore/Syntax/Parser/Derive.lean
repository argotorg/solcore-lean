import Solcore.Syntax.Parser.Delimited
import Solcore.Syntax.Parser.Name
import Solcore.Syntax.Parser.TopLevel

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private def reservedDeriveKeyword? : TokenKind → Option HardKeyword
  | .keyword value => match value with
    | .importKw | .exportKw | .pragmaKw | .typeKw | .dataKw |
        .classKw | .instanceKw | .contractKw | .publicKw | .payableKw |
        .functionKw | .constructorKw | .fallbackKw | .forallKw |
        .defaultKw => some value
    | _ => none
  | _ => none

private def deriveComponent : Parser Identifier := fun state =>
  match state.peek? with
  | some token => match reservedDeriveKeyword? token.value with
    | some keywordValue =>
        let name : Identifier := {
          span := token.span
          value := keywordValue.spelling
        }
        .ok name (({ state with cursor := state.cursor + 1 }).emit {
          span := token.span
          kind := .constraintViolation (.reservedDeriveTarget keywordValue)
        })
    | none => identifier .topItem state
  | none => rejectAt state { head := .identifier, tail := [] } .topItem

private def finishDeriveTarget (first last : Identifier)
    (tailRev : List Identifier) (state : State) : Reply DeriveTarget :=
  .ok {
    span := SourceSpan.cover first.span last.span
    value := { components := { head := first, tail := tailRev.reverse } }
  } state

private def deriveTargetTail (first : Identifier) :
    Nat → Identifier → List Identifier → State → Reply DeriveTarget
  | 0, _, _, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, last, tailRev, state =>
      if isSymbol state .dot then
        match symbol .dot .topItem state with
        | .ok _ afterDot =>
            match deriveComponent afterDot with
            | .ok component next =>
                deriveTargetTail first fuel component
                  (component :: tailRev) next
            | .reject failure next => .reject failure next
            | .invariant error => .invariant error
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else
        finishDeriveTarget first last tailRev state

/-- Parse one dotted trait path inside `derive`. -/
def deriveTarget : Parser DeriveTarget := fun state =>
  match deriveComponent state with
  | .ok first next =>
      deriveTargetTail first (next.remainingCount + 1) first [] next
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

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

/-- Derive-target success never moves the cursor backwards. -/
theorem deriveTarget_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess deriveTarget := by
  intro input name next result
  exact Nat.le_of_lt
    (deriveTarget_ok_state_shape result).choose_spec.2.2.2

private def validDeriveAttribute : Parser DeriveAttribute := do
  let hash ← symbol .hash .topItem
  let _ ← symbol .leftBracket .topItem
  let _ ← contextual .derive .topItem
  let targets ← delimitedNoTrailing .leftParen .rightParen true
    deriveTarget .topItem .topLevel
  let closing ← symbol .rightBracket .topItem
  let span := SourceSpan.cover hash.span closing.span
  if targets.elements.isEmpty then
    let _ ← emitDiagnostic {
      span
      kind := .constraintViolation .deriveRequiresTarget
    }
  else
    pure ()
  pure { span, value := { targets } }

private def startsDeriveContractField (state : State) : Bool :=
  isIdentifier state && state.peekOffsetKind? 1 == some (.symbol .colon)

private def atDeriveDeclarationBoundary (state : State) : Bool :=
  atTopItemStart state || startsDeriveContractField state ||
    isSymbol state .rightBrace

private def finishRecoveredDerive (hash last : SourceSpan)
    (constraint : ParseConstraint) (state : State) : Reply DeriveAttribute :=
  let span := SourceSpan.cover hash last
  .ok {
    span
    value := { targets := { span, elements := [] } }
  } (state.emit { span, kind := .constraintViolation constraint })

private def recoverDeriveTail (hash last : SourceSpan) :
    Nat → State → Reply DeriveAttribute
  | 0, state => .invariant (.fuelExhausted .topLevel state.currentSpan)
  | fuel + 1, state =>
      if isSymbol state .rightBracket then
        match symbol .rightBracket .topItem state with
        | .ok closing next =>
            finishRecoveredDerive hash closing.span
              .malformedDeriveAttribute next
        | .reject failure next => .reject failure next
        | .invariant error => .invariant error
      else if state.atEnd || atDeriveDeclarationBoundary state then
        finishRecoveredDerive hash last .unclosedDeriveAttribute state
      else
        match state.advance? with
        | some (token, next) =>
            recoverDeriveTail hash token.span fuel next
        | none => finishRecoveredDerive hash last .unclosedDeriveAttribute state

private def recoveredDeriveAttribute : Parser DeriveAttribute := fun state =>
  match symbol .hash .topItem state with
  | .ok hash afterHash =>
      match symbol .leftBracket .topItem afterHash with
      | .ok opening next =>
          recoverDeriveTail hash.span opening.span
            (next.remainingCount + 1) next
      | .reject failure next => .reject failure next
      | .invariant error => .invariant error
  | .reject failure next => .reject failure next
  | .invariant error => .invariant error

/--
Parse one canonical derive attribute. Once `#[` has been consumed, malformed
and unclosed forms become empty recovered attributes without consuming the next
declaration boundary.
-/
def deriveAttribute : Parser DeriveAttribute :=
  orElse validDeriveAttribute recoveredDeriveAttribute

end Solcore.Syntax.Parser
