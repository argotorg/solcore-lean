import Solcore.Syntax.Parser.Type
import Solcore.Syntax.Parser.DelimitedAllowEmptySoundnessProperties
import Solcore.Syntax.DeclarativeTypeAliasParametersExactnessProperties
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.DelimitedListRejectionSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.TypeDeclarationValidity
import Solcore.Syntax.Parser.TypeExprSoundnessProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties
import Solcore.Syntax.DeclarativeTypeAliasValueRecoveryExactnessProperties
import Solcore.Syntax.DeclarativeTypeAliasValueExactnessProperties
import Solcore.Syntax.Parser.CoreTypeOutcomeSoundnessProperties
import Solcore.Syntax.Parser.YulKeywordRejectionSoundnessProperties
import Solcore.Syntax.DeclarativeTypeAliasDeclarationExactnessProperties

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

def finishRecoveredType (span : SourceSpan)
    (state : State) : Reply TypeExpr :=
  .ok { span, value := .error } (state.emit {
    span
    kind := .recovered .typeAliasValue
  })

def recoverTypeAliasValueAux (first last : SourceSpan) :
    Nat → State → Reply TypeExpr
  | 0, state => .invariant (.fuelExhausted .typeAlias state.currentSpan)
  | fuel + 1, state =>
      if state.atEnd || isSymbol state .semicolon then
        finishRecoveredType (SourceSpan.cover first last) state
      else
        match state.advance? with
        | some (token, next) =>
            recoverTypeAliasValueAux first token.span fuel next
        | none => finishRecoveredType (SourceSpan.cover first last) state

/-- Consume the nonempty malformed RHS prefix before the first semicolon. -/
def recoverTypeAliasValue (state : State) : Reply TypeExpr :=
  if state.atEnd || isSymbol state .semicolon then
    rejectAt state { head := .typeExpr, tail := [] } .typeAlias
  else
    match state.advance? with
    | some (token, next) =>
        recoverTypeAliasValueAux token.span token.span
          (next.remainingCount + 1) next
    | none => rejectAt state { head := .typeExpr, tail := [] } .typeAlias

def parseAliasValue : Parser TypeExpr := fun state =>
  match typeExpr state with
  | .ok value next => .ok value next
  | .reject failure failedState =>
      let rewound := {
        failedState with
        cursor := state.cursor
      }
      if rewound.atEnd || isSymbol rewound .semicolon then
        .reject failure rewound
      else
        recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)
  | .invariant error => .invariant error

end TypeAliasInternals

/-- Parse the optional parenthesized parameter list of a type alias. -/
def parseTypeAliasParameters : Parser (Option (DelimitedList Identifier)) := do
  let state ← getState
  if isSymbol state .leftParen then
    let values ← delimited .leftParen .rightParen true
      (identifier .parameter) .typeAlias .typeAlias
    pure (some values)
  else
    pure none

/-- Parse one canonical transparent type-alias declaration. -/
def typeAlias : Parser TypeAliasDecl := do
  let typeKeyword ← keyword .typeKw .typeAlias
  let name ← identifier .typeAlias
  let parameters ← parseTypeAliasParameters
  let _ ← symbol .equal .typeAlias
  let value ← TypeAliasInternals.parseAliasValue
  let semicolon ← symbol .semicolon .typeAlias
  pure {
    span := SourceSpan.cover typeKeyword.span semicolon.span
    value := {
      name
      parameters
      value
    }
  }

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasParameterSoundnessProperties`
-/

/-! Success soundness for optional transparent type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parameters follow their prioritized parenthesized grammar. -/
theorem parseTypeAliasParameters_success_sound
    {input next : State}
    {parameters : Option (DelimitedList Identifier)}
    (result : parseTypeAliasParameters input = .ok parameters next) :
    DeclarativeGrammar.OptionalTypeAliasParametersParses
      input.declarativeRemainder parameters next.declarativeRemainder := by
  unfold parseTypeAliasParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · simp only [present, if_true] at result
    cases valuesResult : delimited .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias input with
    | invariant error =>
        simp [valuesResult] at result
    | reject failure rejected =>
        simp [valuesResult] at result
    | ok values afterValues =>
        have valuesGrammar := delimited_allowEmpty_trailing_success_sound
          .leftParen .rightParen (identifier .parameter)
          DeclarativeGrammar.IdentifierParses .typeAlias .typeAlias
          (identifier_success_sound .parameter)
          (identifier_preservesTokenWindow .parameter) valuesResult
        simp only [valuesResult, pure] at result
        cases result
        exact .present valuesGrammar
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp only [absent, Bool.false_eq_true, if_false, pure] at result
    cases result
    exact .absent (symbolAbsentAt_of_isSymbol_eq_false .leftParen absent)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasParametersOrdinaryOutcomeSoundnessProperties`
-/

/-! Exact executable outcomes for optional type-alias parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every successful optional alias-parameter attempt follows its exact
prioritized ordinary grammar. -/
theorem parseTypeAliasParameters_success_ordinaryOutcome_sound
    {input output : State}
    {parameters : Option (DelimitedList Identifier)}
    (result : parseTypeAliasParameters input = .ok parameters output) :
    DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      input.declarativeRemainder parameters output.declarativeRemainder :=
  parseTypeAliasParameters_success_sound result

/-- A rejected optional alias-parameter attempt has a present opening
parenthesis and the exact nested allow-empty, allow-trailing rejection. -/
theorem parseTypeAliasParameters_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : parseTypeAliasParameters input = .reject failure rejected) :
    DeclarativeGrammar.OptionalTypeAliasParametersRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold parseTypeAliasParameters getState at result
  simp only [bind] at result
  by_cases present : isSymbol input .leftParen
  · rcases symbol_eq_ok_of_isSymbol_eq_true .leftParen .typeAlias present with
      ⟨opening, openingResult⟩
    simp only [present, if_true] at result
    cases parametersResult : delimited .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias input with
    | invariant error => simp [parametersResult] at result
    | ok parameters output => simp [parametersResult, pure] at result
    | reject parametersFailure parametersRejected =>
        simp only [parametersResult] at result
        cases result
        exact .present
          ⟨opening.span,
            (symbol_ok_tokenAt .leftParen .typeAlias openingResult).1⟩
          (delimited_reject_sound .leftParen .rightParen true
            (identifier .parameter) DeclarativeGrammar.IdentifierParses
            DeclarativeGrammar.IdentifierRejects .typeAlias .typeAlias
            (identifier_success_sound .parameter)
            (identifier_reject_sound .parameter) parametersResult)
  · have absent : isSymbol input .leftParen = false :=
      Bool.eq_false_iff.mpr present
    simp [absent, pure] at result

/-- Package optional alias-parameter success and exact rejection. -/
theorem parseTypeAliasParameters_ordinaryOutcome_sound :
    (∀ {input output : State}
      {parameters : Option (DelimitedList Identifier)},
      parseTypeAliasParameters input = .ok parameters output →
        DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
          input.declarativeRemainder parameters
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseTypeAliasParameters input = .reject failure rejected →
        DeclarativeGrammar.OptionalTypeAliasParametersRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨parseTypeAliasParameters_success_ordinaryOutcome_sound,
    parseTypeAliasParameters_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic optional alias-parameter outcomes. -/
theorem parseTypeAliasParameters_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      DeclarativeGrammar.OptionalTypeAliasParametersRejects :=
  DeclarativeGrammar.optionalTypeAliasParametersDeterministicOutcomeSpec

/-- Re-export full value and rejection-endpoint functionality for optional
type-alias parameters at the executable reflection boundary. -/
theorem parseTypeAliasParameters_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses
      DeclarativeGrammar.OptionalTypeAliasParametersRejects :=
  DeclarativeGrammar.optionalTypeAliasParametersExactOutcomeSpec

/-- Two successful executable reflections have the same optional parameters
and final declarative remainder. -/
theorem parseTypeAliasParameters_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : Option (DelimitedList Identifier)}
    (leftResult : parseTypeAliasParameters input = .ok left leftOutput)
    (rightResult : parseTypeAliasParameters input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalTypeAliasParametersOrdinaryParses.result_unique
    (parseTypeAliasParameters_success_ordinaryOutcome_sound leftResult)
    (parseTypeAliasParameters_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same exact declarative
endpoint. -/
theorem parseTypeAliasParameters_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : parseTypeAliasParameters input =
      .reject leftFailure leftOutput)
    (rightResult : parseTypeAliasParameters input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.OptionalTypeAliasParametersRejects.output_unique
    (parseTypeAliasParameters_reject_ordinaryOutcome_sound leftResult)
    (parseTypeAliasParameters_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasProperties`
-/

/-! Recovery and declaration contracts for transparent type aliases. -/
set_option autoImplicit false
namespace Solcore.Syntax.Parser
namespace TypeAliasInternals

private theorem typeAlias_advance_state_shape {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩
/-- Finishing alias recovery retains one source-valid error range. -/
theorem finishRecoveredType_validFor (span : SourceSpan) (state : State)
    (stateValid : state.ValidFor) (spanValid : span.ValidFor state.file) :
    (finishRecoveredType span state).ValidFor state TypeExpr.ValidFor := by
  unfold finishRecoveredType Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩
/-- Alias recovery preserves provenance while consuming malformed tokens. -/
theorem recoverTypeAliasValueAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverTypeAliasValueAux first last fuel state).ValidFor state
        TypeExpr.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverTypeAliasValueAux
      split
      · exact finishRecoveredType_validFor _ _ stateValid
          (SourceSpan.cover_validFor firstValid lastValid ordered)
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredType_validFor _ _ stateValid
              (SourceSpan.cover_validFor firstValid lastValid ordered)
        | some pair =>
            rcases pair with ⟨token, next⟩
            have nextValid := stateValid.advance?_validFor advanced
            have shape := typeAlias_advance_state_shape advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt
                lastFound currentFound lastBefore
            have recursive := inductionHypothesis token.span next state.cursor
              token nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl (by
                simp [shape.2])
            exact recursive.of_file_eq (by simp [shape.2])
/-- The complete recovering RHS parser preserves recursive type provenance. -/
theorem recoverTypeAliasValue_validFor (state : State)
    (stateValid : state.ValidFor) :
    (recoverTypeAliasValue state).ValidFor state TypeExpr.ValidFor := by
  unfold recoverTypeAliasValue
  split
  · unfold rejectAt Reply.ValidFor
    exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
  · cases advanced : state.advance? with
    | none =>
        unfold rejectAt Reply.ValidFor
        exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
    | some pair =>
        rcases pair with ⟨token, next⟩
        have shape := typeAlias_advance_state_shape advanced
        have nextValid := stateValid.advance?_validFor advanced
        have tokenValid := stateValid.peek?_span_validFor shape.1
        have tokenFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
        exact (recoverTypeAliasValueAux_validFor token.span
          (next.remainingCount + 1) token.span next state.cursor token
          nextValid (by simpa [shape.2] using tokenValid)
          (by simpa [shape.2] using tokenValid) tokenValid.2.1
          (by simpa [shape.2] using tokenFound) rfl (by
            simp [shape.2])).of_file_eq (by simp [shape.2])
/-- Parsing or recovering an alias RHS retains source-valid type syntax. -/
theorem parseAliasValue_validFor :
    parseAliasValue.ValidFor TypeExpr.ValidFor := by
  intro input inputValid
  unfold parseAliasValue
  cases coreResult : typeExpr input with
  | ok value next =>
      have valid := typeExpr_validFor input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid := typeExpr_validFor input inputValid
      rw [coreResult] at coreValid
      have coreShape := typeExpr_preservesTokenWindow input
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundValid : rewound.ValidFor := {
        tokens := coreValid.2.1.tokens
        cursor_le_endIndex := by
          simpa [rewound, coreShape.2] using inputValid.cursor_le_endIndex
        endIndex_le_size := coreValid.2.1.endIndex_le_size
        endByte_le_source := coreValid.2.1.endByte_le_source
        endByte_boundary := coreValid.2.1.endByte_boundary
        diagnosticsRev := coreValid.2.1.diagnosticsRev
      }
      have rewoundFile : rewound.file = input.file := by
        simpa [rewound] using coreValid.2.2
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue (rewound.emit failure.toDiagnostic)).ValidFor
          input TypeExpr.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have failureValid : failure.span.ValidFor rewound.file := by
          simpa [rewound, coreValid.2.2] using coreValid.1
        have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (recoverTypeAliasValue_validFor
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)
/-- Recovery preserves the complete immutable token window. -/
theorem recoverTypeAliasValueAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow
      (recoverTypeAliasValueAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverTypeAliasValueAux
      split
      · unfold finishRecoveredType Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredType Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            exact (inductionHypothesis token.span next).trans (by
              simp [(typeAlias_advance_state_shape advanced).2])
/-- The recovering RHS entry point preserves every ordinary token window. -/
theorem recoverTypeAliasValue_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverTypeAliasValue := by
  intro input
  unfold recoverTypeAliasValue
  split
  · exact rejectAt_preservesTokenWindow input _ _
  · cases advanced : input.advance? with
    | none => exact rejectAt_preservesTokenWindow input _ _
    | some pair =>
        rcases pair with ⟨token, next⟩
        exact (recoverTypeAliasValueAux_preservesTokenWindow token.span
          token.span (next.remainingCount + 1) next).trans (by
            simp [(typeAlias_advance_state_shape advanced).2])
/-- Alias RHS parsing and recovery preserve every ordinary token window. -/
theorem parseAliasValue_preservesTokenWindow :
    Parser.PreservesTokenWindow parseAliasValue := by
  intro input
  unfold parseAliasValue
  have coreShape := typeExpr_preservesTokenWindow input
  cases coreResult : typeExpr input with
  | ok value next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := by
        exact ⟨by simp [rewound, coreShape.1],
          by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (recoverTypeAliasValue_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

/-- Successful alias RHS parsing retains the immutable token carrier. -/
theorem parseAliasValue_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess parseAliasValue :=
  parseAliasValue_preservesTokenWindow.preservesTokensOnSuccess

/-- Recovery never rewinds the cursor on success. -/
theorem recoverTypeAliasValueAux_cursorMonotoneOnSuccess
    (first last : SourceSpan) (fuel : Nat) :
    Parser.CursorMonotoneOnSuccess
      (recoverTypeAliasValueAux first last fuel) := by
  intro input value next result
  induction fuel generalizing last input with
  | zero => contradiction
  | succ fuel inductionHypothesis =>
      unfold recoverTypeAliasValueAux at result
      split at result
      · unfold finishRecoveredType at result
        cases result
        exact Nat.le_refl _
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredType at result
            cases result
            exact Nat.le_refl _
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at result
            have advanceCursor : input.cursor ≤ afterToken.cursor := by
              rw [(typeAlias_advance_state_shape advanced).2]
              exact Nat.le_add_right _ 1
            exact Nat.le_trans advanceCursor
              (inductionHypothesis token.span afterToken result)

/-- The recovering RHS entry point is cursor-monotone on success. -/
theorem recoverTypeAliasValue_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess recoverTypeAliasValue := by
  intro input value next result
  unfold recoverTypeAliasValue at result
  split at result
  · unfold rejectAt at result; contradiction
  · cases advanced : input.advance? with
    | none => simp [advanced, rejectAt] at result
    | some pair =>
        rcases pair with ⟨token, afterToken⟩
        simp only [advanced] at result
        exact Nat.le_trans (by
          rw [(typeAlias_advance_state_shape advanced).2]
          exact Nat.le_add_right _ 1)
          (recoverTypeAliasValueAux_cursorMonotoneOnSuccess token.span
            token.span (afterToken.remainingCount + 1)
            afterToken value next result)

/-- Alias RHS parsing and recovery never rewind the parser cursor. -/
theorem parseAliasValue_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess parseAliasValue := by
  intro input value next result
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok parsed afterCore =>
      simp only [coreResult] at result
      have monotone := typeExpr_cursorMonotoneOnSuccess
        input parsed afterCore coreResult
      cases result
      exact monotone
  | invariant error => simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := { failedState with cursor := input.cursor }
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          Reply.reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · simpa [rewound, State.emit] using
          (recoverTypeAliasValue_cursorMonotoneOnSuccess
            (rewound.emit failure.toDiagnostic) value next result)

end TypeAliasInternals

private theorem typeAliasBind_ok_components {α β : Type}
    {first : Parser α} {next : α → Parser β} {input final : State}
    {value : β} (parsed : (first >>= next) input = .ok value final) :
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

private theorem getState_preservesTokenWindowForTypeAlias :
    Parser.PreservesTokenWindow getState := by
  exact fun _ => ⟨rfl, rfl⟩

/-- Optional alias parameters preserve delimiter and identifier provenance. -/
theorem parseTypeAliasParameters_validFor :
    parseTypeAliasParameters.ValidFor
      (Option.ValidFor (DelimitedList.ValidFor Located.ValidFor)) := by
  unfold parseTypeAliasParameters
  apply Parser.bind_validFor getState_validFor
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_validFor_of_value
      (delimited_validFor Located.ValidFor .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias
        (identifier_validFor .parameter)
        (identifier_preservesTokensOnSuccess .parameter))
    intro values input inputValid valuesValid
    exact ⟨by simpa only [Option.ValidFor] using valuesValid,
      inputValid, rfl⟩
  · simp only [present]
    exact Parser.pure_validFor none _ (fun _ => trivial)

/-- Optional alias parameters preserve every ordinary token window. -/
theorem parseTypeAliasParameters_preservesTokenWindow :
    Parser.PreservesTokenWindow parseTypeAliasParameters := by
  unfold parseTypeAliasParameters
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForTypeAlias
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_preservesTokenWindow
      (delimited_preservesTokenWindow .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias
        (identifier_preservesTokenWindow .parameter))
    intro values
    exact Parser.pure_preservesTokenWindow _
  · simp only [present]
    exact Parser.pure_preservesTokenWindow none

/-- Successful alias-parameter parsing retains the token carrier. -/
theorem parseTypeAliasParameters_preservesTokensOnSuccess : Parser.PreservesTokensOnSuccess parseTypeAliasParameters :=
  parseTypeAliasParameters_preservesTokenWindow.preservesTokensOnSuccess

/-- Optional alias parameters never rewind the parser cursor. -/
theorem parseTypeAliasParameters_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess parseTypeAliasParameters := by
  unfold parseTypeAliasParameters
  apply Parser.bind_cursorMonotoneOnSuccess getState_cursorMonotoneOnSuccess
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_cursorMonotoneOnSuccess
      (delimited_cursorMonotoneOnSuccess .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias)
    intro values
    exact Parser.pure_cursorMonotoneOnSuccess _
  · simp only [present]
    exact Parser.pure_cursorMonotoneOnSuccess none

/-- A complete type alias retains every declaration and type source range. -/
theorem typeAlias_validFor : typeAlias.ValidFor TypeAliasDecl.ValidFor := by
  have weak : typeAlias.ValidFor (fun _ _ => True) := by
    unfold typeAlias
    apply Parser.bind_validFor (keyword_validFor .typeKw .typeAlias)
    intro typeKeyword
    apply Parser.bind_validFor (identifier_validFor .typeAlias)
    intro name
    apply Parser.bind_validFor parseTypeAliasParameters_validFor
    intro parameters
    apply Parser.bind_validFor (symbol_validFor .equal .typeAlias)
    intro equal
    apply Parser.bind_validFor TypeAliasInternals.parseAliasValue_validFor
    intro value
    apply Parser.bind_validFor (symbol_validFor .semicolon .typeAlias)
    intro semicolon
    exact Parser.pure_validFor _ (fun _ _ => True) (fun _ => trivial)
  intro input inputValid
  have weakResult := weak input inputValid
  cases parsed : typeAlias input with
  | invariant error => trivial
  | reject failure rejected =>
      rw [parsed] at weakResult
      exact weakResult
  | ok declaration final =>
      rw [parsed] at weakResult
      have stages := parsed
      unfold typeAlias at stages
      rcases typeAliasBind_ok_components stages with
        ⟨typeKeyword, afterKeyword, keywordResult, rest⟩
      rcases typeAliasBind_ok_components rest with
        ⟨name, afterName, nameResult, rest⟩
      rcases typeAliasBind_ok_components rest with
        ⟨parameters, afterParameters, parametersResult, rest⟩
      rcases typeAliasBind_ok_components rest with
        ⟨equal, afterEqual, equalResult, rest⟩
      rcases typeAliasBind_ok_components rest with
        ⟨value, afterValue, valueResult, rest⟩
      rcases typeAliasBind_ok_components rest with
        ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
      have keywordValid := keyword_validFor .typeKw .typeAlias input inputValid
      rw [keywordResult] at keywordValid
      have nameValid := identifier_validFor .typeAlias afterKeyword
        keywordValid.2.1
      rw [nameResult] at nameValid
      have parametersValid := parseTypeAliasParameters_validFor afterName
        nameValid.2.1
      rw [parametersResult] at parametersValid
      have equalValid := symbol_validFor .equal .typeAlias afterParameters
        parametersValid.2.1
      rw [equalResult] at equalValid
      have valueValid := TypeAliasInternals.parseAliasValue_validFor afterEqual
        equalValid.2.1
      rw [valueResult] at valueValid
      have semicolonValid := symbol_validFor .semicolon .typeAlias afterValue
        valueValid.2.1
      rw [semicolonResult] at semicolonValid
      have keywordSpanValid : typeKeyword.span.ValidFor input.file := by
        simpa only [Located.ValidFor] using keywordValid.1
      have nameValidInput : name.span.ValidFor input.file := by
        simpa only [Located.ValidFor, keywordValid.2.2] using nameValid.1
      have parametersValidInput : Option.ValidFor
          (DelimitedList.ValidFor Located.ValidFor) input.file parameters := by
        simpa [nameValid.2.2, keywordValid.2.2] using parametersValid.1
      have valueValidInput : TypeExpr.ValidFor input.file value := by
        simpa [equalValid.2.2, parametersValid.2.2, nameValid.2.2,
          keywordValid.2.2] using valueValid.1
      have semicolonSpanValid : semicolon.span.ValidFor input.file := by
        simpa only [Located.ValidFor, valueValid.2.2, equalValid.2.2,
          parametersValid.2.2,
          nameValid.2.2, keywordValid.2.2] using semicolonValid.1
      have keywordShape := acceptToken_ok_state_shape (.keyword .typeKw)
        .typeAlias (· == .keyword .typeKw) keywordResult
      have keywordAt := State.getElem?_eq_some_of_peek?_eq_some keywordShape.1
      have semicolonShape := symbol_ok_state_shape .semicolon .typeAlias
        semicolonResult
      have semicolonAt : input.tokens[afterValue.cursor]? = some semicolon := by
        have found := State.getElem?_eq_some_of_peek?_eq_some semicolonShape.1
        simpa [TypeAliasInternals.parseAliasValue_preservesTokensOnSuccess
            afterEqual value afterValue valueResult,
          symbol_preservesTokensOnSuccess .equal .typeAlias afterParameters
            equal afterEqual equalResult,
          parseTypeAliasParameters_preservesTokensOnSuccess afterName parameters
            afterParameters parametersResult,
          identifier_preservesTokensOnSuccess .typeAlias afterKeyword name
            afterName nameResult,
          keyword_preservesTokensOnSuccess .typeKw .typeAlias input typeKeyword
            afterKeyword keywordResult] using found
      have cursorOrder : input.cursor < afterValue.cursor := by
        apply Nat.lt_of_lt_of_le (acceptToken_cursor_lt_onSuccess
          (.keyword .typeKw) .typeAlias (· == .keyword .typeKw) keywordResult)
        exact Nat.le_trans (identifier_cursorMonotoneOnSuccess .typeAlias
          afterKeyword name afterName nameResult) (Nat.le_trans
            (parseTypeAliasParameters_cursorMonotoneOnSuccess afterName
              parameters afterParameters parametersResult) (Nat.le_trans
                (symbol_cursorMonotoneOnSuccess .equal .typeAlias
                  afterParameters equal afterEqual equalResult)
                (TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
                  afterEqual value afterValue valueResult)))
      have keywordBeforeSemicolon :=
        inputValid.token_end_le_token_start_of_getElem?_lt
          keywordAt semicolonAt cursorOrder
      have outerValid : SourceSpan.ValidFor
          (SourceSpan.cover typeKeyword.span semicolon.span) input.file :=
        SourceSpan.cover_validFor keywordSpanValid semicolonSpanValid
          (Nat.le_trans keywordSpanValid.2.1
            (Nat.le_trans keywordBeforeSemicolon semicolonSpanValid.2.1))
      cases finished
      refine ⟨⟨outerValid, nameValidInput, ?_, ?_, valueValidInput⟩,
        weakResult.2.1, weakResult.2.2⟩
      · cases parameters with
        | none => simp
        | some values => simpa [Option.ValidFor] using parametersValidInput.1
      · cases parameters with
        | none => simp
        | some values =>
            intro retained member parameter parameterMember
            have retainedEq : retained = values := by simpa using member.symm
            subst retained
            exact parametersValidInput.2 parameter parameterMember

/-- Complete type-alias parsing preserves every ordinary token window. -/
theorem typeAlias_preservesTokenWindow :
    Parser.PreservesTokenWindow typeAlias := by
  unfold typeAlias
  apply Parser.bind_preservesTokenWindow
    (keyword_preservesTokenWindow .typeKw .typeAlias)
  intro typeKeyword
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .typeAlias)
  intro name
  apply Parser.bind_preservesTokenWindow
    parseTypeAliasParameters_preservesTokenWindow
  intro parameters
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .equal .typeAlias)
  intro equal
  apply Parser.bind_preservesTokenWindow
    TypeAliasInternals.parseAliasValue_preservesTokenWindow
  intro value
  apply Parser.bind_preservesTokenWindow
    (symbol_preservesTokenWindow .semicolon .typeAlias)
  intro semicolon
  exact Parser.pure_preservesTokenWindow _

/-- Successful type-alias parsing retains the immutable token carrier. -/
theorem typeAlias_preservesTokensOnSuccess : Parser.PreservesTokensOnSuccess typeAlias :=
  typeAlias_preservesTokenWindow.preservesTokensOnSuccess

/-- Complete type-alias parsing never rewinds the parser cursor. -/
theorem typeAlias_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess typeAlias := by
  unfold typeAlias
  apply Parser.bind_cursorMonotoneOnSuccess
    (keyword_cursorMonotoneOnSuccess .typeKw .typeAlias)
  intro typeKeyword
  apply Parser.bind_cursorMonotoneOnSuccess
    (identifier_cursorMonotoneOnSuccess .typeAlias)
  intro name
  apply Parser.bind_cursorMonotoneOnSuccess
    parseTypeAliasParameters_cursorMonotoneOnSuccess
  intro parameters
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .equal .typeAlias)
  intro equal
  apply Parser.bind_cursorMonotoneOnSuccess
    TypeAliasInternals.parseAliasValue_cursorMonotoneOnSuccess
  intro value
  apply Parser.bind_cursorMonotoneOnSuccess
    (symbol_cursorMonotoneOnSuccess .semicolon .typeAlias)
  intro semicolon
  exact Parser.pure_cursorMonotoneOnSuccess _

/-- A complete type alias starts at its leading `type` token. -/
theorem typeAlias_startsAtCurrentTokenOnSuccess :
    Parser.StartsAtCurrentTokenOnSuccess typeAlias (·.span) := by
  unfold typeAlias
  apply Parser.bind_startsAtCurrentTokenOnSuccess_of_first
    (acceptToken_startsAtCurrentTokenOnSuccess
      (.keyword .typeKw) .typeAlias (· == .keyword .typeKw))
  intro typeKeyword input declaration final parsed
  rcases typeAliasBind_ok_components parsed with
    ⟨name, afterName, _nameResult, rest⟩
  rcases typeAliasBind_ok_components rest with
    ⟨parameters, afterParameters, _parametersResult, rest⟩
  rcases typeAliasBind_ok_components rest with
    ⟨equal, afterEqual, _equalResult, rest⟩
  rcases typeAliasBind_ok_components rest with
    ⟨value, afterValue, _valueResult, rest⟩
  rcases typeAliasBind_ok_components rest with
    ⟨semicolon, afterSemicolon, _semicolonResult, finished⟩
  cases finished
  rfl

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasRecoveryDiagnosticProperties`
-/

/-! Diagnostic commitments of transparent type-alias value recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeAliasInternals

/-- Every successful auxiliary alias recovery commits a recovery diagnostic. -/
theorem recoverTypeAliasValueAux_diagnostics_ne_nil_onSuccess
    (first last : SourceSpan) :
    ∀ fuel, ∀ {input next : State} {value : TypeExpr},
      recoverTypeAliasValueAux first last fuel input = .ok value next →
      next.diagnosticsRev ≠ [] := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      simp [recoverTypeAliasValueAux]
  | succ fuel inductionHypothesis =>
      intro input next value recovered
      unfold recoverTypeAliasValueAux at recovered
      split at recovered
      · unfold finishRecoveredType at recovered
        cases recovered
        simp [State.emit]
      · cases advanced : input.advance? with
        | none =>
            simp only [advanced] at recovered
            unfold finishRecoveredType at recovered
            cases recovered
            simp [State.emit]
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            simp only [advanced] at recovered
            exact inductionHypothesis token.span recovered

/-- Every successful complete alias recovery commits a recovery diagnostic. -/
theorem recoverTypeAliasValue_diagnostics_ne_nil_onSuccess
    {input next : State} {value : TypeExpr}
    (recovered : recoverTypeAliasValue input = .ok value next) :
    next.diagnosticsRev ≠ [] := by
  unfold recoverTypeAliasValue at recovered
  split at recovered
  · unfold rejectAt at recovered
    contradiction
  · cases advanced : input.advance? with
    | none =>
        simp [advanced, rejectAt] at recovered
    | some pair =>
        rcases pair with ⟨token, afterToken⟩
        simp only [advanced] at recovered
        exact recoverTypeAliasValueAux_diagnostics_ne_nil_onSuccess
          token.span token.span (afterToken.remainingCount + 1) recovered

end Solcore.Syntax.Parser.TypeAliasInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasRecoveryTotalityProperties`
-/

/-! Fuel adequacy and totality for malformed type-alias RHS recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TypeAliasInternals

/-- More fuel than remaining tokens makes alias-value recovery terminate. -/
theorem recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt
    (first : SourceSpan) :
  ∀ fuel last state, state.remainingCount < fuel →
      ∃ value final,
        recoverTypeAliasValueAux first last fuel state = .ok value final := by
  intro fuel last
  induction fuel generalizing last with
  | zero =>
      intro state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro state adequate
      unfold recoverTypeAliasValueAux
      split
      · simp [finishRecoveredType]
      · cases advanced : state.advance? with
        | none => simp [finishRecoveredType]
        | some pair =>
            rcases pair with ⟨token, next⟩
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : state.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- The production fuel selected by recovery is always adequate. -/
theorem recoverTypeAliasValueAux_production_exists_ok
    (first last : SourceSpan) (state : State) :
    ∃ value final,
      recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
        .ok value final :=
  recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
    (state.remainingCount + 1) last state (by omega)

/-- Adequately fueled auxiliary recovery has an ordinary result. -/
theorem recoverTypeAliasValueAux_ordinary_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel) :
    (∃ value final,
      recoverTypeAliasValueAux first last fuel state = .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValueAux first last fuel state =
          .reject failure final) :=
  Or.inl (recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
    fuel last state adequate)

/-- Adequate auxiliary recovery cannot expose an invariant failure. -/
theorem recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverTypeAliasValueAux first last fuel state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTypeAliasValueAux_exists_ok_of_remainingCount_lt first
      fuel last state adequate with ⟨value, final, result⟩
  rw [result] at invariantResult
  contradiction

/-- The production auxiliary parser has only an ordinary result. -/
theorem recoverTypeAliasValueAux_production_ordinary
    (first last : SourceSpan) (state : State) :
    (∃ value final,
      recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
        .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValueAux first last (state.remainingCount + 1) state =
          .reject failure final) :=
  Or.inl (recoverTypeAliasValueAux_production_exists_ok first last state)

/-- Production auxiliary recovery cannot exhaust its fuel. -/
theorem recoverTypeAliasValueAux_production_ne_invariant
    (first last : SourceSpan) (state : State)
    (error : ParserInvariantError) :
    recoverTypeAliasValueAux first last (state.remainingCount + 1) state ≠
      .invariant error :=
  recoverTypeAliasValueAux_ne_invariant_of_remainingCount_lt first last
    (state.remainingCount + 1) state (by omega) error

/-- Alias-value recovery returns either its recovered type or a rejection. -/
theorem recoverTypeAliasValue_ordinary (state : State) :
    (∃ value final, recoverTypeAliasValue state = .ok value final) ∨
      (∃ failure final,
        recoverTypeAliasValue state = .reject failure final) := by
  unfold recoverTypeAliasValue
  split
  · right
    simp [rejectAt]
  · cases advanced : state.advance? with
    | none =>
        right
        simp [rejectAt]
    | some pair =>
        rcases pair with ⟨token, next⟩
        left
        simpa only [advanced] using
          recoverTypeAliasValueAux_production_exists_ok
            token.span token.span next

/-- The malformed alias-value recovery entry point is invariant-free. -/
theorem recoverTypeAliasValue_ne_invariant (state : State)
    (error : ParserInvariantError) :
    recoverTypeAliasValue state ≠ .invariant error := by
  intro invariantResult
  rcases recoverTypeAliasValue_ordinary state with
    ⟨value, final, result⟩ | ⟨failure, final, result⟩ <;>
    rw [result] at invariantResult <;> contradiction

end Solcore.Syntax.Parser.TypeAliasInternals

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasSoundnessProperties`
-/

/-! Diagnostic-free success soundness for transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace TypeAliasInternals

/-- A diagnostic-free alias RHS success came from the ordinary type parser. -/
theorem parseAliasValue_success_sound_of_diagnosticFree
    {input next : State} {value : TypeExpr}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : parseAliasValue input = .ok value next) :
    DeclarativeGrammar.TypeExprParses input.declarativeRemainder value
      next.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok parsed afterCore =>
      simp only [coreResult] at result
      cases result
      exact typeExpr_success_sound coreResult
  | invariant error =>
      simp [coreResult] at result
  | reject failure failedState =>
      simp only [coreResult] at result
      let rewound : State := {
        failedState with
        cursor := input.cursor
      }
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value next at result
      split at result
      · contradiction
      · exact False.elim
          (recoverTypeAliasValue_diagnostics_ne_nil_onSuccess result
            diagnosticFree)

end TypeAliasInternals

private theorem typeAliasSoundBind_success_components {alpha beta : Type}
    {first : Parser alpha} {nextParser : alpha → Parser beta}
    {input final : State} {value : beta}
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

/-- Every diagnostic-free successful alias follows the exact declaration grammar. -/
theorem typeAlias_success_sound {input next : State}
    {declaration : TypeAliasDecl}
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    DeclarativeGrammar.TypeAliasDeclParses input.declarativeRemainder
      declaration next.declarativeRemainder := by
  unfold typeAlias at result
  rcases typeAliasSoundBind_success_components result with
    ⟨typeKeyword, afterKeyword, keywordResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨name, afterName, nameResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨parameters, afterParameters, parametersResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨equal, afterEqual, equalResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨value, afterValue, valueResult, rest⟩
  rcases typeAliasSoundBind_success_components rest with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  have semicolonShape := symbol_ok_tokenAt .semicolon .typeAlias
    semicolonResult
  have valueDiagnosticFree : afterValue.diagnosticsRev = [] := by
    rw [semicolonShape.2] at diagnosticFree
    exact diagnosticFree
  exact .parsed typeKeyword.span equal.span semicolon.span
    (keyword_success_exactTokenParses .typeKw .typeAlias keywordResult)
    (identifier_success_sound .typeAlias nameResult)
    (parseTypeAliasParameters_success_sound parametersResult)
    (symbol_success_exactTokenParses .equal .typeAlias equalResult)
    (TypeAliasInternals.parseAliasValue_success_sound_of_diagnosticFree
      valueDiagnosticFree valueResult)
    (symbol_success_exactTokenParses .semicolon .typeAlias semicolonResult)

/-- Alias grammar soundness composes with source validity. -/
theorem typeAlias_success_sound_and_validFor {input next : State}
    {declaration : TypeAliasDecl} (inputValid : input.ValidFor)
    (diagnosticFree : next.diagnosticsRev = [])
    (result : typeAlias input = .ok declaration next) :
    DeclarativeGrammar.TypeAliasDeclParses input.declarativeRemainder
        declaration next.declarativeRemainder ∧
      TypeAliasDecl.ValidFor input.file declaration := by
  refine ⟨typeAlias_success_sound diagnosticFree result, ?_⟩
  have valid := typeAlias_validFor input inputValid
  rw [result] at valid
  exact valid.1

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasTotalityProperties`
-/

/-! Conditional totality for complete canonical type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parameters are invariant-free on every valid input. -/
theorem parseTypeAliasParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid parseTypeAliasParameters := by
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (delimited_validFor Located.ValidFor .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias
        (identifier_validFor .parameter)
        (identifier_preservesTokensOnSuccess .parameter))
      (Parser.invariantFreeOnValid_of_ne_invariant (fun input inputValid error =>
        delimited_ne_invariant .leftParen .rightParen true
          (identifier .parameter) .typeAlias .typeAlias
          (identifier_elementTotalityContract .parameter)
          input inputValid error))
    intro values
    exact Parser.pure_invariantFreeOnValid (some values)
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

/-- Optional alias parameters cannot expose an internal invariant. -/
theorem parseTypeAliasParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseTypeAliasParameters input ≠ .invariant error :=
  parseTypeAliasParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

namespace TypeAliasInternals

/-- Alias RHS parsing is total once recursive type parsing is total. -/
theorem parseAliasValue_invariantFreeOnValid
    (typeFree : Parser.InvariantFreeOnValid typeExpr) :
    Parser.InvariantFreeOnValid parseAliasValue := by
  intro input inputValid
  unfold parseAliasValue
  cases coreResult : typeExpr input with
  | ok value next => exact Or.inl ⟨value, next, rfl⟩
  | invariant error =>
      exact False.elim (typeFree.ne_invariant input inputValid error coreResult)
  | reject failure failedState =>
      dsimp only
      split
      · exact Or.inr ⟨failure, _, rfl⟩
      · exact recoverTypeAliasValue_ordinary _

/-- Alias RHS parsing cannot expose an invariant under the type premise. -/
theorem parseAliasValue_ne_invariant
    (typeFree : Parser.InvariantFreeOnValid typeExpr)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseAliasValue input ≠ .invariant error :=
  (parseAliasValue_invariantFreeOnValid typeFree).ne_invariant
    input inputValid error

end TypeAliasInternals

/-- A complete type alias is total once recursive type parsing is total. -/
theorem typeAlias_invariantFreeOnValid_of_type
    (typeFree : Parser.InvariantFreeOnValid typeExpr) :
    Parser.InvariantFreeOnValid typeAlias := by
  unfold typeAlias
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .typeKw .typeAlias)
    (keyword_ordinary .typeKw .typeAlias).invariantFreeOnValid
  intro typeKeyword
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .typeAlias)
    (identifier_ordinary .typeAlias).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    parseTypeAliasParameters_validFor
    parseTypeAliasParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .equal .typeAlias)
    (symbol_ordinary .equal .typeAlias).invariantFreeOnValid
  intro equal
  apply Parser.bind_invariantFreeOnValid
    TypeAliasInternals.parseAliasValue_validFor
    (TypeAliasInternals.parseAliasValue_invariantFreeOnValid typeFree)
  intro value
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .typeAlias)
    (symbol_ordinary .semicolon .typeAlias).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover typeKeyword.span semicolon.span
    value := { name, parameters, value }
  } : TypeAliasDecl)

/-- Complete type aliases cannot expose an invariant under the type premise. -/
theorem typeAlias_ne_invariant_of_type
    (typeFree : Parser.InvariantFreeOnValid typeExpr)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeAlias input ≠ .invariant error :=
  (typeAlias_invariantFreeOnValid_of_type typeFree).ne_invariant
    input inputValid error

/-- Complete canonical type aliases are invariant-free on valid input. -/
theorem typeAlias_invariantFreeOnValid :
    Parser.InvariantFreeOnValid typeAlias :=
  typeAlias_invariantFreeOnValid_of_type typeExpr_invariantFreeOnValid

theorem typeAlias_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeAlias input ≠ .invariant error :=
  typeAlias_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasValueRecoveryOrdinaryOutcomeSoundnessProperties`
-/

/-! Exact executable ordinary outcomes for type-alias value recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .typeAlias present with
    ⟨token, parsed⟩
  exact ⟨token.span, (symbol_ok_tokenAt value .typeAlias parsed).1⟩

/-- A true executable entry guard gives the exact non-consuming recovery
boundary. -/
theorem typeAliasValueBoundaryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = true) :
    DeclarativeGrammar.TypeAliasValueBoundaryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have semicolon : isSymbol input .semicolon = true := by
      simpa [atEndFalse] using boundary
    exact .semicolon
      (tokenAt_of_isSymbol_eq_true .semicolon semicolon).choose_spec

/-- A false executable entry guard excludes every non-consuming recovery
boundary. -/
theorem no_typeAliasValueBoundaryStops_of_guard_eq_false
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = false) :
    ¬ DeclarativeGrammar.TypeAliasValueBoundaryStops
      input.declarativeRemainder := by
  intro stops
  cases stops with
  | windowEnd atEnd =>
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundary
  | semicolon present =>
      have semicolon : isSymbol input .semicolon = true :=
        isSymbol_eq_true_of_tokenAt .semicolon (by
          simpa [State.declarativeRemainder] using present)
      simp [semicolon] at boundary

private theorem typeAliasValueRecoveryStops_of_guard_eq_true
    (input : State)
    (boundary : (input.atEnd || isSymbol input .semicolon) = true) :
    DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  have stops := typeAliasValueBoundaryStops_of_guard_eq_true input boundary
  cases stops with
  | windowEnd atEnd => exact .windowEnd atEnd
  | semicolon token => exact .semicolon token

private theorem typeAliasValueRecoveryStops_of_advance?_eq_none
    (input : State) (advanced : input.advance? = none) :
    DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · exact typeAliasValueRecoveryStops_of_guard_eq_true input boundary
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
      intro atEnd
      have atEndTrue : input.atEnd = true := by
        unfold State.atEnd
        exact decide_eq_true atEnd
      simp [atEndTrue] at boundaryFalse
    have inside : input.cursor < input.window.endIndex := by omega
    apply DeclarativeGrammar.TypeAliasValueRecoveryStops.missingToken inside
    unfold State.advance? State.peek? at advanced
    simpa [State.declarativeRemainder, inside] using advanced

private theorem no_typeAliasValueRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (boundary : (input.atEnd || isSymbol input .semicolon) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.TypeAliasValueRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | semicolon present =>
      have semicolon : isSymbol input .semicolon = true :=
        isSymbol_eq_true_of_tokenAt .semicolon (by
          simpa [State.declarativeRemainder] using present)
      simp [semicolon] at boundary
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

private theorem typeAliasValueRecovery_advance_state_shape
    {input next : State} {token : Token}
    (advanced : input.advance? = some (token, next)) :
    input.peek? = some token ∧
      next = { input with cursor := input.cursor + 1 } := by
  unfold State.advance? at advanced
  cases found : input.peek? with
  | none => simp [found] at advanced
  | some current =>
      simp only [found, Option.map_some] at advanced
      cases advanced
      exact ⟨rfl, rfl⟩

namespace TypeAliasInternals

/-- Every successful executable auxiliary scan records exact boundary
priority, consumed tokens, recovered span, and final remainder. -/
theorem recoverTypeAliasValueAux_success_ordinary_sound
    (first : SourceSpan) :
    ∀ fuel last input value output,
      recoverTypeAliasValueAux first last fuel input = .ok value output →
      DeclarativeGrammar.TypeAliasValueRecoveryScanParses first last
        input.declarativeRemainder value output.declarativeRemainder := by
  intro fuel
  induction fuel with
  | zero =>
      intro last input value output result
      simp [recoverTypeAliasValueAux] at result
  | succ fuel inductionHypothesis =>
      intro last input value output result
      unfold recoverTypeAliasValueAux at result
      by_cases boundary :
          (input.atEnd || isSymbol input .semicolon) = true
      · simp only [boundary, if_true] at result
        unfold finishRecoveredType at result
        cases result
        simpa [State.emit, State.declarativeRemainder] using
          (DeclarativeGrammar.TypeAliasValueRecoveryScanParses.stop
            (first := first) (last := last)
            (typeAliasValueRecoveryStops_of_guard_eq_true input boundary))
      · have boundaryFalse :
            (input.atEnd || isSymbol input .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        cases advanced : input.advance? with
        | none =>
            simp only [advanced] at result
            unfold finishRecoveredType at result
            cases result
            simpa [State.emit, State.declarativeRemainder] using
              (DeclarativeGrammar.TypeAliasValueRecoveryScanParses.stop
                (first := first) (last := last)
                (typeAliasValueRecoveryStops_of_advance?_eq_none input
                  advanced))
        | some pair =>
            rcases pair with ⟨token, next⟩
            simp only [advanced] at result
            rcases typeAliasValueRecovery_advance_state_shape advanced with
              ⟨found, nextEq⟩
            have tail := inductionHypothesis token.span next value output result
            rw [nextEq] at tail
            exact .next
              (no_typeAliasValueRecoveryStops_of_nonBoundary_token
                boundaryFalse found)
              (tokenAt_of_peek?_eq_some found) tail

/-- Every successful recovery consumes its mandatory first token and then
follows the exact semicolon-preserving scan. -/
theorem recoverTypeAliasValue_success_ordinary_sound
    {input output : State} {value : TypeExpr}
    (result : recoverTypeAliasValue input = .ok value output) :
    DeclarativeGrammar.TypeAliasValueRecoveryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold recoverTypeAliasValue at result
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · simp [boundary, rejectAt] at result
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
    cases advanced : input.advance? with
    | none => simp [advanced, rejectAt] at result
    | some pair =>
        rcases pair with ⟨token, next⟩
        simp only [advanced] at result
        rcases typeAliasValueRecovery_advance_state_shape advanced with
          ⟨found, nextEq⟩
        have scan := recoverTypeAliasValueAux_success_ordinary_sound token.span
          (next.remainingCount + 1) token.span next value output result
        rw [nextEq] at scan
        exact .recovered
          (no_typeAliasValueBoundaryStops_of_guard_eq_false input
            boundaryFalse)
          (tokenAt_of_peek?_eq_some found) scan

/-- Every recovery rejection is the exact non-consuming entry boundary or a
missing mandatory carrier token. -/
theorem recoverTypeAliasValue_reject_ordinary_sound
    {input rejected : State} {failure : Failure}
    (result : recoverTypeAliasValue input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasValueRecoveryRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold recoverTypeAliasValue at result
  by_cases boundary : (input.atEnd || isSymbol input .semicolon) = true
  · simp only [boundary, if_true] at result
    unfold rejectAt at result
    cases result
    exact .boundary
      (typeAliasValueBoundaryStops_of_guard_eq_true input boundary)
  · have boundaryFalse :
        (input.atEnd || isSymbol input .semicolon) = false :=
      Bool.eq_false_iff.mpr boundary
    simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
    cases advanced : input.advance? with
    | none =>
        simp only [advanced] at result
        unfold rejectAt at result
        cases result
        have stops := typeAliasValueRecoveryStops_of_advance?_eq_none input
          advanced
        cases stops with
        | windowEnd atEnd =>
            have atEndTrue : input.atEnd = true := by
              unfold State.atEnd
              exact decide_eq_true atEnd
            simp [atEndTrue] at boundaryFalse
        | semicolon present =>
            have semicolon : isSymbol input .semicolon = true :=
              isSymbol_eq_true_of_tokenAt .semicolon (by
                simpa [State.declarativeRemainder] using present)
            simp [semicolon] at boundaryFalse
        | missingToken inside missing => exact .missingToken inside missing
    | some pair =>
        rcases pair with ⟨token, next⟩
        simp only [advanced] at result
        rcases recoverTypeAliasValueAux_production_exists_ok token.span
            token.span next with ⟨recovered, final, recoveredResult⟩
        rw [recoveredResult] at result
        contradiction

/-- Package standalone alias-value recovery success and rejection. -/
theorem recoverTypeAliasValue_ordinaryOutcome_sound :
    (∀ {input output : State} {value : TypeExpr},
      recoverTypeAliasValue input = .ok value output →
        DeclarativeGrammar.TypeAliasValueRecoveryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      recoverTypeAliasValue input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasValueRecoveryRejects
          input.declarativeRemainder rejected.declarativeRemainder) :=
  ⟨recoverTypeAliasValue_success_ordinary_sound,
    recoverTypeAliasValue_reject_ordinary_sound⟩

/-- Re-export deterministic standalone alias-value recovery outcomes. -/
theorem recoverTypeAliasValue_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueRecoveryParses
      DeclarativeGrammar.TypeAliasValueRecoveryRejects :=
  DeclarativeGrammar.typeAliasValueRecoveryDeterministicOutcomeSpec

/-- Re-export exact standalone alias-value recovery outcomes. -/
theorem recoverTypeAliasValue_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueRecoveryParses
      DeclarativeGrammar.TypeAliasValueRecoveryRejects :=
  DeclarativeGrammar.typeAliasValueRecoveryExactOutcomeSpec

/-- Two successful recovery reflections have the same error type and final
declarative remainder. -/
theorem recoverTypeAliasValue_success_result_unique
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : recoverTypeAliasValue input = .ok left leftOutput)
    (rightResult : recoverTypeAliasValue input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueRecoveryParses.result_unique
    (recoverTypeAliasValue_success_ordinary_sound leftResult)
    (recoverTypeAliasValue_success_ordinary_sound rightResult)

/-- Two rejected recovery reflections have the same exact declarative
endpoint. -/
theorem recoverTypeAliasValue_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : recoverTypeAliasValue input =
      .reject leftFailure leftOutput)
    (rightResult : recoverTypeAliasValue input =
      .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueRecoveryRejects.output_unique
    (recoverTypeAliasValue_reject_ordinary_sound leftResult)
    (recoverTypeAliasValue_reject_ordinary_sound rightResult)

end TypeAliasInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasValueOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for recovery-aware alias values. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem rewound_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

private theorem emitted_rewound_declarativeRemainder_eq
    (input failed : State) (diagnostic : ParseDiagnostic)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    State.declarativeRemainder
        (({ failed with cursor := input.cursor } : State).emit diagnostic) =
      input.declarativeRemainder := by
  unfold State.emit State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

namespace TypeAliasInternals

private theorem typeAliasValueCoreRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : typeExpr input = .reject failure failed) :
    DeclarativeGrammar.TypeAliasValueCoreRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape := typeExpr_preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧ failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    typeExpr_ordinaryOutcome_sound.2 result, shape.1,
    congrArg TokenWindow.endIndex shape.2⟩

/-- Every executable alias-value success is direct Core success or exact
recovery after cursor rewind and diagnostic emission. -/
theorem parseAliasValue_success_ordinaryOutcome_sound
    {input output : State} {value : TypeExpr}
    (result : parseAliasValue input = .ok value output) :
    DeclarativeGrammar.TypeAliasValueOrdinaryParses
      input.declarativeRemainder value output.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok coreValue afterCore =>
      simp only [coreResult] at result
      cases result
      exact .core (typeExpr_ordinaryOutcome_sound.1 coreResult)
  | invariant error => simp [coreResult] at result
  | reject failure failed =>
      simp only [coreResult] at result
      have resultShape := typeExpr_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit failure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            failure.toDiagnostic shape
      have coreRejected :=
        typeAliasValueCoreRejectsWithPreservedWindow_of_result coreResult
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject failure rewound
        else recoverTypeAliasValue
          (rewound.emit failure.toDiagnostic)) = .ok value output at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .semicolon) = true
      · simp [boundary] at result
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have recovered := recoverTypeAliasValue_success_ordinary_sound result
        rw [emittedEq] at recovered
        exact .recovered coreRejected recovered

/-- Every executable alias-value rejection is the exact rewound boundary or
the exact non-consuming recovery rejection. -/
theorem parseAliasValue_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : parseAliasValue input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasValueRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold parseAliasValue at result
  cases coreResult : typeExpr input with
  | ok value output => simp [coreResult] at result
  | invariant error => simp [coreResult] at result
  | reject coreFailure failed =>
      simp only [coreResult] at result
      have resultShape := typeExpr_preservesTokenWindow input
      rw [coreResult] at resultShape
      have shape : failed.tokens = input.tokens ∧
          failed.window = input.window := by
        simpa only [Reply.PreservesTokenWindow] using resultShape
      let rewound : State := { failed with cursor := input.cursor }
      have rewoundEq : rewound.declarativeRemainder =
          input.declarativeRemainder := by
        simpa only [rewound] using
          rewound_declarativeRemainder_eq input failed shape
      have emittedEq :
          (rewound.emit coreFailure.toDiagnostic).declarativeRemainder =
            input.declarativeRemainder := by
        simpa only [rewound] using
          emitted_rewound_declarativeRemainder_eq input failed
            coreFailure.toDiagnostic shape
      have coreRejected :=
        typeAliasValueCoreRejectsWithPreservedWindow_of_result coreResult
      change (if rewound.atEnd || isSymbol rewound .semicolon then
          .reject coreFailure rewound
        else recoverTypeAliasValue
          (rewound.emit coreFailure.toDiagnostic)) =
            .reject failure rejected at result
      by_cases boundary :
          (rewound.atEnd || isSymbol rewound .semicolon) = true
      · simp only [boundary, if_true] at result
        have rejectedEq : rewound = rejected := by injection result
        subst rejected
        have stops := typeAliasValueBoundaryStops_of_guard_eq_true rewound
          boundary
        rw [rewoundEq] at stops
        simpa only [rewoundEq] using
          DeclarativeGrammar.TypeAliasValueRejects.boundary coreRejected stops
      · have boundaryFalse :
            (rewound.atEnd || isSymbol rewound .semicolon) = false :=
          Bool.eq_false_iff.mpr boundary
        simp only [boundaryFalse, Bool.false_eq_true, if_false] at result
        have continues := no_typeAliasValueBoundaryStops_of_guard_eq_false
          rewound boundaryFalse
        rw [rewoundEq] at continues
        have recoveryRejected :=
          recoverTypeAliasValue_reject_ordinary_sound result
        rw [emittedEq] at recoveryRejected
        exact .recovery coreRejected continues recoveryRejected

/-- Package both executable ordinary alias-value outcomes. -/
theorem parseAliasValue_ordinaryOutcome_sound :
    (∀ {input output : State} {value : TypeExpr},
      parseAliasValue input = .ok value output →
        DeclarativeGrammar.TypeAliasValueOrdinaryParses
          input.declarativeRemainder value output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      parseAliasValue input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasValueRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨parseAliasValue_success_ordinaryOutcome_sound,
    parseAliasValue_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic recovery-aware alias-value outcomes. -/
theorem parseAliasValue_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueDeterministicOutcomeSpec

/-- Exact Core type outcomes lift to exact recovery-aware executable alias
values. -/
theorem parseAliasValue_exactOutcomeSpec_of_typeExpr
    (typeOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects) :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueExactOutcomeSpecOfTypeExpr typeOutcomes

/-- Re-export unconditional exact recovery-aware alias-value outcomes. -/
theorem parseAliasValue_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasValueOrdinaryParses
      DeclarativeGrammar.TypeAliasValueRejects :=
  DeclarativeGrammar.typeAliasValueExactOutcomeSpec

/-- Under exact Core type outcomes, two successful executable reflections
have the same alias value and final declarative remainder. -/
theorem parseAliasValue_success_result_unique_of_typeExpr
    (typeOutcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeExprOrdinaryParses
      DeclarativeGrammar.TypeExprRejects)
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : parseAliasValue input = .ok left leftOutput)
    (rightResult : parseAliasValue input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique_of_typeExpr
    typeOutcomes
    (parseAliasValue_success_ordinaryOutcome_sound leftResult)
    (parseAliasValue_success_ordinaryOutcome_sound rightResult)

/-- Two successful executable reflections have the same alias value and final
declarative remainder. -/
theorem parseAliasValue_success_result_unique
    {input leftOutput rightOutput : State} {left right : TypeExpr}
    (leftResult : parseAliasValue input = .ok left leftOutput)
    (rightResult : parseAliasValue input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueOrdinaryParses.result_unique
    (parseAliasValue_success_ordinaryOutcome_sound leftResult)
    (parseAliasValue_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable alias-value reflections always have the same
rewound declarative endpoint. -/
theorem parseAliasValue_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : parseAliasValue input = .reject leftFailure leftOutput)
    (rightResult : parseAliasValue input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasValueRejects.output_unique
    (parseAliasValue_reject_ordinaryOutcome_sound leftResult)
    (parseAliasValue_reject_ordinaryOutcome_sound rightResult)

end TypeAliasInternals
end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryRejectionSoundnessProperties`
-/

/-! Exact executable rejection for complete transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Every executable type-alias rejection records its exact first failing
keyword, name, parameter list, equals token, value, or semicolon stage. -/
theorem typeAlias_reject_ordinaryOutcome_sound
    {input rejected : State} {failure : Failure}
    (result : typeAlias input = .reject failure rejected) :
    DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder
      rejected.declarativeRemainder := by
  unfold typeAlias at result
  cases keywordResult : keyword .typeKw .typeAlias input with
  | invariant error => simp [bind, keywordResult] at result
  | reject keywordFailure keywordRejected =>
      have rejectedEq := keyword_reject_state_eq .typeKw .typeAlias
        keywordResult
      subst keywordRejected
      simp only [bind, keywordResult] at result
      cases result
      exact .keywordMissing
        (keyword_reject_tokenKindAbsentAt .typeKw .typeAlias keywordResult)
  | ok typeKeyword afterKeyword =>
      simp only [bind, keywordResult] at result
      have keywordParsed := keyword_success_exactTokenParses .typeKw
        .typeAlias keywordResult
      cases nameResult : identifier .typeAlias afterKeyword with
      | invariant error => simp [nameResult] at result
      | reject nameFailure nameRejected =>
          simp only [nameResult] at result
          cases result
          exact .nameRejected typeKeyword.span keywordParsed
            (identifier_reject_sound .typeAlias nameResult)
      | ok name afterName =>
          simp only [nameResult] at result
          have nameParsed := identifier_success_sound .typeAlias nameResult
          cases parametersResult : parseTypeAliasParameters afterName with
          | invariant error => simp [parametersResult] at result
          | reject parametersFailure parametersRejected =>
              simp only [parametersResult] at result
              cases result
              exact .parametersRejected typeKeyword.span keywordParsed
                nameParsed
                (parseTypeAliasParameters_reject_ordinaryOutcome_sound
                  parametersResult)
          | ok parameters afterParameters =>
              simp only [parametersResult] at result
              have parametersParsed :=
                parseTypeAliasParameters_success_ordinaryOutcome_sound
                  parametersResult
              cases equalResult : symbol .equal .typeAlias afterParameters with
              | invariant error => simp [equalResult] at result
              | reject equalFailure equalRejected =>
                  have rejectedEq := symbol_reject_state_eq .equal .typeAlias
                    equalResult
                  subst equalRejected
                  simp only [equalResult] at result
                  cases result
                  exact .equalMissing typeKeyword.span keywordParsed
                    nameParsed parametersParsed
                    (symbol_reject_tokenKindAbsentAt .equal .typeAlias
                      equalResult)
              | ok equal afterEqual =>
                  simp only [equalResult] at result
                  have equalParsed := symbol_success_exactTokenParses .equal
                    .typeAlias equalResult
                  cases valueResult : TypeAliasInternals.parseAliasValue
                      afterEqual with
                  | invariant error => simp [valueResult] at result
                  | reject valueFailure valueRejected =>
                      simp only [valueResult] at result
                      cases result
                      exact .valueRejected typeKeyword.span equal.span
                        keywordParsed nameParsed parametersParsed equalParsed
                        (TypeAliasInternals.parseAliasValue_reject_ordinaryOutcome_sound
                          valueResult)
                  | ok value afterValue =>
                      simp only [valueResult] at result
                      have valueParsed :=
                        TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
                          valueResult
                      cases semicolonResult : symbol .semicolon .typeAlias
                          afterValue with
                      | invariant error => simp [semicolonResult] at result
                      | ok semicolon output =>
                          simp [semicolonResult, pure] at result
                      | reject semicolonFailure semicolonRejected =>
                          have rejectedEq := symbol_reject_state_eq .semicolon
                            .typeAlias semicolonResult
                          subst semicolonRejected
                          simp only [semicolonResult] at result
                          cases result
                          exact .semicolonMissing typeKeyword.span equal.span
                            keywordParsed nameParsed parametersParsed
                            equalParsed valueParsed
                            (symbol_reject_tokenKindAbsentAt .semicolon
                              .typeAlias semicolonResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasDeclarationOrdinarySuccessSoundnessProperties`
-/

/-! Executable ordinary success for complete transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- Every executable type-alias success records its exact keyword, name,
optional parameters, equals token, recovery-aware value, semicolon, AST,
covering span, and final remainder. -/
theorem typeAlias_success_ordinaryOutcome_sound
    {input output : State} {declaration : TypeAliasDecl}
    (result : typeAlias input = .ok declaration output) :
    DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      input.declarativeRemainder declaration output.declarativeRemainder := by
  unfold typeAlias at result
  rcases bind_ok_components result with
    ⟨typeKeyword, afterKeyword, keywordResult, nameStage⟩
  rcases bind_ok_components nameStage with
    ⟨name, afterName, nameResult, parametersStage⟩
  rcases bind_ok_components parametersStage with
    ⟨parameters, afterParameters, parametersResult, equalStage⟩
  rcases bind_ok_components equalStage with
    ⟨equal, afterEqual, equalResult, valueStage⟩
  rcases bind_ok_components valueStage with
    ⟨value, afterValue, valueResult, semicolonStage⟩
  rcases bind_ok_components semicolonStage with
    ⟨semicolon, afterSemicolon, semicolonResult, finished⟩
  cases finished
  exact .parsed typeKeyword.span equal.span semicolon.span
    (keyword_success_exactTokenParses .typeKw .typeAlias keywordResult)
    (identifier_success_sound .typeAlias nameResult)
    (parseTypeAliasParameters_success_ordinaryOutcome_sound parametersResult)
    (symbol_success_exactTokenParses .equal .typeAlias equalResult)
    (TypeAliasInternals.parseAliasValue_success_ordinaryOutcome_sound
      valueResult)
    (symbol_success_exactTokenParses .semicolon .typeAlias semicolonResult)

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.TypeAliasDeclarationOrdinaryOutcomeSoundnessProperties`
-/

/-! Complete executable ordinary outcomes for transparent type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Package exact executable type-alias success and rejection. -/
theorem typeAlias_ordinaryOutcome_sound :
    (∀ {input output : State} {declaration : TypeAliasDecl},
      typeAlias input = .ok declaration output →
        DeclarativeGrammar.TypeAliasDeclOrdinaryParses
          input.declarativeRemainder declaration
            output.declarativeRemainder) ∧
    (∀ {input rejected : State} {failure : Failure},
      typeAlias input = .reject failure rejected →
        DeclarativeGrammar.TypeAliasDeclRejects input.declarativeRemainder
          rejected.declarativeRemainder) :=
  ⟨typeAlias_success_ordinaryOutcome_sound,
    typeAlias_reject_ordinaryOutcome_sound⟩

/-- Re-export deterministic broad type-alias outcomes. -/
theorem typeAlias_ordinaryOutcomeSpec :
    DeclarativeGrammar.DeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      DeclarativeGrammar.TypeAliasDeclRejects :=
  DeclarativeGrammar.typeAliasDeclDeterministicOutcomeSpec

/-- Re-export full type-alias AST and rejection-endpoint functionality. -/
theorem typeAlias_exactOutcomeSpec :
    DeclarativeGrammar.ExactDeterministicOutcomeSpec
      DeclarativeGrammar.TypeAliasDeclOrdinaryParses
      DeclarativeGrammar.TypeAliasDeclRejects :=
  DeclarativeGrammar.typeAliasDeclExactOutcomeSpec

/-- Two successful executable reflections have the same declaration AST and
final declarative remainder. -/
theorem typeAlias_success_result_unique
    {input leftOutput rightOutput : State}
    {left right : TypeAliasDecl}
    (leftResult : typeAlias input = .ok left leftOutput)
    (rightResult : typeAlias input = .ok right rightOutput) :
    left = right ∧
      leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasDeclOrdinaryParses.result_unique
    (typeAlias_success_ordinaryOutcome_sound leftResult)
    (typeAlias_success_ordinaryOutcome_sound rightResult)

/-- Two rejected executable reflections have the same first failing
declarative endpoint. -/
theorem typeAlias_reject_output_unique
    {input leftOutput rightOutput : State}
    {leftFailure rightFailure : Failure}
    (leftResult : typeAlias input = .reject leftFailure leftOutput)
    (rightResult : typeAlias input = .reject rightFailure rightOutput) :
    leftOutput.declarativeRemainder = rightOutput.declarativeRemainder :=
  DeclarativeGrammar.TypeAliasDeclRejects.output_unique
    (typeAlias_reject_ordinaryOutcome_sound leftResult)
    (typeAlias_reject_ordinaryOutcome_sound rightResult)

end Solcore.Syntax.Parser
