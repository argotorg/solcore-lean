import Solcore.Syntax.Parser.TypeAlias
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.TypeDeclarationValidity

/-! Recovery and declaration contracts for transparent type aliases. -/
set_option autoImplicit false
namespace Solcore.Syntax.Parser
namespace TypeAliasInternals

private theorem advance?_state_shape {input next : State} {token : Token}
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
            have shape := advance?_state_shape advanced
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
        have shape := advance?_state_shape advanced
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
              simp [(advance?_state_shape advanced).2])
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
            simp [(advance?_state_shape advanced).2])
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
              rw [(advance?_state_shape advanced).2]
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
          rw [(advance?_state_shape advanced).2]
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
