import Solcore.Syntax.Parser.Parameter
import Solcore.Syntax.Parser.TypeRecursiveProperties
import Solcore.Syntax.ParameterValidity

/-! Token-window contracts for recovering function parameters. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser
namespace FunctionParameterInternals

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

private theorem getState_preservesTokenWindowForParameter :
    Parser.PreservesTokenWindow getState := fun _ => ⟨rfl, rfl⟩

private theorem emitDiagnostic_preservesTokenWindowForParameter
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokenWindow (emitDiagnostic diagnostic) := by
  intro input
  unfold emitDiagnostic modifyState Reply.PreservesTokenWindow
  exact ⟨rfl, rfl⟩

theorem finishRecoveredParameter_validFor (first last : SourceSpan)
    (state : State) (stateValid : state.ValidFor)
    (firstValid : first.ValidFor state.file)
    (lastValid : last.ValidFor state.file)
    (ordered : first.startByte ≤ last.endByte) :
    (finishRecoveredParameter first last state).ValidFor state
      FunctionParameter.ValidFor := by
  have spanValid := SourceSpan.cover_validFor firstValid lastValid ordered
  unfold finishRecoveredParameter Reply.ValidFor
  exact ⟨.error spanValid, stateValid.emit_validFor _ spanValid, rfl⟩

theorem recoverParameterAux_validFor (first : SourceSpan) :
    ∀ fuel last state lastIndex lastToken,
      state.ValidFor → first.ValidFor state.file →
      last.ValidFor state.file → first.startByte ≤ last.endByte →
      state.tokens[lastIndex]? = some lastToken → lastToken.span = last →
      lastIndex < state.cursor →
      (recoverParameterAux first last fuel state).ValidFor state
        FunctionParameter.ValidFor := by
  intro fuel
  induction fuel with
  | zero => intros; trivial
  | succ fuel inductionHypothesis =>
      intro last state lastIndex lastToken stateValid firstValid lastValid
        ordered lastFound lastSpan lastBefore
      unfold recoverParameterAux
      split
      · exact finishRecoveredParameter_validFor first last state stateValid
          firstValid lastValid ordered
      · cases advanced : state.advance? with
        | none =>
            exact finishRecoveredParameter_validFor first last state
              stateValid firstValid lastValid ordered
        | some pair =>
            rcases pair with ⟨token, next⟩
            have shape := advance?_state_shape advanced
            have nextValid := stateValid.advance?_validFor advanced
            have tokenValid := stateValid.peek?_span_validFor shape.1
            have currentFound :=
              State.getElem?_eq_some_of_peek?_eq_some shape.1
            have lastBeforeCurrent :=
              stateValid.token_end_le_token_start_of_getElem?_lt lastFound
                currentFound lastBefore
            exact (inductionHypothesis token.span next state.cursor token
              nextValid (by simpa [shape.2] using firstValid)
              (by simpa [shape.2] using tokenValid)
              (Nat.le_trans ordered (Nat.le_trans
                (by simpa [lastSpan] using lastBeforeCurrent)
                tokenValid.2.1))
              (by simpa [shape.2] using currentFound) rfl
              (by simp [shape.2])).of_file_eq (by simp [shape.2])

theorem recoverParameter_validFor (state : State)
    (stateValid : state.ValidFor) :
    (recoverParameter state).ValidFor state FunctionParameter.ValidFor := by
  unfold recoverParameter
  cases advanced : state.advance? with
  | none =>
      unfold rejectAt Reply.ValidFor
      exact ⟨stateValid.currentSpan_validFor, stateValid, rfl⟩
  | some pair =>
      rcases pair with ⟨token, next⟩
      have shape := advance?_state_shape advanced
      have nextValid := stateValid.advance?_validFor advanced
      have tokenValid := stateValid.peek?_span_validFor shape.1
      have tokenFound := State.getElem?_eq_some_of_peek?_eq_some shape.1
      exact (recoverParameterAux_validFor token.span
        (next.remainingCount + 1) token.span next state.cursor token
        nextValid (by simpa [shape.2] using tokenValid)
        (by simpa [shape.2] using tokenValid) tokenValid.2.1
        (by simpa [shape.2] using tokenFound) rfl
        (by simp [shape.2])).of_file_eq (by simp [shape.2])

private theorem finishTypedParameter_validFor (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) (input : State) (inputValid : input.ValidFor)
    (spanValid : (SourceSpan.cover start type.span).ValidFor input.file)
    (markerValid : ∀ marker ∈ comptimeMarker,
      marker.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (typeValid : TypeExpr.ValidFor input.file type) :
    (finishTypedParameter start comptimeMarker name type input).ValidFor
      input FunctionParameter.ValidFor := by
  have parameterValid : FunctionParameter.ValidFor input.file {
      span := SourceSpan.cover start type.span
      value := .typed comptimeMarker name type
    } := .typed spanValid markerValid nameValid typeValid
  cases valueEq : type.value <;>
    simp only [finishTypedParameter, valueEq, emitDiagnostic, modifyState,
      bind, pure, Reply.ValidFor]
  case comptime =>
    exact And.intro parameterValid (And.intro
      (inputValid.emit_validFor {
        span := type.span
        kind := .constraintViolation .comptimeTypeInParameter
      } typeValid.span_valid) rfl)
  all_goals exact And.intro parameterValid (And.intro inputValid trivial)

private theorem errorParameter_validFor (span : SourceSpan)
    (constraint : ParseConstraint) (input : State)
    (inputValid : input.ValidFor) (spanValid : span.ValidFor input.file) :
    (errorParameter span constraint input).ValidFor input
      FunctionParameter.ValidFor := by
  unfold errorParameter emitDiagnostic modifyState bind pure Reply.ValidFor
  exact ⟨.error spanValid, inputValid.emit_validFor _ spanValid, rfl⟩

/-- The shared typed-or-error tail retains parameter provenance. -/
theorem namedParameterTail_validFor (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {firstIndex : Nat} {firstToken : Token}
    (input : State) (inputValid : input.ValidFor)
    (startValid : start.ValidFor input.file)
    (markerValid : ∀ marker ∈ comptimeMarker,
      marker.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (errorSpanValid : errorSpan.ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some firstToken)
    (firstSpan : firstToken.span = start)
    (firstBefore : firstIndex < input.cursor) :
    (namedParameterTail start comptimeMarker name errorSpan input).ValidFor
      input FunctionParameter.ValidFor := by
  unfold namedParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    cases colonResult : symbol .colon .parameter input with
    | invariant error => trivial
    | reject failure rejected =>
        have valid := symbol_validFor .colon .parameter input inputValid
        rw [colonResult] at valid
        exact valid
    | ok colon afterColon =>
        have colonValid := symbol_validFor .colon .parameter input inputValid
        rw [colonResult] at colonValid
        simp only
        cases typeResult : typeExpr afterColon with
        | invariant error =>
            change (Reply.invariant error).ValidFor input
              FunctionParameter.ValidFor
            trivial
        | reject failure rejected =>
            change (Reply.reject failure rejected).ValidFor input
              FunctionParameter.ValidFor
            have valid := typeExpr_validFor afterColon colonValid.2.1
            rw [typeResult] at valid
            exact valid.of_file_eq colonValid.2.2
        | ok type afterType =>
            change (finishTypedParameter start comptimeMarker name type
              afterType).ValidFor input FunctionParameter.ValidFor
            have typeReply := typeExpr_validFor afterColon colonValid.2.1
            rw [typeResult] at typeReply
            have typeValid : TypeExpr.ValidFor input.file type := by
              simpa [colonValid.2.2] using typeReply.1
            rcases typeExpr_startsAtCurrentTokenOnSuccess afterColon type
                afterType typeResult with ⟨typeToken, typeFound, typeStart⟩
            have colonShape := symbol_ok_state_shape .colon .parameter
              colonResult
            have typeAtInput :
                input.tokens[afterColon.cursor]? = some typeToken := by
              simpa [colonShape.2] using
                State.getElem?_eq_some_of_peek?_eq_some typeFound
            have beforeType :=
              inputValid.token_end_le_token_start_of_getElem?_lt firstFound
                typeAtInput (Nat.lt_trans firstBefore (by
                  simp [colonShape.2]))
            have ordered : start.startByte ≤ type.span.endByte :=
              Nat.le_trans startValid.2.1 (Nat.le_trans
                (by simpa [firstSpan, typeStart] using beforeType)
                typeValid.span_valid.2.1)
            exact (finishTypedParameter_validFor start comptimeMarker name
              type afterType typeReply.2.1
              (by simpa [typeReply.2.2, colonValid.2.2] using
                (SourceSpan.cover_validFor startValid typeValid.span_valid
                  ordered))
              (by simpa [typeReply.2.2, colonValid.2.2] using markerValid)
              (by simpa [typeReply.2.2, colonValid.2.2] using nameValid)
              (by simpa [typeReply.2.2, colonValid.2.2] using
                typeValid)).of_file_eq
                  (typeReply.2.2.trans colonValid.2.2)
  · simp only [typed]
    change (errorParameter errorSpan .namedParameterRequiresType input).ValidFor
      input FunctionParameter.ValidFor
    exact errorParameter_validFor errorSpan _ input inputValid errorSpanValid

/-- Ordinary named parameters retain name, type, and outer provenance. -/
theorem ordinaryNamedParameter_validFor :
    ordinaryNamedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold ordinaryNamedParameter
  simp only [bind]
  cases nameResult : identifier .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := identifier_validFor .parameter input inputValid
      rw [nameResult] at valid
      exact valid
  | ok name afterName =>
      have nameReply := identifier_validFor .parameter input inputValid
      rw [nameResult] at nameReply
      simp only
      rcases identifier_ok_state_shape .parameter nameResult with
        ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
      have nameAtInput := State.getElem?_eq_some_of_peek?_eq_some nameFound
      have nameAtAfter :
          afterName.tokens[input.cursor]? = some nameToken := by
        simpa [nameTokens] using nameAtInput
      have nameValidAfter : name.span.ValidFor afterName.file := by
        simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
      by_cases warned :
          name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
        let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        change (namedParameterTail name.span none name name.span
          (afterName.emit diagnostic)).ValidFor input
            FunctionParameter.ValidFor
        have emittedValid := nameReply.2.1.emit_validFor diagnostic
          nameValidAfter
        exact (namedParameterTail_validFor name.span none name name.span
          (afterName.emit diagnostic) emittedValid
          (by simpa [State.emit] using nameValidAfter) (by simp)
          (by simpa [State.emit] using nameValidAfter)
          (by simpa [State.emit] using nameValidAfter)
          (by simpa [State.emit] using nameAtAfter) nameSpan
          (by simp [State.emit, nameCursor])).of_file_eq
            (by simpa [State.emit] using nameReply.2.2)
      · simp only [warned]
        exact (namedParameterTail_validFor name.span none name name.span
          afterName nameReply.2.1 nameValidAfter (by simp)
          nameValidAfter nameValidAfter nameAtAfter nameSpan
          (by simp [nameCursor])).of_file_eq nameReply.2.2

/-- Comptime named parameters retain marker, name, type, and outer provenance. -/
theorem comptimeNamedParameter_validFor :
    comptimeNamedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold comptimeNamedParameter
  simp only [bind]
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at valid
      exact valid
  | ok marker afterMarker =>
      have markerReply := contextual_validFor .comptime .parameter input
        inputValid
      rw [markerResult] at markerReply
      simp only
      cases nameResult : identifier .parameter afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := identifier_validFor .parameter afterMarker
            markerReply.2.1
          rw [nameResult] at valid
          exact valid.of_file_eq markerReply.2.2
      | ok name afterName =>
          have nameReply := identifier_validFor .parameter afterMarker
            markerReply.2.1
          rw [nameResult] at nameReply
          simp only
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .parameter (·.isContextual .comptime)
            markerResult
          rcases identifier_ok_state_shape .parameter nameResult with
            ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
          have markerAtInput :=
            State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have markerAtAfter :
              afterName.tokens[input.cursor]? = some marker := by
            simpa [nameTokens, markerShape.2] using markerAtInput
          have nameAtAfterMarker :=
            State.getElem?_eq_some_of_peek?_eq_some nameFound
          have nameAtInput :
              input.tokens[afterMarker.cursor]? = some nameToken := by
            simpa [markerShape.2] using nameAtAfterMarker
          have markerBeforeName :=
            inputValid.token_end_le_token_start_of_getElem?_lt markerAtInput
              nameAtInput (by simp [markerShape.2])
          have markerValidAfter : marker.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2,
              markerReply.2.2] using markerReply.1
          have nameValidAfter : name.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
          have errorSpanValid :
              (SourceSpan.cover marker.span name.span).ValidFor
                afterName.file :=
            SourceSpan.cover_validFor markerValidAfter nameValidAfter
              (Nat.le_trans markerValidAfter.2.1 (Nat.le_trans
                (by simpa [nameSpan] using markerBeforeName)
                nameValidAfter.2.1))
          exact (namedParameterTail_validFor marker.span (some marker.span)
            name (SourceSpan.cover marker.span name.span) afterName
            nameReply.2.1 markerValidAfter (by simp [markerValidAfter])
            nameValidAfter errorSpanValid markerAtAfter rfl
            (by simp [markerShape.2, nameCursor]; omega)).of_file_eq
              (nameReply.2.2.trans markerReply.2.2)

theorem finishTypedParameter_preservesTokenWindow (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (type : TypeExpr) :
    Parser.PreservesTokenWindow
      (finishTypedParameter start comptimeMarker name type) := by
  unfold finishTypedParameter
  split
  · apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    exact Parser.pure_preservesTokenWindow _
  · exact Parser.pure_preservesTokenWindow _

theorem errorParameter_preservesTokenWindow (span : SourceSpan)
    (constraint : ParseConstraint) :
    Parser.PreservesTokenWindow (errorParameter span constraint) := by
  unfold errorParameter
  apply Parser.bind_preservesTokenWindow
    (emitDiagnostic_preservesTokenWindowForParameter _)
  intro _
  exact Parser.pure_preservesTokenWindow _

theorem namedParameterTail_preservesTokenWindow (start : SourceSpan)
    (comptimeMarker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) :
    Parser.PreservesTokenWindow
      (namedParameterTail start comptimeMarker name errorSpan) := by
  unfold namedParameterTail
  apply Parser.bind_preservesTokenWindow
    getState_preservesTokenWindowForParameter
  intro observed
  by_cases typed : isSymbol observed .colon
  · simp only [typed, if_true]
    apply Parser.bind_preservesTokenWindow
      (symbol_preservesTokenWindow .colon .parameter)
    intro _
    apply Parser.bind_preservesTokenWindow typeExpr_preservesTokenWindow
    intro type
    exact finishTypedParameter_preservesTokenWindow start
      comptimeMarker name type
  · simp only [typed]
    exact errorParameter_preservesTokenWindow errorSpan _

theorem ordinaryNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow ordinaryNamedParameter := by
  unfold ordinaryNamedParameter
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  by_cases warned : name.value == ContextualKeyword.comptime.spelling
  · simp only [warned, if_true]
    apply Parser.bind_preservesTokenWindow
      (emitDiagnostic_preservesTokenWindowForParameter _)
    intro _
    exact namedParameterTail_preservesTokenWindow
      name.span none name name.span
  · simp only [warned]
    exact namedParameterTail_preservesTokenWindow
      name.span none name name.span

theorem comptimeNamedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow comptimeNamedParameter := by
  unfold comptimeNamedParameter
  apply Parser.bind_preservesTokenWindow
    (contextual_preservesTokenWindow .comptime .parameter)
  intro marker
  apply Parser.bind_preservesTokenWindow
    (identifier_preservesTokenWindow .parameter)
  intro name
  exact namedParameterTail_preservesTokenWindow marker.span
    (some marker.span) name (SourceSpan.cover marker.span name.span)

/-- The non-recovering parameter choice preserves complete provenance. -/
theorem namedParameterCore_validFor :
    namedParameterCore.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_validFor input inputValid
    · exact ordinaryNamedParameter_validFor input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_validFor input inputValid

theorem namedParameterCore_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameterCore := by
  intro input
  unfold namedParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeNamedParameter_preservesTokenWindow input
    · exact ordinaryNamedParameter_preservesTokenWindow input
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryNamedParameter_preservesTokenWindow input

theorem recoverParameterAux_preservesTokenWindow
    (first last : SourceSpan) (fuel : Nat) :
    Parser.PreservesTokenWindow (recoverParameterAux first last fuel) := by
  intro input
  induction fuel generalizing last input with
  | zero => trivial
  | succ fuel inductionHypothesis =>
      unfold recoverParameterAux
      split
      · unfold finishRecoveredParameter Reply.PreservesTokenWindow
        exact ⟨rfl, rfl⟩
      · cases advanced : input.advance? with
        | none =>
            unfold finishRecoveredParameter Reply.PreservesTokenWindow
            exact ⟨rfl, rfl⟩
        | some pair =>
            rcases pair with ⟨token, afterToken⟩
            exact (inductionHypothesis token.span afterToken).trans (by
              simp [(advance?_state_shape advanced).2])

theorem recoverParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow recoverParameter := by
  intro input
  unfold recoverParameter
  cases advanced : input.advance? with
  | none => exact rejectAt_preservesTokenWindow input _ _
  | some pair =>
      rcases pair with ⟨token, afterToken⟩
      exact (recoverParameterAux_preservesTokenWindow token.span token.span
        (afterToken.remainingCount + 1) afterToken).trans (by
          simp [(advance?_state_shape advanced).2])

end FunctionParameterInternals

namespace LambdaParameterInternals

theorem ofFunctionParameter_validFor {file : SourceFile}
    {parameter : FunctionParameter}
    (valid : FunctionParameter.ValidFor file parameter) :
    LambdaParameter.ValidFor file (ofFunctionParameter parameter) := by
  cases valid with
  | typed spanValid markerValid nameValid typeValid =>
      exact .typed spanValid markerValid nameValid typeValid
  | error spanValid => exact .error spanValid

private theorem mappedFunctionParameter_validFor (parser : Parser FunctionParameter)
    {input : State}
    (valid : (parser input).ValidFor input FunctionParameter.ValidFor) :
    ((do pure (ofFunctionParameter (← parser))) input).ValidFor input
      LambdaParameter.ValidFor := by
  simp only [bind]
  cases parsed : parser input with
  | invariant error => trivial
  | reject failure rejected =>
      simp only [parsed, Reply.ValidFor] at valid ⊢
      exact valid
  | ok parameter final =>
      simp only [parsed, Reply.ValidFor] at valid ⊢
      exact ⟨ofFunctionParameter_validFor valid.1, valid.2.1, valid.2.2⟩

theorem ordinaryLambdaParameterTail_validFor (name : Identifier)
    {firstIndex : Nat} {firstToken : Token} (input : State)
    (inputValid : input.ValidFor) (nameValid : name.span.ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some firstToken)
    (firstSpan : firstToken.span = name.span)
    (firstBefore : firstIndex < input.cursor) :
    (ordinaryLambdaParameterTail name input).ValidFor input
      LambdaParameter.ValidFor := by
  unfold ordinaryLambdaParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    have valid := FunctionParameterInternals.namedParameterTail_validFor name.span
      none name name.span input inputValid nameValid (by simp) nameValid
      nameValid firstFound firstSpan firstBefore
    exact mappedFunctionParameter_validFor _ valid
  · simp only [typed, pure, Reply.ValidFor]
    exact ⟨.inferred nameValid nameValid, inputValid, rfl⟩

theorem comptimeLambdaParameterTail_validFor (marker : Token)
    (name : Identifier) {firstIndex : Nat} (input : State)
    (inputValid : input.ValidFor) (markerValid : marker.span.ValidFor input.file)
    (nameValid : name.span.ValidFor input.file)
    (spanValid : (SourceSpan.cover marker.span name.span).ValidFor input.file)
    (firstFound : input.tokens[firstIndex]? = some marker)
    (firstBefore : firstIndex < input.cursor) :
    (comptimeLambdaParameterTail marker name input).ValidFor input
      LambdaParameter.ValidFor := by
  unfold comptimeLambdaParameterTail getState
  simp only [bind]
  by_cases typed : isSymbol input .colon
  · simp only [typed, if_true]
    have valid := FunctionParameterInternals.namedParameterTail_validFor marker.span
      (some marker.span) name (SourceSpan.cover marker.span name.span)
      input inputValid markerValid (by simp [markerValid]) nameValid spanValid
      firstFound rfl firstBefore
    exact mappedFunctionParameter_validFor _ valid
  · simp only [typed, Bool.false_eq_true, if_false]
    have valid := FunctionParameterInternals.errorParameter_validFor
      (SourceSpan.cover marker.span name.span)
      .comptimeParameterRequiresType input inputValid spanValid
    exact mappedFunctionParameter_validFor _ valid

theorem ordinaryLambdaParameter_validFor :
    ordinaryLambdaParameter.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold ordinaryLambdaParameter
  simp only [bind]
  cases nameResult : identifier .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := identifier_validFor .parameter input inputValid
      rw [nameResult] at valid
      exact valid
  | ok name afterName =>
      have nameReply := identifier_validFor .parameter input inputValid
      rw [nameResult] at nameReply
      simp only
      rcases identifier_ok_state_shape .parameter nameResult with
        ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
      have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
      have nameAtAfter : afterName.tokens[input.cursor]? = some nameToken := by
        simpa [nameTokens] using nameAt
      have nameValid : name.span.ValidFor afterName.file := by
        simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
        let diagnostic : ParseDiagnostic := {
          span := name.span
          kind := .constraintViolation .comptimeUsedAsParameterName
        }
        change (ordinaryLambdaParameterTail name
          (afterName.emit diagnostic)).ValidFor input LambdaParameter.ValidFor
        have emitted := nameReply.2.1.emit_validFor diagnostic nameValid
        exact (ordinaryLambdaParameterTail_validFor name
          (afterName.emit diagnostic) emitted
          (by simpa [State.emit] using nameValid)
          (by simpa [State.emit] using nameAtAfter) nameSpan
          (by simp [State.emit, nameCursor])).of_file_eq
            (by simpa [State.emit] using nameReply.2.2)
      · simp only [warned]
        exact (ordinaryLambdaParameterTail_validFor name afterName
          nameReply.2.1 nameValid nameAtAfter nameSpan
          (by simp [nameCursor])).of_file_eq nameReply.2.2

theorem comptimeLambdaParameter_validFor :
    comptimeLambdaParameter.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold comptimeLambdaParameter
  simp only [bind]
  cases markerResult : contextual .comptime .parameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at valid
      exact valid
  | ok marker afterMarker =>
      have markerReply := contextual_validFor .comptime .parameter input inputValid
      rw [markerResult] at markerReply
      simp only
      cases nameResult : identifier .parameter afterMarker with
      | invariant error => trivial
      | reject failure rejected =>
          have valid := identifier_validFor .parameter afterMarker markerReply.2.1
          rw [nameResult] at valid
          exact valid.of_file_eq markerReply.2.2
      | ok name afterName =>
          have nameReply := identifier_validFor .parameter afterMarker markerReply.2.1
          rw [nameResult] at nameReply
          simp only
          have markerShape := acceptToken_ok_state_shape
            (.contextual .comptime) .parameter (·.isContextual .comptime)
            markerResult
          rcases identifier_ok_state_shape .parameter nameResult with
            ⟨nameToken, nameFound, nameSpan, nameTokens, nameCursor⟩
          have markerAt := State.getElem?_eq_some_of_peek?_eq_some markerShape.1
          have markerAtAfter : afterName.tokens[input.cursor]? = some marker := by
            simpa [nameTokens, markerShape.2] using markerAt
          have nameAt := State.getElem?_eq_some_of_peek?_eq_some nameFound
          have nameAtInput : input.tokens[afterMarker.cursor]? = some nameToken := by
            simpa [markerShape.2] using nameAt
          have beforeName := inputValid.token_end_le_token_start_of_getElem?_lt
            markerAt nameAtInput (by simp [markerShape.2])
          have markerValid : marker.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2, markerReply.2.2]
              using markerReply.1
          have nameValid : name.span.ValidFor afterName.file := by
            simpa only [Located.ValidFor, nameReply.2.2] using nameReply.1
          have spanValid : (SourceSpan.cover marker.span name.span).ValidFor
              afterName.file := SourceSpan.cover_validFor markerValid nameValid
            (Nat.le_trans markerValid.2.1 (Nat.le_trans
              (by simpa [nameSpan] using beforeName) nameValid.2.1))
          exact (comptimeLambdaParameterTail_validFor marker name afterName
            nameReply.2.1 markerValid nameValid spanValid markerAtAfter
            (by simp [markerShape.2, nameCursor]; omega)).of_file_eq
              (nameReply.2.2.trans markerReply.2.2)

theorem lambdaParameterCore_validFor :
    lambdaParameterCore.ValidFor LambdaParameter.ValidFor := by
  intro input inputValid
  unfold lambdaParameterCore
  split
  · simp only [Bool.and_true]
    split
    · exact comptimeLambdaParameter_validFor input inputValid
    · exact ordinaryLambdaParameter_validFor input inputValid
  · simp only [Bool.and_false, Bool.false_eq_true, if_false]
    exact ordinaryLambdaParameter_validFor input inputValid

theorem recoverLambdaParameter_validFor (input : State)
    (inputValid : input.ValidFor) :
    (recoverLambdaParameter input).ValidFor input LambdaParameter.ValidFor := by
  unfold recoverLambdaParameter
  cases parsed : FunctionParameterInternals.recoverParameter input with
  | invariant error => trivial
  | reject failure rejected =>
      have valid := FunctionParameterInternals.recoverParameter_validFor input inputValid
      rw [parsed] at valid
      exact valid
  | ok recovered final =>
      have valid := FunctionParameterInternals.recoverParameter_validFor input inputValid
      rw [parsed] at valid
      exact ⟨.error valid.1.span_valid, valid.2.1, valid.2.2⟩

end LambdaParameterInternals

/-- Named parameters retain provenance through parsing and recovery. -/
theorem namedParameter_validFor :
    namedParameter.ValidFor FunctionParameter.ValidFor := by
  intro input inputValid
  unfold namedParameter
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter next =>
      have valid := FunctionParameterInternals.namedParameterCore_validFor
        input inputValid
      rw [coreResult] at valid
      exact valid
  | invariant error => trivial
  | reject failure failedState =>
      have coreValid :=
        FunctionParameterInternals.namedParameterCore_validFor input inputValid
      rw [coreResult] at coreValid
      have coreShape :=
        FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
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
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)).ValidFor input
            FunctionParameter.ValidFor
      split
      · exact ⟨coreValid.1, rewoundValid, rewoundFile⟩
      · have failureValid : failure.span.ValidFor rewound.file := by
          simpa [rewound, coreValid.2.2] using coreValid.1
        have emittedValid := rewoundValid.emit_validFor failure.toDiagnostic
          (failure.toDiagnostic_span_validFor failureValid)
        exact (FunctionParameterInternals.recoverParameter_validFor
          (rewound.emit failure.toDiagnostic) emittedValid).of_file_eq
            (by simpa [State.emit] using rewoundFile)

/-- Function-parameter parsing preserves every ordinary token window. -/
theorem namedParameter_preservesTokenWindow :
    Parser.PreservesTokenWindow namedParameter := by
  intro input
  unfold namedParameter
  have coreShape :=
    FunctionParameterInternals.namedParameterCore_preservesTokenWindow input
  cases coreResult : FunctionParameterInternals.namedParameterCore input with
  | ok parameter next => rw [coreResult] at coreShape; exact coreShape
  | invariant error => trivial
  | reject failure failedState =>
      rw [coreResult] at coreShape
      let rewound : State := { failedState with cursor := input.cursor }
      have rewoundShape : rewound.tokens = input.tokens ∧
          rewound.window = input.window := ⟨by simp [rewound, coreShape.1],
        by simp [rewound, coreShape.2]⟩
      change (if rewound.atEnd || isSymbol rewound .comma ||
          isSymbol rewound .rightParen then Reply.reject failure rewound
        else FunctionParameterInternals.recoverParameter
          (rewound.emit failure.toDiagnostic)).PreservesTokenWindow input
      split
      · exact rewoundShape
      · exact (FunctionParameterInternals.recoverParameter_preservesTokenWindow
          (rewound.emit failure.toDiagnostic)).trans (by
            simpa [State.emit] using rewoundShape)

/-- Successful function-parameter parsing retains the token carrier. -/
theorem namedParameter_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess namedParameter :=
  namedParameter_preservesTokenWindow.preservesTokensOnSuccess

end Solcore.Syntax.Parser
