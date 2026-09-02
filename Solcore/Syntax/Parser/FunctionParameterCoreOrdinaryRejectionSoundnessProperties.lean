import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties
import Solcore.Syntax.Parser.FunctionParameterCoreOrdinarySuccessSoundnessProperties

/-! Executable ordinary-rejection reflection for `namedParameterCore`. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem contextual_eq_ok_of_present
    (value : ContextualKeyword) (context : ParseContext) {input : State}
    (present : isContextual input value = true) :
    ∃ token, contextual value context input =
      .ok token { input with cursor := input.cursor + 1 } := by
  unfold isContextual State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      simp only [found, Option.map_some] at present
      refine ⟨token, ?_⟩
      unfold contextual acceptToken
      simp only [found, present, ↓reduceIte]

private theorem identifier_exists_ok_of_offset_identifier
    {input : State}
    (present : (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true) :
    ∃ name output, identifier .parameter
      { input with cursor := input.cursor + 1 } = .ok name output := by
  unfold State.peekOffsetKind? at present
  cases found : input.peekOffset? 1 with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found, Option.map_some] at present
      all_goals try contradiction
      case identifier text =>
        let afterMarker : State := { input with cursor := input.cursor + 1 }
        have current : afterMarker.peek? = some {
            span
            value := TokenKind.identifier text
          } := by
          simpa only [afterMarker, State.peek?, State.peekOffset?, Nat.add_comm]
            using found
        have rawResult : rawIdentifier .parameter afterMarker = .ok
            { span, value := text }
            { afterMarker with cursor := afterMarker.cursor + 1 } := by
          unfold rawIdentifier
          rw [current]
        by_cases warned : text.toList.contains '-'
        · exact ⟨{ span, value := text },
            ({ afterMarker with cursor := afterMarker.cursor + 1 }).emit {
              span
              kind := .invalidIdentifierHyphen text
            }, by
              unfold identifier
              rw [rawResult]
              simp only [warned, if_true]⟩
        · have warnedFalse : text.toList.contains '-' = false :=
            Bool.eq_false_iff.mpr warned
          exact ⟨{ span, value := text },
            { afterMarker with cursor := afterMarker.cursor + 1 }, by
              unfold identifier
              rw [rawResult]
              simp only [warnedFalse, Bool.false_eq_true, if_false]⟩

private theorem comptimePrefixAbsent_of_core_false {input : State}
    (absent : (isContextual input .comptime &&
      match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = false) :
    DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
      input.declarativeRemainder := by
  rintro ⟨markerSpan, nameSpan, name, markerToken, nameToken⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span := markerSpan
      value := .identifier ContextualKeyword.comptime.spelling
    } at markerToken
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    (input.cursor + 1) {
      span := nameSpan
      value := .identifier name
    } at nameToken
  have markerPresent : isContextual input .comptime = true := by
    unfold isContextual State.peekKind? State.peek?
    simp only [markerToken.1, ↓reduceIte, markerToken.2, Option.map_some,
      TokenKind.isContextual]
    exact beq_iff_eq.mpr rfl
  have namePresent :
      (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true := by
    unfold State.peekOffsetKind? State.peekOffset?
    simp only [nameToken.1, ↓reduceIte, nameToken.2, Option.map_some]
  rw [markerPresent, namePresent] at absent
  contradiction

namespace FunctionParameterInternals

private theorem namedParameterTail_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    (start : SourceSpan) (marker : Option SourceSpan) (name : Identifier)
    (errorSpan : SourceSpan) {input rejected : State} {failure : Failure}
    (result : namedParameterTail start marker name errorSpan input =
      .reject failure rejected) :
    ∃ colonSpan afterColon,
      DeclarativeGrammar.ExactTokenParses (.symbol .colon)
        input.declarativeRemainder colonSpan afterColon ∧
      typeRejects afterColon rejected.declarativeRemainder := by
  unfold namedParameterTail getState at result
  simp only [bind] at result
  by_cases typed : isSymbol input .colon
  · rcases symbol_eq_ok_of_isSymbol_eq_true .colon .parameter typed with
      ⟨colon, colonResult⟩
    simp only [typed, if_true, colonResult] at result
    cases typeResult : typeExpr { input with cursor := input.cursor + 1 } with
    | invariant error => simp [typeResult] at result
    | reject typeFailure typeRejected =>
        simp only [typeResult] at result
        cases result
        exact ⟨colon.span, _,
          symbol_success_exactTokenParses .colon .parameter colonResult,
          typeRejectSound typeResult⟩
    | ok type afterType =>
        simp only [typeResult] at result
        unfold finishTypedParameter at result
        cases typeValue : type.value <;>
          simp [typeValue, emitDiagnostic, modifyState, bind, pure] at result
  · have typedFalse : isSymbol input .colon = false :=
      Bool.eq_false_iff.mpr typed
    simp only [typedFalse, Bool.false_eq_true, if_false] at result
    unfold errorParameter at result
    simp [emitDiagnostic, modifyState, bind, pure] at result

private theorem ordinaryNamedParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (prefixAbsent : DeclarativeGrammar.ComptimeParameterPrefixAbsentAt
      input.declarativeRemainder)
    (result : ordinaryNamedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold ordinaryNamedParameter at result
  simp only [bind] at result
  cases nameResult : identifier .parameter input with
  | invariant error => simp [nameResult] at result
  | reject nameFailure nameRejected =>
      simp only [nameResult] at result
      cases result
      exact .ordinaryName prefixAbsent
        (identifier_reject_sound .parameter nameResult)
  | ok name afterName =>
      simp only [nameResult] at result
      have nameParsed := identifier_success_sound .parameter nameResult
      by_cases warned : name.value == ContextualKeyword.comptime.spelling
      · simp only [warned, if_true, emitDiagnostic, modifyState]
          at result
        rcases namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name.span none name name.span result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan prefixAbsent nameParsed
          (by simpa [State.emit, State.declarativeRemainder] using colonParsed)
          typeRejected
      · have warnedFalse :
          (name.value == ContextualKeyword.comptime.spelling) = false :=
          Bool.eq_false_iff.mpr warned
        simp only [warnedFalse, Bool.false_eq_true, if_false] at result
        rcases namedParameterTail_reject_ordinary_sound typeRejects
          typeRejectSound name.span none name name.span result with
          ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
        exact .ordinaryType colonSpan prefixAbsent nameParsed colonParsed
          typeRejected

private theorem comptimeNamedParameter_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (markerPresent : isContextual input .comptime = true)
    (namePresent : (match input.peekOffsetKind? 1 with
      | some (.identifier _) => true
      | _ => false) = true)
    (result : comptimeNamedParameter input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  rcases contextual_eq_ok_of_present .comptime .parameter markerPresent with
    ⟨marker, markerResult⟩
  rcases identifier_exists_ok_of_offset_identifier namePresent with
    ⟨name, afterName, nameResult⟩
  unfold comptimeNamedParameter at result
  simp only [bind, markerResult, nameResult] at result
  rcases namedParameterTail_reject_ordinary_sound typeRejects typeRejectSound
      marker.span (some marker.span) name
        (SourceSpan.cover marker.span name.span) result with
    ⟨colonSpan, afterColon, colonParsed, typeRejected⟩
  exact .comptimeType marker.span colonSpan
    (contextual_success_exactTokenParses .comptime .parameter markerResult)
    (identifier_success_sound .parameter nameResult) colonParsed typeRejected

/-- Every executable Core rejection follows the exact selected relation. -/
theorem namedParameterCore_reject_ordinary_sound
    (typeRejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop)
    (typeRejectSound : ∀ {input rejected : State} {failure : Failure},
      typeExpr input = .reject failure rejected → typeRejects
        input.declarativeRemainder rejected.declarativeRemainder)
    {input rejected : State} {failure : Failure}
    (result : namedParameterCore input = .reject failure rejected) :
    DeclarativeGrammar.FunctionParameterCoreRejects typeRejects
      input.declarativeRemainder rejected.declarativeRemainder := by
  unfold namedParameterCore at result
  split at result
  · simp only [Bool.and_true] at result
    split at result
    · exact comptimeNamedParameter_reject_ordinary_sound typeRejects
        typeRejectSound (by simp_all) (by simp_all) result
    · exact ordinaryNamedParameter_reject_ordinary_sound typeRejects
        typeRejectSound (comptimePrefixAbsent_of_core_false (by simp_all))
          result
  · simp only [Bool.and_false, Bool.false_eq_true, if_false] at result
    exact ordinaryNamedParameter_reject_ordinary_sound typeRejects
      typeRejectSound (comptimePrefixAbsent_of_core_false (by simp_all))
        result

end FunctionParameterInternals
end Solcore.Syntax.Parser
