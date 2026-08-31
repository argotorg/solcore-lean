import Solcore.Syntax.Parser.Literal

/-! Provenance and state-preservation laws for primitive token consumers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem advanceAfterPeek_validFor {state : State} {token : Token}
    (valid : state.ValidFor) (found : state.peek? = some token) :
    token.span.ValidFor state.file ∧
      ({ state with cursor := state.cursor + 1 } : State).ValidFor ∧
      ({ state with cursor := state.cursor + 1 } : State).file = state.file := by
  refine ⟨valid.peek?_span_validFor found, ?_, rfl⟩
  apply valid.advance?_validFor (token := token)
  unfold State.advance?
  rw [found]
  rfl

/-- `rejectAt` retains a valid state and uses its valid current span. -/
theorem rejectAt_reject_validFor {α : Type} {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (expected : NonemptyList ParseExpectation) (context : ParseContext)
    (result : rejectAt (α := α) state expected context =
      .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rejectAt at result
  cases result
  exact ⟨valid.currentSpan_validFor, valid, rfl⟩

/-- Accepted tokens have valid spans and advance to a valid state. -/
theorem acceptToken_ok_validFor {state next : State} {token : Token}
    (valid : state.ValidFor) (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state = .ok token next) :
    token.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      · cases result
        exact advanceAfterPeek_validFor valid found
      · unfold rejectAt at result
        contradiction

/-- Successful token acceptance returns the current token and increments only the cursor. -/
theorem acceptToken_ok_state_shape {state next : State} {token : Token}
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state = .ok token next) :
    state.peek? = some token ∧ next = { state with cursor := state.cursor + 1 } := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some current =>
      simp only [found] at result
      split at result
      · cases result
        exact ⟨rfl, rfl⟩
      · unfold rejectAt at result
        contradiction

/-- Successful symbol parsing has the generic token-consumer state shape. -/
theorem symbol_ok_state_shape {state next : State} {token : Token}
    (value : Symbol) (context : ParseContext)
    (result : symbol value context state = .ok token next) :
    state.peek? = some token ∧ next = { state with cursor := state.cursor + 1 } := by
  exact acceptToken_ok_state_shape (.symbol value) context
    (· == .symbol value) result

/-- Rejected token acceptance retains a valid failure span and state. -/
theorem acceptToken_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool)
    (result : acceptToken expected context accepts state =
      .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold acceptToken at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some current =>
      simp only [found] at result
      split at result
      · contradiction
      · exact rejectAt_reject_validFor valid _ _ result

/-- Raw ordinary identifiers preserve span provenance and state validity. -/
theorem rawIdentifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : rawIdentifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rawIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case identifier text =>
        cases result
        exact advanceAfterPeek_validFor valid found

/-- Raw ordinary-identifier rejection preserves failure provenance and state. -/
theorem rawIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : rawIdentifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold rawIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      contradiction

/-- Canonical identifier acceptance, including hyphen reporting, is valid. -/
theorem identifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : identifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | reject failure rejected =>
      simp only [identifier, raw] at result
      contradiction
  | ok parsed afterName =>
      simp only [identifier, raw] at result
      have parsedValid := rawIdentifier_ok_validFor valid context raw
      split at result
      · cases result
        refine ⟨parsedValid.1, ?_, parsedValid.2.2⟩
        apply parsedValid.2.1.emit_validFor
        simpa [parsedValid.2.2] using parsedValid.1
      · cases result
        exact parsedValid

/-- Successful identifier parsing exposes its input token and cursor advance. -/
theorem identifier_ok_state_shape {state next : State} {name : Identifier}
    (context : ParseContext)
    (result : identifier context state = .ok name next) :
    ∃ token,
      state.peek? = some token ∧
        token.span = name.span ∧
        next.tokens = state.tokens ∧
        next.cursor = state.cursor + 1 := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | reject failure rejected =>
      simp only [identifier, raw] at result
      contradiction
  | ok parsed afterName =>
      simp only [identifier, raw] at result
      have rawShape : ∃ token,
          state.peek? = some token ∧
            token.span = parsed.span ∧
            afterName.tokens = state.tokens ∧
            afterName.cursor = state.cursor + 1 := by
        unfold rawIdentifier at raw
        cases found : state.peek? with
        | none =>
            simp only [found] at raw
            unfold rejectAt at raw
            contradiction
        | some token =>
            rcases token with ⟨span, kind⟩
            cases kind <;> simp only [found] at raw
            all_goals try { unfold rejectAt at raw; contradiction }
            case identifier text =>
              cases raw
              exact ⟨_, rfl, rfl, rfl, rfl⟩
      rcases rawShape with
        ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
      split at result
      · cases result
        exact ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩
      · cases result
        exact ⟨token, tokenFound, tokenSpan, tokensEq, cursorEq⟩

/-- Canonical identifier rejection is exactly valid raw rejection. -/
theorem identifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : identifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  cases raw : rawIdentifier context state with
  | invariant error =>
      simp only [identifier, raw] at result
      contradiction
  | ok name afterName =>
      simp only [identifier, raw] at result
      split at result <;> contradiction
  | reject rejected rejectedState =>
      simp only [identifier, raw] at result
      cases result
      exact rawIdentifier_reject_validFor valid context raw

/-- Yul identifiers preserve span provenance and state validity. -/
theorem yulIdentifier_ok_validFor {state next : State} {name : Identifier}
    (valid : state.ValidFor) (context : ParseContext)
    (result : yulIdentifier context state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case yulIdentifier text =>
        cases result
        exact advanceAfterPeek_validFor valid found

/-- Yul-identifier rejection preserves failure provenance and state. -/
theorem yulIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor) (context : ParseContext)
    (result : yulIdentifier context state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold yulIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      contradiction

/-- Core literal acceptance preserves its located span and state validity. -/
theorem coreLiteral_ok_validFor {state next : State} {literal : CoreLiteral}
    (valid : state.ValidFor)
    (result : coreLiteral state = .ok literal next) :
    literal.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold coreLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      all_goals cases result
      all_goals exact advanceAfterPeek_validFor valid found

/-- Core literal rejection preserves failure provenance and state validity. -/
theorem coreLiteral_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (result : coreLiteral state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold coreLiteral at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      all_goals contradiction

/-- Boolean builtin acceptance preserves its located span and state validity. -/
theorem booleanIdentifier_ok_validFor {state next : State}
    {name : Identifier} (valid : state.ValidFor)
    (result : booleanIdentifier state = .ok name next) :
    name.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold booleanIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      unfold rejectAt at result
      contradiction
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { unfold rejectAt at result; contradiction }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { unfold rejectAt at result; contradiction }
        all_goals cases result
        all_goals exact advanceAfterPeek_validFor valid found

/-- Boolean builtin rejection preserves failure provenance and state validity. -/
theorem booleanIdentifier_reject_validFor {state next : State}
    {failure : Failure} (valid : state.ValidFor)
    (result : booleanIdentifier state = .reject failure next) :
    failure.span.ValidFor state.file ∧ next.ValidFor ∧
      next.file = state.file := by
  unfold booleanIdentifier at result
  cases found : state.peek? with
  | none =>
      simp only [found] at result
      exact rejectAt_reject_validFor valid _ _ result
  | some token =>
      rcases token with ⟨span, kind⟩
      cases kind <;> simp only [found] at result
      all_goals try { exact rejectAt_reject_validFor valid _ _ result }
      case keyword keyword =>
        cases keyword <;> simp only at result
        all_goals try { exact rejectAt_reject_validFor valid _ _ result }
        all_goals contradiction

end Solcore.Syntax.Parser
