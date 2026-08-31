import Solcore.Syntax.Parser.PrimitiveProperties

/-! Compositional validity contracts for canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax

namespace Located

/-- A located value has source provenance valid for the supplied file. -/
def ValidFor {α : Type} (file : SourceFile) (value : Located α) : Prop :=
  value.span.ValidFor file

end Located

namespace Parser

namespace Reply

/--
Ordinary parser results preserve source provenance and state validity.
Invariant failures remain admissible because they are outside source-result
semantics and are handled by the total public parser boundary.
-/
def ValidFor {α : Type} (reply : Reply α) (input : State)
    (valueValid : SourceFile → α → Prop) : Prop :=
  match reply with
  | .ok value next =>
      valueValid input.file value ∧ next.ValidFor ∧
        next.file = input.file
  | .reject failure next =>
      failure.span.ValidFor input.file ∧ next.ValidFor ∧
        next.file = input.file
  | .invariant _ => True

namespace ValidFor

/-- Change only the presentation of an input file known to be equal. -/
theorem of_file_eq {α : Type} {reply : Reply α} {input other : State}
    {valueValid : SourceFile → α → Prop}
    (valid : reply.ValidFor input valueValid)
    (fileEq : input.file = other.file) :
    reply.ValidFor other valueValid := by
  cases reply <;> simp [Reply.ValidFor, fileEq] at valid ⊢ <;>
    exact valid

/-- Transport only the successful value predicate of a reply contract. -/
theorem mono {α : Type} {reply : Reply α} {input : State}
    {first second : SourceFile → α → Prop}
    (valid : reply.ValidFor input first)
    (implies : ∀ file value, first file value → second file value) :
    reply.ValidFor input second := by
  cases reply with
  | ok value next =>
      exact ⟨implies input.file value valid.1, valid.2.1, valid.2.2⟩
  | reject failure next => exact valid
  | invariant error => trivial

end ValidFor

end Reply

namespace Parser

/-- A parser satisfies its result contract for every valid input state. -/
def ValidFor {α : Type} (parser : Parser α)
    (valueValid : SourceFile → α → Prop) : Prop :=
  ∀ input, input.ValidFor → (parser input).ValidFor input valueValid

/-- Successful parsing preserves the immutable token carrier. -/
def PreservesTokensOnSuccess {α : Type} (parser : Parser α) : Prop :=
  ∀ input value next, parser input = .ok value next →
    next.tokens = input.tokens

/-- Build a parser contract from its ordinary success and rejection branches. -/
theorem validFor_of_ok_reject {α : Type} (parser : Parser α)
    (valueValid : SourceFile → α → Prop)
    (okValid : ∀ input, input.ValidFor → ∀ value next,
      parser input = .ok value next →
      valueValid input.file value ∧ next.ValidFor ∧
        next.file = input.file)
    (rejectValid : ∀ input, input.ValidFor → ∀ failure next,
      parser input = .reject failure next →
      failure.span.ValidFor input.file ∧ next.ValidFor ∧
        next.file = input.file) :
    parser.ValidFor valueValid := by
  intro input inputValid
  cases result : parser input with
  | ok value next => exact okValid input inputValid value next result
  | reject failure next =>
      exact rejectValid input inputValid failure next result
  | invariant error => trivial

/-- Pure parsers preserve a valid input state. -/
theorem pure_validFor {α : Type} (value : α)
    (valueValid : SourceFile → α → Prop)
    (validValue : ∀ file, valueValid file value) :
    (pure value : Parser α).ValidFor valueValid := by
  intro input inputValid
  exact ⟨validValue input.file, inputValid, rfl⟩

/--
Sequential composition may use the first value's validity evidence when
establishing the continuation at the actual intermediate state.
-/
theorem bind_validFor_of_value {α β : Type} {first : Parser α}
    {next : α → Parser β}
    {firstValueValid : SourceFile → α → Prop}
    {resultValid : SourceFile → β → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (nextValid : ∀ value input, input.ValidFor →
      firstValueValid input.file value →
      (next value input).ValidFor input resultValid) :
    (first >>= next).ValidFor resultValid := by
  intro input inputValid
  have firstResult := firstValid input inputValid
  have binding : (first >>= next) input =
      match first input with
      | .ok value afterFirst => next value afterFirst
      | .reject failure rejected => .reject failure rejected
      | .invariant error => .invariant error := by
    rfl
  cases result : first input with
  | ok value afterFirst =>
      rw [result] at firstResult
      rw [binding, result]
      have valueValidAfter : firstValueValid afterFirst.file value := by
        simpa [firstResult.2.2] using firstResult.1
      exact (nextValid value afterFirst firstResult.2.1
        valueValidAfter).of_file_eq firstResult.2.2
  | reject failure rejected =>
      rw [result] at firstResult
      rw [binding, result]
      exact firstResult
  | invariant error =>
      rw [binding, result]
      trivial

/-- Sequential composition preserves the continuation's result contract. -/
theorem bind_validFor {α β : Type} {first : Parser α}
    {next : α → Parser β}
    {firstValueValid : SourceFile → α → Prop}
    {resultValid : SourceFile → β → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (nextValid : ∀ value, (next value).ValidFor resultValid) :
    (first >>= next).ValidFor resultValid := by
  apply bind_validFor_of_value firstValid
  intro value input inputValid _valueValid
  exact nextValid value input inputValid

/-- Transactional ordered choice preserves a shared result contract. -/
theorem orElse_validFor {α : Type} {first second : Parser α}
    {valueValid : SourceFile → α → Prop}
    (firstValid : first.ValidFor valueValid)
    (secondValid : second.ValidFor valueValid) :
    (orElse first second).ValidFor valueValid := by
  intro input inputValid
  have firstResult := firstValid input inputValid
  unfold orElse
  cases result : first input with
  | ok value next =>
      rw [result] at firstResult
      exact firstResult
  | reject failure rejected => exact secondValid input inputValid
  | invariant error => trivial

/-- Transport a parser's successful value predicate pointwise. -/
theorem ValidFor.mono {α : Type} {parser : Parser α}
    {first second : SourceFile → α → Prop}
    (valid : parser.ValidFor first)
    (implies : ∀ file value, first file value → second file value) :
    parser.ValidFor second := by
  intro input inputValid
  exact (valid input inputValid).mono implies

end Parser

namespace State

/-- A parser-returned state remains valid and owned by the input file. -/
def ValueValidFor (file : SourceFile) (state : State) : Prop :=
  state.ValidFor ∧ state.file = file

end State

/-- Reading the current state preserves it as both value and continuation. -/
theorem getState_validFor :
    getState.ValidFor State.ValueValidFor := by
  intro input inputValid
  exact ⟨⟨inputValid, rfl⟩, inputValid, rfl⟩

/-- A validity- and file-preserving update defines a valid state parser. -/
theorem modifyState_validFor (update : State → State)
    (preserves : ∀ input, input.ValidFor →
      (update input).ValidFor ∧ (update input).file = input.file) :
    (modifyState update).ValidFor (fun _ _ => True) := by
  intro input inputValid
  unfold modifyState Reply.ValidFor
  exact ⟨trivial, (preserves input inputValid).1,
    (preserves input inputValid).2⟩

/-- Emit one diagnostic known valid for this concrete input state. -/
theorem emitDiagnostic_reply_validFor {input : State}
    (inputValid : input.ValidFor) (diagnostic : ParseDiagnostic)
    (diagnosticValid : diagnostic.span.ValidFor input.file) :
    (emitDiagnostic diagnostic input).ValidFor input (fun _ _ => True) := by
  unfold emitDiagnostic modifyState Reply.ValidFor
  exact ⟨trivial, inputValid.emit_validFor diagnostic diagnosticValid, rfl⟩

/-- Emit a fixed diagnostic valid for every admitted input file. -/
theorem emitDiagnostic_validFor (diagnostic : ParseDiagnostic)
    (diagnosticValid : ∀ input : State, input.ValidFor →
      diagnostic.span.ValidFor input.file) :
    (emitDiagnostic diagnostic).ValidFor (fun _ _ => True) := by
  intro input inputValid
  exact emitDiagnostic_reply_validFor inputValid diagnostic
    (diagnosticValid input inputValid)

/-- Committing a valid failure diagnostic preserves state validity and file. -/
theorem emitFailure_validFor {state : State} (stateValid : state.ValidFor)
    (failure : Failure) (failureValid : failure.span.ValidFor state.file) :
    (emitFailure failure state).ValidFor ∧
      (emitFailure failure state).file = state.file := by
  refine ⟨?_, rfl⟩
  apply stateValid.emit_validFor
  exact failure.toDiagnostic_span_validFor failureValid

/-- Generic token acceptance satisfies the located-span contract. -/
theorem acceptToken_validFor (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) :
    (acceptToken expected context accepts).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact acceptToken_ok_validFor inputValid expected context accepts result
  · intro input inputValid failure next result
    exact acceptToken_reject_validFor inputValid expected context accepts result

theorem keyword_validFor (value : HardKeyword) (context : ParseContext) :
    (keyword value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.keyword value) context
    (· == .keyword value)

theorem symbol_validFor (value : Symbol) (context : ParseContext) :
    (symbol value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.symbol value) context
    (· == .symbol value)

theorem contextual_validFor (value : ContextualKeyword)
    (context : ParseContext) :
    (contextual value context).ValidFor Located.ValidFor := by
  exact acceptToken_validFor (.contextual value) context
    (·.isContextual value)

theorem rawIdentifier_validFor (context : ParseContext) :
    (rawIdentifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact rawIdentifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact rawIdentifier_reject_validFor inputValid context result

theorem identifier_validFor (context : ParseContext) :
    (identifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact identifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact identifier_reject_validFor inputValid context result

theorem yulIdentifier_validFor (context : ParseContext) :
    (yulIdentifier context).ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact yulIdentifier_ok_validFor inputValid context result
  · intro input inputValid failure next result
    exact yulIdentifier_reject_validFor inputValid context result

theorem coreLiteral_validFor :
    coreLiteral.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact coreLiteral_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact coreLiteral_reject_validFor inputValid result

theorem booleanIdentifier_validFor :
    booleanIdentifier.ValidFor Located.ValidFor := by
  apply Parser.validFor_of_ok_reject
  · intro input inputValid value next result
    exact booleanIdentifier_ok_validFor inputValid result
  · intro input inputValid failure next result
    exact booleanIdentifier_reject_validFor inputValid result

end Parser

end Solcore.Syntax
