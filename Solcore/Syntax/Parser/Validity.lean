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

/-- Successful parsing never moves the cursor backwards. -/
def CursorMonotoneOnSuccess {α : Type} (parser : Parser α) : Prop :=
  ∀ input value next, parser input = .ok value next →
    input.cursor ≤ next.cursor

/--
A successful located parser starts its result at the current input token.
Requiring the token itself, rather than only `currentSpan`, excludes a
spurious success at the end of an input window.
-/
def StartsAtCurrentTokenOnSuccess {α : Type} (parser : Parser α)
    (spanOf : α → SourceSpan) : Prop :=
  ∀ input value next, parser input = .ok value next →
    ∃ token, input.peek? = some token ∧
      token.span.startByte = (spanOf value).startByte

/-- A pure parser leaves the token carrier unchanged. -/
theorem pure_preservesTokensOnSuccess {α : Type} (value : α) :
    PreservesTokensOnSuccess (pure value : Parser α) := by
  intro input result next parsed
  cases parsed
  rfl

/-- A pure parser leaves the cursor in place. -/
theorem pure_cursorMonotoneOnSuccess {α : Type} (value : α) :
    CursorMonotoneOnSuccess (pure value : Parser α) := by
  intro input result next parsed
  cases parsed
  exact Nat.le_refl _

/-- Sequential composition preserves the carrier when both stages do. -/
theorem bind_preservesTokensOnSuccess {α β : Type} {first : Parser α}
    {next : α → Parser β}
    (firstPreserves : PreservesTokensOnSuccess first)
    (nextPreserves : ∀ value, PreservesTokensOnSuccess (next value)) :
    PreservesTokensOnSuccess (first >>= next) := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      exact (nextPreserves firstValue afterFirst value final parsed).trans
        (firstPreserves input firstValue afterFirst firstResult)
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Sequential composition is monotone when both stages are monotone. -/
theorem bind_cursorMonotoneOnSuccess {α β : Type} {first : Parser α}
    {next : α → Parser β}
    (firstMonotone : CursorMonotoneOnSuccess first)
    (nextMonotone : ∀ value, CursorMonotoneOnSuccess (next value)) :
    CursorMonotoneOnSuccess (first >>= next) := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      exact Nat.le_trans (firstMonotone input firstValue afterFirst firstResult)
        (nextMonotone firstValue afterFirst value final parsed)
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/--
A bind starts with its first parser when every successful continuation keeps
the first value's starting byte. This is the common shape of parsers that
construct an outer covering span from a leading marker.
-/
theorem bind_startsAtCurrentTokenOnSuccess_of_first
    {α β : Type} {first : Parser α} {next : α → Parser β}
    {firstSpan : α → SourceSpan} {resultSpan : β → SourceSpan}
    (firstStarts : StartsAtCurrentTokenOnSuccess first firstSpan)
    (continuationKeepsStart : ∀ firstValue input value final,
      next firstValue input = .ok value final →
      (firstSpan firstValue).startByte = (resultSpan value).startByte) :
    StartsAtCurrentTokenOnSuccess (first >>= next) resultSpan := by
  intro input value final parsed
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      rcases firstStarts input firstValue afterFirst firstResult with
        ⟨token, found, firstStart⟩
      exact ⟨token, found,
        firstStart.trans (continuationKeepsStart _ _ _ _ parsed)⟩
  | reject failure rejected =>
      simp only [firstResult] at parsed
      cases parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves a shared carrier contract. -/
theorem orElse_preservesTokensOnSuccess {α : Type}
    {first second : Parser α}
    (firstPreserves : PreservesTokensOnSuccess first)
    (secondPreserves : PreservesTokensOnSuccess second) :
    PreservesTokensOnSuccess (orElse first second) := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have preserved :=
        firstPreserves input firstValue afterFirst firstResult
      cases parsed
      exact preserved
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondPreserves input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves cursor monotonicity. -/
theorem orElse_cursorMonotoneOnSuccess {α : Type}
    {first second : Parser α}
    (firstMonotone : CursorMonotoneOnSuccess first)
    (secondMonotone : CursorMonotoneOnSuccess second) :
    CursorMonotoneOnSuccess (orElse first second) := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have monotone := firstMonotone input firstValue afterFirst firstResult
      cases parsed
      exact monotone
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondMonotone input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

/-- Transactional ordered choice preserves a shared result-start contract. -/
theorem orElse_startsAtCurrentTokenOnSuccess {α : Type}
    {first second : Parser α} {spanOf : α → SourceSpan}
    (firstStarts : StartsAtCurrentTokenOnSuccess first spanOf)
    (secondStarts : StartsAtCurrentTokenOnSuccess second spanOf) :
    StartsAtCurrentTokenOnSuccess (orElse first second) spanOf := by
  intro input value next parsed
  unfold orElse at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      simp only [firstResult] at parsed
      have starts := firstStarts input firstValue afterFirst firstResult
      cases parsed
      exact starts
  | reject failure rejected =>
      simp only [firstResult] at parsed
      exact secondStarts input value next parsed
  | invariant error =>
      simp only [firstResult] at parsed
      cases parsed

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

/-- Reading the current state leaves the token carrier unchanged. -/
theorem getState_preservesTokensOnSuccess :
    Parser.PreservesTokensOnSuccess getState := by
  intro input value next parsed
  unfold getState at parsed
  cases parsed
  rfl

/-- Reading the current state leaves the cursor in place. -/
theorem getState_cursorMonotoneOnSuccess :
    Parser.CursorMonotoneOnSuccess getState := by
  intro input value next parsed
  unfold getState at parsed
  cases parsed
  exact Nat.le_refl _

/-- A validity- and file-preserving update defines a valid state parser. -/
theorem modifyState_validFor (update : State → State)
    (preserves : ∀ input, input.ValidFor →
      (update input).ValidFor ∧ (update input).file = input.file) :
    (modifyState update).ValidFor (fun _ _ => True) := by
  intro input inputValid
  unfold modifyState Reply.ValidFor
  exact ⟨trivial, (preserves input inputValid).1,
    (preserves input inputValid).2⟩

/-- A state update preserves the carrier when its update function does. -/
theorem modifyState_preservesTokensOnSuccess (update : State → State)
    (preserves : ∀ input, (update input).tokens = input.tokens) :
    Parser.PreservesTokensOnSuccess (modifyState update) := by
  intro input value next parsed
  unfold modifyState at parsed
  cases parsed
  exact preserves input

/-- A state update is monotone when its update function is monotone. -/
theorem modifyState_cursorMonotoneOnSuccess (update : State → State)
    (monotone : ∀ input, input.cursor ≤ (update input).cursor) :
    Parser.CursorMonotoneOnSuccess (modifyState update) := by
  intro input value next parsed
  unfold modifyState at parsed
  cases parsed
  exact monotone input

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

/-- Adding a diagnostic does not alter the immutable token carrier. -/
theorem emitDiagnostic_preservesTokensOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.PreservesTokensOnSuccess (emitDiagnostic diagnostic) := by
  apply modifyState_preservesTokensOnSuccess
  intro input
  rfl

/-- Adding a diagnostic leaves the cursor in place. -/
theorem emitDiagnostic_cursorMonotoneOnSuccess
    (diagnostic : ParseDiagnostic) :
    Parser.CursorMonotoneOnSuccess (emitDiagnostic diagnostic) := by
  apply modifyState_cursorMonotoneOnSuccess
  intro input
  exact Nat.le_refl _

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
