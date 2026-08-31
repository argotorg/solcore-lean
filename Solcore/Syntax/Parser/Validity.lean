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

end ValidFor

end Reply

namespace Parser

/-- A parser satisfies its result contract for every valid input state. -/
def ValidFor {α : Type} (parser : Parser α)
    (valueValid : SourceFile → α → Prop) : Prop :=
  ∀ input, input.ValidFor → (parser input).ValidFor input valueValid

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

/-- Sequential composition preserves the continuation's result contract. -/
theorem bind_validFor {α β : Type} {first : Parser α}
    {next : α → Parser β}
    {firstValueValid : SourceFile → α → Prop}
    {resultValid : SourceFile → β → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (nextValid : ∀ value, (next value).ValidFor resultValid) :
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
      exact (nextValid value afterFirst firstResult.2.1).of_file_eq
        firstResult.2.2
  | reject failure rejected =>
      rw [result] at firstResult
      rw [binding, result]
      exact firstResult
  | invariant error =>
      rw [binding, result]
      trivial

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

end Parser

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
