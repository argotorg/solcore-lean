import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.PrimitiveProperties

/-! Totality contracts for primitive token parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace Parser

/-- A parser has only ordinary success or rejection results. -/
def Ordinary {α : Type} (parser : Parser α) : Prop :=
  ∀ input,
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace Ordinary

/-- An ordinary parser cannot expose an internal invariant result. -/
theorem ne_invariant {α : Type} {parser : Parser α}
    (ordinary : Ordinary parser) (input : State)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases ordinary input with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Ordinary
end Parser

/-- Generic token acceptance is ordinary for every predicate and input. -/
theorem acceptToken_ordinary (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool) :
    Parser.Ordinary (acceptToken expected context accepts) := by
  intro input
  cases result : acceptToken expected context accepts input with
  | ok token next => exact Or.inl ⟨token, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold acceptToken at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          simp only [found] at result
          split at result <;> contradiction

theorem acceptToken_ne_invariant (expected : ParseExpectation)
    (context : ParseContext) (accepts : TokenKind → Bool)
    (input : State) (error : ParserInvariantError) :
    acceptToken expected context accepts input ≠ .invariant error :=
  (acceptToken_ordinary expected context accepts).ne_invariant input error

theorem keyword_ordinary (value : HardKeyword) (context : ParseContext) :
    Parser.Ordinary (keyword value context) :=
  acceptToken_ordinary (.keyword value) context (· == .keyword value)

theorem keyword_ne_invariant (value : HardKeyword) (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    keyword value context input ≠ .invariant error :=
  (keyword_ordinary value context).ne_invariant input error

theorem symbol_ordinary (value : Symbol) (context : ParseContext) :
    Parser.Ordinary (symbol value context) :=
  acceptToken_ordinary (.symbol value) context (· == .symbol value)

theorem symbol_ne_invariant (value : Symbol) (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    symbol value context input ≠ .invariant error :=
  (symbol_ordinary value context).ne_invariant input error

theorem contextual_ordinary (value : ContextualKeyword)
    (context : ParseContext) :
    Parser.Ordinary (contextual value context) :=
  acceptToken_ordinary (.contextual value) context (·.isContextual value)

theorem contextual_ne_invariant (value : ContextualKeyword)
    (context : ParseContext) (input : State) (error : ParserInvariantError) :
    contextual value context input ≠ .invariant error :=
  (contextual_ordinary value context).ne_invariant input error

/-- Raw ordinary-identifier recognition is ordinary on every input. -/
theorem rawIdentifier_ordinary (context : ParseContext) :
    Parser.Ordinary (rawIdentifier context) := by
  intro input
  cases result : rawIdentifier context input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold rawIdentifier at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result

theorem rawIdentifier_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    rawIdentifier context input ≠ .invariant error :=
  (rawIdentifier_ordinary context).ne_invariant input error

/-- Checked identifiers retain ordinary control flow through diagnostics. -/
theorem identifier_ordinary (context : ParseContext) :
    Parser.Ordinary (identifier context) := by
  intro input
  cases result : identifier context input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold identifier at result
      cases rawResult : rawIdentifier context input with
      | invariant rawError =>
          exact False.elim
            (rawIdentifier_ne_invariant context input rawError rawResult)
      | reject failure rejected => simp [rawResult] at result
      | ok name next =>
          simp only [rawResult] at result
          split at result <;> contradiction

theorem identifier_ne_invariant (context : ParseContext)
    (input : State) (error : ParserInvariantError) :
    identifier context input ≠ .invariant error :=
  (identifier_ordinary context).ne_invariant input error

private theorem identifier_cursor_lt_onSuccess (context : ParseContext)
    {input next : State} {name : Identifier}
    (result : identifier context input = .ok name next) :
    input.cursor < next.cursor := by
  rw [(identifier_ok_state_shape context result).choose_spec.2.2.2]
  simp

/-- Generic token acceptance can serve as a strict delimited element parser. -/
theorem acceptToken_elementTotalityContract
    (expected : ParseExpectation) (context : ParseContext)
    (accepts : TokenKind → Bool) :
    ElementTotalityContract (acceptToken expected context accepts) := {
  validFor := (acceptToken_validFor expected context accepts).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow :=
    acceptToken_preservesTokenWindow expected context accepts
  cursorLtOnSuccess :=
    acceptToken_cursor_lt_onSuccess expected context accepts
  invariantFree := fun input _ error =>
    acceptToken_ne_invariant expected context accepts input error
}

theorem keyword_elementTotalityContract
    (value : HardKeyword) (context : ParseContext) :
    ElementTotalityContract (keyword value context) :=
  acceptToken_elementTotalityContract (.keyword value) context
    (· == .keyword value)

theorem symbol_elementTotalityContract
    (value : Symbol) (context : ParseContext) :
    ElementTotalityContract (symbol value context) :=
  acceptToken_elementTotalityContract (.symbol value) context
    (· == .symbol value)

theorem contextual_elementTotalityContract
    (value : ContextualKeyword) (context : ParseContext) :
    ElementTotalityContract (contextual value context) :=
  acceptToken_elementTotalityContract (.contextual value) context
    (·.isContextual value)

/-- Canonical identifiers can instantiate every generic delimited loop. -/
theorem identifier_elementTotalityContract (context : ParseContext) :
    ElementTotalityContract (identifier context) := {
  validFor := (identifier_validFor context).mono (fun _ _ _ => trivial)
  preservesTokenWindow := identifier_preservesTokenWindow context
  cursorLtOnSuccess := identifier_cursor_lt_onSuccess context
  invariantFree := fun input _ error =>
    identifier_ne_invariant context input error
}

end Solcore.Syntax.Parser
