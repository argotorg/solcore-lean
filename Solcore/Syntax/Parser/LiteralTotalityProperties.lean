import Solcore.Syntax.Parser.LiteralProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Totality contracts for canonical literal token consumers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Core-literal recognition has no internal-failure path. -/
theorem coreLiteral_ordinary : Parser.Ordinary coreLiteral := by
  intro input
  cases result : coreLiteral input with
  | ok literal next => exact Or.inl ⟨literal, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold coreLiteral at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result

theorem coreLiteral_ne_invariant (input : State)
    (error : ParserInvariantError) :
    coreLiteral input ≠ .invariant error :=
  coreLiteral_ordinary.ne_invariant input error

/-- Boolean builtin recognition has no internal-failure path. -/
theorem booleanIdentifier_ordinary : Parser.Ordinary booleanIdentifier := by
  intro input
  cases result : booleanIdentifier input with
  | ok name next => exact Or.inl ⟨name, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      unfold booleanIdentifier at result
      cases found : input.peek? with
      | none => simp [found, rejectAt] at result
      | some token =>
          rcases token with ⟨span, kind⟩
          cases kind <;> simp [found, rejectAt] at result
          case keyword keyword =>
            cases keyword <;> simp only at result <;> cases result

theorem booleanIdentifier_ne_invariant (input : State)
    (error : ParserInvariantError) :
    booleanIdentifier input ≠ .invariant error :=
  booleanIdentifier_ordinary.ne_invariant input error

/-- Core literals can serve as strict elements of generic parser loops. -/
theorem coreLiteral_elementTotalityContract :
    ElementTotalityContract coreLiteral := {
  validFor := coreLiteral_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := coreLiteral_preservesTokenWindow
  cursorLtOnSuccess := coreLiteral_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    coreLiteral_ne_invariant input error
}

/-- Boolean builtins can serve as strict elements of generic parser loops. -/
theorem booleanIdentifier_elementTotalityContract :
    ElementTotalityContract booleanIdentifier := {
  validFor := booleanIdentifier_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := booleanIdentifier_preservesTokenWindow
  cursorLtOnSuccess := booleanIdentifier_cursor_lt_onSuccess
  invariantFree := fun input _ error =>
    booleanIdentifier_ne_invariant input error
}

end Solcore.Syntax.Parser
