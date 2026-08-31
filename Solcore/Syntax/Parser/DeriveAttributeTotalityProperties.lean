import Solcore.Syntax.Parser.DeriveTargetTotalityProperties
import Solcore.Syntax.Parser.DeriveRecoveryTotalityProperties
import Solcore.Syntax.Parser.DeriveCarrierProperties

/-! Conditional totality for canonical derive attributes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.DeriveAttributeInternals

/-- The proof-visible valid derive path is ordinary on valid input. -/
theorem valid_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ derive next, valid input = .ok derive next) ∨
      (∃ failure next, valid input = .reject failure next) := by
  unfold valid
  cases hashResult : symbol .hash .topItem input with
  | invariant error =>
      exact False.elim
        (symbol_ne_invariant .hash .topItem input error hashResult)
  | reject failure rejected =>
      right
      simp only [bind, hashResult]
      exact ⟨failure, rejected, rfl⟩
  | ok hash afterHash =>
      have hashReply := symbol_validFor .hash .topItem input inputValid
      rw [hashResult] at hashReply
      simp only [bind, hashResult]
      cases openingResult : symbol .leftBracket .topItem afterHash with
      | invariant error =>
          exact False.elim
            (symbol_ne_invariant .leftBracket .topItem afterHash error
              openingResult)
      | reject failure rejected =>
          simp only
          exact Or.inr ⟨failure, rejected, rfl⟩
      | ok opening afterOpening =>
          have openingReply := symbol_validFor .leftBracket .topItem
            afterHash hashReply.2.1
          rw [openingResult] at openingReply
          simp only
          cases deriveResult : contextual .derive .topItem afterOpening with
          | invariant error =>
              exact False.elim
                (contextual_ne_invariant .derive .topItem afterOpening error
                  deriveResult)
          | reject failure rejected =>
              simp only
              exact Or.inr ⟨failure, rejected, rfl⟩
          | ok deriveKeyword afterDerive =>
              have deriveReply := contextual_validFor .derive .topItem
                afterOpening openingReply.2.1
              rw [deriveResult] at deriveReply
              simp only
              cases targetsResult : delimitedNoTrailing .leftParen .rightParen
                  true deriveTarget .topItem .topLevel afterDerive with
              | invariant error =>
                  exact False.elim
                    (delimitedNoTrailing_ne_invariant .leftParen .rightParen
                      true deriveTarget .topItem .topLevel
                      deriveTarget_elementTotalityContract afterDerive
                      deriveReply.2.1 error targetsResult)
              | reject failure rejected =>
                  simp only
                  exact Or.inr ⟨failure, rejected, rfl⟩
              | ok targets afterTargets =>
                  simp only
                  cases closingResult : symbol .rightBracket .topItem
                      afterTargets with
                  | invariant error =>
                      exact False.elim
                        (symbol_ne_invariant .rightBracket .topItem
                          afterTargets error closingResult)
                  | reject failure rejected =>
                      simp only
                      exact Or.inr ⟨failure, rejected, rfl⟩
                  | ok closing afterClosing =>
                      simp only
                      by_cases empty : targets.elements = []
                      · left
                        simp [empty, emitDiagnostic, modifyState, pure]
                      · left
                        simp [empty, pure]

/-- The valid derive path cannot expose an invariant on valid input. -/
theorem valid_ne_invariant (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    valid input ≠ .invariant error := by
  intro failed
  rcases valid_ordinary input inputValid with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.DeriveAttributeInternals

namespace Solcore.Syntax.Parser

/-- Public derive-attribute parsing is ordinary on every valid input. -/
theorem deriveAttribute_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ derive next, deriveAttribute input = .ok derive next) ∨
      (∃ failure next,
        deriveAttribute input = .reject failure next) := by
  unfold deriveAttribute orElse
  cases validResult : DeriveAttributeInternals.valid input with
  | ok derive next => exact Or.inl ⟨derive, next, rfl⟩
  | invariant error =>
      exact False.elim
        (DeriveAttributeInternals.valid_ne_invariant input inputValid error
          validResult)
  | reject failure rejected =>
      simpa only using DeriveAttributeInternals.recovered_ordinary input

/-- Public derive-attribute parsing cannot expose an invariant on valid input. -/
theorem deriveAttribute_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    deriveAttribute input ≠ .invariant error := by
  intro failed
  rcases deriveAttribute_ordinary input inputValid with
    ⟨derive, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Derive attributes instantiate the generic strict delimited-element boundary. -/
theorem deriveAttribute_elementTotalityContract :
    ElementTotalityContract deriveAttribute := {
  validFor := deriveAttribute_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := deriveAttribute_preservesTokenWindow
  cursorLtOnSuccess := deriveAttribute_cursor_lt_onSuccess
  invariantFree := fun input inputValid error =>
    deriveAttribute_ne_invariant input inputValid error
}

end Solcore.Syntax.Parser
