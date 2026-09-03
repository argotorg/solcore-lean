import Solcore.Syntax.Parser.Pragma
import Solcore.Syntax.Parser.CoreIdentifierOutcomeSoundnessProperties

/-! Unconditional source-file and full-window frame laws for pragma items.
Cursor changes and emitted diagnostics do not alter diagnostic report context. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Successful checked names retain the complete file and window, including
the window end byte, whether or not a hyphen diagnostic was emitted. -/
theorem identifier_success_context_eq (context : ParseContext)
    {input output : State} {name : Identifier}
    (result : identifier context input = .ok name output) :
    output.file = input.file ∧ output.window = input.window := by
  unfold identifier at result
  cases raw : rawIdentifier context input with
  | reject failure rejected => simp [raw] at result
  | invariant error => simp [raw] at result
  | ok parsed afterName =>
      have shape := rawIdentifier_ok_state_shape context raw
      simp only [raw] at result
      split at result <;> cases result <;> rw [shape] <;> exact ⟨rfl, rfl⟩

/-- Rejected checked names retain the original file and full input window. -/
theorem identifier_reject_context_eq (context : ParseContext)
    {input rejected : State} {failure : Failure}
    (result : identifier context input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  rw [identifier_reject_state_eq context result]
  exact ⟨rfl, rfl⟩

private def replyContextEq {alpha : Type} (input : State) : Reply alpha → Prop
  | .ok _ output | .reject _ output =>
      output.file = input.file ∧ output.window = input.window
  | .invariant _ => True

private theorem replyContextEq_trans {alpha : Type}
    {input middle : State} {reply : Reply alpha}
    (outer : replyContextEq middle reply)
    (inner : middle.file = input.file ∧ middle.window = input.window) :
    replyContextEq input reply := by
  cases reply with
  | ok _ _ | reject _ _ => exact ⟨outer.1.trans inner.1, outer.2.trans inner.2⟩
  | invariant => trivial

namespace PragmaInternals

private theorem pragmaItemsTail_context_frame :
    ∀ fuel itemsRev input, replyContextEq input (pragmaItemsTail fuel itemsRev input) := by
  intro fuel
  induction fuel with
  | zero => intro itemsRev input; trivial
  | succ fuel ih =>
      intro itemsRev input
      unfold pragmaItemsTail
      split
      · cases commaResult : symbol .comma .pragmaDecl input with
        | invariant => trivial
        | reject failure rejected =>
            have stateEq := acceptToken_reject_state_shape (.symbol .comma) .pragmaDecl
              (· == .symbol .comma) commaResult
            exact ⟨congrArg State.file stateEq, congrArg State.window stateEq⟩
        | ok comma afterComma =>
            have commaShape := (symbol_ok_state_shape .comma .pragmaDecl commaResult).2
            have commaContext : afterComma.file = input.file ∧
                afterComma.window = input.window := by
              rw [commaShape]
              exact ⟨rfl, rfl⟩
            simp only
            split
            · exact commaContext
            · cases itemResult : identifier .pragmaDecl afterComma with
              | invariant => trivial
              | reject failure rejected =>
                  have context := identifier_reject_context_eq .pragmaDecl itemResult
                  exact ⟨context.1.trans commaContext.1, context.2.trans commaContext.2⟩
              | ok item next =>
                  have context := identifier_success_context_eq .pragmaDecl itemResult
                  exact replyContextEq_trans (ih (item :: itemsRev) next)
                    ⟨context.1.trans commaContext.1, context.2.trans commaContext.2⟩
      · exact ⟨rfl, rfl⟩

private theorem pragmaItems_context_frame (input : State) :
    replyContextEq input (pragmaItems input) := by
  unfold pragmaItems
  split
  · exact ⟨rfl, rfl⟩
  · cases itemResult : identifier .pragmaDecl input with
    | invariant => trivial
    | reject failure rejected => exact identifier_reject_context_eq .pragmaDecl itemResult
    | ok item next =>
        exact replyContextEq_trans
          (pragmaItemsTail_context_frame (next.remainingCount + 1) [item] next)
          (identifier_success_context_eq .pragmaDecl itemResult)

/-- Successful tail scanning preserves the file and full window for every
fuel and reverse prefix, independently of input/diagnostic validity. -/
theorem pragmaItemsTail_success_context_eq (fuel : Nat) (itemsRev : List Identifier)
    {input output : State} {items : List Identifier}
    (result : pragmaItemsTail fuel itemsRev input = .ok items output) :
    output.file = input.file ∧ output.window = input.window := by
  have frame := pragmaItemsTail_context_frame fuel itemsRev input
  rw [result] at frame
  exact frame

/-- Ordinary tail rejection retains the original source and end-byte context,
even after successful earlier items have emitted diagnostics. -/
theorem pragmaItemsTail_reject_context_eq (fuel : Nat) (itemsRev : List Identifier)
    {input rejected : State} {failure : Failure}
    (result : pragmaItemsTail fuel itemsRev input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have frame := pragmaItemsTail_context_frame fuel itemsRev input
  rw [result] at frame
  exact frame

/-- Full successful item scanning retains both report-context carriers. -/
theorem pragmaItems_success_context_eq
    {input output : State} {items : List Identifier}
    (result : pragmaItems input = .ok items output) :
    output.file = input.file ∧ output.window = input.window := by
  have frame := pragmaItems_context_frame input
  rw [result] at frame
  exact frame

/-- Full item rejection retains the input file and complete active window. -/
theorem pragmaItems_reject_context_eq
    {input rejected : State} {failure : Failure}
    (result : pragmaItems input = .reject failure rejected) :
    rejected.file = input.file ∧ rejected.window = input.window := by
  have frame := pragmaItems_context_frame input
  rw [result] at frame
  exact frame

end PragmaInternals
end Solcore.Syntax.Parser
