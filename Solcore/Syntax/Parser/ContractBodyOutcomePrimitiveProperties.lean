import Solcore.Syntax.DeclarativeContractBodyOutcomeGrammar
import Solcore.Syntax.Parser.ContractMemberRecoveryBoundaryProperties
import Solcore.Syntax.Parser.ContractMemberWithAttributeOrdinaryRejectionSoundnessProperties

/-! Shared executable primitives for broad contract-body outcomes. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input output : State} {value : beta}
    (result : (first >>= next) input = .ok value output) :
    ∃ firstValue afterFirst,
      first input = .ok firstValue afterFirst ∧
        next firstValue afterFirst = .ok value output := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value output at result
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at result
      exact ⟨firstValue, afterFirst, rfl, result⟩
  | reject failure rejected => rw [firstResult] at result; contradiction
  | invariant error => rw [firstResult] at result; contradiction

/-- A derive-aware member rejection and its canonical state contract supply the
declarative rewind witness used by the body loop. -/
theorem contractMemberRejectsWithPreservedWindow_of_result
    {input failed : State} {failure : Failure}
    (result : contractMemberWithAttribute input = .reject failure failed) :
    DeclarativeGrammar.ContractMemberRejectsWithPreservedWindow
      input.declarativeRemainder := by
  have resultShape :=
    contractMemberWithAttribute_canonical_contract.preservesTokenWindow input
  rw [result] at resultShape
  have shape : failed.tokens = input.tokens ∧
      failed.window = input.window := by
    simpa only [Reply.PreservesTokenWindow] using resultShape
  exact ⟨failed.declarativeRemainder,
    contractMemberWithAttribute_reject_ordinaryOutcome_sound result,
    shape.1, congrArg TokenWindow.endIndex shape.2⟩

/-- Preserved carrier and active window make the member-loop cursor rewind
declaratively invisible. -/
theorem rewoundContractMember_declarativeRemainder_eq
    (input failed : State)
    (shape : failed.tokens = input.tokens ∧ failed.window = input.window) :
    ({ failed with cursor := input.cursor } : State).declarativeRemainder =
      input.declarativeRemainder := by
  unfold State.declarativeRemainder
  simp only
  rw [shape.1, shape.2]

/-- A false executable end guard is exactly strict containment in the active
token window. -/
theorem cursor_lt_endIndex_of_atEnd_eq_false {input : State}
    (notAtEnd : input.atEnd = false) :
    input.cursor < input.window.endIndex := by
  unfold State.atEnd at notAtEnd
  have outside : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    rw [decide_eq_true atEnd] at notAtEnd
    contradiction
  omega

/-- A true executable recovery-boundary guard exposes the corresponding exact
declarative boundary. -/
theorem contractMemberRecoveryBoundaryStartsAt_of_guard_eq_true
    {input : State} (present : atContractRecoveryBoundary input = true) :
    DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder :=
  recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true present

/-- A false executable recovery-boundary guard excludes every exact
declarative boundary. -/
theorem no_contractMemberRecoveryBoundaryStartsAt_of_guard_eq_false
    {input : State} (absent : atContractRecoveryBoundary input = false) :
    ¬ DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder := by
  intro starts
  have present :=
    atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt starts
  rw [present] at absent
  contradiction

/-- A successful close exposes the exact closing brace and constructed body. -/
theorem closeContractBody_success_exact (opening : Token)
    (membersRev : List ContractMember) {input output : State}
    {body : ContractBody}
    (result : closeContractBody opening membersRev input = .ok body output) :
    ∃ closingSpan,
      body = {
        span := SourceSpan.cover opening.span closingSpan
        members := membersRev.reverse
      } ∧
      DeclarativeGrammar.ExactTokenParses (.symbol .rightBrace)
        input.declarativeRemainder closingSpan output.declarativeRemainder := by
  unfold closeContractBody at result
  rcases bind_ok_components result with
    ⟨closing, afterClosing, closingResult, finished⟩
  cases finished
  exact ⟨closing.span, rfl,
    symbol_success_exactTokenParses .rightBrace .topItem closingResult⟩

/-- A positive right-brace lookahead makes body closing total and successful. -/
theorem closeContractBody_success_of_rightBrace_guard (opening : Token)
    (membersRev : List ContractMember) {input : State}
    (present : isSymbol input .rightBrace = true) :
    ∃ body output, closeContractBody opening membersRev input =
      .ok body output := by
  rcases symbol_eq_ok_of_isSymbol_eq_true .rightBrace .topItem present with
    ⟨closing, closingResult⟩
  exact ⟨{
      span := SourceSpan.cover opening.span closing.span
      members := membersRev.reverse
    }, { input with cursor := input.cursor + 1 }, by
      simp only [closeContractBody, bind, closingResult, pure]⟩

end Solcore.Syntax.Parser.ContractInternals
