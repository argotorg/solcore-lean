import Solcore.Syntax.DeclarativeExactOutcomeSpec
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties

/-! Exact ordinary grammar outcomes correspond to executable outcomes when
the fixed input cannot produce an internal invariant failure. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Exact success functionality and branch exclusion turn ordinary soundness
into completeness, preserving the AST and declarative remainder only. -/
theorem ordinary_success_iff_exists_ok {α : Type} (parser : Parser α)
    {Parses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop}
    {Rejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec Parses Rejects)
    {input : State}
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    (successSound : ∀ {value : α} {output : State},
      parser input = .ok value output →
        Parses input.declarativeRemainder value output.declarativeRemainder)
    (rejectSound : ∀ {failure : Failure} {output : State},
      parser input = .reject failure output →
        Rejects input.declarativeRemainder output.declarativeRemainder)
    {value : α} {remainder : DeclarativeGrammar.Remainder} :
    Parses input.declarativeRemainder value remainder ↔
      ∃ output, parser input = .ok value output ∧
        output.declarativeRemainder = remainder := by
  constructor
  · intro parsed
    cases result : parser input with
    | ok actual output =>
        rcases outcomes.successResultUnique (successSound result) parsed with
          ⟨valueEq, remainderEq⟩
        cases valueEq
        exact ⟨output, rfl, remainderEq⟩
    | reject failure output =>
        exact False.elim (outcomes.successRejectDisjoint (rejectSound result)
          ⟨value, remainder, parsed⟩)
    | invariant error => exact False.elim (invariantFree error result)
  · rintro ⟨output, result, remainderEq⟩
    exact remainderEq ▸ successSound result

/-- Exact rejection functionality turns ordinary soundness into completeness
at the declarative endpoint, without identifying diagnostics or full states. -/
theorem ordinary_reject_iff_exists_reject {α : Type} (parser : Parser α)
    {Parses : DeclarativeGrammar.Remainder → α →
      DeclarativeGrammar.Remainder → Prop}
    {Rejects : DeclarativeGrammar.Remainder →
      DeclarativeGrammar.Remainder → Prop}
    (outcomes : DeclarativeGrammar.ExactDeterministicOutcomeSpec Parses Rejects)
    {input : State}
    (invariantFree : ∀ error, parser input ≠ .invariant error)
    (successSound : ∀ {value : α} {output : State},
      parser input = .ok value output →
        Parses input.declarativeRemainder value output.declarativeRemainder)
    (rejectSound : ∀ {failure : Failure} {output : State},
      parser input = .reject failure output →
        Rejects input.declarativeRemainder output.declarativeRemainder)
    {rejected : DeclarativeGrammar.Remainder} :
    Rejects input.declarativeRemainder rejected ↔
      ∃ failure output, parser input = .reject failure output ∧
        output.declarativeRemainder = rejected := by
  constructor
  · intro rejection
    cases result : parser input with
    | ok value output =>
        exact False.elim (outcomes.successRejectDisjoint rejection
          ⟨value, output.declarativeRemainder, successSound result⟩)
    | reject failure output =>
        exact ⟨failure, output, rfl,
          outcomes.rejectOutputUnique (rejectSound result) rejection⟩
    | invariant error => exact False.elim (invariantFree error result)
  · rintro ⟨failure, output, result, remainderEq⟩
    exact remainderEq ▸ rejectSound result

end Solcore.Syntax.Parser
