import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Compositional invariant-freedom laws for canonical parsers. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.Parser

/-- Every valid input receives an ordinary success or rejection reply. -/
def InvariantFreeOnValid {alpha : Type} (parser : Parser alpha) : Prop :=
  ∀ input, input.ValidFor →
    (∃ value next, parser input = .ok value next) ∨
      (∃ failure next, parser input = .reject failure next)

namespace InvariantFreeOnValid

/-- Valid-input ordinary classification excludes every invariant reply. -/
theorem ne_invariant {alpha : Type} {parser : Parser alpha}
    (invariantFree : InvariantFreeOnValid parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error := by
  intro failed
  rcases invariantFree input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
    rw [result] at failed <;> contradiction

end InvariantFreeOnValid

/-- Excluding every invariant constructor recovers ordinary classification. -/
theorem invariantFreeOnValid_of_ne_invariant {alpha : Type}
    {parser : Parser alpha}
    (noInvariant : ∀ input, input.ValidFor → ∀ error,
      parser input ≠ .invariant error) :
    InvariantFreeOnValid parser := by
  intro input inputValid
  cases result : parser input with
  | ok value next => exact Or.inl ⟨value, next, rfl⟩
  | reject failure next => exact Or.inr ⟨failure, next, rfl⟩
  | invariant error =>
      exact False.elim (noInvariant input inputValid error result)

/-- Ordinary classification and no-invariant formulations are equivalent. -/
theorem invariantFreeOnValid_iff_ne_invariant {alpha : Type}
    {parser : Parser alpha} :
    InvariantFreeOnValid parser ↔
      ∀ input, input.ValidFor → ∀ error,
        parser input ≠ .invariant error :=
  ⟨fun free => free.ne_invariant, invariantFreeOnValid_of_ne_invariant⟩

/-- An ordinary parser is invariant-free on the smaller valid-input domain. -/
theorem Ordinary.invariantFreeOnValid {alpha : Type}
    {parser : Parser alpha} (ordinary : Ordinary parser) :
    InvariantFreeOnValid parser :=
  fun input _inputValid => ordinary input

/-- Pure parsers are invariant-free on every valid input. -/
theorem pure_invariantFreeOnValid {alpha : Type} (value : alpha) :
    InvariantFreeOnValid (pure value : Parser alpha) := by
  intro input _inputValid
  exact Or.inl ⟨value, input, rfl⟩

/--
Bind is invariant-free when its first parser preserves valid states and both
stages are invariant-free on valid inputs.
-/
theorem bind_invariantFreeOnValid {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {firstValueValid : SourceFile → alpha → Prop}
    (firstValid : first.ValidFor firstValueValid)
    (firstFree : InvariantFreeOnValid first)
    (nextFree : ∀ value, InvariantFreeOnValid (next value)) :
    InvariantFreeOnValid (first >>= next) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨firstValue, afterFirst, firstResult⟩ |
    ⟨failure, rejected, firstResult⟩
  · have firstReply := firstValid input inputValid
    rw [firstResult] at firstReply
    rcases nextFree firstValue afterFirst firstReply.2.1 with
      ⟨value, final, nextResult⟩ | ⟨failure, final, nextResult⟩
    · exact Or.inl ⟨value, final, by
        simp only [bind, firstResult, nextResult]⟩
    · exact Or.inr ⟨failure, final, by
        simp only [bind, firstResult, nextResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [bind, firstResult]⟩

/-- Transactional choice is invariant-free when both alternatives are. -/
theorem orElse_invariantFreeOnValid {alpha : Type}
    {first second : Parser alpha}
    (firstFree : InvariantFreeOnValid first)
    (secondFree : InvariantFreeOnValid second) :
    InvariantFreeOnValid (orElse first second) := by
  intro input inputValid
  rcases firstFree input inputValid with
    ⟨value, next, firstResult⟩ | ⟨failure, rejected, firstResult⟩
  · exact Or.inl ⟨value, next, by
      simp only [orElse, firstResult]⟩
  · rcases secondFree input inputValid with
      ⟨value, next, secondResult⟩ | ⟨failure, next, secondResult⟩
    · exact Or.inl ⟨value, next, by
        simp only [orElse, firstResult, secondResult]⟩
    · exact Or.inr ⟨failure, next, by
        simp only [orElse, firstResult, secondResult]⟩

/-- Reading the parser state is invariant-free. -/
theorem getState_invariantFreeOnValid :
    InvariantFreeOnValid getState := by
  intro input _inputValid
  exact Or.inl ⟨input, input, rfl⟩

/-- Any total state update has an ordinary parser result. -/
theorem modifyState_invariantFreeOnValid (update : State → State) :
    InvariantFreeOnValid (modifyState update) := by
  intro input _inputValid
  exact Or.inl ⟨(), update input, rfl⟩

/-- Emitting one diagnostic is invariant-free. -/
theorem emitDiagnostic_invariantFreeOnValid
    (diagnostic : ParseDiagnostic) :
    InvariantFreeOnValid (emitDiagnostic diagnostic) := by
  unfold emitDiagnostic
  exact modifyState_invariantFreeOnValid _

/-- A parser that rejects at its input state is invariant-free. -/
theorem rejectAt_invariantFreeOnValid {alpha : Type}
    (expected : NonemptyList ParseExpectation) (context : ParseContext) :
    InvariantFreeOnValid (fun state =>
      rejectAt (α := alpha) state expected context) := by
  intro input _inputValid
  exact Or.inr ⟨_, input, rfl⟩

end Solcore.Syntax.Parser.Parser
