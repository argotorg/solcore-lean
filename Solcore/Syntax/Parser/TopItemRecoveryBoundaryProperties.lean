import Solcore.Syntax.DeclarativeTopItemRecoveryOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.File
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties

/-! Executable-to-declarative stop bridges for top-item recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.FileInternals

/-- Every exact declarative top-item boundary makes the executable lookahead
guard true. -/
theorem atTopItemStart_eq_true_of_topItemRecoveryBoundary
    {input : State}
    (starts : DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder) :
    atTopItemStart input = true := by
  rcases starts with ⟨kind, member, span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at token
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  unfold atTopItemStart
  rw [peekKind]
  exact (importTerminatorTopItemStartKind_iff kind).mpr member

/-- A true auxiliary scan guard gives an exact nonconsuming recovery stop. -/
theorem topItemRecoveryStops_of_guard_eq_true (input : State)
    (stops : (input.atEnd || atTopItemStart input) = true) :
    DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atTopItemStart input = true := by
      simpa [atEndFalse] using stops
    exact .boundary
      (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true boundary)

/-- Under a false auxiliary guard, failed advancement is an exact missing
carrier slot inside the active token window. -/
theorem topItemRecoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atTopItemStart input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.TopItemRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false auxiliary guard excludes every exact stop,
so recovery must scan that token. -/
theorem no_topItemRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atTopItemStart input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.TopItemRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | boundary starts =>
      have boundary :=
        atTopItemStart_eq_true_of_topItemRecoveryBoundary starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end Solcore.Syntax.Parser.FileInternals
