import Solcore.Syntax.Parser.ExportProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Production-fuel adequacy for export-path parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace ExportInternals

/-- More fuel than remaining tokens makes the export-path tail ordinary. -/
theorem exportPathTail_ordinary_of_remainingCount_lt (first : Identifier) :
    ∀ fuel last tailRev state, state.remainingCount < fuel →
      (∃ path next,
        exportPathTail first fuel last tailRev state = .ok path next) ∨
      (∃ failure next,
        exportPathTail first fuel last tailRev state = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold exportPathTail
      split
      · cases dotResult : symbol .dot .exportDecl state with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .dot .exportDecl state error dotResult)
        | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            dsimp only
            cases componentResult : identifier .exportDecl afterDot with
            | invariant error =>
                exact False.elim
                  (identifier_ne_invariant .exportDecl afterDot error
                    componentResult)
            | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
            | ok component next =>
                change
                  (∃ path final,
                    exportPathTail first fuel component
                      (component :: tailRev) next = .ok path final) ∨
                  (∃ failure final,
                    exportPathTail first fuel component
                      (component :: tailRev) next = .reject failure final)
                apply inductionHypothesis component (component :: tailRev) next
                have dotShape := symbol_ok_state_shape .dot .exportDecl dotResult
                rcases identifier_ok_state_shape .exportDecl componentResult with
                  ⟨_, _, _, _, componentCursor⟩
                have dotWindow := symbol_preservesTokenWindow .dot .exportDecl
                  state
                rw [dotResult] at dotWindow
                have componentWindow := identifier_preservesTokenWindow
                  .exportDecl afterDot
                rw [componentResult] at componentWindow
                have nextWindow : next.window = state.window :=
                  componentWindow.2.trans dotWindow.2
                have endIndexEq :
                    next.window.endIndex = state.window.endIndex :=
                  congrArg TokenWindow.endIndex nextWindow
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some dotShape.1
                have nextCursor : next.cursor = state.cursor + 2 := by
                  rw [componentCursor, dotShape.2]
                simp only [State.remainingCount] at adequate ⊢
                rw [endIndexEq, nextCursor]
                omega
      · exact Or.inl ⟨_, _, rfl⟩

theorem exportPathTail_ne_invariant_of_remainingCount_lt
    (first last : Identifier) (fuel : Nat) (tailRev : List Identifier)
    (state : State) (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    exportPathTail first fuel last tailRev state ≠ .invariant error := by
  intro failed
  rcases exportPathTail_ordinary_of_remainingCount_lt first fuel last tailRev
      state adequate with
    ⟨path, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The production choice `remainingCount + 1` is adequate. -/
theorem exportPathTail_production_ordinary (first last : Identifier)
    (tailRev : List Identifier) (state : State) :
    (∃ path next,
      exportPathTail first (state.remainingCount + 1) last tailRev state =
        .ok path next) ∨
    (∃ failure next,
      exportPathTail first (state.remainingCount + 1) last tailRev state =
        .reject failure next) :=
  exportPathTail_ordinary_of_remainingCount_lt first
    (state.remainingCount + 1) last tailRev state (by omega)

/-- Public export paths are ordinary on every input. -/
theorem exportPath_ordinary : Parser.Ordinary exportPath := by
  intro input
  unfold exportPath
  cases firstResult : identifier .exportDecl input with
  | invariant error =>
      exact False.elim
        (identifier_ne_invariant .exportDecl input error firstResult)
  | reject failure rejected => exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      dsimp only
      exact exportPathTail_production_ordinary first first [] next

theorem exportPath_invariantFreeOnValid :
    Parser.InvariantFreeOnValid exportPath :=
  exportPath_ordinary.invariantFreeOnValid

theorem exportPath_ne_invariant (input : State)
    (error : ParserInvariantError) :
    exportPath input ≠ .invariant error :=
  exportPath_ordinary.ne_invariant input error

end ExportInternals

end Solcore.Syntax.Parser
