import Solcore.Syntax.Parser.Name
import Solcore.Syntax.Parser.PrimitiveTotalityProperties

/-! Fuel adequacy and totality for qualified-name parsing. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

namespace QualifiedNameInternals

/-- More fuel than remaining tokens makes the dotted-name tail ordinary. -/
theorem qualifiedNameTail_ordinary_of_remainingCount_lt
    (context : ParseContext) (phase : ParserPhase) (first : Identifier) :
    ∀ fuel last tailRev state, state.remainingCount < fuel →
      (∃ name next,
        qualifiedNameTail context phase first fuel last tailRev state =
          .ok name next) ∨
      (∃ failure next,
        qualifiedNameTail context phase first fuel last tailRev state =
          .reject failure next) := by
  intro fuel
  induction fuel with
  | zero =>
      intro last tailRev state adequate
      omega
  | succ fuel inductionHypothesis =>
      intro last tailRev state adequate
      unfold qualifiedNameTail
      split
      · cases dotResult : symbol .dot context state with
        | invariant error =>
            exact False.elim
              (symbol_ne_invariant .dot context state error dotResult)
        | reject failure rejected =>
            exact Or.inr ⟨failure, rejected, rfl⟩
        | ok dot afterDot =>
            dsimp only
            cases componentResult : identifier context afterDot with
            | invariant error =>
                exact False.elim
                  (identifier_ne_invariant context afterDot error
                    componentResult)
            | reject failure rejected =>
                exact Or.inr ⟨failure, rejected, rfl⟩
            | ok component next =>
                change
                  (∃ name final,
                    qualifiedNameTail context phase first fuel component
                      (component :: tailRev) next = .ok name final) ∨
                  (∃ failure final,
                    qualifiedNameTail context phase first fuel component
                      (component :: tailRev) next = .reject failure final)
                apply inductionHypothesis component (component :: tailRev) next
                have dotShape := symbol_ok_state_shape .dot context dotResult
                rcases identifier_ok_state_shape context componentResult with
                  ⟨_, _, _, _, componentCursor⟩
                have dotWindow := symbol_preservesTokenWindow .dot context state
                rw [dotResult] at dotWindow
                have componentWindow :=
                  identifier_preservesTokenWindow context afterDot
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

/-- Adequate dotted-name fuel excludes all internal invariant results. -/
theorem qualifiedNameTail_ne_invariant_of_remainingCount_lt
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (fuel : Nat) (tailRev : List Identifier) (state : State)
    (adequate : state.remainingCount < fuel)
    (error : ParserInvariantError) :
    qualifiedNameTail context phase first fuel last tailRev state ≠
      .invariant error := by
  intro failed
  rcases qualifiedNameTail_ordinary_of_remainingCount_lt context phase first
      fuel last tailRev state adequate with
    ⟨name, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- The exact production fuel for a qualified-name tail is sufficient. -/
theorem qualifiedNameTail_production_ordinary
    (context : ParseContext) (phase : ParserPhase) (first last : Identifier)
    (tailRev : List Identifier) (state : State) :
    (∃ name next,
      qualifiedNameTail context phase first (state.remainingCount + 1)
        last tailRev state = .ok name next) ∨
      (∃ failure next,
        qualifiedNameTail context phase first (state.remainingCount + 1)
          last tailRev state = .reject failure next) :=
  qualifiedNameTail_ordinary_of_remainingCount_lt context phase first
    (state.remainingCount + 1) last tailRev state (by omega)

end QualifiedNameInternals

/-- Public qualified-name parsing is ordinary on every input. -/
theorem qualifiedName_ordinary (context : ParseContext) (phase : ParserPhase) :
    Parser.Ordinary (qualifiedName context phase) := by
  intro input
  unfold qualifiedName
  cases firstResult : identifier context input with
  | invariant error =>
      exact False.elim
        (identifier_ne_invariant context input error firstResult)
  | reject failure rejected =>
      exact Or.inr ⟨failure, rejected, rfl⟩
  | ok first next =>
      dsimp only
      exact QualifiedNameInternals.qualifiedNameTail_production_ordinary
        context phase first first [] next

/-- Public qualified names cannot expose fuel or primitive invariants. -/
theorem qualifiedName_ne_invariant (context : ParseContext)
    (phase : ParserPhase) (input : State) (error : ParserInvariantError) :
    qualifiedName context phase input ≠ .invariant error :=
  (qualifiedName_ordinary context phase).ne_invariant input error

/-- Qualified names can instantiate generic delimited element parsing. -/
theorem qualifiedName_elementTotalityContract (context : ParseContext)
    (phase : ParserPhase) :
    ElementTotalityContract (qualifiedName context phase) := {
  validFor := (qualifiedName_validFor context phase).mono
    (fun _ _ _ => trivial)
  preservesTokenWindow := qualifiedName_preservesTokenWindow context phase
  cursorLtOnSuccess := qualifiedName_cursor_lt_onSuccess context phase
  invariantFree := fun input _ error =>
    qualifiedName_ne_invariant context phase input error
}

end Solcore.Syntax.Parser
