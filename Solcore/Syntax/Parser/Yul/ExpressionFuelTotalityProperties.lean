import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.Yul.LeafTotalityProperties

/-! Fuel-aware totality for one inline-Yul expression layer and recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional call arguments inherit bounded delimited totality. -/
theorem optionalYulCallArguments_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ arguments next,
      optionalYulCallArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      optionalYulCallArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .leftParen
  · rcases delimited_ordinary_of_elementFuel .leftParen .rightParen true
        nested .yulExpression .yul nestedFuel contract input inputValid adequate
      with ⟨arguments, next, argumentsResult⟩ |
        ⟨failure, rejected, argumentsResult⟩
    · exact Or.inl ⟨some arguments, next, by
        simp only [optionalYulCallArguments, present, ↓reduceIte, orElse,
          bind, argumentsResult, pure]⟩
    · exact Or.inl ⟨none, input, by
        simp only [optionalYulCallArguments, present, ↓reduceIte, orElse,
          bind, argumentsResult, pure]⟩
  · have absent : isSymbol input .leftParen = false := by
      cases found : isSymbol input .leftParen with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [optionalYulCallArguments, absent, Bool.false_eq_true,
        ↓reduceIte]⟩

theorem optionalYulCallArguments_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    optionalYulCallArguments nested input ≠ .invariant error := by
  intro failed
  rcases optionalYulCallArguments_ordinary_of_elementFuel nested nestedFuel
      contract input inputValid adequate with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- One non-recovering Yul layer is ordinary below the recursive fuel bound. -/
theorem yulExpressionCore_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next,
      yulExpressionCore nested input = .ok expression next) ∨
    (∃ failure next,
      yulExpressionCore nested input = .reject failure next) := by
  unfold yulExpressionCore
  split
  · rcases yulLiteral_ordinary input with
      ⟨literal, next, literalResult⟩ | ⟨failure, rejected, literalResult⟩
    · exact Or.inl ⟨{
          span := literal.span
          value := .literal literal
        }, next, by simp only [literalResult]⟩
    · exact Or.inr ⟨failure, rejected, by simp only [literalResult]⟩
  · split
    · rcases yulName_ordinary input with
        ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
      · have nameValid := yulName_validFor input inputValid
        rw [nameResult] at nameValid
        have nameWindow := yulName_preservesTokenWindow input
        rw [nameResult] at nameWindow
        have afterNameAdequate : afterName.remainingCount < nestedFuel :=
          remainingCount_lt_after_strict_progress nameValid.2.1 nameWindow.2
            (yulName_cursor_lt_onSuccess nameResult) adequate
        rcases optionalYulCallArguments_ordinary_of_elementFuel nested
            nestedFuel contract afterName nameValid.2.1 (by omega) with
          ⟨arguments, next, argumentsResult⟩ |
          ⟨failure, rejected, argumentsResult⟩
        · cases arguments with
          | none => exact Or.inl ⟨{
              span := name.span
              value := .identifier name
            }, next, by
              simp only [nameResult, argumentsResult]⟩
          | some arguments => exact Or.inl ⟨{
              span := SourceSpan.cover name.span arguments.span
              value := .call name arguments
            }, next, by
              simp only [nameResult, argumentsResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [nameResult, argumentsResult]⟩
      · exact Or.inr ⟨failure, rejected, by simp only [nameResult]⟩
    · split <;> try { exact rejectedMeta_ordinary input }
      exact Or.inr ⟨_, input, rfl⟩

theorem yulExpressionCore_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    yulExpressionCore nested input ≠ .invariant error := by
  intro failed
  rcases yulExpressionCore_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

namespace YulExpressionInternals

/-- More fuel than remaining tokens makes recovery terminate successfully. -/
theorem recoverAux_exists_ok_of_remainingCount_lt
    (first last : SourceSpan) :
    ∀ fuel input, input.remainingCount < fuel →
      ∃ expression final,
        recoverAux first last fuel input = .ok expression final := by
  intro fuel
  induction fuel generalizing last with
  | zero =>
      intro input adequate
      omega
  | succ fuel inductionHypothesis =>
      intro input adequate
      unfold recoverAux
      split
      · exact ⟨_, _, rfl⟩
      · cases advanced : input.advance? with
        | none => exact ⟨_, _, rfl⟩
        | some pair =>
            rcases pair with ⟨token, next⟩
            change ∃ expression final,
              recoverAux first token.span fuel next = .ok expression final
            apply inductionHypothesis token.span next
            unfold State.advance? at advanced
            cases found : input.peek? with
            | none => simp [found] at advanced
            | some current =>
                simp only [found, Option.map_some] at advanced
                cases advanced
                have cursorBeforeEnd :=
                  State.cursor_lt_endIndex_of_peek?_eq_some found
                simp only [State.remainingCount] at adequate ⊢
                omega

/-- The recovery fuel selected by `layer` is always sufficient. -/
theorem recoverAux_production_exists_ok
    (first last : SourceSpan) (input : State) :
    ∃ expression final,
      recoverAux first last (input.remainingCount + 1) input =
        .ok expression final :=
  recoverAux_exists_ok_of_remainingCount_lt first last
    (input.remainingCount + 1) input (by omega)

theorem recoverAux_ne_invariant_of_remainingCount_lt
    (first last : SourceSpan) (fuel : Nat) (input : State)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    recoverAux first last fuel input ≠ .invariant error := by
  intro failed
  rcases recoverAux_exists_ok_of_remainingCount_lt first last fuel input
      adequate with ⟨expression, final, result⟩
  rw [result] at failed
  contradiction

/-- Recovery does not reintroduce invariants after an ordinary core rejection. -/
theorem layer_ordinary_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ expression next, layer nested input = .ok expression next) ∨
    (∃ failure next, layer nested input = .reject failure next) := by
  rcases yulExpressionCore_ordinary_of_elementFuel nested nestedFuel contract
      input inputValid adequate with
    ⟨expression, next, coreResult⟩ |
    ⟨failure, failedState, coreResult⟩
  · exact Or.inl ⟨expression, next, by simp only [layer, coreResult]⟩
  · let rewound := { failedState with cursor := input.cursor }
    by_cases boundary : isBoundary rewound
    · exact Or.inr ⟨failure, rewound, by
        simp only [layer, coreResult, rewound, boundary, ↓reduceIte]⟩
    · cases advanced : rewound.advance? with
      | none => exact Or.inr ⟨failure, rewound, by
          simp only [layer, coreResult, rewound, boundary,
            Bool.false_eq_true, ↓reduceIte, advanced]⟩
      | some pair =>
          rcases pair with ⟨token, afterToken⟩
          rcases recoverAux_production_exists_ok token.span token.span
              (afterToken.emit failure.toDiagnostic) with
            ⟨recovered, final, recoveredResult⟩
          have recoveredAtProductionFuel :
              recoverAux token.span token.span
                (afterToken.remainingCount + 1)
                (afterToken.emit failure.toDiagnostic) =
                  .ok recovered final := by
            have emitRemaining :
                (afterToken.emit failure.toDiagnostic).remainingCount =
                  afterToken.remainingCount := rfl
            rw [emitRemaining] at recoveredResult
            exact recoveredResult
          exact Or.inl ⟨recovered, final, by
            simp only [layer, coreResult, rewound, boundary,
              Bool.false_eq_true, ↓reduceIte, advanced,
              recoveredAtProductionFuel]⟩

theorem layer_ne_invariant_of_elementFuel
    (nested : Parser YulExpr) (nestedFuel : Nat)
    (contract : FuelElementTotalityContract nested nestedFuel)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < nestedFuel + 1)
    (error : ParserInvariantError) :
    layer nested input ≠ .invariant error := by
  intro failed
  rcases layer_ordinary_of_elementFuel nested nestedFuel contract input
      inputValid adequate with
    ⟨expression, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end YulExpressionInternals

end Solcore.Syntax.Parser
