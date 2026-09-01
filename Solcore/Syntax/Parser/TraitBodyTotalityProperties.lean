import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.FunctionSignatureTotalityProperties
import Solcore.Syntax.Parser.TraitProperties

/-! Valid-input totality for canonical trait methods and trait bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.TraitInternals

/-- A signature-only trait method has only ordinary outcomes on valid input. -/
theorem traitMethod_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitMethod := by
  unfold traitMethod
  apply Parser.bind_invariantFreeOnValid
    (functionSignature_validFor .module)
    (functionSignature_invariantFreeOnValid .module)
  intro signature
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .topItem)
    (symbol_ordinary .semicolon .topItem).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover signature.span semicolon.span
    value := {
      leadingComments := []
      signature
      semicolon := semicolon.span
    }
  } : TraitMethod)

theorem traitMethod_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ method next, traitMethod input = .ok method next) ∨
      (∃ failure next, traitMethod input = .reject failure next) :=
  traitMethod_invariantFreeOnValid input inputValid

theorem traitMethod_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitMethod input ≠ .invariant error :=
  traitMethod_invariantFreeOnValid.ne_invariant input inputValid error

/-- A trait method is a strict reusable parser element. -/
theorem traitMethod_elementTotalityContract :
    ElementTotalityContract traitMethod := {
  validFor := traitMethod_validFor.mono (fun _ _ _ => trivial)
  preservesTokenWindow := traitMethod_preservesTokenWindow
    (functionSignature_preservesTokenWindow .module)
  cursorLtOnSuccess := traitMethod_cursor_lt_onSuccess
  invariantFree := traitMethod_ne_invariant
}

private theorem closeTraitBody_ordinary (opening : Token)
    (methodsRev : List TraitMethod) :
    Parser.Ordinary (closeTraitBody opening methodsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
      span := SourceSpan.cover opening.span closing.span
      methods := methodsRev.reverse
    }, next, by
      simp only [closeTraitBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeTraitBody, bind, closingResult]⟩

/--
Strict method progress spends one unit of the loop's explicit fuel bound.
Thus neither fuel exhaustion nor the no-progress invariant is reachable.
-/
theorem traitMethods_ordinary_of_remainingCount_lt (opening : Token) :
    ∀ fuel methodsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        traitMethods opening fuel methodsRev input = .ok body next) ∨
      (∃ failure next,
        traitMethods opening fuel methodsRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro methodsRev input inputValid adequate
      unfold traitMethods
      by_cases closes : isSymbol input .rightBrace
      · simpa only [closes, if_true] using
          closeTraitBody_ordinary opening methodsRev input
      · by_cases methodPresent : isKeyword input .functionKw
        · rcases traitMethod_ordinary input inputValid with
            ⟨method, next, methodResult⟩ |
            ⟨failure, rejected, methodResult⟩
          · have methodReply := traitMethod_validFor input inputValid
            rw [methodResult] at methodReply
            have methodWindow := traitMethod_preservesTokenWindow
              (functionSignature_preservesTokenWindow .module) input
            rw [methodResult] at methodWindow
            have progress := traitMethod_cursor_lt_onSuccess methodResult
            have nextAdequate : next.remainingCount < fuel :=
              remainingCount_lt_after_strict_progress methodReply.2.1
                methodWindow.2 progress adequate
            simpa only [closes, Bool.false_eq_true, if_false,
              methodPresent, if_true, methodResult, if_pos progress] using
                inductionHypothesis (method :: methodsRev) next
                  methodReply.2.1 nextAdequate
          · exact Or.inr ⟨failure, rejected, by
              simp only [closes, Bool.false_eq_true, if_false,
                methodPresent, if_true, methodResult]⟩
        · simpa only [closes, Bool.false_eq_true, if_false,
            methodPresent] using
              (Parser.rejectAt_invariantFreeOnValid
                (alpha := TraitBody)
                { head := .keyword .functionKw,
                  tail := [.symbol .rightBrace] }
                .topItem) input inputValid

/-- Production fuel is exactly one more than the remaining token count. -/
theorem traitMethods_production_ordinary
    (opening : Token) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body next,
      traitMethods opening (input.remainingCount + 1) methodsRev input =
        .ok body next) ∨
      (∃ failure next,
        traitMethods opening (input.remainingCount + 1) methodsRev input =
          .reject failure next) :=
  traitMethods_ordinary_of_remainingCount_lt opening
    (input.remainingCount + 1) methodsRev input inputValid (by omega)

/-- The production loop parser is invariant-free on every valid input. -/
theorem traitMethods_production_invariantFreeOnValid
    (opening : Token) (methodsRev : List TraitMethod) :
    Parser.InvariantFreeOnValid (fun input =>
      traitMethods opening (input.remainingCount + 1) methodsRev input) :=
  traitMethods_production_ordinary opening methodsRev

theorem traitMethods_production_ne_invariant
    (opening : Token) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitMethods opening (input.remainingCount + 1) methodsRev input ≠
      .invariant error :=
  (traitMethods_production_invariantFreeOnValid opening methodsRev
    ).ne_invariant input inputValid error

theorem traitMethods_ne_invariant_of_remainingCount_lt
    (opening : Token) (fuel : Nat) (methodsRev : List TraitMethod)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    traitMethods opening fuel methodsRev input ≠ .invariant error := by
  intro failed
  rcases traitMethods_ordinary_of_remainingCount_lt opening fuel methodsRev
      input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- A canonical trait body has only ordinary outcomes on valid input. -/
theorem traitBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid traitBody := by
  intro input inputValid
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, next, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    simpa only [traitBody, openingResult] using
      traitMethods_production_ordinary opening [] next openingReply.2.1
  · exact Or.inr ⟨failure, rejected, by
      simp only [traitBody, openingResult]⟩

theorem traitBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, traitBody input = .ok body next) ∨
      (∃ failure next, traitBody input = .reject failure next) :=
  traitBody_invariantFreeOnValid input inputValid

theorem traitBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    traitBody input ≠ .invariant error :=
  traitBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.TraitInternals
