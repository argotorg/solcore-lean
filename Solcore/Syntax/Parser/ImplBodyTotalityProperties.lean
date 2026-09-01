import Solcore.Syntax.Parser.DelimitedFuelTotalityProperties
import Solcore.Syntax.Parser.FunctionDeclarationTotalityProperties
import Solcore.Syntax.Parser.ImplProperties

/-! Valid-input totality for canonical implementation methods and bodies. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ImplInternals

private theorem bind_ok_components {alpha beta : Type}
    {first : Parser alpha} {next : alpha → Parser beta}
    {input final : State} {value : beta}
    (parsed : (first >>= next) input = .ok value final) :
    ∃ firstValue afterFirst, first input = .ok firstValue afterFirst ∧
      next firstValue afterFirst = .ok value final := by
  change (match first input with
    | .ok firstValue afterFirst => next firstValue afterFirst
    | .reject failure rejected => .reject failure rejected
    | .invariant error => .invariant error) = .ok value final at parsed
  cases firstResult : first input with
  | ok firstValue afterFirst =>
      rw [firstResult] at parsed
      exact ⟨firstValue, afterFirst, rfl, parsed⟩
  | reject failure rejected => rw [firstResult] at parsed; contradiction
  | invariant error => rw [firstResult] at parsed; contradiction

/-- An implementation method inherits totality from a module function. -/
theorem implMethod_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implMethod := by
  unfold implMethod
  apply Parser.bind_invariantFreeOnValid
    (functionDecl_validFor CoreStatement.ValidFor .module
      (block_canonical_validFor .allow))
    (functionDecl_invariantFreeOnValid .module)
  intro declaration
  exact Parser.pure_invariantFreeOnValid ({
    span := declaration.span
    value := { leadingComments := [], declaration }
  } : ImplMethod)

theorem implMethod_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ method next, implMethod input = .ok method next) ∨
      (∃ failure next, implMethod input = .reject failure next) :=
  implMethod_invariantFreeOnValid input inputValid

theorem implMethod_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implMethod input ≠ .invariant error :=
  implMethod_invariantFreeOnValid.ne_invariant input inputValid error

/-- A successful implementation method consumes its function signature. -/
theorem implMethod_cursor_lt_onSuccess {input final : State}
    {method : ImplMethod}
    (parsed : implMethod input = .ok method final) :
    input.cursor < final.cursor := by
  unfold implMethod at parsed
  rcases bind_ok_components parsed with
    ⟨declaration, afterDeclaration, declarationResult, finished⟩
  cases finished
  unfold functionDecl at declarationResult
  rcases bind_ok_components declarationResult with
    ⟨signature, afterSignature, signatureResult, rest⟩
  rcases bind_ok_components rest with
    ⟨body, afterBody, bodyResult, finished⟩
  cases finished
  exact Nat.lt_of_lt_of_le
    (FunctionInternals.functionSignature_cursor_lt_onSuccess .module
      signatureResult)
    (isolateBlock_cursorMonotoneOnSuccess (block .allow)
      (block_canonical_cursorMonotoneOnSuccess .allow)
      afterSignature body final bodyResult)

private theorem closeImplBody_ordinary (opening : Token)
    (methodsRev : List ImplMethod) :
    Parser.Ordinary (closeImplBody opening methodsRev) := by
  intro input
  rcases (symbol_ordinary .rightBrace .topItem) input with
    ⟨closing, next, closingResult⟩ |
    ⟨failure, rejected, closingResult⟩
  · exact Or.inl ⟨{
      span := SourceSpan.cover opening.span closing.span
      methods := methodsRev.reverse
    }, next, by
      simp only [closeImplBody, bind, closingResult, pure]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [closeImplBody, bind, closingResult]⟩

/-- Adequate loop fuel excludes both exhaustion and no-progress invariants. -/
theorem implMethods_ordinary_of_remainingCount_lt (opening : Token) :
    ∀ fuel methodsRev input,
      input.ValidFor → input.remainingCount < fuel →
      (∃ body next,
        implMethods opening fuel methodsRev input = .ok body next) ∨
      (∃ failure next,
        implMethods opening fuel methodsRev input = .reject failure next) := by
  intro fuel
  induction fuel with
  | zero => intros; omega
  | succ fuel inductionHypothesis =>
      intro methodsRev input inputValid adequate
      unfold implMethods
      by_cases closes : isSymbol input .rightBrace
      · simpa only [closes, if_true] using
          closeImplBody_ordinary opening methodsRev input
      · by_cases methodPresent : isKeyword input .functionKw
        · rcases implMethod_ordinary input inputValid with
            ⟨method, next, methodResult⟩ |
            ⟨failure, rejected, methodResult⟩
          · have methodReply := implMethod_validFor CoreStatement.ValidFor
              (block_canonical_validFor .allow) input inputValid
            rw [methodResult] at methodReply
            have methodWindow := implMethod_preservesTokenWindow_of_block
              (block_canonical_preservesTokenWindow .allow) input
            rw [methodResult] at methodWindow
            have progress := implMethod_cursor_lt_onSuccess methodResult
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
                (alpha := ImplBody)
                { head := .keyword .functionKw,
                  tail := [.symbol .rightBrace] }
                .topItem) input inputValid

/-- Production fuel is one more than the current remaining token count. -/
theorem implMethods_production_ordinary
    (opening : Token) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor) :
    (∃ body next,
      implMethods opening (input.remainingCount + 1) methodsRev input =
        .ok body next) ∨
      (∃ failure next,
        implMethods opening (input.remainingCount + 1) methodsRev input =
          .reject failure next) :=
  implMethods_ordinary_of_remainingCount_lt opening
    (input.remainingCount + 1) methodsRev input inputValid (by omega)

theorem implMethods_production_invariantFreeOnValid
    (opening : Token) (methodsRev : List ImplMethod) :
    Parser.InvariantFreeOnValid (fun input =>
      implMethods opening (input.remainingCount + 1) methodsRev input) :=
  fun input inputValid =>
    implMethods_production_ordinary opening methodsRev input inputValid

theorem implMethods_production_ne_invariant
    (opening : Token) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implMethods opening (input.remainingCount + 1) methodsRev input ≠
      .invariant error :=
  (implMethods_production_invariantFreeOnValid opening methodsRev
    ).ne_invariant input inputValid error

theorem implMethods_ne_invariant_of_remainingCount_lt
    (opening : Token) (fuel : Nat) (methodsRev : List ImplMethod)
    (input : State) (inputValid : input.ValidFor)
    (adequate : input.remainingCount < fuel)
    (error : ParserInvariantError) :
    implMethods opening fuel methodsRev input ≠ .invariant error := by
  intro failed
  rcases implMethods_ordinary_of_remainingCount_lt opening fuel methodsRev
      input inputValid adequate with
    ⟨body, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- A complete canonical implementation body is total on valid input. -/
theorem implBody_invariantFreeOnValid :
    Parser.InvariantFreeOnValid implBody := by
  intro input inputValid
  rcases (symbol_ordinary .leftBrace .topItem) input with
    ⟨opening, next, openingResult⟩ |
    ⟨failure, rejected, openingResult⟩
  · have openingReply := symbol_validFor .leftBrace .topItem input inputValid
    rw [openingResult] at openingReply
    simpa only [implBody, openingResult] using
      implMethods_production_ordinary opening [] next openingReply.2.1
  · exact Or.inr ⟨failure, rejected, by
      simp only [implBody, openingResult]⟩

theorem implBody_ordinary (input : State) (inputValid : input.ValidFor) :
    (∃ body next, implBody input = .ok body next) ∨
      (∃ failure next, implBody input = .reject failure next) :=
  implBody_invariantFreeOnValid input inputValid

theorem implBody_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    implBody input ≠ .invariant error :=
  implBody_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser.ImplInternals
