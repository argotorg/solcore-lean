import Solcore.Syntax.Parser.ExpressionAtomTupleUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionAtomCollectionUnrestrictedFuelTotalityProperties
import Solcore.Syntax.Parser.ExpressionAtomDispatchSelectionTraceProperties
import Solcore.Syntax.Parser.LambdaExpressionTraceProperties
import Solcore.Syntax.Parser.Expression.Atom

/-! One atom layer is ordinary under an explicit remaining-count bound and
the minimal three-field nested contract. Blocks need only ordinary execution.
Public recovery preserves this bounded result without inspecting child frames;
no global ordinary contract or recursive trace existence is inferred. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ExpressionAtomInternals

open DeclarativeGrammar ExpressionAtomDispatchTraceInternals

private theorem ordinary_bind {α β : Type} {first : Parser α} {next : α → Parser β}
    (firstOrdinary : Parser.Ordinary first) (nextOrdinary : ∀ value, Parser.Ordinary (next value)) :
    Parser.Ordinary (first >>= next) := by
  intro input
  rcases firstOrdinary input with ⟨value, after, result⟩ | ⟨failure, rejected, result⟩
  · rcases nextOrdinary value after with ⟨value, output, nextResult⟩ | ⟨failure, rejected, nextResult⟩
    · exact .inl ⟨value, output, by simp only [bind, result, nextResult]⟩
    · exact .inr ⟨failure, rejected, by simp only [bind, result, nextResult]⟩
  · exact .inr ⟨failure, rejected, by simp only [bind, result]⟩

private theorem literal_ordinary : Parser.Ordinary literalExpression := by
  unfold literalExpression
  apply ordinary_bind coreLiteral_ordinary
  intro literal input
  exact .inl ⟨_, input, rfl⟩

private theorem name_ordinary : Parser.Ordinary identifierExpression := by
  unfold identifierExpression
  apply ordinary_bind expressionName_ordinary
  intro name input
  exact .inl ⟨_, input, rfl⟩

private theorem proxy_ordinary : Parser.Ordinary proxyExpression := by
  unfold proxyExpression
  apply ordinary_bind (symbol_ordinary .at .expression)
  intro marker
  apply ordinary_bind typeExpr_ordinary
  intro type input
  exact .inl ⟨_, input, rfl⟩

private theorem raw_ordinary (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block) (branch : ExpressionAtomDispatchBranch)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, rawParser nested block branch input = .ok value next) ∨
    (∃ failure next, rawParser nested block branch input = .reject failure next) := by
  cases branch with
  | literal => exact literal_ordinary input
  | name => exact name_ordinary input
  | dotConstructor => exact dotConstructor_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | proxy => exact proxy_ordinary input
  | parenthesized => exact parenthesized_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | array => exact arrayLiteral_ordinary_of_unrestrictedElementFuel nested nestedFuel contract input adequate
  | lambda => exact lambdaExpression_ordinary_unrestricted blockOrdinary input
  | final => exact .inr ⟨_, input, rfl⟩

theorem expressionAtomCore_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, expressionAtomCore nested block input = .ok value next) ∨
    (∃ failure next, expressionAtomCore nested block input = .reject failure next) := by
  rw [expressionAtomCore_eq_selected_raw]
  exact raw_ordinary nested block nestedFuel contract blockOrdinary (selectedBranch input) input adequate

theorem expressionAtomCore_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionAtomCore nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

/-- Recovery needs no bound on a failed child's replacement carrier: its
standalone parser is ordinary on every rewound and report-extended State. -/
theorem expressionAtom_ordinary_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) :
    (∃ value next, expressionAtom nested block input = .ok value next) ∨
    (∃ failure next, expressionAtom nested block input = .reject failure next) := by
  rcases expressionAtomCore_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, failed, result⟩
  · exact .inl ⟨value, next, by simp only [expressionAtom, result]⟩
  · simp only [expressionAtom, result]
    split
    · exact .inr ⟨_, _, rfl⟩
    · exact recoverAtom_ordinary _

theorem expressionAtom_ne_invariant_of_unrestrictedElementFuel
    (nested : Parser Expr) (block : Parser Block) (nestedFuel : Nat)
    (contract : UnrestrictedFuelElementContract nested nestedFuel)
    (blockOrdinary : Parser.Ordinary block)
    (input : State) (adequate : input.remainingCount < nestedFuel + 1) (error : ParserInvariantError) :
    expressionAtom nested block input ≠ .invariant error := by
  intro failed
  rcases expressionAtom_ordinary_of_unrestrictedElementFuel nested block nestedFuel contract blockOrdinary input adequate with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;> rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser.ExpressionAtomInternals
