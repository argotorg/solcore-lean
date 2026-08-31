import Solcore.Syntax.Parser.DelimitedNonemptyProperties
import Solcore.Syntax.Parser.DelimitedTotalityProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.QualifiedNameTotalityProperties
import Solcore.Syntax.Parser.TypeNamedProperties

/-! Valid-input totality for the named-type parser path. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- A successful syntactically nonempty delimited parse satisfies `requireNonempty`. -/
theorem requireNonempty_ok_of_delimited_false_ok {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input afterDelimited : State} {parsed : DelimitedList α}
    (parsedResult : delimited opening closing false element context phase input =
      .ok parsed afterDelimited) :
    ∃ nonempty,
      requireNonempty parsed phase afterDelimited = .ok nonempty afterDelimited := by
  have nonempty := delimited_false_elements_ne_nil_onSuccess opening closing
    element context phase parsedResult
  unfold requireNonempty
  cases elements : parsed.elements with
  | nil => exact False.elim (nonempty elements)
  | cons head tail => exact ⟨_, rfl⟩

/-- In particular, `requireNonempty` cannot expose its defensive invariant. -/
theorem requireNonempty_ne_invariant_of_delimited_false_ok {α : Type}
    (opening closing : Symbol) (element : Parser α)
    (context : ParseContext) (phase : ParserPhase)
    {input afterDelimited : State} {parsed : DelimitedList α}
    (parsedResult : delimited opening closing false element context phase input =
      .ok parsed afterDelimited)
    (error : ParserInvariantError) :
    requireNonempty parsed phase afterDelimited ≠ .invariant error := by
  intro failed
  rcases requireNonempty_ok_of_delimited_false_ok opening closing element
      context phase parsedResult with ⟨nonempty, result⟩
  rw [result] at failed
  contradiction

theorem parseNamedTypeArguments_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ arguments next,
      parseNamedTypeArguments nested input = .ok arguments next) ∨
    (∃ failure next,
      parseNamedTypeArguments nested input = .reject failure next) := by
  by_cases present : isSymbol input .less
  · rcases delimited_ordinary .less .greater false nested .typeExpr .typeExpr
        contract input inputValid with
      ⟨parsed, afterDelimited, parsedResult⟩ |
      ⟨failure, rejected, parsedResult⟩
    · rcases requireNonempty_ok_of_delimited_false_ok .less .greater nested
        .typeExpr .typeExpr parsedResult with ⟨nonempty, nonemptyResult⟩
      exact Or.inl ⟨some nonempty, afterDelimited, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult, nonemptyResult, pure]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedTypeArguments, getState, bind, present,
          ↓reduceIte, parsedResult]⟩
  · have absent : isSymbol input .less = false := by
      cases found : isSymbol input .less with
      | false => rfl
      | true => exact False.elim (present found)
    exact Or.inl ⟨none, input, by
      simp only [parseNamedTypeArguments, getState, bind, absent,
        Bool.false_eq_true, ↓reduceIte, pure]⟩

theorem parseNamedTypeArguments_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedTypeArguments nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedTypeArguments_ordinary nested contract input inputValid with
    ⟨arguments, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

/-- Finishing a named type only performs total state update and construction. -/
theorem finishNamedType_ordinary (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr)) :
    Parser.Ordinary (finishNamedType name arguments) := by
  intro input
  unfold finishNamedType
  split
  · exact Or.inl ⟨makeNamedType name arguments, _, rfl⟩
  · exact Or.inl ⟨makeNamedType name arguments, input, rfl⟩

theorem finishNamedType_ne_invariant (name : QualifiedName)
    (arguments : Option (NonemptyDelimitedList TypeExpr))
    (input : State) (error : ParserInvariantError) :
    finishNamedType name arguments input ≠ .invariant error :=
  (finishNamedType_ordinary name arguments).ne_invariant input error

theorem parseNamedType_ordinary
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor) :
    (∃ value next, parseNamedType nested input = .ok value next) ∨
    (∃ failure next, parseNamedType nested input = .reject failure next) := by
  rcases (qualifiedName_ordinary .typeExpr .typeExpr) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := qualifiedName_validFor .typeExpr .typeExpr input inputValid
    rw [nameResult] at nameValid
    rcases parseNamedTypeArguments_ordinary nested contract afterName
        nameValid.2.1 with
      ⟨arguments, afterArguments, argumentsResult⟩ |
      ⟨failure, rejected, argumentsResult⟩
    · rcases finishNamedType_ordinary name arguments afterArguments with
        ⟨value, final, finished⟩ | ⟨failure, rejected, finished⟩
      · exact Or.inl ⟨value, final, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [parseNamedType, bind, nameResult, argumentsResult,
            finished]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [parseNamedType, bind, nameResult, argumentsResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [parseNamedType, bind, nameResult]⟩

theorem parseNamedType_ne_invariant
    (nested : Parser TypeExpr) (contract : ElementTotalityContract nested)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseNamedType nested input ≠ .invariant error := by
  intro failed
  rcases parseNamedType_ordinary nested contract input inputValid with
    ⟨value, next, result⟩ | ⟨failure, next, result⟩ <;>
      rw [result] at failed <;> contradiction

end Solcore.Syntax.Parser
