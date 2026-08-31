import Solcore.Syntax.Parser.ContractProperties
import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Valid-input totality laws local to contract fields. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

/-- An optional initializer introduces no invariant beyond its expression parser. -/
theorem optionalFieldInitializer_invariantFreeOnValid
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid
      (optionalFieldInitializer expressionParser) := by
  intro input inputValid
  by_cases present : isSymbol input .equal
  · rcases (symbol_ordinary .equal .contractMember) input with
      ⟨equal, afterEqual, equalResult⟩ |
      ⟨failure, rejected, equalResult⟩
    · have equalValid := symbol_validFor .equal .contractMember input inputValid
      rw [equalResult] at equalValid
      rcases expressionFree afterEqual equalValid.2.1 with
        ⟨value, final, expressionResult⟩ |
        ⟨failure, final, expressionResult⟩
      · exact Or.inl ⟨some value, final, by
          simp only [optionalFieldInitializer, getState, bind, present,
            ↓reduceIte, equalResult, expressionResult, pure]⟩
      · exact Or.inr ⟨failure, final, by
          simp only [optionalFieldInitializer, getState, bind, present,
            ↓reduceIte, equalResult, expressionResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [optionalFieldInitializer, getState, bind, present,
          ↓reduceIte, equalResult]⟩
  · exact Or.inl ⟨none, input, by
      have absent : isSymbol input .equal = false :=
        by
          cases found : isSymbol input .equal with
          | false => rfl
          | true => exact False.elim (present found)
      simp only [optionalFieldInitializer, getState, bind, absent, Bool.false_eq_true,
        ↓reduceIte, pure]⟩

theorem optionalFieldInitializer_ne_invariant
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    optionalFieldInitializer expressionParser input ≠ .invariant error :=
  (optionalFieldInitializer_invariantFreeOnValid expressionParser
    expressionFree).ne_invariant input inputValid error

/--
A contract field introduces no invariant beyond its expression parser. Public
recursive type parsing and the final semicolon parser are already total.
-/
theorem contractField_invariantFreeOnValid
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser) :
    Parser.InvariantFreeOnValid (contractField expressionParser) := by
  intro input inputValid
  rcases (identifier_ordinary .contractMember) input with
    ⟨name, afterName, nameResult⟩ | ⟨failure, rejected, nameResult⟩
  · have nameValid := identifier_validFor .contractMember input inputValid
    rw [nameResult] at nameValid
    rcases (symbol_ordinary .colon .contractMember) afterName with
      ⟨colon, afterColon, colonResult⟩ |
      ⟨failure, rejected, colonResult⟩
    · have colonValid := symbol_validFor .colon .contractMember afterName
        nameValid.2.1
      rw [colonResult] at colonValid
      rcases typeExpr_invariantFreeOnValid afterColon colonValid.2.1 with
        ⟨type, afterType, typeResult⟩ |
        ⟨failure, rejected, typeResult⟩
      · have typeValid := typeExpr_validFor afterColon colonValid.2.1
        rw [typeResult] at typeValid
        rcases optionalFieldInitializer_invariantFreeOnValid expressionParser
            expressionFree afterType typeValid.2.1 with
          ⟨initializer, afterInitializer, initializerResult⟩ |
          ⟨failure, rejected, initializerResult⟩
        · rcases (symbol_ordinary .semicolon .contractMember)
              afterInitializer with
            ⟨semicolon, final, semicolonResult⟩ |
            ⟨failure, rejected, semicolonResult⟩
          · exact Or.inl ⟨{
                span := SourceSpan.cover name.span semicolon.span
                value := { name, type, initializer }
              }, final, by
              simp only [contractField, bind, nameResult, colonResult,
                typeResult, initializerResult, semicolonResult, pure]⟩
          · exact Or.inr ⟨failure, rejected, by
              simp only [contractField, bind, nameResult, colonResult,
                typeResult, initializerResult, semicolonResult]⟩
        · exact Or.inr ⟨failure, rejected, by
            simp only [contractField, bind, nameResult, colonResult,
              typeResult, initializerResult]⟩
      · exact Or.inr ⟨failure, rejected, by
          simp only [contractField, bind, nameResult, colonResult, typeResult]⟩
    · exact Or.inr ⟨failure, rejected, by
        simp only [contractField, bind, nameResult, colonResult]⟩
  · exact Or.inr ⟨failure, rejected, by
      simp only [contractField, bind, nameResult]⟩

theorem contractField_ne_invariant
    (expressionParser : Parser Expr)
    (expressionFree : Parser.InvariantFreeOnValid expressionParser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    contractField expressionParser input ≠ .invariant error :=
  (contractField_invariantFreeOnValid expressionParser
    expressionFree).ne_invariant input inputValid error

end Solcore.Syntax.Parser.ContractInternals
