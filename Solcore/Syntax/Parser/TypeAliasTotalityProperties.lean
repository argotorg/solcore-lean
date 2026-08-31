import Solcore.Syntax.Parser.InvariantFreeProperties
import Solcore.Syntax.Parser.PrimitiveTotalityProperties
import Solcore.Syntax.Parser.TypeAliasProperties
import Solcore.Syntax.Parser.TypeAliasRecoveryTotalityProperties
import Solcore.Syntax.Parser.TypeFuelTotalityProperties

/-! Conditional totality for complete canonical type aliases. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional alias parameters are invariant-free on every valid input. -/
theorem parseTypeAliasParameters_invariantFreeOnValid :
    Parser.InvariantFreeOnValid parseTypeAliasParameters := by
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .leftParen
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (delimited_validFor Located.ValidFor .leftParen .rightParen true
        (identifier .parameter) .typeAlias .typeAlias
        (identifier_validFor .parameter)
        (identifier_preservesTokensOnSuccess .parameter))
      (Parser.invariantFreeOnValid_of_ne_invariant (fun input inputValid error =>
        delimited_ne_invariant .leftParen .rightParen true
          (identifier .parameter) .typeAlias .typeAlias
          (identifier_elementTotalityContract .parameter)
          input inputValid error))
    intro values
    exact Parser.pure_invariantFreeOnValid (some values)
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

/-- Optional alias parameters cannot expose an internal invariant. -/
theorem parseTypeAliasParameters_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseTypeAliasParameters input ≠ .invariant error :=
  parseTypeAliasParameters_invariantFreeOnValid.ne_invariant
    input inputValid error

namespace TypeAliasInternals

/-- Alias RHS parsing is total once recursive type parsing is total. -/
theorem parseAliasValue_invariantFreeOnValid
    (typeFree : Parser.InvariantFreeOnValid typeExpr) :
    Parser.InvariantFreeOnValid parseAliasValue := by
  intro input inputValid
  unfold parseAliasValue
  cases coreResult : typeExpr input with
  | ok value next => exact Or.inl ⟨value, next, rfl⟩
  | invariant error =>
      exact False.elim (typeFree.ne_invariant input inputValid error coreResult)
  | reject failure failedState =>
      dsimp only
      split
      · exact Or.inr ⟨failure, _, rfl⟩
      · exact recoverTypeAliasValue_ordinary _

/-- Alias RHS parsing cannot expose an invariant under the type premise. -/
theorem parseAliasValue_ne_invariant
    (typeFree : Parser.InvariantFreeOnValid typeExpr)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parseAliasValue input ≠ .invariant error :=
  (parseAliasValue_invariantFreeOnValid typeFree).ne_invariant
    input inputValid error

end TypeAliasInternals

/-- A complete type alias is total once recursive type parsing is total. -/
theorem typeAlias_invariantFreeOnValid_of_type
    (typeFree : Parser.InvariantFreeOnValid typeExpr) :
    Parser.InvariantFreeOnValid typeAlias := by
  unfold typeAlias
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .typeKw .typeAlias)
    (keyword_ordinary .typeKw .typeAlias).invariantFreeOnValid
  intro typeKeyword
  apply Parser.bind_invariantFreeOnValid
    (identifier_validFor .typeAlias)
    (identifier_ordinary .typeAlias).invariantFreeOnValid
  intro name
  apply Parser.bind_invariantFreeOnValid
    parseTypeAliasParameters_validFor
    parseTypeAliasParameters_invariantFreeOnValid
  intro parameters
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .equal .typeAlias)
    (symbol_ordinary .equal .typeAlias).invariantFreeOnValid
  intro equal
  apply Parser.bind_invariantFreeOnValid
    TypeAliasInternals.parseAliasValue_validFor
    (TypeAliasInternals.parseAliasValue_invariantFreeOnValid typeFree)
  intro value
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .semicolon .typeAlias)
    (symbol_ordinary .semicolon .typeAlias).invariantFreeOnValid
  intro semicolon
  exact Parser.pure_invariantFreeOnValid ({
    span := SourceSpan.cover typeKeyword.span semicolon.span
    value := { name, parameters, value }
  } : TypeAliasDecl)

/-- Complete type aliases cannot expose an invariant under the type premise. -/
theorem typeAlias_ne_invariant_of_type
    (typeFree : Parser.InvariantFreeOnValid typeExpr)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeAlias input ≠ .invariant error :=
  (typeAlias_invariantFreeOnValid_of_type typeFree).ne_invariant
    input inputValid error

/-- Complete canonical type aliases are invariant-free on valid input. -/
theorem typeAlias_invariantFreeOnValid :
    Parser.InvariantFreeOnValid typeAlias :=
  typeAlias_invariantFreeOnValid_of_type typeExpr_invariantFreeOnValid

theorem typeAlias_ne_invariant
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    typeAlias input ≠ .invariant error :=
  typeAlias_invariantFreeOnValid.ne_invariant input inputValid error

end Solcore.Syntax.Parser
