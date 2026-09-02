import Solcore.Syntax.DeclarativeContractMemberRecoveryOutcomeGrammar
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.ContractRecoveryProperties
import Solcore.Syntax.Parser.CoreTypeOutcomePrimitiveProperties

/-! Executable-to-declarative boundary bridges for contract-member recovery. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser.ContractInternals

private theorem symbolPresent_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol value) := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .topItem result).1⟩

private theorem keywordPresent_of_isKeyword_eq_true (value : HardKeyword)
    {input : State} (present : isKeyword input value = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value) := by
  rcases keyword_eq_ok_of_isKeyword_eq_true value .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (keyword_success_exactTokenParses value .topItem result).1⟩

private theorem enumPresent_of_isContextual_eq_true {input : State}
    (present : isContextual input .enum = true) :
    DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling) := by
  rcases contextual_eq_ok_of_isContextual_eq_true .enum .topItem present with
    ⟨token, result⟩
  exact ⟨token.span,
    (contextual_success_exactTokenParses .enum .topItem result).1⟩

private theorem isSymbol_eq_true_of_present (value : Symbol)
    {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.symbol value)) :
    isSymbol input value = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .symbol value } at token
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem isKeyword_eq_true_of_present (value : HardKeyword)
    {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder (.keyword value)) :
    isKeyword input value = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := .keyword value } at token
  unfold isKeyword State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  change instBEqTokenKind.beq (.keyword value) (.keyword value) = true
  simp only [instBEqTokenKind.beq]
  change instBEqHardKeyword.beq value value = true
  unfold instBEqHardKeyword.beq
  cases value <;> rfl

private theorem isEnum_eq_true_of_present {input : State}
    (present : DeclarativeGrammar.ContractMemberCoreTokenPresentAt
      input.declarativeRemainder
        (.identifier ContextualKeyword.enum.spelling)) :
    isContextual input .enum = true := by
  rcases present with ⟨span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor {
      span
      value := .identifier ContextualKeyword.enum.spelling
    } at token
  unfold isContextual State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some,
    TokenKind.isContextual]
  exact beq_iff_eq.mpr rfl

/-- A true executable boundary guard exposes one exact declarative boundary. -/
theorem recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
    {input : State} (present : atContractRecoveryBoundary input = true) :
    DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder := by
  unfold atContractRecoveryBoundary at present
  by_cases hash : isSymbol input .hash = true
  · exact .hash (symbolPresent_of_isSymbol_eq_true .hash hash)
  · have hashFalse : isSymbol input .hash = false := Bool.eq_false_iff.mpr hash
    by_cases function : isKeyword input .functionKw = true
    · exact .function
        (keywordPresent_of_isKeyword_eq_true .functionKw function)
    · have functionFalse : isKeyword input .functionKw = false :=
        Bool.eq_false_iff.mpr function
      by_cases constructor : isKeyword input .constructorKw = true
      · exact .constructor
          (keywordPresent_of_isKeyword_eq_true .constructorKw constructor)
      · have constructorFalse : isKeyword input .constructorKw = false :=
          Bool.eq_false_iff.mpr constructor
        by_cases fallback : isKeyword input .fallbackKw = true
        · exact .fallback
            (keywordPresent_of_isKeyword_eq_true .fallbackKw fallback)
        · have fallbackFalse : isKeyword input .fallbackKw = false :=
            Bool.eq_false_iff.mpr fallback
          by_cases typeAlias : isKeyword input .typeKw = true
          · exact .typeAlias
              (keywordPresent_of_isKeyword_eq_true .typeKw typeAlias)
          · have typeFalse : isKeyword input .typeKw = false :=
              Bool.eq_false_iff.mpr typeAlias
            by_cases closing : isSymbol input .rightBrace = true
            · exact .rightBrace
                (symbolPresent_of_isSymbol_eq_true .rightBrace closing)
            · have closingFalse : isSymbol input .rightBrace = false :=
                Bool.eq_false_iff.mpr closing
              have enum : isContextual input .enum = true := by
                simpa [hashFalse, functionFalse, constructorFalse,
                  fallbackFalse, typeFalse, closingFalse] using present
              exact .enum (enumPresent_of_isContextual_eq_true enum)

/-- Every exact declarative boundary makes the executable guard true. -/
theorem atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ContractMemberRecoveryBoundaryStartsAt
      input.declarativeRemainder) :
    atContractRecoveryBoundary input = true := by
  cases starts with
  | hash present =>
      simp [atContractRecoveryBoundary,
        isSymbol_eq_true_of_present .hash present]
  | function present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .functionKw present]
  | constructor present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .constructorKw present]
  | fallback present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .fallbackKw present]
  | typeAlias present =>
      simp [atContractRecoveryBoundary,
        isKeyword_eq_true_of_present .typeKw present]
  | rightBrace present =>
      simp [atContractRecoveryBoundary,
        isSymbol_eq_true_of_present .rightBrace present]
  | enum present =>
      simp [atContractRecoveryBoundary, isEnum_eq_true_of_present present]

/-- A true auxiliary guard gives an exact nonconsuming recovery stop. -/
theorem contractMemberRecoveryStops_of_guard_eq_true (input : State)
    (stops : (input.atEnd || atContractRecoveryBoundary input) = true) :
    DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atContractRecoveryBoundary input = true := by
      simpa [atEndFalse] using stops
    exact .boundary
      (recoveryBoundaryStartsAt_of_atContractRecoveryBoundary_eq_true
        boundary)

/-- Under a false auxiliary guard, failed advancement is an exact missing
carrier slot inside the active window. -/
theorem contractMemberRecoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atContractRecoveryBoundary input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.ContractMemberRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false auxiliary guard excludes every exact stop. -/
theorem no_contractMemberRecoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atContractRecoveryBoundary input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.ContractMemberRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | boundary starts =>
      have boundary :=
        atContractRecoveryBoundary_eq_true_of_recoveryBoundaryStartsAt starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end Solcore.Syntax.Parser.ContractInternals
