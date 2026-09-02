import Solcore.Syntax.DeclarativeDeriveAttributeRecoveryOutcomeGrammar
import Solcore.Syntax.Parser.ContractMemberCoreSoundnessProperties
import Solcore.Syntax.Parser.DelimitedRejectionPrimitiveProperties
import Solcore.Syntax.Parser.Derive
import Solcore.Syntax.Parser.ImportTerminatorOrdinarySuccessSoundnessProperties

/-!
Executable-to-declarative boundary bridges for malformed derive-attribute
recovery.  Recursive tail reflection is intentionally kept separate.
-/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

private theorem isSymbol_eq_true_of_tokenAt (value : Symbol)
    {input : State} {span : SourceSpan}
    (token : DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value }) :
    isSymbol input value = true := by
  unfold isSymbol State.peekKind? State.peek?
  simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  cases value <;> rfl

private theorem tokenAt_of_isSymbol_eq_true (value : Symbol)
    {input : State} (present : isSymbol input value = true) :
    ∃ span, DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
      input.cursor { span, value := .symbol value } := by
  rcases symbol_eq_ok_of_isSymbol_eq_true value .topItem present with
    ⟨token, parsed⟩
  exact ⟨token.span,
    (symbol_success_exactTokenParses value .topItem parsed).1⟩

private theorem atTopItemStart_eq_true_of_importTerminatorTopItemStartsAt
    {input : State}
    (starts : DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder) :
    atTopItemStart input = true := by
  rcases starts with ⟨kind, member, span, token⟩
  change DeclarativeGrammar.TokenAt input.tokens input.window.endIndex
    input.cursor { span, value := kind } at token
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [token.1, ↓reduceIte, token.2, Option.map_some]
  unfold atTopItemStart
  rw [peekKind]
  exact (importTerminatorTopItemStartKind_iff kind).mpr member

namespace DeriveAttributeInternals

private theorem declarationBoundaryGuard_eq (input : State) :
    atDeriveDeclarationBoundary input =
      (atTopItemStart input || ContractInternals.startsContractField input ||
        isSymbol input .rightBrace) := by
  rfl

/-- A true executable declaration-boundary guard exposes the exact first
matching declarative boundary in dispatcher priority order. -/
theorem recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
    {input : State} (present : atDeriveDeclarationBoundary input = true) :
    DeclarativeGrammar.DeriveAttributeRecoveryDeclarationStartsAt
      input.declarativeRemainder := by
  rw [declarationBoundaryGuard_eq] at present
  by_cases topItem : atTopItemStart input = true
  · exact .topItem
      (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true topItem)
  · have topItemFalse : atTopItemStart input = false :=
      Bool.eq_false_iff.mpr topItem
    by_cases field : ContractInternals.startsContractField input = true
    · exact .contractField
        (ContractInternals.contractFieldStartsAt_of_startsContractField_eq_true
          field)
    · have fieldFalse :
          ContractInternals.startsContractField input = false :=
        Bool.eq_false_iff.mpr field
      have rightBrace : isSymbol input .rightBrace = true := by
        simpa [topItemFalse, fieldFalse] using present
      rcases tokenAt_of_isSymbol_eq_true .rightBrace rightBrace with
        ⟨span, token⟩
      exact .rightBrace span token

/-- Every declarative recovery declaration boundary makes the executable
boundary guard true. -/
theorem atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
    {input : State}
    (starts : DeclarativeGrammar.DeriveAttributeRecoveryDeclarationStartsAt
      input.declarativeRemainder) :
    atDeriveDeclarationBoundary input = true := by
  rw [declarationBoundaryGuard_eq]
  cases starts with
  | topItem topItemStarts =>
      have topItem :=
        atTopItemStart_eq_true_of_importTerminatorTopItemStartsAt topItemStarts
      simp [topItem]
  | contractField fieldStarts =>
      have field :=
        ContractInternals.startsContractField_eq_true_of_contractFieldStartsAt
          fieldStarts
      simp [field]
  | rightBrace span token =>
      have rightBrace := isSymbol_eq_true_of_tokenAt .rightBrace token
      simp [rightBrace]

/-- The second executable tail guard gives an exact nonconsuming unclosed
recovery stop.  A preceding right-bracket guard is handled by the caller. -/
theorem recoveryStops_of_unclosedGuard_eq_true (input : State)
    (stops : (input.atEnd || atDeriveDeclarationBoundary input) = true) :
    DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  by_cases atEnd : input.window.endIndex ≤ input.cursor
  · exact .windowEnd atEnd
  · have atEndFalse : input.atEnd = false := by
      unfold State.atEnd
      exact decide_eq_false atEnd
    have boundary : atDeriveDeclarationBoundary input = true := by
      simpa [atEndFalse] using stops
    exact .declaration
      (recoveryDeclarationStartsAt_of_atDeriveDeclarationBoundary_eq_true
        boundary)

/-- With the second guard false, failure to advance is exactly a missing array
slot inside the active token window. -/
theorem recoveryStops_of_advance?_eq_none (input : State)
    (guard : (input.atEnd || atDeriveDeclarationBoundary input) = false)
    (advanced : input.advance? = none) :
    DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  have notAtEnd : ¬ input.window.endIndex ≤ input.cursor := by
    intro atEnd
    have atEndTrue : input.atEnd = true := by
      unfold State.atEnd
      exact decide_eq_true atEnd
    simp [atEndTrue] at guard
  have inside : input.cursor < input.window.endIndex := by omega
  apply DeclarativeGrammar.DeriveAttributeRecoveryStops.missingToken inside
  unfold State.advance? State.peek? at advanced
  simpa [State.declarativeRemainder, inside] using advanced

/-- A current token under a false second guard excludes every declarative
recovery stop, so the tail must advance after its separate `]` check. -/
theorem no_recoveryStops_of_nonBoundary_token
    {input : State} {token : Token}
    (guard : (input.atEnd || atDeriveDeclarationBoundary input) = false)
    (found : input.peek? = some token) :
    ¬ DeclarativeGrammar.DeriveAttributeRecoveryStops
      input.declarativeRemainder := by
  intro stops
  have current := tokenAt_of_peek?_eq_some found
  cases stops with
  | windowEnd atEnd =>
      exact Nat.not_lt_of_ge atEnd
        (State.cursor_lt_endIndex_of_peek?_eq_some found)
  | declaration starts =>
      have boundary :=
        atDeriveDeclarationBoundary_eq_true_of_recoveryDeclarationStartsAt
          starts
      simp [boundary] at guard
  | missingToken inside missing =>
      change input.tokens[input.cursor]? = none at missing
      rw [current.2] at missing
      contradiction

end DeriveAttributeInternals
end Solcore.Syntax.Parser
