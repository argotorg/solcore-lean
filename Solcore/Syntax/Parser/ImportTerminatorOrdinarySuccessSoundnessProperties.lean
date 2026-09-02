import Solcore.Syntax.DeclarativeImportTerminatorOutcomeGrammar
import Solcore.Syntax.Parser.DeclarativePrimitiveProperties
import Solcore.Syntax.Parser.Import

/-! Broad ordinary-success reflection for import terminators. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable top-item-start predicate admits exactly the finite token
kinds recorded by the declarative import-terminator grammar. -/
theorem importTerminatorTopItemStartKind_iff (kind : TokenKind) :
    isTopItemStartKind kind = true ↔
      kind ∈ DeclarativeGrammar.ImportTerminatorTopItemStartKinds := by
  cases kind with
  | keyword keyword =>
      cases keyword <;> simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | symbol symbol =>
      cases symbol <;> simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | identifier text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual, Bool.or_eq_true, or_assoc]
  | yulIdentifier text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | decimalLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | hexadecimalLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | stringLiteral text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | yulMetaBacktick text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]
  | yulMetaInterpolation text =>
      simp [isTopItemStartKind,
        DeclarativeGrammar.ImportTerminatorTopItemStartKinds,
        TokenKind.isContextual]

/-- Positive executable top-item lookahead exposes the exact current token. -/
theorem importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true
    {input : State} (present : atTopItemStart input = true) :
    DeclarativeGrammar.ImportTerminatorTopItemStartsAt
      input.declarativeRemainder := by
  unfold atTopItemStart State.peekKind? at present
  cases found : input.peek? with
  | none => simp [found] at present
  | some token =>
      rcases token with ⟨span, kind⟩
      simp only [found, Option.map_some] at present
      exact ⟨kind, (importTerminatorTopItemStartKind_iff kind).mp present,
        span, tokenAt_of_peek?_eq_some found⟩

/-- Negative executable top-item lookahead excludes every admitted start
kind at the current cursor. -/
theorem importTerminatorTopItemStartAbsentAt_of_atTopItemStart_eq_false
    {input : State} (absent : atTopItemStart input = false) :
    DeclarativeGrammar.TopItemKindsAbsentAt input.declarativeRemainder
      DeclarativeGrammar.ImportTerminatorTopItemStartKinds := by
  intro kind member
  rintro ⟨span, inside, found⟩
  change input.cursor < input.window.endIndex at inside
  change input.tokens[input.cursor]? = some { span, value := kind } at found
  have peekKind : input.peekKind? = some kind := by
    unfold State.peekKind? State.peek?
    simp only [inside, ↓reduceIte, found, Option.map_some]
  have stopped : isTopItemStartKind kind = false := by
    simpa [atTopItemStart, peekKind] using absent
  have starts : isTopItemStartKind kind = true :=
    (importTerminatorTopItemStartKind_iff kind).mpr member
  rw [starts] at stopped
  contradiction

/-- Every executable import-terminator success is an exact semicolon success
or the nonconsuming diagnostic recovery before a top-item start. -/
theorem importTerminator_success_ordinaryOutcome_sound (lastSpan : SourceSpan)
    {input output : State} {endSpan : SourceSpan}
    (result : ImportInternals.terminator lastSpan input = .ok endSpan output) :
    DeclarativeGrammar.ImportTerminatorOrdinaryParses lastSpan
      input.declarativeRemainder endSpan output.declarativeRemainder := by
  unfold ImportInternals.terminator at result
  by_cases semicolonPresent : isSymbol input .semicolon = true
  · simp only [semicolonPresent, if_true] at result
    cases semicolonResult : symbol .semicolon .importDecl input with
    | invariant error => simp [semicolonResult] at result
    | reject failure rejected => simp [semicolonResult] at result
    | ok token next =>
        simp only [semicolonResult] at result
        cases result
        exact .semicolon token.span
          (symbol_success_exactTokenParses .semicolon .importDecl
            semicolonResult)
  · have semicolonAbsent : isSymbol input .semicolon = false :=
      Bool.eq_false_iff.mpr semicolonPresent
    simp only [semicolonAbsent, Bool.false_eq_true, if_false] at result
    by_cases topItemPresent : atTopItemStart input = true
    · simp only [topItemPresent, if_true] at result
      cases result
      simpa only [State.emit, State.declarativeRemainder] using
        (DeclarativeGrammar.ImportTerminatorOrdinaryParses.recovered
          (lastSpan := lastSpan)
          (symbolAbsentAt_of_isSymbol_eq_false .semicolon semicolonAbsent)
          (importTerminatorTopItemStartsAt_of_atTopItemStart_eq_true
            topItemPresent))
    · have topItemAbsent : atTopItemStart input = false :=
        Bool.eq_false_iff.mpr topItemPresent
      simp [topItemAbsent, rejectAt] at result

end Solcore.Syntax.Parser
