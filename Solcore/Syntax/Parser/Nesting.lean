import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.DeclarativeNestingOutcomeGrammar
import Solcore.Syntax.Parser.Diagnostic
import Solcore.Syntax.DeclarativeNestingOutcomeProperties

/-! Bounded nesting preflight for the canonical syntax parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical parser guard applied before recursive token grammar. -/
def maxSyntaxNesting : Nat :=
  DeclarativeGrammar.canonicalNestingLimit

private abbrev NestingState := DeclarativeGrammar.NestingContext

private def nestingError (kind : NestingKind)
    (token : Token) : ParseDiagnostic := {
  span := token.span
  kind := .nestingExceeded kind maxSyntaxNesting
}

private def checkNestingAux :
    NestingState → List Token → Option ParseDiagnostic
  | _, [] => none
  | state, token :: rest =>
      match DeclarativeGrammar.nestingAction token.value with
      | .conditional =>
          let depth := state.conditionalDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .conditional token)
          else
            checkNestingAux { state with conditionalDepth := depth } rest
      | .groupOpen =>
          let depth := state.delimiterDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .delimiter token)
          else
            checkNestingAux {
              delimiterDepth := depth
              conditionalDepth := state.conditionalDepth
              conditionalBases := state.conditionalDepth ::
                state.conditionalBases
            } rest
      | .blockOpen =>
          let depth := state.delimiterDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .delimiter token)
          else
            checkNestingAux {
              delimiterDepth := depth
              conditionalDepth := 0
              conditionalBases := 0 :: state.conditionalBases
            } rest
      | .close => checkNestingAux state.closeDelimiter rest
      | .reset => checkNestingAux state.resetConditional rest
      | .preserve => checkNestingAux state rest

/-- First delimiter or conditional nesting violation, if one exists. -/
def checkNesting (tokens : List Token) : Option ParseDiagnostic :=
  checkNestingAux {} tokens

/-- Convert a parser-independent nesting overflow to its public diagnostic. -/
def nestingOverflowDiagnostic
    (overflow : DeclarativeGrammar.NestingOverflow) : ParseDiagnostic := {
  span := overflow.span
  kind := .nestingExceeded
    (match overflow.dimension with
      | .delimiter => .delimiter
      | .conditional => .conditional)
    overflow.limit
}

private theorem checkNestingAux_eq_map_of_scan
    {context : DeclarativeGrammar.NestingContext} {tokens : List Token}
    {result : Option DeclarativeGrammar.NestingOverflow}
    (scan : DeclarativeGrammar.NestingScans maxSyntaxNesting
      context tokens result) :
    checkNestingAux context tokens = result.map nestingOverflowDiagnostic := by
  induction scan with
  | done => rfl
  | conditionalExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | conditionalContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | groupExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | groupContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | blockExceeded action exceeds =>
      simp [checkNestingAux, action, if_pos exceeds, nestingError,
        nestingOverflowDiagnostic, DeclarativeGrammar.nestingOverflow]
  | blockContinues action within tail inductionHypothesis =>
      have notExceeded :
          ¬ maxSyntaxNesting < _ + 1 := Nat.not_lt_of_ge within
      simp [checkNestingAux, action, if_neg notExceeded,
        inductionHypothesis]
  | close action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]
  | reset action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]
  | preserve action tail inductionHypothesis =>
      simp [checkNestingAux, action, inductionHypothesis]

/-- Every declarative root scan computes the identical executable result. -/
theorem checkNesting_eq_map_of_outcome
    {tokens : List Token}
    {result : Option DeclarativeGrammar.NestingOverflow}
    (outcome : DeclarativeGrammar.NestingOutcome tokens result) :
    checkNesting tokens = result.map nestingOverflowDiagnostic := by
  exact checkNestingAux_eq_map_of_scan outcome

private theorem checkNestingAux_some_span_validFor
    (file : SourceFile) (state : NestingState) (tokens : List Token)
    (tokensValid : ∀ token ∈ tokens, token.span.ValidFor file)
    {diagnostic : ParseDiagnostic}
    (result : checkNestingAux state tokens = some diagnostic) :
    diagnostic.span.ValidFor file := by
  induction tokens generalizing state with
  | nil => simp [checkNestingAux] at result
  | cons token rest inductionHypothesis =>
      have tokenValid : token.span.ValidFor file :=
        tokensValid token (by simp)
      have restValid : ∀ retained ∈ rest,
          retained.span.ValidFor file := by
        intro retained member
        exact tokensValid retained (by simp [member])
      cases action : DeclarativeGrammar.nestingAction token.value <;>
          simp only [checkNestingAux, action] at result
      all_goals first
        | (split at result
           · cases result
             exact tokenValid
           · exact inductionHypothesis _ restValid result)
        | exact inductionHypothesis _ restValid result

/-- A reported nesting violation always points into the validated token file. -/
theorem checkNesting_some_span_validFor
    (file : SourceFile) (tokens : List Token)
    (tokensValid : SpanSequence.ValidFor file
      (fun token : Token => token.span) 0 tokens)
    {diagnostic : ParseDiagnostic}
    (result : checkNesting tokens = some diagnostic) :
    diagnostic.span.ValidFor file := by
  exact checkNestingAux_some_span_validFor file {} tokens
    (fun _ member => tokensValid.span_valid member) result

/-- Nesting diagnostics from a valid lexer result retain source provenance. -/
theorem checkNesting_lexed_some_span_validFor
    (file : SourceFile) (lexed : LexedFile)
    (lexedValid : lexed.ValidFor file)
    {diagnostic : ParseDiagnostic}
    (result : checkNesting lexed.tokens = some diagnostic) :
    diagnostic.span.ValidFor file :=
  checkNesting_some_span_validFor file lexed.tokens lexedValid.tokens result

end Solcore.Syntax.Parser

/-!
## Consolidated module: `Solcore.Syntax.Parser.NestingOutcomeSoundnessProperties`
-/

/-! Exact correspondence between executable and declarative nesting scans. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- The executable checker always exposes one exact declarative outcome. -/
theorem checkNesting_reflects_outcome (tokens : List Token) :
    ∃ result,
      DeclarativeGrammar.NestingOutcome tokens result ∧
        checkNesting tokens = result.map nestingOverflowDiagnostic := by
  rcases DeclarativeGrammar.nestingOutcome_total tokens with
    clears | ⟨overflow, exceeds⟩
  · exact ⟨none, clears, checkNesting_eq_map_of_outcome clears⟩
  · exact ⟨some overflow, exceeds,
      checkNesting_eq_map_of_outcome exceeds⟩

/-- Executable success is equivalent to a clear declarative nesting scan. -/
theorem checkNesting_none_iff_nestingClears (tokens : List Token) :
    checkNesting tokens = none ↔
      DeclarativeGrammar.NestingClears tokens := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => exact outcome
    | some overflow => simp at equation
  · intro clears
    simpa using checkNesting_eq_map_of_outcome clears

/-- An executable diagnostic is exactly the mapped first declarative
overflow, including its span, dimension, and canonical bound. -/
theorem checkNesting_some_iff_nestingExceeds
    (tokens : List Token) (diagnostic : ParseDiagnostic) :
    checkNesting tokens = some diagnostic ↔
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow := by
  constructor
  · intro checked
    rcases checkNesting_reflects_outcome tokens with
      ⟨result, outcome, equation⟩
    rw [checked] at equation
    cases result with
    | none => simp at equation
    | some overflow =>
        exact ⟨overflow, outcome, Option.some.inj equation⟩
  · rintro ⟨overflow, exceeds, rfl⟩
    simpa using checkNesting_eq_map_of_outcome exceeds

/-- Package both ordinary executable nesting outcomes. -/
theorem checkNesting_ordinaryOutcome_sound (tokens : List Token) :
    (checkNesting tokens = none →
      DeclarativeGrammar.NestingClears tokens) ∧
    (∀ diagnostic, checkNesting tokens = some diagnostic →
      ∃ overflow,
        DeclarativeGrammar.NestingExceeds tokens overflow ∧
          diagnostic = nestingOverflowDiagnostic overflow) :=
  ⟨(checkNesting_none_iff_nestingClears tokens).mp,
    fun diagnostic =>
      (checkNesting_some_iff_nestingExceeds tokens diagnostic).mp⟩

end Solcore.Syntax.Parser
