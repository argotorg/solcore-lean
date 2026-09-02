import Solcore.Syntax.Lexer.Contract
import Solcore.Syntax.Parser.Diagnostic

/-! Bounded nesting preflight for the canonical syntax parser. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical parser guard applied before recursive token grammar. -/
def maxSyntaxNesting : Nat := 128

private structure NestingState where
  delimiterDepth : Nat := 0
  conditionalDepth : Nat := 0
  conditionalBases : List Nat := []

private def nestingError (kind : NestingKind)
    (token : Token) : ParseDiagnostic := {
  span := token.span
  kind := .nestingExceeded kind maxSyntaxNesting
}

private def closeDelimiter (state : NestingState) : NestingState := {
  delimiterDepth := state.delimiterDepth - 1
  conditionalDepth := state.conditionalBases.head?.getD 0
  conditionalBases := state.conditionalBases.tail
}

private def resetConditional (state : NestingState) : NestingState := {
  state with
  conditionalDepth := state.conditionalBases.head?.getD 0
}

private def checkNestingAux :
    NestingState → List Token → Option ParseDiagnostic
  | _, [] => none
  | state, token :: rest =>
      match token.value with
      | .keyword .ifKw =>
          let depth := state.conditionalDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .conditional token)
          else
            checkNestingAux { state with conditionalDepth := depth } rest
      | .symbol .leftParen | .symbol .leftBracket =>
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
      | .symbol .leftBrace =>
          let depth := state.delimiterDepth + 1
          if depth > maxSyntaxNesting then
            some (nestingError .delimiter token)
          else
            checkNestingAux {
              delimiterDepth := depth
              conditionalDepth := 0
              conditionalBases := 0 :: state.conditionalBases
            } rest
      | .symbol .rightParen | .symbol .rightBracket |
          .symbol .rightBrace =>
            checkNestingAux (closeDelimiter state) rest
      | .symbol .comma | .symbol .semicolon =>
          checkNestingAux (resetConditional state) rest
      | _ => checkNestingAux state rest

/-- First delimiter or conditional nesting violation, if one exists. -/
def checkNesting (tokens : List Token) : Option ParseDiagnostic :=
  checkNestingAux {} tokens

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
      cases kind : token.value with
      | keyword keyword =>
          cases keyword <;> simp only [checkNestingAux, kind] at result
          all_goals first
            | (split at result
               · cases result
                 exact tokenValid
               · exact inductionHypothesis _ restValid result)
            | exact inductionHypothesis _ restValid result
      | symbol symbol =>
          cases symbol <;> simp only [checkNestingAux, kind] at result
          all_goals first
            | (split at result
               · cases result
                 exact tokenValid
               · exact inductionHypothesis _ restValid result)
            | exact inductionHypothesis _ restValid result
      | identifier text =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | yulIdentifier text =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | decimalLiteral spelling =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | hexadecimalLiteral spelling =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | stringLiteral spelling =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | yulMetaBacktick spelling =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)
      | yulMetaInterpolation spelling =>
          exact inductionHypothesis _ restValid (by
            simpa only [checkNestingAux, kind] using result)

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
