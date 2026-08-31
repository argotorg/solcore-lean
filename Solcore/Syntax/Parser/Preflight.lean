import Solcore.Syntax.Parser.State

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Canonical parser guard applied before recursive token grammar. -/
def maxSyntaxNesting : Nat := 128

private def validateTokens (file : SourceFile) :
    Nat → Nat → List Token → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, token :: rest =>
      if token.span.isValidFor file &&
          previousEnd ≤ token.span.startByte &&
          token.span.startByte < token.span.endByte then
        validateTokens file (index + 1) token.span.endByte rest
      else
        .error (.invalidTokenSpan index token.span)

private def validateComments (file : SourceFile) :
    Nat → Nat → List Comment → Except ParserInvariantError Unit
  | _, _, [] => .ok ()
  | index, previousEnd, comment :: rest =>
      if comment.span.isValidFor file &&
          previousEnd ≤ comment.span.startByte &&
          comment.span.startByte < comment.span.endByte then
        validateComments file (index + 1) comment.span.endByte rest
      else
        .error (.invalidCommentSpan index comment.span)

private def validateLexicalDiagnostics (file : SourceFile) :
    Nat → List LexicalDiagnostic → Except ParserInvariantError Unit
  | _, [] => .ok ()
  | index, diagnostic :: rest =>
      if diagnostic.span.isValidFor file then
        validateLexicalDiagnostics file (index + 1) rest
      else
        .error (.invalidLexicalDiagnosticSpan index diagnostic.span)

/-- Validate all provenance consumed or retained by `parseLexed`. -/
def validateLexed (file : SourceFile)
    (lexed : LexedFile) : Except ParserInvariantError Unit := do
  if lexed.source != file.id then
    throw (.invalidLexedSource file.id lexed.source)
  validateTokens file 0 0 lexed.tokens
  validateComments file 0 0 lexed.comments
  validateLexicalDiagnostics file 0 lexed.diagnostics

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

end Solcore.Syntax.Parser
