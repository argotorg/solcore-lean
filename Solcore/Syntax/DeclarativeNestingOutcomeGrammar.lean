import Solcore.Syntax.Declaration

/-!
Parser-independent exact outcomes for the bounded nesting preflight. The
relation scans tokens in source order and returns the first delimiter or
conditional overflow without exposing the executable scanner state.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Stable nesting limit of the canonical source grammar. -/
def canonicalNestingLimit : Nat := 128

/-- Declarative nesting context carried between source-order tokens. -/
structure NestingContext where
  delimiterDepth : Nat := 0
  conditionalDepth : Nat := 0
  conditionalBases : List Nat := []
  deriving Repr, BEq, DecidableEq

/-- Declarative recursive dimension checked by the nesting preflight. -/
inductive NestingDimension where
  | delimiter
  | conditional
  deriving Repr, BEq, DecidableEq

/-- Exact first token and bound of one declarative nesting overflow. -/
structure NestingOverflow where
  span : SourceSpan
  dimension : NestingDimension
  limit : Nat
  deriving Repr, BEq, DecidableEq

/-- Grammar-relevant effect of one token on bounded nesting. -/
inductive NestingAction where
  | conditional
  | groupOpen
  | blockOpen
  | close
  | reset
  | preserve
  deriving Repr, BEq, DecidableEq

/-- Classify one token by its declarative nesting effect. -/
def nestingAction : TokenKind → NestingAction
  | .keyword .ifKw => .conditional
  | .symbol .leftParen | .symbol .leftBracket => .groupOpen
  | .symbol .leftBrace => .blockOpen
  | .symbol .rightParen | .symbol .rightBracket |
      .symbol .rightBrace => .close
  | .symbol .comma | .symbol .semicolon => .reset
  | _ => .preserve

/-- Closing a delimiter restores the conditional base of its outer scope. -/
def NestingContext.closeDelimiter
    (context : NestingContext) : NestingContext := {
  delimiterDepth := context.delimiterDepth - 1
  conditionalDepth := context.conditionalBases.head?.getD 0
  conditionalBases := context.conditionalBases.tail
}

/-- A comma or semicolon restarts conditionals at the current scope base. -/
def NestingContext.resetConditional
    (context : NestingContext) : NestingContext := {
  context with
  conditionalDepth := context.conditionalBases.head?.getD 0
}

/-- Exact overflow generated at the first token beyond one bound. -/
def nestingOverflow (limit : Nat) (dimension : NestingDimension)
    (token : Token) : NestingOverflow := {
  span := token.span
  dimension
  limit
}

/-- Priority-ordered bounded nesting scan. Each continuation consumes exactly
one token; an exceeded constructor stops at the first overflowing token. -/
inductive NestingScans (limit : Nat) :
    NestingContext → List Token → Option NestingOverflow → Prop where
  | done {context : NestingContext} :
      NestingScans limit context [] none
  | conditionalExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .conditional)
      (exceeds : limit < context.conditionalDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .conditional token))
  | conditionalContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .conditional)
      (within : context.conditionalDepth + 1 ≤ limit)
      (tail : NestingScans limit
        { context with conditionalDepth := context.conditionalDepth + 1 }
        rest result) :
      NestingScans limit context (token :: rest) result
  | groupExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .groupOpen)
      (exceeds : limit < context.delimiterDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .delimiter token))
  | groupContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .groupOpen)
      (within : context.delimiterDepth + 1 ≤ limit)
      (tail : NestingScans limit {
        delimiterDepth := context.delimiterDepth + 1
        conditionalDepth := context.conditionalDepth
        conditionalBases := context.conditionalDepth ::
          context.conditionalBases
      } rest result) :
      NestingScans limit context (token :: rest) result
  | blockExceeded {context : NestingContext} {token : Token}
      {rest : List Token}
      (action : nestingAction token.value = .blockOpen)
      (exceeds : limit < context.delimiterDepth + 1) :
      NestingScans limit context (token :: rest)
        (some (nestingOverflow limit .delimiter token))
  | blockContinues {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .blockOpen)
      (within : context.delimiterDepth + 1 ≤ limit)
      (tail : NestingScans limit {
        delimiterDepth := context.delimiterDepth + 1
        conditionalDepth := 0
        conditionalBases := 0 :: context.conditionalBases
      } rest result) :
      NestingScans limit context (token :: rest) result
  | close {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .close)
      (tail : NestingScans limit context.closeDelimiter rest result) :
      NestingScans limit context (token :: rest) result
  | reset {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .reset)
      (tail : NestingScans limit context.resetConditional rest result) :
      NestingScans limit context (token :: rest) result
  | preserve {context : NestingContext} {token : Token}
      {rest : List Token} {result : Option NestingOverflow}
      (action : nestingAction token.value = .preserve)
      (tail : NestingScans limit context rest result) :
      NestingScans limit context (token :: rest) result

/-- Canonical whole-token nesting outcome from the root context. -/
def NestingOutcome (tokens : List Token)
    (result : Option NestingOverflow) : Prop :=
  NestingScans canonicalNestingLimit {} tokens result

/-- No token exceeds either canonical nesting bound. -/
def NestingClears (tokens : List Token) : Prop :=
  NestingOutcome tokens none

/-- Exact first canonical nesting violation. -/
def NestingExceeds (tokens : List Token)
    (overflow : NestingOverflow) : Prop :=
  NestingOutcome tokens (some overflow)

end Solcore.Syntax.DeclarativeGrammar
