import Solcore.Syntax.DeclarativeYulStatementBasicGrammar

/-! Parser-independent priority evidence for the Yul statement dispatcher. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- The token-kind decision implemented by `startsYulName`. -/
def tokenKindStartsYulName : TokenKind → Bool
  | .identifier _
  | .yulIdentifier _
  | .symbol .underscore
  | .keyword .fallbackKw => true
  | _ => false

/-- An exact current token accepted by the Yul-name lookahead. -/
def YulNameStartAt (input : Remainder) : Prop :=
  ∃ token,
    TokenAt input.tokens input.endIndex input.cursor token ∧
      tokenKindStartsYulName token.value = true

/-- Exact absence of every token kind accepted by Yul-name lookahead. -/
def YulNameStartAbsentAt (input : Remainder) : Prop :=
  ¬ YulNameStartAt input

/--
Exact abstract evidence for the transactional assignment rejection path.
Disjointness prevents the fallback predicate from overlapping a clean
assignment derivation.
-/
structure YulAssignmentFallbackSpec
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) where
  rejects : Remainder → Prop
  disjoint : ∀ input, rejects input →
    ¬ ∃ statement output,
      YulAssignmentParses expressionParses input statement output

/-- Ordered decision points in `yulStatementCore`. -/
inductive YulStatementCoreStage where
  | blockGuard
  | letGuard
  | ifGuard
  | forGuard
  | switchGuard
  | functionGuard
  | returnGuard
  | leaveGuard
  | breakGuard
  | continueGuard
  | nameGuard
  | fallback

/-- Every executable guard before the indexed stage is exactly absent. -/
inductive YulStatementCorePrefixAbsent (input : Remainder) :
    YulStatementCoreStage → Prop where
  | start : YulStatementCorePrefixAbsent input .blockGuard
  | afterBlock
      (prior : YulStatementCorePrefixAbsent input .blockGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .leftBrace)) :
      YulStatementCorePrefixAbsent input .letGuard
  | afterLet
      (prior : YulStatementCorePrefixAbsent input .letGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .letKw)) :
      YulStatementCorePrefixAbsent input .ifGuard
  | afterIf
      (prior : YulStatementCorePrefixAbsent input .ifGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .ifKw)) :
      YulStatementCorePrefixAbsent input .forGuard
  | afterFor
      (prior : YulStatementCorePrefixAbsent input .forGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .forKw)) :
      YulStatementCorePrefixAbsent input .switchGuard
  | afterSwitch
      (prior : YulStatementCorePrefixAbsent input .switchGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .switchKw)) :
      YulStatementCorePrefixAbsent input .functionGuard
  | afterFunction
      (prior : YulStatementCorePrefixAbsent input .functionGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw)) :
      YulStatementCorePrefixAbsent input .returnGuard
  | afterReturn
      (prior : YulStatementCorePrefixAbsent input .returnGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .returnKw)) :
      YulStatementCorePrefixAbsent input .leaveGuard
  | afterLeave
      (prior : YulStatementCorePrefixAbsent input .leaveGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .leaveKw)) :
      YulStatementCorePrefixAbsent input .breakGuard
  | afterBreak
      (prior : YulStatementCorePrefixAbsent input .breakGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .breakKw)) :
      YulStatementCorePrefixAbsent input .continueGuard
  | afterContinue
      (prior : YulStatementCorePrefixAbsent input .continueGuard)
      (absent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .continueKw)) :
      YulStatementCorePrefixAbsent input .nameGuard
  | afterName
      (prior : YulStatementCorePrefixAbsent input .nameGuard)
      (absent : YulNameStartAbsentAt input) :
      YulStatementCorePrefixAbsent input .fallback

end Solcore.Syntax.DeclarativeGrammar
