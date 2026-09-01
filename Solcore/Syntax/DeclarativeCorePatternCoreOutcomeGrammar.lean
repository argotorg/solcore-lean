import Solcore.Syntax.DeclarativeCoreIdentifierOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreLiteralOutcomeGrammar
import Solcore.Syntax.DeclarativeCorePatternGrammar
import Solcore.Syntax.DeclarativeDelimitedOutcomeGrammar

/-!
Generic parser-independent ordinary outcomes for the ordered `patternCore`
dispatcher.  The four recursive branches are parameters so their concrete
nested pattern and expression outcomes can be connected independently.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

abbrev WildcardPatternOrdinaryParses := WildcardPatternParses
abbrev LiteralPatternOrdinaryParses := LiteralPatternParses
abbrev BooleanBinderPatternOrdinaryParses := BooleanBinderPatternParses

/-- Exact non-consuming wildcard-leaf rejection. -/
inductive WildcardPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore)) :
      WildcardPatternRejects input input

/-- Exact non-consuming literal-pattern rejection. -/
inductive LiteralPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (literalAbsent : CoreLiteralAbsentAt input) :
      LiteralPatternRejects input input

/-- Neither Boolean hard keyword starts at this cursor. -/
def BooleanPatternAbsentAt (input : Remainder) : Prop :=
  TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .trueKw) ∧
    TokenKindAbsentAt input.tokens input.endIndex input.cursor
      (.keyword .falseKw)

/-- Exact non-consuming Boolean-binder rejection. -/
inductive BooleanBinderPatternRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder} (booleanAbsent : BooleanPatternAbsentAt input) :
      BooleanBinderPatternRejects input input

/-- The seven successful branches in executable priority order. -/
inductive PatternCoreBranch where
  | wildcard
  | literal
  | boolean
  | parenthesized
  | dotConstructor
  | comptime
  | qualified
  deriving DecidableEq

/-- Exact guard evidence selecting one ordered Core-pattern branch. -/
inductive PatternCoreBranchSelected : PatternCoreBranch → Remainder → Prop where
  | wildcard {input : Remainder} {span : SourceSpan}
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .underscore }) :
      PatternCoreBranchSelected .wildcard input
  | literal {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (starts : CoreLiteralStartsAt input) :
      PatternCoreBranchSelected .literal input
  | boolean {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (starts : BooleanPatternStartsAt input) :
      PatternCoreBranchSelected .boolean input
  | parenthesized {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .leftParen }) :
      PatternCoreBranchSelected .parenthesized input
  | dotConstructor {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .symbol .dot }) :
      PatternCoreBranchSelected .dotConstructor input
  | comptime {input : Remainder} {span : SourceSpan}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .identifier ContextualKeyword.comptime.spelling
      }) : PatternCoreBranchSelected .comptime input
  | qualified {input : Remainder} {span : SourceSpan} {text : String}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor
          (.identifier ContextualKeyword.comptime.spelling))
      (marker : TokenAt input.tokens input.endIndex input.cursor {
        span, value := .identifier text }) :
      PatternCoreBranchSelected .qualified input

/-- Successful payload of the selected branch. -/
inductive PatternCoreBranchOrdinaryParses
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    PatternCoreBranch → Remainder → Syntax.Pattern → Remainder → Prop where
  | wildcard {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : WildcardPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .wildcard
          input pattern output
  | literal {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : LiteralPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .literal
          input pattern output
  | boolean {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : BooleanBinderPatternOrdinaryParses input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .boolean
          input pattern output
  | parenthesized {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : parenthesizedOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
          .parenthesized input pattern output
  | dotConstructor {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : dotConstructorOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary
          .dotConstructor input pattern output
  | comptime {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : comptimeOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .comptime
          input pattern output
  | qualified {input output : Remainder} {pattern : Syntax.Pattern}
      (parsed : qualifiedOrdinary input pattern output) :
      PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary .qualified
          input pattern output

/-- Exact selected ordinary success of the ordered dispatcher. -/
inductive PatternCoreOrdinaryParses
    (parenthesizedOrdinary dotConstructorOrdinary comptimeOrdinary
      qualifiedOrdinary : Remainder → Syntax.Pattern → Remainder → Prop) :
    Remainder → Syntax.Pattern → Remainder → Prop where
  | selected {branch : PatternCoreBranch} {input output : Remainder}
      {pattern : Syntax.Pattern}
      (selection : PatternCoreBranchSelected branch input)
      (parsed : PatternCoreBranchOrdinaryParses parenthesizedOrdinary
        dotConstructorOrdinary comptimeOrdinary qualifiedOrdinary branch input
          pattern output) :
      PatternCoreOrdinaryParses parenthesizedOrdinary dotConstructorOrdinary
        comptimeOrdinary qualifiedOrdinary input pattern output

/-- Rejection payload of one of the four fallible selected branches. -/
inductive PatternCoreBranchRejects
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop) :
    PatternCoreBranch → Remainder → Remainder → Prop where
  | parenthesized {input rejected : Remainder}
      (branchRejected : parenthesizedRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .parenthesized input rejected
  | dotConstructor {input rejected : Remainder}
      (branchRejected : dotConstructorRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .dotConstructor input rejected
  | comptime {input rejected : Remainder}
      (branchRejected : comptimeRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .comptime input rejected
  | qualified {input rejected : Remainder}
      (branchRejected : qualifiedRejects input rejected) :
      PatternCoreBranchRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects .qualified input rejected

/-- Exact final non-consuming dispatcher rejection. -/
inductive PatternCoreFinalRejects : Remainder → Remainder → Prop where
  | final {input : Remainder}
      (underscoreAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .underscore))
      (literalAbsent : ¬ CoreLiteralStartsAt input)
      (booleanAbsent : ¬ BooleanPatternStartsAt input)
      (leftParenAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen))
      (dotAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .dot))
      (comptimeAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.identifier ContextualKeyword.comptime.spelling))
      (identifierAbsent : IdentifierAbsentAt input) :
      PatternCoreFinalRejects input input

/-- Exact selected or final rejection of the ordered dispatcher. -/
inductive PatternCoreRejects
    (parenthesizedRejects dotConstructorRejects comptimeRejects
      qualifiedRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | selected {branch : PatternCoreBranch} {input rejected : Remainder}
      (selection : PatternCoreBranchSelected branch input)
      (branchRejected : PatternCoreBranchRejects parenthesizedRejects
        dotConstructorRejects comptimeRejects qualifiedRejects branch input
          rejected) :
      PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects input rejected
  | final {input : Remainder}
      (rejected : PatternCoreFinalRejects input input) :
      PatternCoreRejects parenthesizedRejects dotConstructorRejects
        comptimeRejects qualifiedRejects input input

end Solcore.Syntax.DeclarativeGrammar
