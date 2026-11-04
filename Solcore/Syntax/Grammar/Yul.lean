import Solcore.Syntax.Grammar.Basics

/-!
Declarative grammar of Yul names, expressions and statements.

These are stated over abstract child relations. `Grammar/YulOrdinary` and
`Grammar/YulFuel`
tie the recursion. Main declarations: `YulNameOrdinaryParses`, `YulNamesOrdinaryParses`,
`YulExpressionRejects`, `YulStatementLayerOrdinaryParses`.
-/

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementOrdinaryRecoveryGrammar
/-!
Parser-independent ordinary outcomes for the outer recovering Yul-statement
layer.  The terminated core relations remain abstract so their recursive
outcomes can be supplied by one preceding fuel level.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming rejection boundary of one Yul statement layer. -/
inductive YulStatementRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      YulStatementRejects input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightBrace
      }) :
      YulStatementRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      YulStatementRejects input input

/-- Exact scan performed after statement recovery consumes its first token. -/
inductive YulStatementRecoveryScanParses (first : SourceSpan) :
    SourceSpan → Remainder → Syntax.YulStmt → Remainder → Prop where
  | stop {last : SourceSpan} {input : Remainder}
      (stops : YulStatementRejects input input) :
      YulStatementRecoveryScanParses first last input {
        span := SourceSpan.cover first last
        value := .error
      } input
  | next {last : SourceSpan} {input output : Remainder} {token : Token}
      {statement : Syntax.YulStmt}
      (continues : ¬ YulStatementRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (tail : YulStatementRecoveryScanParses first token.span
        { input with cursor := input.cursor + 1 } statement output) :
      YulStatementRecoveryScanParses first last input statement output

/-- Ordinary success of one outer recovering statement layer.

The rejected remainder of the terminated attempt is retained as evidence even
though the executable layer rewinds its cursor before starting recovery.
-/
inductive YulStatementLayerOrdinaryParses
    (terminatedOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (terminatedRejects : Remainder → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | terminated {input output : Remainder} {statement : Syntax.YulStmt}
      (parsed : terminatedOrdinary input statement output) :
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output
  | recovered {input failed output : Remainder} {token : Token}
      {statement : Syntax.YulStmt}
      (terminatedRejected : terminatedRejects input failed)
      (continues : ¬ YulStatementRejects input input)
      (current : TokenAt input.tokens input.endIndex input.cursor token)
      (scan : YulStatementRecoveryScanParses token.span token.span
        { input with cursor := input.cursor + 1 } statement output) :
      YulStatementLayerOrdinaryParses terminatedOrdinary terminatedRejects
        input statement output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionRejectionGrammar
/-!
Parser-independent binary rejection grammar for one inline-Yul expression.

The executable recovery layer rejects only at a recovery boundary or when an
active-window cursor has no corresponding array slot.  Every rejection is
non-consuming.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming rejection of one inline-Yul expression layer. -/
inductive YulExpressionRejects : Remainder → Remainder → Prop where
  | windowEnd {input : Remainder}
      (atEnd : input.endIndex ≤ input.cursor) :
      YulExpressionRejects input input
  | comma {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .comma
      }) :
      YulExpressionRejects input input
  | rightParen {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightParen
      }) :
      YulExpressionRejects input input
  | rightBrace {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .rightBrace
      }) :
      YulExpressionRejects input input
  | missingToken {input : Remainder}
      (inside : input.cursor < input.endIndex)
      (missing : input.tokens[input.cursor]? = none) :
      YulExpressionRejects input input

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeCoreYulStatementBasicGrammar
/-!
Parser-independent grammar for keyword-only Yul statements and optional
statement semicolons.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- One keyword-only inline-Yul control statement. -/
inductive YulControlTokenParses
    (keyword : HardKeyword) (statementValue : Syntax.YulStmtValue) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword keyword) input markerSpan
        output) :
      YulControlTokenParses keyword statementValue input {
        span := markerSpan
        value := statementValue
      } output

/-- Prioritized optional semicolon after an already parsed Yul statement. -/
inductive OptionalYulSemicolonParses :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | absent {input : Remainder} {value : Syntax.YulStmt}
      (semicolonAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .semicolon)) :
      OptionalYulSemicolonParses input value input
  | present {input output : Remainder} {value : Syntax.YulStmt}
      (semicolonSpan : SourceSpan)
      (semicolonParsed : ExactTokenParses (.symbol .semicolon) input
        semicolonSpan output) :
      OptionalYulSemicolonParses input value output

/-- One supplied non-terminating Yul statement followed by its maximal
optional semicolon. -/
def YulStatementTerminatedParses
    (coreParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (input : Remainder) (value : Syntax.YulStmt)
    (output : Remainder) : Prop :=
  ∃ afterCore,
    coreParses input value afterCore ∧
    OptionalYulSemicolonParses afterCore value output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionLeafGrammar
/-!
Parser-independent leaf grammar for inline-Yul expressions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact diagnostic-free grammar of one inline-Yul name.

The first three constructors are Yul-specific spellings.  The ordinary
identifier constructor records the checked identifier parser's sole
diagnostic boundary: a spelling containing `-` is accepted operationally but
is not a diagnostic-free grammar success.
-/
inductive YulNameParses :
    Remainder → Syntax.YulIdentifier → Remainder → Prop where
  | marked {input : Remainder} {span : SourceSpan} {text : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulIdentifier text
      }) :
      YulNameParses input {
        span
        value := text
      } { input with cursor := input.cursor + 1 }
  | underscore {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .underscore
      }) :
      YulNameParses input {
        span
        value := "_"
      } { input with cursor := input.cursor + 1 }
  | fallbackKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .fallbackKw
      }) :
      YulNameParses input {
        span
        value := "fallback"
      } { input with cursor := input.cursor + 1 }
  | identifier {input output : Remainder} {name : Syntax.YulIdentifier}
      (hyphenAbsent : name.value.toList.contains '-' = false)
      (parsed : IdentifierParses input name output) :
      YulNameParses input name output

/-- Exact grammar of one literal admitted by inline Yul. -/
inductive YulLiteralParses :
    Remainder → Syntax.YulLiteral → Remainder → Prop where
  | decimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .decimalLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .decimal spelling
      } { input with cursor := input.cursor + 1 }
  | hexadecimal {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .hexadecimalLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .hexadecimal spelling
      } { input with cursor := input.cursor + 1 }
  | string {input : Remainder} {span : SourceSpan} {spelling : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .stringLiteral spelling
      }) :
      YulLiteralParses input {
        span
        value := .string spelling
      } { input with cursor := input.cursor + 1 }
  | trueKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .trueKw
      }) :
      YulLiteralParses input {
        span
        value := .boolean true
      } { input with cursor := input.cursor + 1 }
  | falseKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .falseKw
      }) :
      YulLiteralParses input {
        span
        value := .boolean false
      } { input with cursor := input.cursor + 1 }

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulNamesGrammar
/-!
Parser-independent grammar for nonempty, non-trailing inline-Yul name
sequences.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact non-consuming result assembled by `finishYulNames`. -/
inductive FinishYulNamesParses
    (first last : Syntax.YulIdentifier) (tailRev : List Syntax.YulIdentifier) :
    Remainder → SourceSpan → NonemptyList Syntax.YulIdentifier →
      Remainder → Prop where
  | parsed {input : Remainder} :
      FinishYulNamesParses first last tailRev input
        (SourceSpan.cover first.span last.span) {
          head := first
          tail := tailRev.reverse
        } input

/-- Exact comma-prioritized tail of a Yul name sequence.

There is no trailing-comma constructor: after a comma, another strict
`YulNameParses` transition is required before recursion can continue.
-/
inductive YulNamesTailParses (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      SourceSpan → NonemptyList Syntax.YulIdentifier → Remainder →
        Prop where
  | done {input : Remainder} {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      {output : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma))
      (finished : FinishYulNamesParses first last tailRev input span names
        output) :
      YulNamesTailParses first input last tailRev span names output
  | next {input afterComma afterName output : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : ExactTokenParses (.symbol .comma) input commaSpan
        afterComma)
      (nameParsed : YulNameParses afterComma name afterName)
      (progress : afterComma.cursor < afterName.cursor)
      (tail : YulNamesTailParses first afterName name (name :: tailRev)
        span names output) :
      YulNamesTailParses first input last tailRev span names output

/-- Exact public grammar of one nonempty Yul name sequence. -/
inductive YulNamesParses :
    Remainder → SourceSpan → NonemptyList Syntax.YulIdentifier →
      Remainder → Prop where
  | parsed {input afterFirst output : Remainder}
      {first : Syntax.YulIdentifier}
      {span : SourceSpan} {names : NonemptyList Syntax.YulIdentifier}
      (firstParsed : YulNameParses input first afterFirst)
      (progress : input.cursor < afterFirst.cursor)
      (tail : YulNamesTailParses first afterFirst first [] span names output) :
      YulNamesParses input span names output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementBasicGrammar
/-!
Parser-independent grammar for the basic inline-Yul statement forms.

The grammar is parameterized by the public inline-Yul expression relation.
It retains the optional `:=` priority of `let`, the nonempty target sequence
of assignment, and the allow-empty/trailing-comma argument grammar of the
source-level `return(...)` builtin.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Prioritized optional initializer of an inline-Yul `let`. -/
inductive YulLetInitializerParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Option Syntax.YulExpr → Remainder → Prop where
  | absent {input : Remainder}
      (operatorAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .colonEqual)) :
      YulLetInitializerParses expressionParses input none input
  | present {input afterOperator output : Remainder}
      {value : Syntax.YulExpr} (operatorSpan : SourceSpan)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) input
        operatorSpan afterOperator)
      (valueParsed : expressionParses afterOperator value output) :
      YulLetInitializerParses expressionParses input (some value) output

/-- Final span selected for an inline-Yul `let`. -/
def yulLetEnd (namesSpan : SourceSpan)
    (initializer : Option Syntax.YulExpr) : SourceSpan :=
  initializer.map (fun value => value.span) |>.getD namesSpan

/-- Exact grammar of one inline-Yul `let` declaration. -/
inductive YulLetStatementParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterNames output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier}
      {initializer : Option Syntax.YulExpr}
      (markerSpan namesSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .letKw) input markerSpan
        afterMarker)
      (namesParsed : YulNamesParses afterMarker namesSpan names afterNames)
      (initializerParsed : YulLetInitializerParses expressionParses afterNames
        initializer output) :
      YulLetStatementParses expressionParses input {
        span := SourceSpan.cover markerSpan (yulLetEnd namesSpan initializer)
        value := .letDecl names initializer
      } output

/-- Exact grammar of one nonempty inline-Yul assignment. -/
inductive YulAssignmentParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterNames afterOperator output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier} {value : Syntax.YulExpr}
      (namesSpan operatorSpan : SourceSpan)
      (namesParsed : YulNamesParses input namesSpan names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueParsed : expressionParses afterOperator value output) :
      YulAssignmentParses expressionParses input {
        span := SourceSpan.cover namesSpan value.span
        value := .assign names value
      } output

/-- Exact lifting of one inline-Yul expression into statement position. -/
inductive YulExpressionStatementParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} {expression : Syntax.YulExpr}
      (expressionParsed : expressionParses input expression output) :
      YulExpressionStatementParses expressionParses input {
        span := expression.span
        value := .expression expression
      } output

/-- Exact grammar of source-level `return(...)` as a synthesized Yul call. -/
inductive YulReturnBuiltinParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .returnKw) input markerSpan
        afterMarker)
      (argumentsParsed : TrailingDelimitedListParses .leftParen .rightParen
        expressionParses afterMarker arguments output) :
      YulReturnBuiltinParses expressionParses input {
        span := SourceSpan.cover markerSpan arguments.span
        value := .expression {
          span := SourceSpan.cover markerSpan arguments.span
          value := .call { span := markerSpan, value := "return" } arguments
        }
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCorePriorityGrammar
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
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulNameOutcomeGrammar
/-!
Parser-independent ordinary outcomes for one Yul name and one nonempty Yul
name sequence.  Ordinary success retains diagnosed identifier spellings;
rejection records the exact rejected remainder.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact token-kind decision for ordinary Yul names. -/
def tokenKindStartsOrdinaryYulName : TokenKind → Bool
  | .identifier _
  | .yulIdentifier _
  | .symbol .underscore
  | .keyword .fallbackKw => true
  | _ => false

/-- One ordinary Yul-name success, including a diagnosed hyphenated ordinary
identifier. -/
inductive YulNameOrdinaryParses :
    Remainder → Syntax.YulIdentifier → Remainder → Prop where
  | marked {input : Remainder} {span : SourceSpan} {text : String}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .yulIdentifier text
      }) :
      YulNameOrdinaryParses input {
        span
        value := text
      } { input with cursor := input.cursor + 1 }
  | underscore {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .symbol .underscore
      }) :
      YulNameOrdinaryParses input {
        span
        value := "_"
      } { input with cursor := input.cursor + 1 }
  | fallbackKeyword {input : Remainder} {span : SourceSpan}
      (token : TokenAt input.tokens input.endIndex input.cursor {
        span
        value := .keyword .fallbackKw
      }) :
      YulNameOrdinaryParses input {
        span
        value := "fallback"
      } { input with cursor := input.cursor + 1 }
  | identifier {input output : Remainder} {name : Syntax.YulIdentifier}
      (parsed : IdentifierParses input name output) :
      YulNameOrdinaryParses input name output

/-- Exact binary rejection of one ordinary Yul name. -/
inductive YulNameRejects : Remainder → Remainder → Prop where
  | absent {input : Remainder}
      (noSuccess : ¬ ∃ name output,
        YulNameOrdinaryParses input name output) :
      YulNameRejects input input

/-- Parser-independent public value of a nonempty Yul name sequence. -/
structure YulNamesOrdinaryValue where
  span : SourceSpan
  names : NonemptyList Syntax.YulIdentifier

/-- Ordinary non-consuming assembly of a forward-order name sequence. -/
inductive FinishYulNamesOrdinaryParses
    (first last : Syntax.YulIdentifier)
    (tailRev : List Syntax.YulIdentifier) :
    Remainder → YulNamesOrdinaryValue → Remainder → Prop where
  | parsed {input : Remainder} :
      FinishYulNamesOrdinaryParses first last tailRev input {
        span := SourceSpan.cover first.span last.span
        names := { head := first, tail := tailRev.reverse }
      } input

/-- Comma-prioritized ordinary success after the first Yul name. -/
inductive YulNamesTailOrdinaryParses (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      YulNamesOrdinaryValue → Remainder → Prop where
  | done {input : Remainder} {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {value : YulNamesOrdinaryValue} {output : Remainder}
      (commaAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .comma))
      (finished : FinishYulNamesOrdinaryParses first last tailRev input value
        output) :
      YulNamesTailOrdinaryParses first input last tailRev value output
  | next {input afterName output : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      {value : YulNamesOrdinaryValue}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameParsed : YulNameOrdinaryParses
        { input with cursor := input.cursor + 1 } name afterName)
      (tail : YulNamesTailOrdinaryParses first afterName name
        (name :: tailRev) value output) :
      YulNamesTailOrdinaryParses first input last tailRev value output

/-- Ordinary success of one nonempty, non-trailing Yul name sequence. -/
inductive YulNamesOrdinaryParses :
    Remainder → YulNamesOrdinaryValue → Remainder → Prop where
  | parsed {input afterFirst output : Remainder}
      {first : Syntax.YulIdentifier} {value : YulNamesOrdinaryValue}
      (firstParsed : YulNameOrdinaryParses input first afterFirst)
      (tail : YulNamesTailOrdinaryParses first afterFirst first [] value
        output) :
      YulNamesOrdinaryParses input value output

/-- Exact ordinary rejection after a successfully parsed first Yul name. -/
inductive YulNamesTailRejects (first : Syntax.YulIdentifier) :
    Remainder → Syntax.YulIdentifier → List Syntax.YulIdentifier →
      Remainder → Prop where
  | commaNameRejected {input rejected : Remainder}
      {last : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameRejected : YulNameRejects
        { input with cursor := input.cursor + 1 } rejected) :
      YulNamesTailRejects first input last tailRev rejected
  | laterRejected {input afterName rejected : Remainder}
      {last name : Syntax.YulIdentifier}
      {tailRev : List Syntax.YulIdentifier}
      (commaSpan : SourceSpan)
      (commaToken : TokenAt input.tokens input.endIndex input.cursor {
        span := commaSpan
        value := .symbol .comma
      })
      (nameParsed : YulNameOrdinaryParses
        { input with cursor := input.cursor + 1 } name afterName)
      (tailRejected : YulNamesTailRejects first afterName name
        (name :: tailRev) rejected) :
      YulNamesTailRejects first input last tailRev rejected

/-- Exact binary rejection of the public nonempty Yul name sequence. -/
inductive YulNamesRejects : Remainder → Remainder → Prop where
  | firstRejected {input rejected : Remainder}
      (firstRejected : YulNameRejects input rejected) :
      YulNamesRejects input rejected
  | tailRejected {input afterFirst rejected : Remainder}
      {first : Syntax.YulIdentifier}
      (firstParsed : YulNameOrdinaryParses input first afterFirst)
      (tailRejected : YulNamesTailRejects first afterFirst first [] rejected) :
      YulNamesRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulAssignmentOutcomeGrammar
/-!
Executable-independent ordinary rejection of one transactional inline-Yul
assignment attempt.

The relation retains the exact rejected remainder.  Successful name prefixes
use the ordinary name-sequence grammar because they may already have emitted a
diagnostic before a later stage rejects and the caller rewinds the attempt.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact binary rejection of a transactional inline-Yul assignment. -/
inductive YulAssignmentRejects
    (expressionRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | namesRejected {input rejected : Remainder}
      (namesRejected : YulNamesRejects input rejected) :
      YulAssignmentRejects expressionRejects input rejected
  | operatorAbsent {input afterNames : Remainder}
      {names : YulNamesOrdinaryValue}
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorAbsent : TokenKindAbsentAt afterNames.tokens
        afterNames.endIndex afterNames.cursor (.symbol .colonEqual)) :
      YulAssignmentRejects expressionRejects input afterNames
  | expressionRejected
      {input afterNames afterOperator rejected : Remainder}
      {names : YulNamesOrdinaryValue}
      (operatorSpan : SourceSpan)
      (namesParsed : YulNamesOrdinaryParses input names afterNames)
      (operatorParsed : ExactTokenParses (.symbol .colonEqual) afterNames
        operatorSpan afterOperator)
      (valueRejected : expressionRejects afterOperator rejected) :
      YulAssignmentRejects expressionRejects input rejected

/-- Existential projection used by the transactional statement fallback. -/
def YulAssignmentFallbackRejects
    (expressionRejects : Remainder → Remainder → Prop)
    (input : Remainder) : Prop :=
  ∃ rejected, YulAssignmentRejects expressionRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulExpressionGrammar
/-!
Parser-independent ordered grammar for one inline-Yul expression layer.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact successful grammar of a parenthesized inline-Yul call argument list. -/
def YulCallArgumentsParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (input : Remainder) (arguments : DelimitedList Syntax.YulExpr)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen nestedParses input
    arguments output

/-- Parser-independent fallback semantics for transactional call arguments.

The disjointness law makes rejection evidence incompatible with any successful
argument-list derivation, so a fallback cannot also bypass a valid preferred
branch.
-/
structure YulCallArgumentsFallbackSpec
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop) where
  rejects : Remainder → Prop
  disjoint : ∀ input, rejects input →
    ¬ ∃ (arguments : DelimitedList Syntax.YulExpr) (output : Remainder),
      YulCallArgumentsParses nestedParses input arguments output

/-- Exact ordered outcomes of optional transactional Yul call arguments. -/
inductive OptionalYulCallArgumentsParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Option (DelimitedList Syntax.YulExpr) → Remainder → Prop where
  | absent {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftParen)) :
      OptionalYulCallArgumentsParses nestedParses fallback input none input
  | rewound {input : Remainder} (openingSpan : SourceSpan)
      (openingToken : TokenAt input.tokens input.endIndex input.cursor {
        span := openingSpan
        value := .symbol .leftParen
      })
      (attemptRejected : fallback.rejects input) :
      OptionalYulCallArgumentsParses nestedParses fallback input none input
  | present {input output : Remainder}
      {arguments : DelimitedList Syntax.YulExpr}
      (parsed : YulCallArgumentsParses nestedParses input arguments output) :
      OptionalYulCallArgumentsParses nestedParses fallback input
        (some arguments) output

/-- Inline-Yul literal tokens recognized by the first core-expression guard. -/
def YulLiteralStartsAt (input : Remainder) : Prop :=
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .decimalLiteral spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .hexadecimalLiteral spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .stringLiteral spelling
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .trueKw
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .falseKw
  }

/-- All token forms recognized by the inline-Yul name guard. -/
def YulNameStartsAt (input : Remainder) : Prop :=
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .identifier spelling
  }) ∨
  (∃ span spelling, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .yulIdentifier spelling
  }) ∨
  (∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .symbol .underscore
  }) ∨
  ∃ span, TokenAt input.tokens input.endIndex input.cursor {
    span
    value := .keyword .fallbackKw
  }

/-- Exact named-or-called inline-Yul expression grammar. -/
inductive YulNamedExpressionParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | identifier {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      (nameParsed : YulNameParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsParses nestedParses fallback
        afterName none output) :
      YulNamedExpressionParses nestedParses fallback input {
        span := name.span
        value := .identifier name
      } output
  | call {input afterName output : Remainder}
      {name : Syntax.YulIdentifier}
      {arguments : DelimitedList Syntax.YulExpr}
      (nameParsed : YulNameParses input name afterName)
      (argumentsParsed : OptionalYulCallArgumentsParses nestedParses fallback
        afterName (some arguments) output) :
      YulNamedExpressionParses nestedParses fallback input {
        span := SourceSpan.cover name.span arguments.span
        value := .call name arguments
      } output

/-- Diagnostic-free literal-before-name grammar of `yulExpressionCore`. -/
inductive YulExpressionCoreParses
    (nestedParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulCallArgumentsFallbackSpec nestedParses) :
    Remainder → Syntax.YulExpr → Remainder → Prop where
  | literal {input output : Remainder} {literal : Syntax.YulLiteral}
      (parsed : YulLiteralParses input literal output) :
      YulExpressionCoreParses nestedParses fallback input {
        span := literal.span
        value := .literal literal
      } output
  | named {input output : Remainder} {expression : Syntax.YulExpr}
      (literalAbsent : ¬ YulLiteralStartsAt input)
      (parsed : YulNamedExpressionParses nestedParses fallback input
        expression output) :
      YulExpressionCoreParses nestedParses fallback input expression output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBlockGrammar
/-!
Parser-independent grammar for braced Yul statement blocks.

The item grammar retains right-brace priority, excludes the missing-close
at-end path, requires strict statement progress, and returns statements in
source order.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact closing brace and covering span for an accumulated Yul block body. -/
inductive CloseYulBlockParses (openingSpan : SourceSpan)
    (body : List Syntax.YulStmt) :
    Remainder → SourceSpan → Remainder → Prop where
  | parsed {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) input
        closingSpan output) :
      CloseYulBlockParses openingSpan body input
        (SourceSpan.cover openingSpan closingSpan) output

/--
Forward-order Yul statements followed by their exact closing brace.  The
recursive branch records both preferred-close absence and non-end-of-window.
-/
inductive YulBlockItemsParses
    (statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (openingSpan : SourceSpan) :
    Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingParsed : ExactTokenParses (.symbol .rightBrace) input
        closingSpan output) :
      YulBlockItemsParses statementParses openingSpan input
        (SourceSpan.cover openingSpan closingSpan) [] output
  | next {input afterStatement output : Remainder}
      {bodySpan : SourceSpan} {statement : Syntax.YulStmt}
      {statements : List Syntax.YulStmt}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementParses input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tail : YulBlockItemsParses statementParses openingSpan afterStatement
        bodySpan statements output) :
      YulBlockItemsParses statementParses openingSpan input bodySpan
        (statement :: statements) output

/-- Exact opening brace, block span, forward body, and final remainder. -/
inductive YulBlockParses
    (statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → SourceSpan → List Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterOpening output : Remainder}
      {bodySpan : SourceSpan} {body : List Syntax.YulStmt}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (bodyParsed : YulBlockItemsParses statementParses openingSpan
        afterOpening bodySpan body output) :
      YulBlockParses statementParses input bodySpan body output

theorem CloseYulBlockParses.cursor_lt
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : CloseYulBlockParses openingSpan body input bodySpan output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      simp

theorem CloseYulBlockParses.output_window
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : CloseYulBlockParses openingSpan body input bodySpan output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩

theorem YulBlockItemsParses.cursor_lt
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementParses openingSpan input bodySpan
      body output) : input.cursor < output.cursor := by
  induction parsed with
  | close closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      simp
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      exact Nat.lt_trans progress inductionHypothesis

theorem YulBlockItemsParses.output_window
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {openingSpan bodySpan : SourceSpan} {body : List Syntax.YulStmt}
    {input output : Remainder}
    (parsed : YulBlockItemsParses statementParses openingSpan input bodySpan
      body output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  induction parsed with
  | close closingSpan closingParsed =>
      rcases closingParsed with ⟨_, rfl⟩
      exact ⟨rfl, rfl⟩
  | next notAtEnd closingAbsent statementParsed progress tail
      inductionHypothesis =>
      have step := statementWindow statementParsed
      exact ⟨inductionHypothesis.1.trans step.1,
        inductionHypothesis.2.trans step.2⟩

theorem YulBlockParses.cursor_lt
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementParses input bodySpan body output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      rcases openingParsed with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp) bodyParsed.cursor_lt

theorem YulBlockParses.output_window
    {statementParses :
      Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {bodySpan : SourceSpan}
    {body : List Syntax.YulStmt}
    (parsed : YulBlockParses statementParses input bodySpan body output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed openingSpan openingParsed bodyParsed =>
      rcases openingParsed with ⟨_, rfl⟩
      exact bodyParsed.output_window statementWindow

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulFunctionGrammar
/-!
Parser-independent grammar for inline-Yul function signatures and bodies.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Allow-empty, trailing-comma parameter grammar used by Yul functions. -/
def YulParametersParses (input : Remainder)
    (parameters : DelimitedList Syntax.YulIdentifier)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen YulNameParses input
    parameters output

/-- Exact arrow and nonempty return-name clause. -/
inductive YulReturnClauseParses :
    Remainder → Syntax.YulReturnClause → Remainder → Prop where
  | parsed {input afterArrow output : Remainder}
      {names : NonemptyList Syntax.YulIdentifier}
      (arrowSpan namesSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesParsed : YulNamesParses afterArrow namesSpan names output) :
      YulReturnClauseParses input {
        span := SourceSpan.cover arrowSpan namesSpan
        value := { arrow := arrowSpan, names }
      } output

/-- Prioritized optional function return-name clause. -/
inductive YulReturnsParses :
    Remainder → Option Syntax.YulReturnClause → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnsParses input none input
  | present {input output : Remainder} {clause : Syntax.YulReturnClause}
      (clauseParsed : YulReturnClauseParses input clause output) :
      YulReturnsParses input (some clause) output

/-- Exact function keyword, signature, returns, body, span, and AST. -/
inductive YulFunctionStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterName afterParameters afterReturns output :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameParses afterMarker name afterName)
      (parametersParsed : YulParametersParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsParses afterParameters returns afterReturns)
      (bodyParsed : YulBlockParses statementParses afterReturns bodySpan body
        output) :
      YulFunctionStatementParses statementParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .functionDef name parameters returns body
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulSwitchGrammar
/-!
Parser-independent grammar for inline-Yul switch arms and statements.

The case list is forward ordered and maximal at the first token that is not
`case`.  The optional default branch records the parser's keyword priority.
Only the diagnostic-free, nonempty switch result has a statement constructor.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact grammar of one `case literal { ... }` arm. -/
inductive YulCaseArmParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulCase → Remainder → Prop where
  | parsed {input afterMarker afterLiteral output : Remainder}
      {literal : Syntax.YulLiteral} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .caseKw) input markerSpan
        afterMarker)
      (literalParsed : YulLiteralParses afterMarker literal afterLiteral)
      (bodyParsed : YulBlockParses statementParses afterLiteral bodySpan body
        output) :
      YulCaseArmParses statementParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .arm literal body
      } output

/-- Forward, maximal sequence of switch cases. -/
inductive YulCaseListParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → List Syntax.YulCase → Remainder → Prop where
  | done {input : Remainder}
      (caseAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .caseKw)) :
      YulCaseListParses statementParses input [] input
  | next {input afterArm output : Remainder} {arm : Syntax.YulCase}
      {arms : List Syntax.YulCase}
      (armParsed : YulCaseArmParses statementParses input arm afterArm)
      (progress : input.cursor < afterArm.cursor)
      (tail : YulCaseListParses statementParses afterArm arms output) :
      YulCaseListParses statementParses input (arm :: arms) output

/-- Prioritized optional `default { ... }` branch.

The two optional indices stay aligned: both are absent, or both contain the
span and forward body of the same parsed block.
-/
inductive OptionalYulDefaultParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Option SourceSpan → Option (List Syntax.YulStmt) →
      Remainder → Prop where
  | absent {input : Remainder}
      (defaultAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.keyword .defaultKw)) :
      OptionalYulDefaultParses statementParses input none none input
  | present {input afterMarker output : Remainder}
      {body : List Syntax.YulStmt} (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .defaultKw) input markerSpan
        afterMarker)
      (bodyParsed : YulBlockParses statementParses afterMarker bodySpan body
        output) :
      OptionalYulDefaultParses statementParses input (some bodySpan)
        (some body) output

/-- Endpoint selection performed by the executable switch parser. -/
def yulSwitchEnd (scrutineeSpan : SourceSpan) (cases : List Syntax.YulCase)
    (defaultSpan : Option SourceSpan) : SourceSpan :=
  match defaultSpan with
  | some bodySpan => bodySpan
  | none => match cases.reverse with
    | last :: _ => last.span
    | [] => scrutineeSpan

/-- Exact diagnostic-free grammar of a nonempty inline-Yul switch. -/
inductive YulSwitchStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterScrutinee afterCases output : Remainder}
      {scrutinee : Syntax.YulExpr} {head : Syntax.YulCase}
      {tail : List Syntax.YulCase} {defaultSpan : Option SourceSpan}
      {defaultBody : Option (List Syntax.YulStmt)} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .switchKw) input markerSpan
        afterMarker)
      (scrutineeParsed : expressionParses afterMarker scrutinee
        afterScrutinee)
      (casesParsed : YulCaseListParses statementParses afterScrutinee
        (head :: tail) afterCases)
      (defaultParsed : OptionalYulDefaultParses statementParses afterCases
        defaultSpan defaultBody output) :
      YulSwitchStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan
          (yulSwitchEnd scrutinee.span (head :: tail) defaultSpan)
        value := .switch scrutinee { head, tail } defaultBody
      } output

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulBlockOutcomeGrammar
/-!
Parser-independent ordinary rejection traces for braced inline-Yul blocks.

Successful prefixes use a broad ordinary statement relation.  A failed item
retains its exact rejected remainder, while the block loop records closing
brace priority, the active-window boundary, and strict statement progress.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Ordinary block success is the existing exact block grammar instantiated
with an ordinary statement relation. -/
abbrev YulBlockOrdinaryParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop) :=
  YulBlockParses statementOrdinary

/-- Parser-independent value carrier for one parsed Yul block. -/
structure YulBlockValue where
  span : SourceSpan
  body : List Syntax.YulStmt
  deriving Repr

/-- Package the exact block grammar as a three-place outcome relation. -/
def YulBlockOutcomeParses
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (input : Remainder) (value : YulBlockValue)
    (output : Remainder) : Prop :=
  YulBlockOrdinaryParses statementOrdinary input value.span value.body output

/-- Exact rejection after a block opening brace has already been consumed. -/
inductive YulBlockItemsRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | missingClose {input : Remainder}
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (atEnd : input.endIndex ≤ input.cursor) :
      YulBlockItemsRejects statementOrdinary statementRejects input input
  | statementRejected {input rejected : Remainder}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (rejectedStatement : statementRejects input rejected) :
      YulBlockItemsRejects statementOrdinary statementRejects input rejected
  | laterRejected {input afterStatement rejected : Remainder}
      {statement : Syntax.YulStmt}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementOrdinary input statement afterStatement)
      (progress : input.cursor < afterStatement.cursor)
      (tailRejected : YulBlockItemsRejects statementOrdinary statementRejects
        afterStatement rejected) :
      YulBlockItemsRejects statementOrdinary statementRejects input rejected

/-- Exact rejection of a complete braced inline-Yul block. -/
inductive YulBlockRejects
    (statementOrdinary :
      Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | openingMissing {input : Remainder}
      (openingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .leftBrace)) :
      YulBlockRejects statementOrdinary statementRejects input input
  | itemsRejected {input afterOpening rejected : Remainder}
      (openingSpan : SourceSpan)
      (openingParsed : ExactTokenParses (.symbol .leftBrace) input
        openingSpan afterOpening)
      (itemsRejected : YulBlockItemsRejects statementOrdinary statementRejects
        afterOpening rejected) :
      YulBlockRejects statementOrdinary statementRejects input rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulFunctionOutcomeGrammar
/-!
Parser-independent ordinary successes and exact sequential rejection traces
for inline-Yul function definitions.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Diagnosed Yul names are retained in an allow-empty, trailing-comma
parameter list. -/
def YulParametersOrdinaryParses (input : Remainder)
    (parameters : DelimitedList Syntax.YulIdentifier)
    (output : Remainder) : Prop :=
  TrailingDelimitedListParses .leftParen .rightParen YulNameOrdinaryParses
    input parameters output

/-- Exact rejection of an ordinary Yul parameter-list attempt. -/
abbrev YulParametersRejects :=
  DelimitedListRejects .leftParen .rightParen true true
    YulNameOrdinaryParses YulNameRejects

/-- Ordinary arrow and nonempty return-name clause. -/
inductive YulReturnClauseOrdinaryParses :
    Remainder → Syntax.YulReturnClause → Remainder → Prop where
  | parsed {input afterArrow output : Remainder}
      {names : YulNamesOrdinaryValue} (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesParsed : YulNamesOrdinaryParses afterArrow names output) :
      YulReturnClauseOrdinaryParses input {
        span := SourceSpan.cover arrowSpan names.span
        value := { arrow := arrowSpan, names := names.names }
      } output

/-- Exact sequential rejection of a direct return-clause attempt. -/
inductive YulReturnClauseRejects : Remainder → Remainder → Prop where
  | arrowMissing {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnClauseRejects input input
  | namesRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesRejected : YulNamesRejects afterArrow rejected) :
      YulReturnClauseRejects input rejected

/-- Prioritized optional ordinary return-name clause. -/
inductive YulReturnsOrdinaryParses :
    Remainder → Option Syntax.YulReturnClause → Remainder → Prop where
  | absent {input : Remainder}
      (arrowAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.symbol .arrow)) :
      YulReturnsOrdinaryParses input none input
  | present {input output : Remainder} {clause : Syntax.YulReturnClause}
      (clauseParsed : YulReturnClauseOrdinaryParses input clause output) :
      YulReturnsOrdinaryParses input (some clause) output

/-- Optional returns reject only after the preferred arrow branch was taken. -/
inductive YulReturnsRejects : Remainder → Remainder → Prop where
  | namesRejected {input afterArrow rejected : Remainder}
      (arrowSpan : SourceSpan)
      (arrowParsed : ExactTokenParses (.symbol .arrow) input arrowSpan
        afterArrow)
      (namesRejected : YulNamesRejects afterArrow rejected) :
      YulReturnsRejects input rejected

/-- Exact ordinary function keyword, signature, returns, body, span, and AST. -/
inductive YulFunctionStatementOrdinaryParses
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterName afterParameters afterReturns output :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} {body : List Syntax.YulStmt}
      (markerSpan bodySpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsOrdinaryParses afterParameters returns
        afterReturns)
      (bodyParsed : YulBlockOrdinaryParses statementOrdinary afterReturns
        bodySpan body output) :
      YulFunctionStatementOrdinaryParses statementOrdinary input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .functionDef name parameters returns body
      } output

/-- Exact first-rejecting stage of an ordinary Yul function attempt. -/
inductive YulFunctionStatementRejects
    (statementOrdinary : Remainder → Syntax.YulStmt → Remainder → Prop)
    (statementRejects : Remainder → Remainder → Prop) :
    Remainder → Remainder → Prop where
  | markerMissing {input : Remainder}
      (markerAbsent : TokenKindAbsentAt input.tokens input.endIndex input.cursor
        (.keyword .functionKw)) :
      YulFunctionStatementRejects statementOrdinary statementRejects input input
  | nameRejected {input afterMarker rejected : Remainder}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameRejected : YulNameRejects afterMarker rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | parametersRejected {input afterMarker afterName rejected : Remainder}
      {name : Syntax.YulIdentifier} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersRejected : YulParametersRejects afterName rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | returnsRejected
      {input afterMarker afterName afterParameters rejected : Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsRejected : YulReturnsRejects afterParameters rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected
  | bodyRejected
      {input afterMarker afterName afterParameters afterReturns rejected :
        Remainder}
      {name : Syntax.YulIdentifier}
      {parameters : DelimitedList Syntax.YulIdentifier}
      {returns : Option Syntax.YulReturnClause} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .functionKw) input markerSpan
        afterMarker)
      (nameParsed : YulNameOrdinaryParses afterMarker name afterName)
      (parametersParsed : YulParametersOrdinaryParses afterName parameters
        afterParameters)
      (returnsParsed : YulReturnsOrdinaryParses afterParameters returns
        afterReturns)
      (bodyRejected : YulBlockRejects statementOrdinary statementRejects
        afterReturns rejected) :
      YulFunctionStatementRejects statementOrdinary statementRejects input
        rejected

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementControlGrammar
/-!
Parser-independent grammar for Yul block, `if`, and `for` statements.
-/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Lift one exact braced Yul block into statement position. -/
inductive YulBlockStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input output : Remainder} {bodySpan : SourceSpan}
      {body : List Syntax.YulStmt}
      (bodyParsed : YulBlockParses statementParses input bodySpan body
        output) :
      YulBlockStatementParses statementParses input {
        span := bodySpan
        value := .block body
      } output

/-- Exact keyword, condition, block, span, and AST of a Yul `if`. -/
inductive YulIfStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterCondition output : Remainder}
      {condition : Syntax.YulExpr} {bodySpan : SourceSpan}
      {body : List Syntax.YulStmt} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .ifKw) input markerSpan
        afterMarker)
      (conditionParsed : expressionParses afterMarker condition
        afterCondition)
      (bodyParsed : YulBlockParses statementParses afterCondition bodySpan
        body output) :
      YulIfStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .ifThen condition body
      } output

/-- Exact source-order blocks, condition, spans, and AST of a Yul `for`. -/
inductive YulForStatementParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | parsed {input afterMarker afterInitializer afterCondition afterPost
        output : Remainder}
      {initializerSpan postSpan bodySpan : SourceSpan}
      {initializer post body : List Syntax.YulStmt}
      {condition : Syntax.YulExpr} (markerSpan : SourceSpan)
      (markerParsed : ExactTokenParses (.keyword .forKw) input markerSpan
        afterMarker)
      (initializerParsed : YulBlockParses statementParses afterMarker
        initializerSpan initializer afterInitializer)
      (conditionParsed : expressionParses afterInitializer condition
        afterCondition)
      (postParsed : YulBlockParses statementParses afterCondition postSpan
        post afterPost)
      (bodyParsed : YulBlockParses statementParses afterPost bodySpan body
        output) :
      YulForStatementParses statementParses expressionParses input {
        span := SourceSpan.cover markerSpan bodySpan
        value := .forLoop initializer condition post body
      } output

theorem YulBlockStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementParses input statement output) :
    input.cursor < output.cursor := by
  cases parsed with
  | parsed bodyParsed => exact bodyParsed.cursor_lt

theorem YulBlockStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulBlockStatementParses statementParses input statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed bodyParsed => exact bodyParsed.output_window statementWindow

theorem YulIfStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (expressionCursor : ∀ {input expression output},
      expressionParses input expression output →
        input.cursor ≤ output.cursor)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementParses expressionParses input
      statement output) : input.cursor < output.cursor := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      exact Nat.lt_trans (by simp)
        (Nat.lt_of_le_of_lt (expressionCursor conditionParsed)
          bodyParsed.cursor_lt)

theorem YulIfStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    (expressionWindow : ∀ {input expression output},
      expressionParses input expression output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulIfStatementParses statementParses expressionParses input
      statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed markerSpan markerParsed conditionParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have conditionWindow := expressionWindow conditionParsed
      have blockWindow := bodyParsed.output_window statementWindow
      exact ⟨blockWindow.1.trans conditionWindow.1,
        blockWindow.2.trans conditionWindow.2⟩

theorem YulForStatementParses.cursor_lt
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (expressionCursor : ∀ {input expression output},
      expressionParses input expression output →
        input.cursor ≤ output.cursor)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementParses expressionParses input
      statement output) : input.cursor < output.cursor := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have markerProgress : input.cursor <
          ({ input with cursor := input.cursor + 1 } : Remainder).cursor := by
        simp
      have throughInitializer := Nat.lt_trans markerProgress
        initializerParsed.cursor_lt
      have throughCondition := Nat.lt_of_lt_of_le throughInitializer
        (expressionCursor conditionParsed)
      exact Nat.lt_trans (Nat.lt_trans throughCondition postParsed.cursor_lt)
        bodyParsed.cursor_lt

theorem YulForStatementParses.output_window
    {statementParses : Remainder → Syntax.YulStmt → Remainder → Prop}
    {expressionParses :
      Remainder → Syntax.YulExpr → Remainder → Prop}
    (statementWindow : ∀ {input statement output},
      statementParses input statement output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    (expressionWindow : ∀ {input expression output},
      expressionParses input expression output →
        output.tokens = input.tokens ∧ output.endIndex = input.endIndex)
    {input output : Remainder} {statement : Syntax.YulStmt}
    (parsed : YulForStatementParses statementParses expressionParses input
      statement output) :
    output.tokens = input.tokens ∧ output.endIndex = input.endIndex := by
  cases parsed with
  | parsed markerSpan markerParsed initializerParsed conditionParsed
      postParsed bodyParsed =>
      rcases markerParsed with ⟨_, rfl⟩
      have initializerWindow := initializerParsed.output_window statementWindow
      have conditionWindow := expressionWindow conditionParsed
      have postWindow := postParsed.output_window statementWindow
      have bodyWindow := bodyParsed.output_window statementWindow
      exact ⟨bodyWindow.1.trans (postWindow.1.trans
          (conditionWindow.1.trans initializerWindow.1)),
        bodyWindow.2.trans (postWindow.2.trans
          (conditionWindow.2.trans initializerWindow.2))⟩

end Solcore.Syntax.DeclarativeGrammar
end

section
-- leanmerge: from Solcore.Syntax.DeclarativeYulStatementCoreGrammar
/-! Exact parser-independent grammar for the public Yul statement layers. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Exact outcomes of the transactional name-start assignment choice. -/
inductive YulNameStatementChoiceParses
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | assignment {input output : Remainder} {value : Syntax.YulStmt}
      (nameStart : YulNameStartAt input)
      (parsed : YulAssignmentParses expressionParses input value output) :
      YulNameStatementChoiceParses expressionParses fallback input value output
  | rewound {input output : Remainder} {value : Syntax.YulStmt}
      (nameStart : YulNameStartAt input)
      (assignmentRejected : fallback.rejects input)
      (parsed : YulExpressionStatementParses expressionParses input value
        output) :
      YulNameStatementChoiceParses expressionParses fallback input value output

/-- Exact clean grammar of the complete ordered `yulStatementCore`. -/
inductive YulStatementCoreParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :
    Remainder → Syntax.YulStmt → Remainder → Prop where
  | block {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .blockGuard)
      (parsed : YulBlockStatementParses statementParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | letDecl {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .letGuard)
      (parsed : YulLetStatementParses expressionParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | ifThen {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .ifGuard)
      (parsed : YulIfStatementParses statementParses expressionParses input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | forLoop {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .forGuard)
      (parsed : YulForStatementParses statementParses expressionParses input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | switch {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .switchGuard)
      (parsed : YulSwitchStatementParses statementParses expressionParses
        input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | functionDef {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .functionGuard)
      (parsed : YulFunctionStatementParses statementParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | returnBuiltin {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .returnGuard)
      (parsed : YulReturnBuiltinParses expressionParses input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | leave {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .leaveGuard)
      (parsed : YulControlTokenParses .leaveKw .leave input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | break {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .breakGuard)
      (parsed : YulControlTokenParses .breakKw .break input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | continue {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .continueGuard)
      (parsed : YulControlTokenParses .continueKw .continue input value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | nameChoice {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .nameGuard)
      (parsed : YulNameStatementChoiceParses expressionParses fallback input
        value output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output
  | expressionFallback {input output} {value : Syntax.YulStmt}
      (priority : YulStatementCorePrefixAbsent input .fallback)
      (parsed : YulExpressionStatementParses expressionParses input value
        output) :
      YulStatementCoreParses statementParses expressionParses fallback input
        value output

/-- One exact core statement followed by its maximal optional semicolon. -/
def YulStatementTerminatedLayerParses
    (statementParses : Remainder → Syntax.YulStmt → Remainder → Prop)
    (expressionParses : Remainder → Syntax.YulExpr → Remainder → Prop)
    (fallback : YulAssignmentFallbackSpec expressionParses) :=
  YulStatementTerminatedParses
    (YulStatementCoreParses statementParses expressionParses fallback)

/-- Clean recovery-layer success is exactly an unchanged terminated success. -/
abbrev YulStatementLayerParses := YulStatementTerminatedLayerParses

end Solcore.Syntax.DeclarativeGrammar
end
