import Solcore.Syntax.DeclarativeCoreBlockOutcomeGrammar
import Solcore.Syntax.DeclarativeCoreBlockTailTraceGrammar

/-! Independent successful raw Core blocks with exact diagnostic sequences.
Statement events follow source order. Tail-validation events are appended only
after the closing brace, not interleaved with individual statement events. -/

set_option autoImplicit false

namespace Solcore.Syntax.DeclarativeGrammar

/-- Successful statements followed by the preferred exact closing brace.
Source and byte-window context are shared by every abstract statement judgment. -/
inductive CoreBlockItemsTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (source : SourceId) (endByte : Nat) :
    Remainder → List Syntax.Statement → SourceSpan → Remainder →
      List ParseDiagnostic → Prop where
  | close {input output : Remainder} (closingSpan : SourceSpan)
      (closingToken : ExactTokenParses (.symbol .rightBrace) input closingSpan output) :
      CoreBlockItemsTraceParses statementTrace source endByte input [] closingSpan output []
  | next {input afterStatement output : Remainder}
      {statement : Syntax.Statement} {statements : List Syntax.Statement}
      {closingSpan : SourceSpan} {statementEvents tailEvents : List ParseDiagnostic}
      (notAtEnd : input.cursor < input.endIndex)
      (closingAbsent : TokenKindAbsentAt input.tokens input.endIndex
        input.cursor (.symbol .rightBrace))
      (statementParsed : statementTrace source endByte input statement afterStatement statementEvents)
      (progress : input.cursor < afterStatement.cursor)
      (tail : CoreBlockItemsTraceParses statementTrace source endByte afterStatement
        statements closingSpan output tailEvents) :
      CoreBlockItemsTraceParses statementTrace source endByte input
        (statement :: statements) closingSpan output (statementEvents ++ tailEvents)

/-- The completed AST retains exact braces and written statement order. Only
then does policy-dependent tail validation append its complete ordered trace. -/
inductive CoreBlockTraceParses
    (statementTrace : SourceId → Nat → Remainder → Syntax.Statement →
      Remainder → List ParseDiagnostic → Prop)
    (policy : CoreBlockTailPolicy) (source : SourceId) (endByte : Nat) :
    Remainder → Syntax.Block → Remainder → List ParseDiagnostic → Prop where
  | parsed {input afterOpening output : Remainder}
      {statements : List Syntax.Statement} {statementEvents validationEvents : List ParseDiagnostic}
      (openingSpan closingSpan : SourceSpan)
      (openingToken : ExactTokenParses (.symbol .leftBrace) input openingSpan afterOpening)
      (bodyParsed : CoreBlockItemsTraceParses statementTrace source endByte afterOpening
        statements closingSpan output statementEvents)
      (validated : CoreBlockTailsDiagnosticTrace policy statements validationEvents) :
      CoreBlockTraceParses statementTrace policy source endByte input {
        span := SourceSpan.cover openingSpan closingSpan
        value := statements
      } output (statementEvents ++ validationEvents)

end Solcore.Syntax.DeclarativeGrammar
