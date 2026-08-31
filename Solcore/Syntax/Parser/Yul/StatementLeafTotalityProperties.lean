import Solcore.Syntax.Parser.Yul.StatementProperties
import Solcore.Syntax.Parser.Yul.ExpressionRecursiveTotalityProperties
import Solcore.Syntax.Parser.Yul.NamesTotalityProperties

/-! Valid-input totality for the non-recursive inline-Yul statements. -/

set_option autoImplicit false

namespace Solcore.Syntax.Parser

/-- Optional `let` initialization is ordinary on every valid input. -/
theorem yulLetInitializer_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulLetInitializer := by
  unfold yulLetInitializer
  apply Parser.bind_invariantFreeOnValid getState_validFor
    Parser.getState_invariantFreeOnValid
  intro observed
  by_cases present : isSymbol observed .colonEqual
  · simp only [present, if_true]
    apply Parser.bind_invariantFreeOnValid
      (symbol_validFor .colonEqual .yulStatement)
      (symbol_ordinary .colonEqual .yulStatement).invariantFreeOnValid
    intro marker
    apply Parser.bind_invariantFreeOnValid yulExpression_validFor
      yulExpression_invariantFreeOnValid
    intro expression
    exact Parser.pure_invariantFreeOnValid (some expression)
  · simp only [present]
    exact Parser.pure_invariantFreeOnValid none

theorem yulLetInitializer_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ initializer next,
      yulLetInitializer input = .ok initializer next) ∨
    (∃ failure next, yulLetInitializer input = .reject failure next) :=
  yulLetInitializer_invariantFreeOnValid input inputValid

theorem yulLetInitializer_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulLetInitializer input ≠ .invariant error :=
  yulLetInitializer_invariantFreeOnValid.ne_invariant input inputValid error

/-- A non-recursive Yul `let` statement is ordinary on valid input. -/
theorem yulLetStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulLetStatement := by
  unfold yulLetStatement
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .letKw .yulStatement)
    (keyword_ordinary .letKw .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid yulNames_validFor
    yulNames_invariantFreeOnValid
  intro names
  apply Parser.bind_invariantFreeOnValid yulLetInitializer_validFor
    yulLetInitializer_invariantFreeOnValid
  intro initializer
  exact Parser.pure_invariantFreeOnValid _

theorem yulLetStatement_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulLetStatement input = .ok statement next) ∨
    (∃ failure next, yulLetStatement input = .reject failure next) :=
  yulLetStatement_invariantFreeOnValid input inputValid

theorem yulLetStatement_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulLetStatement input ≠ .invariant error :=
  yulLetStatement_invariantFreeOnValid.ne_invariant input inputValid error

/-- A nonempty Yul assignment is ordinary on valid input. -/
theorem yulAssignment_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulAssignment := by
  unfold yulAssignment
  apply Parser.bind_invariantFreeOnValid yulNames_validFor
    yulNames_invariantFreeOnValid
  intro names
  apply Parser.bind_invariantFreeOnValid
    (symbol_validFor .colonEqual .yulStatement)
    (symbol_ordinary .colonEqual .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid yulExpression_validFor
    yulExpression_invariantFreeOnValid
  intro value
  exact Parser.pure_invariantFreeOnValid _

theorem yulAssignment_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulAssignment input = .ok statement next) ∨
    (∃ failure next, yulAssignment input = .reject failure next) :=
  yulAssignment_invariantFreeOnValid input inputValid

theorem yulAssignment_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulAssignment input ≠ .invariant error :=
  yulAssignment_invariantFreeOnValid.ne_invariant input inputValid error

/-- Lifting a Yul expression into statement position preserves totality. -/
theorem yulExpressionStatement_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulExpressionStatement := by
  unfold yulExpressionStatement
  apply Parser.bind_invariantFreeOnValid yulExpression_validFor
    yulExpression_invariantFreeOnValid
  intro expression
  exact Parser.pure_invariantFreeOnValid _

theorem yulExpressionStatement_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next,
      yulExpressionStatement input = .ok statement next) ∨
    (∃ failure next,
      yulExpressionStatement input = .reject failure next) :=
  yulExpressionStatement_invariantFreeOnValid input inputValid

theorem yulExpressionStatement_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulExpressionStatement input ≠ .invariant error :=
  yulExpressionStatement_invariantFreeOnValid.ne_invariant input inputValid
    error

private theorem yulReturnArguments_invariantFreeOnValid :
    Parser.InvariantFreeOnValid
      (delimited .leftParen .rightParen true yulExpression
        .yulExpression .yul) :=
  delimited_ordinary .leftParen .rightParen true yulExpression
    .yulExpression .yul yulExpression_elementTotalityContract

/-- Source-level `return(...)` is ordinary on valid input. -/
theorem yulReturnBuiltin_invariantFreeOnValid :
    Parser.InvariantFreeOnValid yulReturnBuiltin := by
  unfold yulReturnBuiltin
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor .returnKw .yulStatement)
    (keyword_ordinary .returnKw .yulStatement).invariantFreeOnValid
  intro marker
  apply Parser.bind_invariantFreeOnValid
    (delimited_validFor YulExpr.ValidFor .leftParen .rightParen true
      yulExpression .yulExpression .yul yulExpression_validFor
        yulExpression_preservesTokensOnSuccess)
    yulReturnArguments_invariantFreeOnValid
  intro arguments
  exact Parser.pure_invariantFreeOnValid _

theorem yulReturnBuiltin_ordinary (input : State)
    (inputValid : input.ValidFor) :
    (∃ statement next, yulReturnBuiltin input = .ok statement next) ∨
    (∃ failure next, yulReturnBuiltin input = .reject failure next) :=
  yulReturnBuiltin_invariantFreeOnValid input inputValid

theorem yulReturnBuiltin_ne_invariant (input : State)
    (inputValid : input.ValidFor) (error : ParserInvariantError) :
    yulReturnBuiltin input ≠ .invariant error :=
  yulReturnBuiltin_invariantFreeOnValid.ne_invariant input inputValid error

/-- Keyword-only control statements are ordinary on valid input. -/
theorem yulControlToken_invariantFreeOnValid (value : HardKeyword)
    (result : YulStmtValue) :
    Parser.InvariantFreeOnValid (yulControlToken value result) := by
  unfold yulControlToken
  apply Parser.bind_invariantFreeOnValid
    (keyword_validFor value .yulStatement)
    (keyword_ordinary value .yulStatement).invariantFreeOnValid
  intro marker
  exact Parser.pure_invariantFreeOnValid _

theorem yulControlToken_ordinary (value : HardKeyword)
    (result : YulStmtValue) (input : State) (inputValid : input.ValidFor) :
    (∃ statement next,
      yulControlToken value result input = .ok statement next) ∨
    (∃ failure next,
      yulControlToken value result input = .reject failure next) :=
  yulControlToken_invariantFreeOnValid value result input inputValid

theorem yulControlToken_ne_invariant (value : HardKeyword)
    (result : YulStmtValue) (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    yulControlToken value result input ≠ .invariant error :=
  (yulControlToken_invariantFreeOnValid value result).ne_invariant input
    inputValid error

/-- Syntax/state contracts paired with valid-input totality for Yul leaves. -/
structure YulStatementTotalityContract (parser : Parser YulStmt) : Prop
    extends YulStatementParserContracts parser where
  preservesTokenWindow : Parser.PreservesTokenWindow parser
  invariantFree : Parser.InvariantFreeOnValid parser

namespace YulStatementTotalityContract

theorem ne_invariant {parser : Parser YulStmt}
    (contract : YulStatementTotalityContract parser)
    (input : State) (inputValid : input.ValidFor)
    (error : ParserInvariantError) :
    parser input ≠ .invariant error :=
  contract.invariantFree.ne_invariant input inputValid error

end YulStatementTotalityContract

theorem yulLetStatement_totalityContract :
    YulStatementTotalityContract yulLetStatement := {
  toYulStatementParserContracts := {
    validFor := yulLetStatement_validFor
    preservesTokens := yulLetStatement_preservesTokensOnSuccess
    cursorMonotone := yulLetStatement_cursorMonotoneOnSuccess
    startsAtToken := yulLetStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulLetStatement_preservesTokenWindow
  invariantFree := yulLetStatement_invariantFreeOnValid
}

theorem yulAssignment_totalityContract :
    YulStatementTotalityContract yulAssignment := {
  toYulStatementParserContracts := {
    validFor := yulAssignment_validFor
    preservesTokens := yulAssignment_preservesTokensOnSuccess
    cursorMonotone := yulAssignment_cursorMonotoneOnSuccess
    startsAtToken := yulAssignment_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulAssignment_preservesTokenWindow
  invariantFree := yulAssignment_invariantFreeOnValid
}

theorem yulExpressionStatement_totalityContract :
    YulStatementTotalityContract yulExpressionStatement := {
  toYulStatementParserContracts := {
    validFor := yulExpressionStatement_validFor
    preservesTokens := yulExpressionStatement_preservesTokensOnSuccess
    cursorMonotone := yulExpressionStatement_cursorMonotoneOnSuccess
    startsAtToken := yulExpressionStatement_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulExpressionStatement_preservesTokenWindow
  invariantFree := yulExpressionStatement_invariantFreeOnValid
}

theorem yulReturnBuiltin_totalityContract :
    YulStatementTotalityContract yulReturnBuiltin := {
  toYulStatementParserContracts := {
    validFor := yulReturnBuiltin_validFor
    preservesTokens := yulReturnBuiltin_preservesTokensOnSuccess
    cursorMonotone := yulReturnBuiltin_cursorMonotoneOnSuccess
    startsAtToken := yulReturnBuiltin_startsAtCurrentTokenOnSuccess
  }
  preservesTokenWindow := yulReturnBuiltin_preservesTokenWindow
  invariantFree := yulReturnBuiltin_invariantFreeOnValid
}

theorem yulControlToken_totalityContract (value : HardKeyword)
    (result : YulStmtValue)
    (resultValid : ∀ file span, span.ValidFor file →
      YulStmt.ValidFor file { span, value := result }) :
    YulStatementTotalityContract (yulControlToken value result) := {
  toYulStatementParserContracts := {
    validFor := yulControlToken_validFor value result resultValid
    preservesTokens := yulControlToken_preservesTokensOnSuccess value result
    cursorMonotone := yulControlToken_cursorMonotoneOnSuccess value result
    startsAtToken := yulControlToken_startsAtCurrentTokenOnSuccess value result
  }
  preservesTokenWindow := yulControlToken_preservesTokenWindow value result
  invariantFree := yulControlToken_invariantFreeOnValid value result
}

end Solcore.Syntax.Parser
